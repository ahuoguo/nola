# Performance traps in this port

Four of these cost hours each, and three of them present as a *hang* rather
than an error, so they are worth recognising on sight.

Every build below was run under a watchdog that polls the combined RSS of
`rocq`/`coqc` and kills the process group past a limit — macOS honours
neither `ulimit -v` nor `ulimit -d`, so there is no cheaper guard.  Without
one, a single file took the machine down.

## 1. The `typeG` resolution cycle

**Symptom.**  A single `exists` against a goal mentioning `typed_body` ran to
9.1 GB over 25 minutes without finishing.  No error, no progress; memory
climbing steadily.

**Diagnosis.**  `Set Typeclasses Debug Verbosity 1` shows the path deepening
forever:

```
typeG ?FML ?Σ
  --eapply typeG_cif-->      verus_haltGS (cifOF verus_haltCON) ?Σ
     --apply type_verus_haltGS-->   typeG (cifOF verus_haltCON) ?Σ
        --eapply typeG_cif-->      verus_haltGS …
           …
```

`typing/type.v` declares

```coq
Class typeG (FML : oFunctor) Σ : Type := TypeG {
  #[global] type_verus_haltGS :: verus_haltGS FML Σ;
  …
}.
```

so every field is a projection instance, and `typing/model_inst.v`'s
`typeG_cif` is a global instance that *needs* an `verus_haltGS`.  Resolution can
therefore build a `typeG` out of a `typeG`, forever.

**What makes it fire.**  Only when no `verus_haltGS` is available in the local
context.  Writing the hypothesis with an *anonymous* binder,

```coq
(∀ _ : verus_haltGS (cifOF verus_haltCON) Σ, ⊢ typed_body … e tr) →
```

is enough: resolution does not use the anonymous hypothesis, so instead of
finding the `verus_haltGS` sitting right there it goes off to construct one.

**Fix**, both halves needed:

```coq
(* typing/model_inst.v, after the section *)
Global Hint Cut [ _* typeG_cif
  (type_verus_haltGS | type_verus_haltSem | type_heapSem | type_gsrcSem |
   type_typeFml | type_stBor | type_stBorSem | type_altSem) ]
  : typeclass_instances.
```

and **name the binder** (`∀ H : verus_haltGS …`).  After both, the same proof
elaborates in 16 MB, instantly.  Cutting the cycle does not affect finding an
`verus_haltGS` in the context, which is not an instance application.

**Is this a problem for Nola, or for upstream VerusBelt?**  No, and for the
same reason in both cases: neither ever builds the bundle by resolution.

* `nola/examples/rust_halt/base.v` declares `rust_haltGS` with the same
  `::` projection fields, but there is no instance anywhere that
  *constructs* a `rust_haltGS` — it is assumed through `Context` and built
  once, explicitly, inside `rust_wsat_alloc`.  `rust_halt` has no `typeG`-style
  bundling class at all; its typing rules take
  `` `{!rust_haltGS CON Σ, !rust_haltC CON, …} `` directly.
* Upstream VerusBelt declares `Class typeG Σ`, and its only construction is
  `set (Htype := TypeG Σ _ _ _ _ _ _ _)` *inside* the soundness proof — a
  local `set`, not a global instance.

The cycle appeared here only once the model became concrete and `typeG_cif`
was made a global instance (`af5aee0`).  **The rule:** a bundling class whose
fields are projection instances must not also have a global instance that
constructs it from one of those fields.  If it does, cut the path.

## 2. `apply` versus `refine`

`apply (type_soundness (CON := verus_haltCON) (JUDG := verus_haltJUDG Σ) e tr Htr)`
was a second, independent cost: `apply` elaborates its argument against the
goal with conversion heuristics that rebuild large terms.  `refine` of the
same term is instant.  Both concrete soundness theorems use `refine`.

Elaborating the *statement* — `Check (type_soundness (CON := verus_haltCON) …)` —
was always instant, which is what localised the cost to the tactic.

## 3. Rules stated with `of_val` cannot be applied to a program

`typing/programs.v`'s generic

```coq
Lemma type_val … : … -∗ typed_body E L I C T (let: xb := v in e)%E …
```

has a *value* `v` in its conclusion, so `iApply`ing it to a concrete program
asks unification to invert `of_val ?v` against a literal.  That diverges —
20 minutes at a flat 1.1 GB.  Each type's own rule (`int.v`'s `type_int`,
`bool.v`'s `type_bool`) puts the literal in the conclusion and applies
first-order.  Upstream's `typing/examples/` never applies `type_val` either.

The same holds of any rule stated with `of_val`, including `type_done` in
`typing/examples/basic.v`: pass the value explicitly, and `simpl_subst` after
each binder.

## 4. Size arguments must be passed, not unified

`own.v`'s `type_new` binds `let n' := Z.to_nat n in` and uses `n'` in the
continuation's type context, so leaving `n` to unification diverges —
`Timeout 60` on the `iApply` fails.  Passing it (`type_new 1 "b"`) is
instant, which is why upstream's `typing/examples/` passes the size to
`type_new_subtype`.

Related, and a cheap way to lose an hour: the `Closed` side conditions of
`type_new` and `type_delete` are discharged by type class resolution before
the goal brackets are reached, so a `solve_closed` branch lands on the
*next* goal and fails there with a misleading error.

## 5. Transformers must be built forward

Stating a `typed_body` goal with its predicate transformer already reduced
makes `iApply` solve for the continuation's transformer by higher-order
unification, which does not terminate.  Apply `typed_body_impl` first, let
the transformer be an evar solved forward, and discharge the implication at
the end — the idiom upstream's examples use.  Pin the innermost transformer
so the final goal is ground.

## 6. `solve_inG` does not scale to a `Σ` this size

`typing/level_ctx.v`'s `subG_verus_haltGpreS` was `Proof. solve_inG. Qed.` and
did not finish: a build left on it ran **over eight hours** on that one
command without completing, with an empty `-time-file`.  The explicit
proof now in its place takes **0.00s**, and the whole file 3.3s.

The cost is not where it looks.  `solve_inG`'s first three steps — unfold
the `Σ`, `repeat apply subG_inv`, turn singletons into `inG` — total
0.05s and leave a context of only twenty-one hypotheses, with
`subG (lrustΣ FML) Σ` among them.  Nor is it `simpl in *`.  It is the
last line,

```coq
split; (assumption || by apply _).
```

which hands each of the ten `verus_haltGpreS` fields to typeclass
resolution.  Nine of them come back at once.  The first,
`lrustGpreS FML Σ`, does not: `subG_lrustGpreS` is one `apply` away with
its premise sitting in the context, but the search does not find it by
that route, and what it does instead does not terminate in any practical
time.  Timing the fields one at a time is what localises this — `Time`
on `solve_inG` as a whole tells you nothing except that it is slow.

So discharge the fields **by name**:

```coq
intros H. unfold verus_haltΣ in H.
apply subG_inv in H as [Hlrust H]. (* ...one per entry... *)
split.
- by apply subG_lrustGpreS.
- by apply subG_lt_logicΣ.
  (* ... *)
- exact (subG_inG _ _ Hetern).
```

Two details.  Take the `subG` apart one entry at a time rather than with
`repeat`, so every entry has a name to be discharged by.  And a field
that is a bare `inG` rather than a class — here
`inG Σ (authUR (gsetUR lft))` — needs `subG_inG`'s functor argument
supplied, which `exact (subG_inG _ _ H)` does by unifying against the
hypothesis; `apply subG_inG` leaves it as an evar and fails.

Expect this of any `xΣ` that grows past a handful of entries, and note
that the failure arrives *late* and from a distance: the command that
stopped terminating here was not edited at all.  What changed was
`llft_logicΣ`, one entry down, which gained a `GFunctor` for the outlives
witness; `subG_verus_haltGpreS` is two levels above that and went from
compiling to not finishing.  A `solve_inG` that passes today is not
evidence that it will pass after an unrelated `Σ` grows.

## 7. A world satisfaction left to unification

Giving `fn` its execution level meant the callee's body is stated over
`∗_{k<j} Winv_k` while the caller holds the whole world, so somewhere the
two have to be related.  Three ways of writing that one step:

```coq
(* ~10 min, killed *)  iApply (twpw_incl_fupd (E:=∅) with "[] [-]").
(* ~10 min, killed *)  iApply (twpw_incl_fupd (E:=∅) (W:=…) (W':=…) with "[] [-]").
(* ~10 min, killed *)  rewrite fn_gho_1'.   (* the lifted form, by rewrite *)
(*   0.3s         *)   iDestruct (fn_gho_1' with "gho") as (…) "…".
```

The file is 4.8s without the level and 5.1s with it, so the level itself
costs nothing; what costs is leaving either world satisfaction to be
solved rather than named.  Note the second line: pinning `W` and `W'`
explicitly did **not** help, because the expensive unification was not
theirs — it was `typed_body_at`'s own implicit arguments, six of them,
against a goal the size of a function-call rule.

The shape that works is to do the lifting **once, in its own lemma**,
where the goal is small and both sides are written out, and to use the
result by `iDestruct` rather than `rewrite`.  `rewrite` has to match the
lemma's whole right-hand side against the goal; `iDestruct` applies it to
a named hypothesis and never searches.

Same family as § 4 and § 5: in this development, anything that leaves a
world satisfaction, a size or a transformer to be inferred rather than
passed will not terminate in any time worth waiting for.  Pass it.
