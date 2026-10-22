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
  --eapply typeG_cif-->      alerusGS (cifOF alerusCON) ?Σ
     --apply type_alerusGS-->   typeG (cifOF alerusCON) ?Σ
        --eapply typeG_cif-->      alerusGS …
           …
```

`typing/type.v` declares

```coq
Class typeG (FML : oFunctor) Σ : Type := TypeG {
  #[global] type_alerusGS :: alerusGS FML Σ;
  …
}.
```

so every field is a projection instance, and `typing/model_inst.v`'s
`typeG_cif` is a global instance that *needs* an `alerusGS`.  Resolution can
therefore build a `typeG` out of a `typeG`, forever.

**What makes it fire.**  Only when no `alerusGS` is available in the local
context.  Writing the hypothesis with an *anonymous* binder,

```coq
(∀ _ : alerusGS (cifOF alerusCON) Σ, ⊢ typed_body … e tr) →
```

is enough: resolution does not use the anonymous hypothesis, so instead of
finding the `alerusGS` sitting right there it goes off to construct one.

**Fix**, both halves needed:

```coq
(* typing/model_inst.v, after the section *)
Global Hint Cut [ _* typeG_cif
  (type_alerusGS | type_alerusSem | type_heapSem | type_gsrcSem |
   type_typeFml | type_stBor | type_stBorSem | type_altSem) ]
  : typeclass_instances.
```

and **name the binder** (`∀ H : alerusGS …`).  After both, the same proof
elaborates in 16 MB, instantly.  Cutting the cycle does not affect finding an
`alerusGS` in the context, which is not an instance application.

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

`apply (type_soundness (CON := alerusCON) (JUDG := alerusJUDG Σ) e tr Htr)`
was a second, independent cost: `apply` elaborates its argument against the
goal with conversion heuristics that rebuild large terms.  `refine` of the
same term is instant.  Both concrete soundness theorems use `refine`.

Elaborating the *statement* — `Check (type_soundness (CON := alerusCON) …)` —
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

## 4. Transformers must be built forward

Stating a `typed_body` goal with its predicate transformer already reduced
makes `iApply` solve for the continuation's transformer by higher-order
unification, which does not terminate.  Apply `typed_body_impl` first, let
the transformer be an evar solved forward, and discharge the implication at
the end — the idiom upstream's examples use.  Pin the innermost transformer
so the final goal is ground.
