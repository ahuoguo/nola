# Porting VerusBelt into Nola, later-free

Branch `later-free-guard`.  Upstream: `verus-belt/src/`.  Keep Leaf's
guarding logic (`P &&{W}&&> Q`); drop `▷` and `iLöb`; use Nola's magic
derivability, `cif` formulas and explicit world satisfactions.  Replacing
the guards with Nola's own borrows is *not* the route.

Everything ported builds green (`make -f Makefile.coq -j4`).

## Where it stands

The model is **done**: `nola/verus_halt/typing/model.v` builds the `cif` model
of `typing/ctx.v`'s interface (`FML := cifOF CON`, `bor_sem := ⟦⟧ᶜ(der)`,
four judgments - the guard, the indexed borrow, the stored inclusion and
the borrow's alteration), `model_inst.v` bundles it into a `typeG` with the remaining
formula-language classes, and `soundness.v` allocates the world
satisfaction and proves both

> a closed, semantically well-typed program has no data race and no thread
> gets stuck  (`type_safety`, the original's conclusion)

and

> it **terminates**  (`type_soundness`)

The second is one the original cannot state: its weakest precondition is
partial, because a guard there hands out a `▷` that only a later credit
pays for.  `Print Assumptions` reports only `Eq_rect_eq` for both.

`typing/inst.v` then builds a concrete `CON` and `JUDG` **with their
semantics**, so neither theorem is vacuous; `verus_halt_type_soundness` and
`verus_halt_type_safety` are the concrete forms, and `Print Assumptions` gives
only `Eq_rect_eq` for those too.  Neither this development nor
`nola/examples/rust_halt/` had ever instantiated `sigTCT`/`sigTO` before.

`typing/rec.v` then builds recursive types by `profix`, as
`nola/examples/rust_halt/rec.v` does, so the `Cofe (FML $oi Σ)` that
`typing/fixpoint.v` assumes is no longer on any path.  `&shr{κ}` is the
guarded former and is *proved* productive; the owning pointer is
*also* productive, now that its pointee sits in a simple invariant; and
`ty_shr_list` and `ty_own_list` - `μ X. Σ! [(); 𝔄 * &shr{κ} X]` and
`μ X. Σ! [(); 𝔄 * own n X]` - are worked recursive types built from them.

`FnFml` used to be the only class in `typing/` with no instance
anywhere.  It has two now: `typing/fn_inst.v`'s stratified one, over
`typing/level_ctx.v`'s family of execution levels, and
`typing/function.v`'s `fnFml_flat`, which is upstream's own setting - no
levels - and is available at every `verus_haltGS`.  So `fn` is
interpreted, and `typing/soundness.v` carries VerusBelt's own theorem as
well as the judgment-shaped pair: `type_soundness_main` and
`type_safety_main` are about a `main` function value the runtime
applies, which is the statement the port could not make before.
(`TypeContractive` still has no instance, but it is superseded: `rec.v`
uses `Productive` over `cif`'s `prost`, which is what the model actually
has.)

`typing/examples/assert.v` and `typing/examples/pcell_example.v` are
upstream's two `fn`-using examples, ported unchanged apart from the
arrow's execution level, and `typing/examples/pcell_adequacy.v` ends on
upstream's own last line plus one upstream cannot state:

> `pcell_example_terminates : sn erased_step ([pcell_example [exit_cont]], (∅, false))`

`typing/strat.v` mechanizes the thesis's Chapter 5 end to end and
axiom-free, and `typing/strat_bor.v` the Landin's-knot argument over a
model that *does* index its slots by level - which is what the port's
own borrow formers still do not do, and the one place the execution
level is not yet load-bearing.

Of that refactor (item 2 below), **steps 1-5 are done** and step 6 is
half done.  The execution levels share one lifetime logic - `@[κ]` is one
proposition for the whole run, not one per level - and
`verus_halt_wsat_below P ns j` is the thesis's `∗_{k<j} Winv_k` beside one
shared copy.  `typed_body` is stated over a world satisfaction that is a
parameter, `≤-→` is one `twpw_incl_fupd`, every type former carries a
level, and `fn` carries its arrow's.

`fn_fml_sem_2`, the one field in the development that had no model, is
now a **lemma**: `nola/bi/deriv.v`'s `der_const` says a judgment whose
semantics ignores the candidate *is* its body, in both directions, so
`FnFml` collapses to one equation.  And the formula side of `fn` turns
out to need no judgment at all - this port's `fn` is capture-free, so
`pure_fml (⊢ fn_body …)` satisfies every obligation, candidate-
independent for free.

What is left is therefore **not** carrying the interpretation through the
program logic.  It is the **borrow-slot level discipline**: `&uniq`,
`&shr` and the owning pointers must record the level of the machinery
they use, so that storing a function of execution level `j` in a slot of
level `k` forces `j ≤ k` while opening it forces `> k`.  That is what
blocks Landin's knot - `typing/strat_bor.v`'s `knot_not_typable`, not
totality - and it is where all of `fn`'s soundness sits.  `ty_lev`
records the level, `strat_bor.v` is the specification, and
`verus_halt_wsat_below … j` is the world satisfaction it indexes.

### Where that stands, after the TODO audit and the work it led to

All four pieces are now in the tree, `FnFml` has models, and the two
upstream examples that use `fn` are ported and instantiated end to end.

* **`verus_halt_wsat_below_acc`** (`typing/level_ctx.v`) is the
  primitive the discipline runs on, and the port's counterpart of
  `strat_bor.v`'s `bors_below_acc`: a body at execution level `j`
  reaches the machinery of any level `k < j`, and what comes back is
  *level `k`'s* world satisfaction, never level `j`'s.  That asymmetry
  is the whole content of the level.
* **`knot_not_typable`** (`typing/function.v`) is `strat_bor.v`'s lemma
  at the port's own types, and it is closed under the global context.
  `ty_lev (fn j fp spec) = S j`, a slot at level `k` holds a type only
  when `ty_lev ty ≤ k`, and reaching that slot asks for `> k`; no `k`
  is both.
* **A family of levels exists at all.**  `verus_halt_wsats_alloc`
  allocates the ghost names and then takes the family of
  *interpretations*, `P : ∀ k n, LvlAt n`, as a parameter - and nothing
  in the tree had ever supplied one, so the apparatus stood over an
  empty type as far as the concrete model was concerned.
  `typing/inst.v`'s `verus_halt_lvl_const` is one and
  `verus_halt_levels_alloc` allocates as many levels of the concrete
  model as asked for, out of one `Σ`.
* **`FnFml` is realisable, and realised.**  Two of its fields had no
  model and the audit found both.  The formula side asked for an `⊣⊢`
  whose introduction direction is `fn_body ⊢ ⌜⊢ fn_body⌝`, which is
  *false*; it is now elimination at every candidate plus introduction
  at the Coq level, which is the shape every use already has.  The
  world side asked for `verus_halt_wsat ={∅}=∗ fn_wsat_lv j ∗ …` with
  no side condition, which forces `fn_wsat_lv` to be constant; it is
  now `fn_wsat_top`, one equation saying the ambient world *is* the
  family's top, plus an accessor with the thesis's `j ≤ i`.
  `typing/fn_inst.v` instantiates it over the family, and
  `typing/function.v`'s `fnFml_flat` over every `verus_haltGS`.

With `fn` interpreted, VerusBelt's own soundness theorem - about a
`main` *function value* the runtime applies, rather than about a closed
`typed_body` - becomes statable, and `typing/soundness.v` states it:
`type_soundness_main` and `type_safety_main`, on top of
`typing/function.v`'s `type_main_body`.  `typing/examples/assert.v` and
`typing/examples/pcell_example.v` port unchanged apart from the arrow's
level, and `typing/examples/pcell_adequacy.v` ends on upstream's own
last line beside one upstream cannot state, `pcell_example_terminates`.

#### A correction, because the earlier version of this section was wrong

This section used to say that `FnFml` must **not** be instantiated over
the constant family, because with a `Wlv` that ignores the level "a
diverging program would satisfy `verus_halt_type_soundness`".  That
cannot happen, and the reason is worth keeping written down.
`type_soundness` is an ordinary Rocq theorem taking `⊢ typed_body … e
tr` to `sn erased_step`, and every typing rule here is machine-checked
against a total `twp`.  So no choice of `fn_wsat_lv` - not even the
constant `verus_halt_wsat` - can make a divergent program typable; if
one could, Rocq would be inconsistent.

What a degenerate instance costs is **content**, not soundness.  The
level stops constraining anything, and whatever blocks Landin's knot is
then something else.  Here that something else is cruder and quite
separate from the levels: a total `twp` has no Löb rule, so
`⊢ fn_body …` has nothing to prove itself with - which is exactly why
VerusBelt's `type_fnrec`, the rule proved by `iLöb`, is not ported as it
stands, and neither was `type_cont`.  `typing/recursion.v` supplies
well-founded forms of both; see the "Recursion" section below.

#### The family's length, and a second correction

`fn_inst.v`'s `fn_lv_top` used to be 1, and this plan used to blame the
borrow formers for it.  That was wrong, and the real reason was one
conjunct.  `fn_wsat_top` says the family's top *is* the ambient
`verus_halt_wsat`; `verus_halt_wsat` was one level's machinery; a family
of length `L` has top `verus_halt_shared ∗ ∗_{k<L} Wbor_k`, and no
frame-preserving step makes up the difference, because the lower levels
have to exist before the body runs and nothing creates them.

So `verus_haltGS` gained `verus_halt_Wx`, a conjunct of
`verus_halt_wsat` for the levels above the ambient one.
`verus_haltGS_of` sets it to `emp`, which is what every level package
and the single-level development use; `verus_haltGS_of_lv` fills it;
nothing inside `verus_halt_wsat_core` mentions it, so a level's own
package stays a function of its names alone and the levels stay
non-circular.  `fn_inst.v`'s `fnFml_levels` is the model at the family's
full length, with the ambient names as level 0.

The world is allocated too.  `verus_halt_names_alloc_lv` is
`verus_halt_names_alloc` with `verus_halt_Wx` universally quantified -
which its proof always was, since it never mentions the field - so the
bottom level's half lands at the *ambient* package rather than at
`verus_haltGS_of … n0`; `fnlv_names_alloc` assembles it with the further
levels from `verus_halt_names_alloc_more`, and `fnlv_wsat_parts` says
that beside `send_wsat` those are the whole of `verus_halt_wsat`.

#### What the level still owes

One thing, and it is not the family's length.

The borrow formers still do not record the level of the machinery
they use: `typing/own.v`, `own_rec.v`, `uniq_bor.v` and `shr_bor.v` all
set a slot's level to its *pointee's*, and `verus_halt_wsat_lvl` is one
monolithic block per level.  So `knot_not_typable`'s premise is never
discharged from anything.  Recording that level is what would make the
level-indexed family - level `k`'s `Csem` reading an arrow of level
`j < k` at `P j`'s interpretation - buy something; that family is still
the thing to build, but `FnFml` no longer waits on it.

File-by-file map to upstream: `nola/verus_halt/CORRESPONDENCE.md`.
Performance traps, five of which present as a hang - one of them for
over eight hours: `nola/verus_halt/PERF.md`.

## Recursion, and why Löb is not missed

`type_cont` and `type_fnrec` are the two rules VerusBelt proves by
`iLöb`, and a *total* weakest precondition has no Löb rule.  That is not
an accident of the port: Löb proves a loop safe without proving it
terminates, which is exactly what totality may not do.

Neither source has a rule to copy.  The thesis's Chapter 5 stratifies a
*functional* language and never reaches loops or continuations.
`nola/examples/rust_halt/` has lifetimes, borrows and total correctness
and *no function type and no continuation rule at all* - it types the
Ackermann function (`verify/ack.v`) by a nested `elim` on the arguments,
with each recursive call unfolded by its own `type_call` and the
induction hypothesis applied through `type_in`.  Recursion there is
ordinary Coq well-founded recursion, and `type_real` is what moves a
refinement to the Coq level so the induction can start.

`typing/recursion.v` is that method at this port's judgment, and it needs
no `type_real`: `~~𝔄` is already the *prophecy independent*
interpretation, so a continuation's argument refinements are ordinary
Coq values and a measure on them is an ordinary Coq function.

* `type_pure` - a pure step of `typed_body_at`, which nothing in the port
  had, since every other rule names a concrete expression former.
* `type_call_rec` - the unfolding of a direct call to a `rec:` value;
  `rust_halt`'s `type_call`.
* `type_cont_wf` - `type_cont` with `iLöb` replaced by
  `well_founded_induction`.  `cont_at μ trk a` is what the loop body may
  assume about its arguments, `cont_lt R μ trk a` what a jump must
  establish, and the gap between them is one application of `R`.  The
  body is handed the continuation at `cont_lt … a`, so every jump
  descends.

`typing/examples/loop.v` runs a countdown through it and ends on
`countdown_terminates : sn erased_step ([countdown], (∅, false))` -
a termination statement about a loop, which is the thing the Löb rule
could not have given.  Change the decrement to `- #0` and the `lia` on
the last line fails, so the measure is load bearing.

* `type_fnrec_wf` - the same for the function *type*.  A function that
  calls itself does so through its own arrow rather than by applying a
  `rec:` value, so the measure cannot sit in the premise; it sits in the
  arrow.  The body is handed `fn j (fp_lt R fp x) spec`, the arrow with
  its parameter range cut down to `{y | R y x}`, so making the recursive
  call asks the caller for a proof that the argument descends.
  `type_fnrec_top_wf` is it at the ambient level, and
  `type_fn_top_of_fnrec_wf` derives `type_fn_top` from it with `R` empty
  - upstream's own derivation of `type_fn` from `type_fnrec`, and the
  check that the premise is dischargeable.

Of these only `type_cont_wf` rests on `Eq_rect_eq`; the rest are closed
under the global context.

What the tree does not have is a worked *recursive function* example:
`typing/examples/loop.v` exercises `type_cont_wf`, not `type_fnrec_wf`.
`rust_halt`'s Ackermann is what one would look like.

## Not ported

| upstream | lines | why |
|---|---|---|
| `typing/spawn.v` | 394 | `join` is a busy-wait spin loop - **not** a missing technique, see below |

The whole of `guarding/` is now here, `storage_protocol/`,
`lib/rwlock.v` and both halves of `own_and_own_sep.v` included, and so is
`typing/protocol.v`, all eighteen of its rules.  The line counts shrink
because Leaf's later/`iLöb`/`pers` machinery disappears.

This plan used to predict that the chain was feasible later-free and that
the obstacle was size rather than principle.  That was right: Leaf's 28
`▷`s were all around `f b`, the interpretation of the protocol state held in an
Iris invariant, which is exactly the shape `boxes.v` and `frac_guard.v`
shed here - the content a formula, the invariant a world satisfaction.
`inved.v` (364), `storage_protocol.v` (354), `base_storage_opt.v` (122),
`storage_protocol_logic.v` (541), `rwlock.v` (505) and
`typing/protocol.v` (1121).

**`spawn.v` is not a matter of technique, and the audit settled it.**
`join` is

```
rec: "join" ["c"] := if: !ˢᶜ"c" then (* read the result *) else "join" ["c"]
```

a spin loop with no decreasing measure, and upstream's `join_spec`
(`lang/lib/spawn.v`, not `typing/spawn.v`, which contains no `iLöb` of
its own) is proved by `iLöb`.  Under a *total* weakest precondition the
specification is not merely unproved but **false**: `twp` quantifies
over every schedule with no fairness assumption, and a scheduler that
never runs the spawned thread makes `join` diverge.  So this entry does
not move without a fair-scheduling total weakest precondition, which
neither λRust's operational semantics nor Iris's `twp` provides.  It is
the one line in this table that is closed rather than deferred.

## Is the model concrete?  Yes, as of `af5aee0`

`model.v` gives the interpretation parametrically in `CON` and `JUDG`, as
`nola/examples/rust_halt/` does; `typing/inst.v` now builds the smallest
`CON` and `JUDG` satisfying the constraints **and their semantics**.
Neither development had ever instantiated `sigTCT`/`sigTO` before - they
appear nowhere in `nola/examples/`.

The obstruction was that `Jsem` would have had to be defined from itself.
Nola's construction order (thesis Def. 4.1) is

> `Csem` (from the `Ecsem`s) → `Jsem` (**applying** δ) → `Deriv`, `der`

and upstream holds to it everywhere: `⟦Px ⇒ Qx⟧δ = ⟦Px⟧δ -∗ |⇛ ⟦Qx⟧δ`
(§ 6.4).  The quantification over interpretations lives in the *lemmas* -
`Deriv_factor'`, `Deriv_map`, `bor_wand` - never inside the semantics.
`guardJT_sem` here already had that shape; `idxborJT_sem` and `inclJT_sem`
were instead made **constant** in δ, and the only way to make a guard
constant in δ is to quantify over every δ - which has to be restricted to
the *good* ones, which is `Deriv`, which is defined from `Jsem`.

Both offenders are gone, and in the same way: `st_incl` and `st_iff` both
quantify over **every** interpretation rather than over the good ones.  The
cycle is the *restriction*, not the family.  See step 0 below for what that
cost.

(An earlier version of this plan recorded `st_incl` as a *token* instead -
a covering set of eternalized lifetimes.  That was wrong, and the place it
was wrong is `fn_incl_of_all`: the inclusion `type_call_iris'` manufactures
for the call's own lifetime is *semantic*, and no token expresses it.)

## Next

The model is closed and both of the blockers that were open after it are
gone; what is written up in `nola/verus_halt/typing/inst.v` is the record of
how.  What remains is one small item and two large ones, and the two large
ones are large for reasons now understood rather than guessed at.

1. **A worked example** - done.  `typing/examples/basic.v` types four
   programs against the rules, parametric in `CON`/`JUDG` exactly as
   `rust_halt/verify/` is: a binding, two bindings and an addition, a box
   allocated and freed, and a box allocated, *written* and freed - the last
   bringing `own_ptr`'s `typed_write` in through `write_own`.  Two subtyping
   facts exercise the relaxed borrow, including a unique borrow of a unique
   borrow, which is the case `uniq_subtype` could not state before.

   The traps are recorded in `nola/verus_halt/PERF.md` and each one bit here:
   `type_val` cannot be applied to a concrete program, `type_new`'s size
   must be passed rather than unified, transformers must be built forward
   into an evar, and `Closed` premises are discharged by resolution *before*
   the bracket list, which silently shifts every branch.

2. **`fn` must be stratified by an execution level** (thesis § 5).
   This was open because `FnFml`'s `fn_fml_sem_2` had no model, so `fn`
   was the one type former the model did not interpret - which is why
   `soundness.v` was stated about a typing judgment, as `rust_halt`'s
   adequacy is.  That field is gone (it asked for `fn_body ⊢ ⌜⊢
   fn_body⌝`, which is false), `FnFml` has instances, and `soundness.v`
   now carries VerusBelt's own `main`-shaped theorem beside the
   judgment-shaped one.  What the level still owes is below.

   Its sibling `fn_incl_of_all` **is** closed, and separately from the
   levels: see "Done: a lifetime inclusion is a guard family again" below.

   And the device itself is no longer a plan.  `typing/strat.v` mechanizes
   Chapter 5 - leveled types, the level-indexed interpretation, the
   function type, the list type, the typing rules and Corollary 5.3 -
   axiom-free, over `nola.lrust`.  What that settles, and what it says the
   port would have to change, is "Done: Chapter 5, mechanized" below.

   ### The thesis's recipe, read off Chapter 5

   Types carry a level `i`.  The function type's arrow carries an execution
   level `j ≤ i`, meaning the function body touches only references whose
   body level is `< j`, and the interpretation is a total Hoare triple whose
   *world satisfaction mentions only lower levels*:

   > `⟦T →ⱼ U⟧ᵢᵟ v ≜ ∀u. [⟦T⟧ᵢᵟ u] v(u) [⟦U⟧ᵢᵟ] { ∗_{k<j} Winv_k ⟦⟧ᵟ*_k }`   (5.4)

   The typing judgment is the same triple with `∗_{k<i} Winv_k`, and
   adequacy (Cor. 5.3) allocates those `k < i` and applies the extended
   total Hoare triple's adequacy.

   **The level is what cuts the circularity**, and that is the part this
   plan had not taken in.  (5.4) is well-formed because `k < j ≤ i`, so
   `Winv_k ⟦⟧ᵟ*_k` is *already defined* when level `i` is being defined.
   The port's obstruction - `Deriv_factor'` asks for `typed_body` at every
   candidate, and `typed_body` is stated at the ambient interpretation - is
   the same circularity, and the thesis does not solve it with derivability.
   It solves it with the level, and uses derivability for a different job
   (below).

   ### What that costs here - less than this plan said

   The thesis's own estimate (§ 5.2 fn. 3) is one component RA per level,
   capped at a global maximum `L`:

   > Unfortunately, in the current Coq mechanization of Iris, only a finite
   > number of component RAs are allowed for the global camera.  So we
   > parameterized our proof with the maximum level `L ∈ N` to be used.

   **With Nola's present `sinv` interface that is no longer so**, and
   `typing/levels.v` now proves it, axiom-free:

   ```coq
   lvs_wsat_alloc L : … ⊢ |==> ∃ γs, ⌜length γs = L⌝ ∗ lvs_wsat γs smf
   lvs_below γs smf j := lvs_wsat (take j γs) smf            (* ∗_{k<j} Winv_k *)
   wsat_incl_lvs_below : j ≤ j' → WsatIncl (lvs_below … j') (lvs_below … j) _
   ```

   `sinv_wsat_alloc_name` mints a fresh ghost name against the `inG` an
   existing instance already carries, so **a level is a `gname`, not a
   component of the global camera** - allocate as many as a proof needs, no
   global maximum, no new `inG`.  This port already leans on the same trick
   once, for the store world satisfaction inside `verus_halt_WGuard` beside
   `boxes.v`'s.

   On top of that sit the two rules that make a level worth having, and
   both are short *because* a level is a ghost name - no camera is indexed
   by it, so nothing has to be re-proved per level:

   ```coq
   lvs_below_acc : k < j → γs !! k = Some γ →
     lv_tok γ i Px -∗ lvs_below γs smf j -∗
       smf k i Px ∗ (smf k i Px -∗ lvs_below γs smf j)
   twpw_lvs_le : j ≤ j' →
     WP[lvs_below γs smf j] e @ s; E [{ Φ }] ⊢
     WP[lvs_below γs smf j'] e @ s; E [{ Φ }]
   ```

   The first is the thesis's dereference rule, and it is where the
   circularity is cut: the content comes back at `smf k`, *level `k`'s*
   interpretation and never level `j`'s, so the definition of level `j` may
   mention it - which is (5.4)'s well-formedness, spelled out.  The second
   is `ty-lev`, raising a judgment's execution level, and it is
   `twpw_incl_fupd` along `lvs_below_le`.  `wpw_lvs_le` and
   `thoarew_lvs_le` come with it.  All of `levels.v` is
   `Closed under the global context`.

   Two more items of the old estimate are wrong, and one is right.

   * **The formula *type* need not be levelled, but the *interpretation*
     must be.**  The thesis indexes `nProp_i` because its invariant stores
     `ℓ ↦ T_i` with `T_i : Typ_i`, and `⟦⟧*_i` calls `⟦T⟧_i`, which for a
     function type calls `∗_{k<j} Winv_k ⟦⟧*_k` with `k < j ≤ i`: the
     interpretation is a *family*, well-defined by recursion on the level.
     The port's invariants store one `cif` whatever the level, so `cif`
     itself can stay single - but `⟦⟧ᶜ(δ)` cannot.  It has to become
     `⟦⟧ᶜ_i(δ)`, defined by strong recursion on `i`, with `fn_fml`'s
     selector carrying its execution level `j` (a `nat`, discrete, so no
     trouble with `cifc_data_contractive`) and its semantics calling
     `⟦⟧ᶜ_k` only for `k < j ≤ i`.  Without that the circularity is *not*
     cut: a single `⟦⟧ᶜ(δ)` that mentions `fn` is exactly the loop
     `Deriv_factor'` runs into.  A family of `Csem`s indexed by level is a
     new class and a real change, though a smaller one than indexing `FML`.
   * **Which world satisfactions must be levelled** was the one genuinely
     open question, and `typing/strat.v` answers it by construction:
     **all of the invariant-carrying ones, and as separate ghost
     families**, not merely at separate interpretations.

     This plan previously guessed otherwise, on the grounds that `⟦⟧ᶜ_i` is
     *monotone* - `fn_fml` is the only constructor whose semantics mentions
     the level, and `⟦fn →ⱼ⟧ᶜ_i` is the same for every `i ≥ j` - so that a
     run of top level `L` could keep one `verus_halt_wsat ⟦⟧ᶜ_L` with the
     levelled part beside it.  **That does not work**, and the reason is
     one line of `strat.v`'s `twp_read_lv`: a caller at level `i` must hand
     a callee at level `j ≤ i` a world satisfaction *it can give away*,
     and the callee's is interpreted by `⟦⟧ᶜ_j`.  One family cannot be
     read at two interpretations at once - `verus_halt_wsat ⟦⟧ᶜ_j` and
     `verus_halt_wsat ⟦⟧ᶜ_i` are the same ghost state under different `BorSem`s
     and neither entails the other - so the split has to be in the *ghost
     state*, which is exactly `∗_{k<j} Winv_k` and exactly `lvs_below`.

     So `verus_haltGS` becomes a chain: `L` instances sharing the `inG`s and
     differing in their ghost names, for everything that holds a formula -
     `llft_logicGS`, the box's and the shared borrow's `sinvGS`, `cnaGS`,
     `naInvGS`, `fracGuardGS`, the two `fracKeyGS`, the eternal and store
     names.  The heap stays single, as it does in the thesis, where it
     lives in the state interpretation rather than in `Winv`.  Each of
     those classes needs the `sinvGS`-style split into a `_pre` and a bare
     ghost name before `L` of them can be allocated from one `Σ`, which is
     the first concrete task.
   * **A level on every type former, and on `typed_body`, does remain**, and
     that is the bulk of the work - it touches every file in `typing/`.

   ### And `fn_fml` still has to be a judgment

   Making it an ordinary formula would need an arbitrary `iProp` -
   `typed_body` - in a constructor's *data*, and `nola/iris/cif.v`'s
   `cifcon` requires `cifc_data_contractive :: oFunctorContractive
   (cifc_data s)`.  The identity functor is not contractive, which is why
   `cif_later` carries a `Next` and why the only `▷`-free way into a `cif`
   is a judgment.  The thesis is consistent with this: its function type is
   never *stored*, only interpreted, because its `nProp_i` holds `ℓ ↦ T`
   and nothing else.  A port whose types' ghost assertions are themselves
   formulas has no such luxury, so `fn_fml` stays a judgment and the level
   is what makes its introduction dischargeable.

   ### Done: a lifetime inclusion is a guard family again

   `fn_incl_of_all` is gone from `FnFml`, and what removed it is a
   one-line change of definition.

   `lifetime_full.v`'s note on `StBor` always gave the intended instance of
   `st_incl` as the *family* of lifetime guards, one at every good
   interpretation.  It had been weakened to a token - `⌜κ' ⊆ κ⌝` together
   with a finite set of eternalized lifetimes - to keep `Deriv` out of
   `Jsem`, since `st_incl` sits inside `idx_bor`.  **The cycle is the
   restriction, not the family.**  Drop the `⌜Deriv ⊤ δ⌝`:

   ```coq
   st_incl κ κ' := □ ∀ δ, @[κ] &&{verus_halt_WGuard_at δ}&&> @[κ']
   ```

   mentions no `Deriv`, so `Jsem` may be defined from it, and nothing is
   lost, because every proof the lifetime logic has about a guard is
   parametric in `BorSem` - `st_sub_at`, `st_glb_at`, `eternal_incl_at`
   and `shr_tok_guard_at` all took an arbitrary `δ` already.

   What it buys is exactly the rule that had no model.  `type_call_iris'`
   creates a fresh `ϝ` for the call and guards its aliveness by the
   caller's local lifetime context; the inclusion it then has is
   *semantic*, and a token cannot express it.  The rule is now
   `dincl_fguardx` in `ctx.v` and its proof is three lines.

   The token survives as `eternal_incl_cif` - it is what eternalizing a
   lifetime produces, and it implies the family.  The cost of the
   weakening is that every *producer* of a guard family produces it at
   every interpretation rather than at the good ones: `fguardx`,
   `lctx_lft_alive_all`, `guard_fml_borrow_shared`, `Ltok_guard_frac_at`
   and `st_incl_at` are all over `alt_any` now, and each was already
   proved that way.

   ### Done: Chapter 5, mechanized

   `typing/strat.v` (1030 lines) is the thesis's Chapter 5 case study, in
   Nola, axiom-free: leveled types `unit | nat | ref°ₖ T | T →ⱼ U |
   listₖ T`, the interpretation as a family `⟦⟧ᵢᵟ` indexed by *both* the
   level (5.4) and a derivability candidate (5.5), the typing rules, the
   subtyping rules, Corollary 5.3, and three closed programs that it
   types and that therefore terminate - including a function stored in a
   shared mutable reference and called back (`ex_horef_total`), and a
   *cyclic* list walked one step (`ex_clist_total`).

   Both of the thesis's devices are there, and the file exists to show
   they compose, because the port needs both: the level for `fn`, the
   indirection for `&shr`.  (5.5) is what `≤-ref` needs - a reference
   stores a *different* type, tied to the declared one by two
   derivability assertions, because an invariant token names the formula
   it holds - and `subty_ref` is then three lines of transitivity.

   It is built over `nola.lrust`, not `nola.verus_halt.lang`, for a reason the
   stratification is about: the thesis keeps the heap in the **state
   interpretation** and only the invariants in `Winv`, and the port's own
   language keeps guards over `verus_halt_WGuard` in the heap's read and write
   banks.  Separating them is the point, so the demonstration uses the
   language in which they are already separate.

   Three things it settles.

   * **The function type needs no derivability at all.**  (5.4) is a total
     Hoare triple whose world satisfaction is `∗_{k<j} Winv_k`, and the
     recursion on the level is well-founded because `k < j ≤ i`.
     `tsem_fn` is that equation and it is an `⊣⊢` - no `Deriv`, no
     candidate, no `Deriv_factor'`.  The level *replaces* magic
     derivability for this one connective, which is what this plan claimed
     and what is now checked.
   * **The price is per-level ghost state**, as recorded above.
   * **In the thesis a type is syntax**, so its `nPropᵢ` is literally
     `loc × Typ` and poses no domain equation.  `strat.v`'s formulas are
     `loc * styp` pairs and there is no `cif` in the file.  The port's
     types are semantic records whose ghost assertions must be formulas
     because they are borrowable; that difference, and not the level, is
     why `fn_fml` has to be a judgment.

   `subty_list` is § 5.1 fn. 1: `≤-ref` used **coinductively**, by
   `Deriv_ind` over an induction hypothesis that is the pair of list
   judgments.  One deviation from the footnote, and it is forced rather
   than a gap: the footnote also relaxes the level, but `≤-ref` wants the
   body types related in *both* directions, so the tail reference of
   `listᵢ T` needs `listⱼ U ≤ listᵢ T` too, which is itself a `≤-ref` at
   the tail and asks for `j ≤ i`.  The two force `i = j`.

   That is the exact counterpart of item 3 below, from the other side.
   `rec.v` proves subtyping of the port's recursive types by *induction
   on the depth* and needs neither coinduction nor `Deriv`, because the
   port's guarded formers carry an index to descend on and `type_incl` is
   already quantified over every candidate; the thesis's `rec` is plain
   substitution, has no index, and the loop is cut coinductively.  And
   `rec.v`'s owning pointer had no rule until its pointee moved behind a
   stored guard - the same move (5.5) makes, for the same reason.

   § 5.1's closing example is there too, in semantic form
   (`twp_iter_list`, `ex_iter_total`): an arbitrary terminating function
   iterated a bounded number of times over a list that may be *cyclic*.
   That is the one the thesis cites as the point of the whole exercise.

   What `strat.v` leaves out is a general `rec Xⱼ. Tⱼ`.  `listₖ T` is a
   constructor instead, and that is not a shortcut past the interesting
   part - it *is* the interesting part.  Mechanizing a general `rec` needs
   a measure on types that descends through substitution, and the measure
   exists exactly because every recursive occurrence is guarded by `ref`,
   whose interpretation (5.3) never looks at the body.  Taking the guarded
   unfolding as primitive makes `⟦listₖ T⟧` outright non-recursive: two
   invariant tokens holding *syntax*, so `typed_list_tail` needs no level
   conversion at all.  `rec.v` records the same fact from the other side -
   a former is `Productive` over `cif` exactly when its argument reaches
   only `cdom` children, which an `Ecsem` may hand to `δ` but never
   interpret.

   ### What remains, and what the audit says about it

   The step this plan previously listed first - "split each ghost-state
   class into a `_pre` and a bare ghost name" - **is already done**, in
   every class that would have to be levelled.  `llft_logicGS` is
   `llft_logicGpreS` plus three gnames, `naInvGS` is `sinvGpreS` plus one,
   `cnaGS`, `fracGuardGS`, `fracKeyGS` and `sinvGS` likewise.  `L`
   instances can be allocated from one `Σ` today; `soundness.v`'s
   `verus_halt_wsat_alloc` is already the one-level case of it.

   And of what `verus_halt_wsat` and `verus_halt_WGuard` contain, these carry the
   interpretation and so have to be levelled:

   | carries the interpretation | does not |
   |---|---|
   | `shr_wsat`, `box_wsat bor_sem`, `llft_inv_main`, `cna_wsat … bor_sem`, `na_inv_wsat … bor_sem`, `frac_wsat bor_sem`, `verus_halt_store_wsat` | `eternal_wsat`, the two `frac_key_wsat`s, `send_wsat` |

   #### Done: step 1, `verus_haltGS_at` and `∗_{k<j} Winv_k`

   `typing/level_ctx.v` builds the levelled package at the port's own
   world satisfaction: `verus_haltNames` (one level's ghost names, each a bare
   `gname` or a `_pre` class plus `gname`s), `verus_haltGS_of`,
   `verus_halt_names_alloc`, the family `verus_halt_wsats`, `verus_halt_wsat_below`
   (the thesis's `∗_{k<j} Winv_k`) and `ty-lev` as `twpw_verus_halt_le`.  As
   many levels as asked for come out of one `Σ`; `typing/soundness.v` now
   takes its `verus_haltGpreS` and its allocation from that file, since
   allocating one level and allocating `L` of them are the same lemma.

   Two things the construction forces, both recorded in the file:

   * **`send_wsat` is shared, and that is a fact rather than a choice.**
     It is `cna_lifetimes atomic_pool_name ∅`, whose `own` is at an `inG`
     of `cnaGpreS` and at a pool name from `uniqG`, so it mentions no
     `cna_name` and is literally the same proposition at every level.  It
     therefore sits beside the family, as `verus_halt_wsat` has it sit beside
     `verus_halt_wsat_core`.
   * **The weakest precondition's `invGS_gen` has to be the program
     logic's own.**  A `fupd` at a second `invGS_gen` is a different
     proposition; the first `twpw_verus_halt_le` failed with a goal and a
     lemma that printed identically.

   #### Correction, twice over: `LtRa` *does* need splitting - and now it is split

   A previous version of this plan said `LtRa` had to be split; the one
   after it said that was wrong, on the grounds that `llft_inv_main` is
   interpretation-free.  **That second claim is false, and the first was
   right.**  `llft_inv_main` is

   ```coq
   ∃ sa sd blocked, LtState llft_name sa sd ∗ llft_alive_def' sa
     ∗ outer_inv llft_name … sa sd blocked ∗ llft_alive_def' blocked
   ```

   and `outer_inv` is `inner_inv`, which is

   ```coq
   ∃ mbs mprops Ptotal outlives,
     AuthBorState … mbs ∗ ModuloDead … dead
       ∗ box bor_sem (boxmap alive dead mbs) Ptotal
       ∗ future_vs alive dead outlives mbs mprops
       ∗ ⌜dom mbs = dom mprops ∧ …⌝
       ∗ ([∗ map] sn ↦ Q ∈ mprops, sinv_tok sn Q) ∗ Outlives …
   ```

   - the interpretation-carrying box and the borrow bookkeeping in one
   existential, tied by `dom mbs = dom mprops`.  So levelling the box
   means levelling the bookkeeping, and the bookkeeping was at
   `llft_name`, which is also where the lifetime tokens live.

   **The split is done** (`lifetime/ra.v`, `lifetime/inv.v`,
   `lifetime/lifetime_full.v` and the files between).  `llft_logicGS`
   gains `bor_name`; `AuthBorState`, `OwnBorState` and `ModuloDead` move
   there, `LtState`, `Alive` and `Dead` stay at `llft_name`.

   **It needed no new camera**, which is what made it affordable, and the
   reason is worth recording because it is the opposite of what the
   previous estimate feared.  In `lt_inv`

   ```coq
   lt_inv (LtOk (Some (sa, sd)) a d (Some g) gs (Some w) wp) :=
     sd = d ∧ sa ∩ sd = ∅ ∧ w = wp ∧ w ⊆ d ∧ (multiplicity condition)
       ∧ consistent_modulo w g gs
   ```

   the only term joining the lifetime components to the borrow components
   was **`w ⊆ d`**, and it was there only because `modulo_dead w` put `w`
   into the *global* dead component `d`.  `consistent_modulo` has always
   been stated about the borrow side's own copy `w` and nothing else - so
   the earlier worry that `consistent_modulo` "would have fought the
   split" was misplaced; it is indifferent to it.  Drop `modulo_dead`'s
   contribution to `d`, drop the conjunct, and the two halves are
   independent.  Since `lt_valid a := ∃ b, lt_inv (a ⋅ b)`, each half is
   then valid on its own, the existential frame supplying the other.

   What the camera used to enforce, the invariant now enforces, and that
   trade is the interesting part:

   * `inner_inv` carries `□ ∀ d ∈ dead, Dead γlt d` - persistent, so free
     to carry and free to duplicate - so a level's view of the dead set
     cannot run ahead of the real one;
   * `ModuloDeadPers` carries that witness beside the borrow-side one,
     since `modulo_dead_pers_implies_dead` is no longer a fact about the
     camera;
   * `modulo_dead_new` loses its `Dead` premise and becomes an update **at
     the borrow name alone** - which is exactly the point, because that is
     the name that has to vary with the level.

   #### What was in the way: every level's view of the dead set

   The split is necessary and it is not sufficient, and the remaining
   obstruction is sharper than "lifetime death needs the box".

   `inner_inv alive dead blocked` is *indexed by the dead set*, and
   killing an atom changes it: `inner_kill_lt` empties the slices the
   death invalidates and fills the ones it revalidates
   (`slice_empty_many`, `slice_fill_many`), both of which are operations
   on that level's box.  With one `inner_inv` per level, killing a
   lifetime would have to advance **every** level at once, and a body at
   execution level `j` never holds the levels at or above `j`.

   Nola is free of this because its settlement is lazy - `lft_end` is
   `1.[α] ==∗ [†α]` and a lender reclaims later, one level at a time -
   and that is why `typing/strat_bor.v` works there.  Leaf's lifetime
   logic settles eagerly, and rewriting it to settle lazily is a rewrite
   of `inv.v`, `expire_lt.v`, `unnest.v` and `reborrow.v`, not a
   refactor.

   The cheaper route, and the one the split has just made expressible, is
   **a per-level view of the dead set that catches up lazily**:

   * level `k`'s `inner_inv` carries its own `sd_k`, with `sd_k ⊆ sd`
     witnessed by the persistent `□ ∀ d ∈ sd_k, Dead llft_name d` the
     invariant now holds - no shared existential, no shared authority;
   * killing an atom updates the shared `LtState` and only the levels the
     killer holds; a level that lags catches up the next time its own
     world satisfaction is held, by running the existing `inner_kill_lt`
     over `sd ∖ sd_k`, which is sound precisely because the persistent
     witness says those atoms really are dead;
   * and this plan expected a *lifetime-level invariant* on top - a
     lifetime carrying a level, created and killed only at an execution
     level at least that high - to make the lag invisible.  It is not
     needed, and the section after next says why: lifetimes are not
     levelled at all, borrows are, and a level learns of a lifetime when
     it is first borrowed there.

   #### Checked: the bookkeeping does not need `alive` at all

   The design above has one thing that could have sunk it, so it is
   checked in `lifetime/inv.v` rather than assumed.  A level that lags
   can be *bounded* by a persistent witness, because death is persistent;
   **aliveness is not**, and `inner_inv` consults `alive` in three
   places - `boxmap`, `invalidated` and `revalidated`.  If level `k`
   needed `κ ⊆ alive_k` to open a borrow of `κ`, nothing would carry that
   in from the shared lifetime tokens and the design would not close.

   It does not need it.  Every one of those three consults `alive` only
   as `al ⊆ alive` for a borrow's own alive set, and `map_wf` says
   `al ∪ de ⊆ alive ∪ dead` with `alive ## dead`, so

   >  `al ⊆ alive  ↔  al ## dead`

   (`subseteq_alive_iff`).  `boxmap_alive_free`,
   `invalidated_alive_free` and `revalidated_alive_free` are that
   substitution carried out, each an equality of the *boolean*, so each
   rewrites under `boxmap` and under `borrow_sum` without disturbing a
   single proof that follows.

   So level `k` can be indexed by its own `dead_k` alone, and "κ is
   alive" transfers into it for free: the user's `@[κ]` and the shared
   `LtState` give `κ ## dead`, and `dead_k ⊆ dead` gives `κ ## dead_k`.

   #### Done: the reindexing, in `lifetime/level.v`

   With `alive` eliminable, `inner_inv` is *reparametrized* rather than
   rewritten: indexed by the created atoms instead of the live ones,

   >  `inner_inv_c created dead blocked  :=  inner_inv (created ∖ dead) dead blocked`

   a pure change of variable, faithful exactly when `dead ⊆ created`,
   which every operation preserves.  In these coordinates **death leaves
   `created` alone** (`inner_kill_lt_c`), creation moves only `created`
   (`inner_new_lt_c`), and an atom a level never heard of dies there by
   `inner_instant_kill_c`, which moves both.  `inner_catch_up_one`
   unifies the last two, and the file is closed under the global
   context.

   Two things the construction forced, and both correct this plan.

   **A level's invariant has to be a closed proposition.**  It may not
   mention the shared `(sa, sd)` at all, because `∗_{k<j} Wbor_k` is
   held on its own by a body that was passed nothing else.  The plan
   above has `dead_k ⊆ sd` carried by the persistent witness, and that
   much is right - but it is not even needed as a *statement*: what a
   lagging level actually wants is that a lifetime the lender holds a
   token for is not dead there, and that is `lv_alive_disj_dead`, the
   level's own death witness against the lender's `Alive` token.  The
   other half, `created_k ⊆ sa ∪ sd`, has **no** persistent witness -
   aliveness is the non-persistent side - and it is exactly what
   freshness would want.  So creation is made to need no freshness:
   `lv_create` skips an atom the level believes dead and is the identity
   on one it has already heard of.  What is left of a level's
   well-formedness, `lv_dead s ⊆ lv_created s`, is local to the level,
   and `llft_lv_inv` mentions nothing shared.  A kill in the shared
   logic therefore leaves it *syntactically* unchanged - there is no
   lemma to state, which is lazy catch-up in its sharpest form.

   **Lifetime creation does not have to reach down the levels.**  The
   plan said `new_lt` for a lifetime of level `ℓ` has to reach the
   levels below `ℓ`.  It has to reach none of them.  `lv_borrow_ready`:
   a borrow of `κ` can be made at a level that has never heard of `κ`,
   because the level creates `κ`'s atoms on the spot and needs only that
   it does not believe them dead.  So a lifetime reaches a level lazily
   too, when it is first borrowed there.  That is the right design and
   not merely a cheaper one - lifetimes are not levelled, *borrows* are,
   and the argument that the knot cannot close never asked anything of
   lifetime creation.

   #### Done too: catching up, and the order it has to follow

   A level catches up by replaying the shared kill order (`lv_catch_up`
   over a `kill_run`).  Two facts about that, both checked:

   * **It is a list, not a set.**  `no_greedy_kill_order` exhibits an
     outlives set consistent with its dead set in which no atom may be
     killed first - a two-cycle, `a` before `b` and `b` before `a`.
     Such a state is unreachable, but unreachability is a fact about the
     real kill order, not about `outlives_consistent`, so the level
     replays that order rather than choosing its own.

   * **A past run stays valid as the outlives relation grows**
     (`kill_run_mono`).  `kill_run` quantifies over the relation as it
     stands *now*, so a pair added later could in principle invalidate a
     step the shared logic had already checked.  It cannot:
     `llft_augment_outlives` adds `(κ, k)` only for `k ∈ κ' ⊆ sa`, so a
     new pair's second component is alive and therefore not in the run.
     Without this the levels would have to be caught up before every
     augmentation, and a body at level `j` cannot catch up the levels at
     or above `j` - which would have sunk the design.

   One more thing falls out: **the levelled invariant has no use for
   `Delayed`.**  `outer_inv`'s two phases exist because the shared kill
   has to close the `NllftG` mask between taking `[†κ]` and updating the
   borrows; at a level those steps are decoupled by construction.
   `outer_inv_open`/`outer_inv_close` say the two invariants agree while
   no kill is in flight, so `lv_inv` is built from `inner_inv` directly.

   #### Done: the decoupling, in `lifetime_full.v`

   `lifetime_full.v`'s `llft_inv_main` no longer ties the borrow
   bookkeeping's indices to the shared `(sa, sd)`.  The bookkeeping keeps
   its own view - created, dead, blocked - and all fourteen rules are
   re-proved against it.  The user-facing statements never mentioned
   those sets, so the whole of `typing/` is untouched and the tree is
   green.  That makes the family a substitution: `llft_inv_main` holds
   one `lv_inv`, and holding `llft_lv_inv ls` instead is a change of that
   one conjunct.

   What the invariant carries now:

   * a **kill order** - a `mono_list` of the atoms in the order they
     died, with `sd` its set.  A level's dead set is a prefix of it, and
     `kill_run` records the outlives condition the shared logic checked
     at each kill, which is what a lagging level needs verbatim;
   * **a second half of the outlives relation**, at `oset_name`, so the
     run's well-formedness - which mentions `outlives` - can be stated
     where `sd` and the log are bound.  `o_name`'s two halves are
     already spoken for, one by `inner_inv` and one by the client, and
     that is the whole reason for the extra name;
   * **`Delayed`, re-purposed.**  It used to mark the gap between the
     shared dead set and a borrow invariant; it now marks the one-atom
     gap between the shared dead set and the kill order.  That gap
     exists only inside the vacuous branch of `llftl_end`, where the
     kill is taken and the contradiction derived, and every rule that
     holds `llft_inv_other` sees `pend = None`.  So the bookkeeping is
     level with the order whenever a rule looks, and no rule ever has to
     catch up.

   Three things only the integration could settle:

   * **`guard_helper2` asked the wrong question.**  It wanted
     `set_map LtAtomSwell κ' ⊆ alive`, which a caller cannot produce once
     the bookkeeping's dead set is its own.  It now asks `## dead` - the
     same thing by `inv.subseteq_alive_iff` - and that is where the
     `alive`-free lemmas earn their keep.
   * **Creating a borrow does not need the coupling.**
     `inner_borrow_create` threads an `LtState γlt alive dead` it never
     uses, so `lv_borrow_create` goes through
     `inner_borrow_create_empty` and `inner_reborrow` and asks nothing
     of the shared lifetime state.
   * **`outer_inv`'s two phases are gone from every rule.**  They kept a
     borrow invariant in step with a kill; the bookkeeping is not in
     step by construction any more.

   One practical finding worth recording: `set_solver` does not
   terminate in a context holding `kill_run`.  A fixpoint over a list in
   scope is enough to make `naive_solver` diverge, so the set reasoning
   in these proofs is done by named lemmas in small contexts.

   #### Done too: the last tie, by a persistent witness

   One pure conjunct still tied a level to the shared world:
   `lv_created s ⊆ sa ∪ sd`.  It cannot survive the family - with one
   bookkeeping per level the shared invariant cannot see the levels'
   states - so it is carried by a persistent witness instead.  `sa ∪ sd`
   only ever grows, so an authority with duplicable fragments is enough:
   `Minted X := own γmint (◯ X)`, held by the level for its own created
   set, against `MintAuth (sa ∪ sd)` in the shared part.

   With that, everything a level needs is inside `lv_inv`: the kill
   order's prefix, the minted atoms, its own well-formedness.
   `llft_inv_main`'s pure part now says nothing about the level except
   that it is in step with the order while no kill is in flight - and
   that is exactly the clause the family replaces by a per-level prefix.

   One incident worth recording: adding
   `inG Σ (authUR (gsetUR lt_atom))` made typeclass resolution pick
   `lt_atom` for `eternal_wsat_alloc` in `typing/level_ctx.v`, where it
   has to be `lft`.  A second `authUR (gsetUR _)` in scope is enough to
   make that ambiguous, and the fix is to give `K` at the use site.

   #### Done: a level may lag behind the kill order

   `llft_inv_main_at` used to say the bookkeeping was level with the
   kill order whenever no kill was in flight.  That conjunct is gone,
   and dropping it is what makes a level's piece a *closed*
   proposition - which is the whole point, since `∗_{k<j} Wbor_k` is
   held by a body that was passed nothing else.

   The three rules that need a lifetime to be dead *at the level* -
   `llftl_borrow_rev`, `llftl_borrow`'s reclaim and `llftl_bor_fake` -
   catch it up themselves, by replaying the whole order with
   `level.lv_catch_up_to_log`.  Replaying runs `future_vs`, which lives
   at `↑NllftUsr ∪ ↑NllftUsr2`, so those three carry that mask, and it
   walks out as a side condition on `E` through `llftl_bor_freeze`,
   `llftl_bor_pers{,_from_wand,_from_wand2}`, `llftl_bor_unnest`,
   `llftl_reborrow{,_meet}` and `ctx.v`'s `dFullBor_exact`.  `Nverus_haltE`
   already contains both namespaces, so every caller in `typing/`
   discharges it from a hypothesis it already had.

   #### Done: the shared half and the level's, named

   `llft_wsatG`'s two halves now have names, and the split is a lemma
   rather than a rewrite of the rules:

   ```coq
   llft_inv_shared_at sa sd log ol pend  (* tokens, kill order, mint, oset *)
   llft_bor_inv := ∃ s, lv_inv … bn s
   llft_bor_wsat := shr_wsat ∗ box_wsat bor_sem ∗ llft_bor_inv
   llft_wsatG_split : llft_wsatG ⊣⊢ (WG ∗ llft_inv_shared) ∗ llft_bor_wsat
   ```

   and the same for the other half, `llft_inv_other_split`.  The main
   invariant keeps its flat shape, because every rule destructures it;
   `llft_inv_main_at_split` is the reassociation.

   #### Done: the outlives relation lags too, and `Osub` bounds it

   A level's copy of the outlives relation cannot be kept in step with
   the shared one, for the same reason its dead set cannot:
   `llftl_augment_outlives` may run while the level is not held, and a
   body at execution level `j` never holds the levels at or above `j`.
   So `llft_outlives` is now the *level's* relation, `olk`, and what it
   carries about the shared one is a bound - `Osub osub_name olk`
   against `OsetAuth osub_name ol`, the same persistent-witness shape
   `Minted` already has, and for the same reason.

   The bound is all a level needs, because **`kill_run` and
   `outlives_consistent` are both antitone in the relation**
   (`level.kill_run_anti`, a corollary of `kill_run_mono` with a vacuous
   hypothesis): a level with *fewer* pairs may replay a run the shared
   logic checked with more.  `llft_augment_outlives` grows `ol` and
   `olk` separately and re-establishes `olk ⊆ ol`; the new pairs'
   second components are alive, so the level's `outlives_consistent`
   survives them for free.

   #### Done: the stored guards are a family, and the world is a parameter

   The last thing in the shared half that was a function of the
   execution level was not the bookkeeping - it was
   `llft_outlives_guards_at ol`, the family

   >  `∀ o ∈ ol, @[o.1] &&{llft_wsatG}&&> Alive llft_name o.2`

   whose *world satisfaction* was a level's `llft_wsatG`.  The guards
   have to be keyed to the **shared** relation, not a level's:
   `llftl_end`'s contradiction branch picks a pair out of the shared
   `ol` - the one whose violation blocks the kill - and opens its
   guard.  A lagging level need not have that pair, so the guards moved
   into the shared half; but a guard taken over level `k`'s
   `llft_wsatG` is not usable by a body holding only `∗_{h<j} Wbor_h`.

   The fix is the move this port had already made once, in the other
   dimension: `st_incl` became **a family of guards, one at every
   interpretation**.  The lifetime logic now simply does not fix the
   world its stored guards live at.  `LlftWG` gains `llft_Wix` and
   `llft_Wmore`, and a stored guard is

   ```coq
   fguard P Q := ∀ i, P &&{llft_Wat_ext i}&&> Q
   llft_Wat_ext None     := llft_wsatG
   llft_Wat_ext (Some i) := llft_wsatG ∗ llft_Wmore i
   ```

   with `llft_incl`, `idx_bor_def'` and `llft_outlives_guards_at` all
   `fguard`s.  Two choices make it cost almost nothing.

   The family is **extended** by the ambient world rather than required
   to contain it, so `fguard_here` is an instantiation and the client
   owes no proof.  (The first attempt asked for the ambient world as a
   class obligation and put it in the section's `Context`; with
   `Set Default Proof Using "All"` that silently made every later lemma
   - `big_sepS_set_map` among them - abstract over it, and the file's
   second section, which has no instance, could no longer use them.
   The error surfaces as a `rewrite` whose "LHS matches but type
   classes inference fails", a long way from the cause.)

   And every world of the family **contains** the ambient one, so
   `guard_wsat_sep` turns any guard already proved at `llft_wsatG` into
   a member of the family (`fguard_of_here`).  That is not a
   convenience, it is the right shape: an inclusion can be backed by a
   *shared borrow*, which lives in the ambient level's `shr_wsat`, so a
   guard stored at level `k` is usable exactly where that level's
   machinery survives - the thesis's `∗_{k<j} Winv_k` for `j` above it.
   A family of arbitrary worlds would have been unsound for exactly the
   guards that matter.

   The structural inclusions keep world-parametric forms
   (`llftl_incl_sub_at` and three others), which is what the typing
   layer needs when it proves a guard at another interpretation's
   world; the family versions are a line each on top.  `typing/` gains
   `dincl_incl` beside `dincl_sem`, for rules whose inclusion is going
   to be stored.

   #### Done: the borrow names leave `llft_logicGS`

   `bor_name` and `o_name` are exactly what a level varies.  They were
   fields of `llft_logicGS`, which made "the same lifetime logic with
   another level's borrows" unnameable; they are now `LlftBorNames`, a
   class of its own, so `llft_wsatG` is a function of it.  `verus_haltGS`
   carries the field and `verus_haltNames` carries it beside `an_llft`.

   #### What is left: construction, not expressibility

   Nothing in `llft_wsat` now stands in the way, and the two remaining
   items are both *building* what is already sayable.

   1. **Allocating one level's borrow machinery against the existing
      shared state** - **done**, `llft_bor_wsat_alloc`.  A second level
      gets its own `bor_name`, `o_name`, box and shared-borrow family
      over the same lifetime algebra, kill order, minted set and
      outlives authority.  It is born at the *empty* prefix of the kill
      order, which is sound precisely because a level may lag - before
      that change the lemma could not have been stated, since a fresh
      level would have had to be born knowing every kill that had
      already happened.  What it needs of the state already there is
      four persistent facts, collected as `llft_shared_wits` and handed
      out by `llft_wsat_alloc`.
   2. **Naming the two halves of `verus_halt_wsat_core`** - **done**,
      `verus_halt_wsat_core_split`: `verus_halt_wsat_shared` (the lifetime
      tokens, the kill order, the minted atoms, the outlives relation)
      beside `verus_halt_wsat_lvl` (everything that holds a formula or names
      a borrow).  As with `llft_inv_main`, the flat definition stays and
      the split is a lemma, because every rule in `typing/` destructures
      the flat form.

   #### What is left, and a correction to the shape of it

   Hoisting `an_llft` out of `verus_haltNames` and rebuilding
   `verus_halt_wsat_below` as one shared copy beside `∗_{k<j} Wbor_k` is now
   a change confined to `typing/level_ctx.v` and `soundness.v` - except
   for one thing, which scoping it turned up and which is sharper than
   what is written above.

   **The shared half is not quite level-independent, and the guard
   family as built does not yet say why that is all right.**
   `llft_other_shared` holds `llft_outlives_guards_at ol`, and an
   `fguard` is `∀ i, P &&{llft_wsatG ∗ llft_Wmore i}&&> Q` - it names
   *the ambient level's* `llft_wsatG`.  That is right for a guard this
   level stored, and it is what makes `fguard_of_here` sound.  But the
   shared half is held once and the guards in it were stored by
   *different* levels, so what it should say is

   >  `∀ o ∈ ol, ∃ k, ∀ i ≥ k, @[o.1] &&{W i}&&> Alive llft_name o.2`

   - each guard usable at every world **above the level that stored
   it**.  The existential over the storer is the part that is missing,
   and it needs `llft_Wix` to carry an order rather than being a bare
   type, with `llft_Wat` monotone in it.  (The current family is the
   special case where every guard was stored by the ambient level, which
   is exactly the one-level situation `typing/ctx.v` instantiates.)

   So the remaining order is: give `llft_Wix` its order and
   `llft_outlives_guards_at` the existential; then hoist `an_llft`;
   then the rest of step 5 below.

   

   ### Done: levelled borrows, mechanized

   Before doing that refactor it was worth asking whether the design it
   bets on is sound, because **neither source has built it**.  The
   thesis's Chapter 5 stratifies a *functional* language: its only
   sharing mechanism is Nola's invariant, and it has no lifetimes and no
   borrows.  `nola/examples/rust_halt/` has lifetimes and borrows and
   proves total correctness with them - and has **no function type at
   all**; there is no `ty_fn` anywhere in that directory.  "A function
   type whose execution level bounds what it may reach, stored in a
   borrow" is in neither place, and it is exactly what `fn_fml` needs.

   `typing/strat_bor.v` builds it, and the answer is yes.  Two things had
   to hold, and both are facts about Nola's existing code rather than
   guesses:

   - the separation of lifetime tokens from borrow bookkeeping, above;
   - **ending a lifetime needs no world satisfaction.**  `lft_end` is
     `1.[α] ==∗ [†α]`, a bare basic update, and a dead lifetime's borrows
     are settled *lazily* by the lender, with whichever level's world
     satisfaction it happens to hold.  Had killing a lifetime needed
     every level at once, levelling the borrows would have been
     impossible outright, because a body at level `j` never holds the
     levels above it.

   What those two leave open is whether the recursion on the level still
   closes with borrows in it, and it does, for (5.5)'s reason:
   `⟦&{α}ₖ T⟧ v` is a borrow *token* naming the syntax `T`, and never
   interprets it.  So level `k`'s world satisfaction holds types whose
   function types are at levels `≤ k`, which mention only `Wbor_h` for
   `h < k`.  Strictly decreasing, so the construction is `strat.v`'s
   unchanged.

   `typed_call_borrowed` is the payoff: a closure of type `A →ⱼ B` stored
   in a borrow at slot level `k`, retrieved at execution level `i` and
   called.  Its two side conditions are forced - `j ≤ k` to store
   (`bwf`), `k < i` to open (`bor_open_lv`) - and together they are the
   whole argument, since the callee then runs under `∗_{h<j} Wbor_h`
   while the borrow holding it lives at level `k ≥ j`, which the callee
   does not hold.  `knot_not_typable` states that, and `ex_borfn_total`
   runs a closed program of that shape and proves it terminates.

   `nola/iris/borrow.v` gained one lemma for this, `borrow_wsat_alloc_name`,
   the exact analogue of `sinv_wsat_alloc_name`: several borrowing
   machineries have to hand out their ghost names *before* the
   interpretation that mentions them is built.

   ### Why the cheap design does not work

   It is worth writing down why the borrows have to be levelled at all,
   because the cheap alternative is tempting and `strat.v` is what rules
   it out.

   The cheap design: keep **one** `verus_halt_wsat` at `⟦⟧ᶜ_L`, and put the
   levelled part beside it as `lvs_below γs (λ k, ⟦⟧ᶜ_k) j`, which
   `typing/levels.v` already builds.  A body at level `j` would then run
   under `verus_halt_wsat ∗ lvs_below γs _ j`.

   It is unsound, and Landin's knot is the counterexample.  Take
   `f : fn →ⱼ` and store it in an ordinary borrow.  The borrow's content
   is interpreted at `⟦⟧ᶜ_L`, which interprets `fn →ⱼ` for every `j < L`;
   so `f`'s own body, running at level `j` and holding `verus_halt_wsat`, can
   open that borrow, read `f` back, and call it - because calling
   `fn →ⱼ` asks for `lvs_below … j`, which the body has.  The knot
   closes.

   What stops it in the thesis is that a reference at level `k` holds a
   type interpreted at `⟦⟧ₖ`, and `⟦fn →ⱼ⟧ₖ` is `False` unless `j ≤ k`.
   So anything a level-`i` body can reach through a reference has
   execution level `≤ k < i`, and that function's body cannot reach the
   reference back.  `strat.v`'s `tsem_gen` carries that `⌜j ≤ length l⌝`
   for exactly this reason, and `typed_call_stored` is the rule where it
   bites.

   In the port, "a reference at level `k`" means a borrow whose content
   is interpreted at `⟦⟧ᶜ_k` - so the borrow families must be levelled,
   and there is no way round it.

   ### The remaining order of work

   1. **The ghost state** - done, `typing/level_ctx.v`: `verus_haltGS_of`
      (the port's `verus_haltGS_at`) and `verus_halt_wsat_below`.  One thing it
      still gets wrong on purpose: `verus_haltNames` carries a whole
      `llft_logicGS`, so each level has its own *lifetime tokens*.  The
      design wants `llft_name`, `d_name`, `log_name`, `mint_name`,
      `oset_name` and `osub_name` shared and only `bor_name`/`o_name`
      varying.  Those two are now `LlftBorNames`, a class of their own,
      and `verus_haltNames` carries it - so the split is *expressible*; what
      is left is the two construction items under step 4.
   2. **`LtRa`'s two halves on two ghost names** - done, so that
      `bor_name` can vary with the level while `llft_name` does not.
   3. **A per-level view of the dead set**, with lazy catch-up - done,
      `lifetime/level.v`: the change of variable, the three operations
      in it, `lv_borrow_ready`, `lv_catch_up`, `kill_run_mono`.  No
      lifetime-level invariant was needed; two of this plan's
      expectations were wrong and the sections above record how.
   4. **Decouple `lifetime_full.v`'s invariant** - **done**, and with
      it the lag (dead set *and* outlives), the naming of the two
      halves (`llft_wsatG_split` / `llft_inv_other_split`), the stored
      guards as a family over client-supplied worlds (`fguard`), and
      the borrow names as a class of their own (`LlftBorNames`).
      Nothing in `llft_wsat` fixes the execution level any more.  All
      of `typing/` is untouched except for the mask side conditions the
      catch-up forces, a handful of `fguard_here`/`fguard_of_here`
      insertions where a stored guard meets an ambient one, and the
      trivial instantiation of the world family in `typing/ctx.v`.  The
      two items under "What is left: construction, not expressibility"
      above are *building* the family of levels, not making it
      sayable.
   5. **A level on every type former and on `typed_body`** - **done**.

      `typed_body`'s world satisfaction is a parameter (`typed_body_at`),
      and `typed_body` is the instance at the ambient world, so all 162
      of its use sites across `typing/` are unchanged.  `≤-→` is
      `typed_body_at_wsat` - one `twpw_incl_fupd` - and
      `typed_body_lv_le` is that over `verus_halt_wsat_below_le`.  Nothing
      else is needed for it: no induction on the level, no condition on
      the context's types, nothing about the interpretation, because the
      family is built so that `below j` is literally a conjunct of
      `below j'`.

      The `type` record gains `ty_lev`, threaded exactly as `ty_size` is,
      and the structural formers compute it: a product is the max of its
      components', a sum the max over its variants, a modification, an
      owning pointer and a unique borrow inherit their pointee's, and the
      fixpoint's is the chain's.

      The order was the opposite of how this item used to read, and the
      note that got it right is kept below: adding `ty_lev` *first* would
      have bought a hundred edits and no theorem.

      Its two halves are *not* independent, and the order is forced the
      other way round from how it reads.  Adding `ty_lev : nat` to the
      `type` record is the small half - twenty-two formers define
      `ty_size`, and `ty_lev` would be threaded exactly as `ty_size` is,
      through the OFE mixin, `ty_size_ne`, `type_ne`/`type_contractive`,
      subtyping and `rec.v`'s chain - but on its own it is a field with
      **no law**: the level only means something once `ty_gho` is
      interpreted at *that level's* ghost state, and that is step 4's
      two construction items, not this one.  So the useful order is:
      finish building the family of levels, then give `typed_body` its
      `verus_halt_wsat_below ... j`, and let the formers' levels fall out of
      what that forces.  Adding the field first buys a hundred edits and
      no theorem.

      `twpw_verus_halt_le` and `verus_halt_wsat_below_le` (`typing/level_ctx.v`)
      are already proved, so `ty-lev` itself costs nothing when the time
      comes.
   6. **`fn_fml`'s judgment carrying its execution level** - the shape of
      what is left changed twice while doing it, and both times toward
      something smaller.

      Done: `fn_params` carries nothing, `fn` carries the arrow's level
      `j` and sits strictly above it (`fn_ty_lev : ty_lev (fn j fp spec)
      = S j`); `FnFml` carries `fn_wsat_lv : nat → iProp Σ`; and the
      class has **collapsed to one equation**.  `fn_fml_sem_2`, the field
      with no model, is now a *lemma*: `nola/bi/deriv.v`'s

      ```coq
      Deriv_const : (∀ δ', ⟦J⟧(δ') ⊣⊢ Body) → Body ⊢ δ J
      der_const   : (∀ δ', ⟦J⟧(δ') ⊣⊢ Body) → der J ⊣⊢ Body
      ```

      says that a judgment whose semantics ignores the candidate *is* its
      body, introduction as well as elimination.  So `FnFml`'s obligation
      is `fn_fml_sem`, one `⊣⊢` at every candidate; persistence,
      specialisation and both directions follow.

      **And the formula side needs no judgment at all.**  This port's
      `fn` is capture-free - `type_fn`'s premise is `∀x ϝ k wl, ⊢
      typed_body …`, a *tautology* - so the body's derivability is a fact
      about the code, carrying no resources.  `fn_pure_candidate` in
      `typing/function.v` takes the ghost assertion to be
      `pure_fml (⊢ fn_body Wlv j fp spec x)` and checks all five
      obligations, closed under the global context: `pure_sem_at_any`
      makes it candidate-independent for free, which is exactly what
      `der_const` wants.

      It does not give the `⊣⊢` the class used to ask for, because the
      missing direction `fn_body ⊢ ⌜⊢ fn_body⌝` is false.  So the class
      stopped asking: `fn_fml_elim` at every candidate and
      `fn_fml_intro` at the Coq level, which is the shape every use in
      the development already had.  `fn_pure_candidate` then supplies
      exactly those, and `typing/fn_inst.v` and `fnFml_flat` are the two
      instances built on it.

      **Where the soundness actually sits.**  This paragraph used to
      say that with `Wlv := λ _, verus_halt_wsat` "a diverging program
      would satisfy `verus_halt_type_soundness`", and that totality does
      not rescue it because the knot's body needs no Löb step.  Both
      halves are wrong and the correction is worth keeping.

      `type_soundness` is an ordinary Rocq theorem taking `⊢ typed_body
      … e tr` to `sn erased_step`, and every rule here is checked
      against a total `twp`, so no `FnFml` whose obligations are
      provable can make a divergent program typable - Rocq would be
      inconsistent.  And the knot's body *does* need a Löb step: its
      premise is `⊢ fn_body …`, a closed Coq-level entailment, and a
      self-referential one has nothing to prove it with once `twp` has
      dropped Löb.  VerusBelt's `type_fnrec` is precisely the rule
      proved by `iLöb`, and precisely the rule this port does not have -
      until `typing/recursion.v`, which replaces it and `type_cont` with
      their well-founded forms: the self-reference is at a *smaller*
      argument, which a knot cannot use.

      So a degenerate `Wlv` costs **content**, not soundness: the level
      stops constraining anything and something cruder does the work.
      The level is still what *should* do it, and
      `typing/strat_bor.v`'s `knot_not_typable` is the argument in one
      line - a borrow slot of level `k` admits a function of execution
      level `j ≤ k`, while *opening* that slot asks for `> k` - over a
      model that indexes its slots by level, which this port's borrow
      formers still do not.

      So what is left is **not** "carry the interpretation through the
      program logic" - that estimate, 226 occurrences of
      `tctx_interp`/`cctx_interp`/`ty_own` plus every rule replayed at an
      arbitrary candidate, was for the judgment route and the judgment
      route is no longer needed.  What is left is the **borrow-slot level
      discipline**: `&uniq`, `&shr` and the owning pointers must record
      the level of the machinery they use, so that storing a function of
      execution level `j` in a slot of level `k` forces `j ≤ k` while
      opening it forces `> k`.  `ty_lev` is the field that records it,
      `strat_bor.v` is the specification, and `verus_halt_wsat_below … j` -
      built on this branch - is the world satisfaction it indexes.

3. **Recursive types** - done, in `typing/rec.v`; what follows is the
   record of how, because every step of it was forced.

   `typing/fixpoint.v` builds a recursive type as a COFE limit, and a `cif`
   is complete as a `prost`, not an OFE, so it had to move to
   `profix`/`Productive`.  Until then it assumed `Cofe (FML $oi Σ)`, which
   the model cannot discharge.  `rec.v` now takes that fixpoint and nothing
   depends on the assumption; `fixpoint.v` stays for its lifetime half (see
   "Still to do").

   **The design, and why the split alone is not enough.**  `profix` needs
   its carrier to be a `prost` with `Cprost` - a genuine limit constructor.
   `cif` has both (`cifPR`, `cit_cprost`), and `prod_cprost`/`fun_cprost`
   lift them through products and `-pr>`, so the structure is there.  `cif`
   is confirmed *not* a COFE: `nola/util/cit.v` gives only an `OfeMixin`,
   with no `Cofe` instance anywhere, so the present `Cofe (FML $oi Σ)`
   assumption really is unsatisfiable in the model.

   The record would split as `tyd 𝔄` (data) plus `Ty (T : tyd 𝔄)` (laws),
   keeping `Record type 𝔄 := { ty_d :> tyd 𝔄; ty_laws : Ty ty_d }` with
   `ty_d` a coercion and `ty_laws` an instance, so the 245 uses of `ty_size`
   and the 168 uses of the laws keep working; arity-preserving wrappers
   (`ty_size_eq` taking `T` and a `Ty T` instance) cover all but the handful
   of uses written in projection syntax.  32 definitions split into data
   plus a `Ty` instance.

   **But the split is necessary and not sufficient.**  `rust_halt/rec.v`
   proves `Ty (ty_rec F)` by `rewrite ty_rec_unfold`, and that works only
   because its laws are *unconditional*: `ty_box_ty {X T} : Ty (ty_box T)`
   asks nothing of `T`.  Ours are conditional.  `own_ptr`'s
   `ty_gho_depth_mono_at` obligation applies `ty_gho_depth_mono_at ty` to
   the inner type, and five of the eight laws are like it - the depth pair,
   `ty_guard_proph`, `ty_gho_pers_pers_at`, `ty_gho_pers_impl`.  The reason
   is the depth discipline: `[Sx(d') := d]` passes `d'` *inward*, so bumping
   the outer depth bumps the inner one, whereas `rust_halt` writes
   `∃ d', ⌜d' < d⌝ ∧ …` and bumping `d` is then free.

   **Which way `rust_halt` does it.**  Not by making *every* former
   unconditional - `ty_prod_ty` and `ty_sum_ty` are
   `{!Ty T, !Ty U}`-conditional, like ours.  The pattern is three layers:

   * *guarded* formers - `ty_box`, `ty_mutref`, `ty_shrref` - write
     `∃ d', ⌜d' < d⌝ ∧ …` and have **unconditional** `Ty`;
   * *unguarded* formers are conditional, and that is fine;
   * `ty_rec_ty` asks for `∀ T, Ty (F T)`, which holds exactly when `F` is
     built from guarded formers.

   That last line is the thesis's guardedness condition (§ 5.1: a recursive
   type variable must be "guarded by the reference type constructor" or sit
   at a lower level).  The syntactic condition on the type system and the
   unconditionality of `Ty` are the same fact.

   The genuinely semantic laws are not in `Ty` at all upstream: `TyOp`,
   `Resol` and `Real` are separate classes with `…Le` ("at every lower
   depth") variants, and `ty_rec_ty_op`, `ty_rec_resol`, `ty_rec_real` are
   proved by **induction on the depth index**.  That is how a conditional
   law survives a fixpoint without any limit preservation.

   **So the route that follows the development is the first**, and it is
   narrower than "change every former".  Only four files pass the depth
   inward - `own.v`, `shr_bor.v`, `pcell.v`, and `type.v`'s `by_succx` - and
   `&uniq` is already in the bounded form (`⌜S d' ≤ d⌝` with `d'` carried in
   the refinement), which is why its depth obligations close by `lia` rather
   than by the inner type's law.  The work is then:

   1. convert the *guarded* formers to bounded indices;
   2. split the eight laws into a structural `Ty`, unconditional for the
      guarded formers, plus depth-indexed classes for `ty_guard_proph` and
      the persistence pair;
   3. then the `tyd`/`Ty` record split above, after which `Ty (ty_rec F)` is
      `rewrite ty_rec_unfold` and the semantic laws are depth inductions.

   ### Step 1 is done, and it is narrower than it looked

   Bounding the depth *globally* - redefining `by_succ` as `∃ d' < d` - was
   tried first and is the wrong move.  It costs churn in every former and it
   buys nothing outside the guarded ones, because an unguarded former's
   index weakening reaches its argument's law anyway.  Worse, it breaks
   `own_ptr`'s `ty_guard_proph`: the ghost part and the persistent part then
   carry *separate* witnesses with no reason to agree, and the field needs
   them at one depth.  `by_succ` is back to its exact match.

   The bound belongs to `&shr{κ}` alone, and there it must cover **both**
   indices, not just the depth.  Weakening `g` is obstructed for exactly the
   reason weakening `d` is: the contents sit behind a guard, and a guard is
   not monotone in its right-hand side.  `type.v` therefore gains
   `by_ltx`/`by_lex` (`[Ltx(d') := d]`, `[Lex(gg) := g]`), used only by
   `shr_bor.v`:

   ```coq
   st_ghox x d g tid := [Ltx(d') := d] [Lex(gg) := g]
     (guard_fml (alive_fml κ) (… ↦[^ …]!∗ ty.(ty_phys) (snd x) tid) ∗
      guard_fml (alive_fml κ) (ty.(ty_ghox) (snd x) d' gg tid) ∗
      ty.(ty_gho_persx) (snd x) d' gg tid)
   ```

   Both weakening obligations are then *widen the bound and `lia`* - they do
   not mention `ty`'s laws at all, which is the whole point.  The cost is
   that the triple is no longer reachable by `rewrite shr_bor_gho /=`;
   `shr_bor.v` exports `shr_bor_gho_elim` (names both witnesses) and
   `shr_bor_gho_intro'` (takes the pieces plus the two bounds) and the ~20
   call sites in `pptr.v`, `pcell.v`, `borrow.v`, `type_sum.v`,
   `product_split.v`, `ra.v`, `atomic_inv.v` and `local_inv.v` go through
   those.  `dguard_depth_mono` is gone: every site that used it was building
   a `&shr` ghost assertion and now supplies the witness it already had.

   `own_ptr` and `pcell` keep `[Sx(d') := d]` and stay conditional on their
   argument, which is what `ty_prod_ty` does upstream.

   ### Persistence had to become structural too

   Bounding the indices fixes two of the eight obligations; a third,
   `ty_gho_pers_pers_at`, was still reaching for `ty`'s persistence law,
   because `&shr`'s third component is `ty.(ty_gho_persx) …`.  Upstream does
   not prove that either - `sty_shrref` writes `□ cif_store (ty_shr T …)`
   and `Sty (sty_shrref α T)` closes it by `exact _`.

   `TypeFml` therefore gains `pers_fml` (instantiated to `cif`'s own `□`,
   with `pers_fml_sem` and `pers_sem_at_any` both `done` in the model), and
   `&shr`'s ghost assertion is `[Ltx(d') := d] [Lex(gg) := g] pers_fml (…)`.
   Persistence is then structural.  The `□` does not leak: all three
   components are persistent for a `ty : type 𝔄`, so `shr_bor_gho` strips it
   by `bi.intuitionistic_intuitionistically` and every client is unchanged.

   ### What is left, and the real obstruction

   Exactly one of `&shr`'s eight obligations still reaches into `ty`:
   `ty_guard_proph`.  That is not a defect of the encoding - upstream keeps
   the semantic laws (`TyOp`, `Resol`, `Real`) out of `Ty` precisely so that
   the guarded formers' instances can be unconditional, and `ty_guard_proph`
   is one of those (`ty_shrref_ty_op` is `{!Ty T, !TyOpLe T κ 1 d}`).

   So the record split itself is a single, well-identified move: data +
   sizes + physical length equations + index weakening + persistence +
   `ty_gho_pers_impl` form the unconditional `Ty`; `ty_guard_proph` becomes
   a side class, discharged at the fixpoint by depth induction the way
   `ty_rec_ty_op` is.  Every other former stays exactly as conditional as it
   is today.

   **But the split is still not the hard part.**  `profix F` needs
   `Productive F`, and productivity over `cif` is a *syntactic* condition:
   `≡[0]≡` identifies two `cit`s whose `cdom` children differ but whose
   `idom` children do not, so **every occurrence of the recursion variable
   must sit in a `cdom` position**, and a `cdom` child is one a constructor's
   `Ecsem` may only hand to `δ` as a judgment - never take the semantics of.
   Checking the model:

   | constructor | definition | position |
   | --- | --- | --- |
   | `cif_guard Px Qx` | `cif_in guardCT () nullary (binary Px Qx) ()` | **cdom** |
   | `cif_pers Px` (`pers_fml`) | `cif_un cifs_pers` = `Citg _ (unary Px) nullary ()` | idom |
   | `cif_sep`, `cif_ex`, `cif_pure` | `cif_bin` / `Citg _ … nullary` | idom |

   `&shr{κ} ty`'s body is two guards *and* `ty.(ty_gho_persx) …` sitting
   bare, so `λ T, shr_tyd κ T` is `Preserv` but **not** `Productive`.  That
   third component is the whole obstruction.

   Upstream does not have it: `sty_shrref`'s body is
   `□ cif_store (ty_shr T …)` and `cif_store` is `Productive` by
   construction - rust_halt's sharing predicate is a *single* persistent
   formula, so there is no separate persistent part to leave outside.

   Three ways out, with what each costs:

   1. **Move the persistent part behind the same guard.**  `&shr`'s own
      prophecy law no longer needs it: `type.v` now proves
      `ty_gho_pers_dup` (the persistent part comes out of the ghost
      assertion without consuming it, because it is persistent) and hence
      `guard_gho_pers`, `(R &&{W}&&> ghox) ⊢ (R &&{W}&&> persx)`.  So
      `ty_guard_proph`'s plain-`persx` premise is redundant for every
      implementor and could simply be deleted.  What blocks it is the
      *clients*: `pptr.v`, `pcell.v`, `borrow.v` and `product_split.v`
      destructure the inner persistent part to peel a depth layer
      (`own_ptr_gho_pers` is `False` at depth 0, so `destruct dd` is how
      they learn `dd = S dd0`).  Under a guard a sep splits
      (`dguard_rhs_sep_l/r`) but an existential does not, and
      `guard_exist_strengthen` only *adds* a persistent fact under one - it
      cannot pull the witness out.  `typed_pptr_borrow` has no
      `lctx_lft_alive` premise, so it cannot open the guard either.
   2. **Store it instead of guarding it** - the faithful port.
      `nola/iris/store_deriv.v` already has `cif_store` with
      `cif_store_productive` and `stored_acc : stored Px -∗[dinv_wsat ⟦⟧ᶜ]◇
      ⟦Px⟧ᶜ`, which needs only an update and the world satisfaction, *not* a
      lifetime token - so the clients above can open it where they are.  The
      cost is that `dinvGS (cifOF CON) Σ` and `dinv_wsat ⟦⟧ᶜ` join
      `verus_haltGS` and `verus_halt_wsat` (as they do `rust_haltGS`), a `storeCT`
      joins the CON, and every `&shr` construction site becomes an
      allocation (`store_alloc_pers`, a fupd) rather than just supplying a
      formula.  That is a change to the soundness statement's world
      satisfaction, so it is the largest of the three - and it is what
      upstream actually does.
   3. **Expose the inner depth.**  Keep the persistent part out of the body
      and give `&shr` a pure witness that the clients can use instead of
      peeling.  This is not upstream and looks ad hoc, but it is local.

   Route 2 is the one that follows the development.  Nothing before it is
   wasted: the bounded indices and the structural `□` are needed whichever
   way the persistent part goes, and `guard_gho_pers` is what lets
   `ty_guard_proph` drop its premise under any of the three.

   Route 2 is cheaper than it sounds in one respect: `storeCT`, `cif_store`,
   `cif_store_productive`, `storeCT_ecsem`, `storeJT` and `storeJT_dsem` are
   all already written in `nola/iris/store_deriv.v`, so what is new there is
   one constructor in `verus_haltCONF` and one judgment in `verus_haltJUDGF` - both
   of which `inst.v` already extends six and four times over.

   It is *dearer* than it sounds in another.  `dinvGS FML Σ` is
   definitionally `sinvGS FML Σ`, which `verus_haltGS` already carries - but
   that family is taken: `nola/verus_halt/boxes.v` defines
   `box_wsat sm := sinv_wsat (λ γ Px, slice_body sm γ Px)` on it, and
   `box_wsat bor_sem` is a conjunct of `verus_halt_WGuard`.  A `sinvGS` carries
   exactly one `sinv_name`, so the store needs a second family: a new
   `verus_halt_store_name : gname` field beside `verus_halt_shr_name` and
   `verus_halt_eternal_name`, a non-global `sinvGS` built from it, and care that
   `storeCT_ecsem` and `store_as_cif` resolve `dinvGS` to *that* one rather
   than the box's.  Then `dinv_wsat bor_sem` joins `verus_halt_wsat`, whose
   eight `WsatIncl` instances in `ctx.v` spell their remainders out and so
   all change, and the soundness proof allocates one more family.

   ### The rest of the productivity audit

   The persistent part is the *interesting* obstruction, but it is not the
   only one.  A `cit` compares selectors and data by plain equality and
   `idom` children by `≡[k]≡`; only `cdom` children get `≡[<k]≡`.  So every
   component of the argument that `&shr{κ}` mentions has to be checked:

   * `ty_phys` - appears as `cells_fml … (ty.(ty_phys) (snd x) tid)`, and
     `cif_cells l cs fv` puts all three in the **selector**.  Harmless, but
     only because `ty_phys_eq2 x tid : syn_phys x = ty_phys x tid` *forces*
     it: writing `syn_phys (snd x)` in the definition instead removes the
     dependence outright, and `shr_bor_gho` can keep its present statement
     by rewriting with `ty_phys_eq2`.
   * `ty_size` - same situation, forced by `ty_size_eq2`.
   * `ty_lfts` and `ty_E` - **not** forced, and genuinely not fixpointable:
     `st_lfts := κ :: ty.(ty_lfts)` would need
     `ty_lfts T = ty_lfts T'` for *all* `T`, `T'` at level 0.  rust_halt
     does not have this problem because its `ty` is `natPR * (ownty *
     shrty)` - it carries no lifetime list at all, and lifetime inclusion
     is a `LftIncl` side condition.

   ### Done: [&shr{κ}] is productive

   `typing/inst.v` now proves it, at the concrete `verus_haltCON` where the
   `prost` lives:

   ```coq
   Lemma shr_bor_ghox_productive {𝔄} κ (ty ty' : type 𝔄) k x d g tid :
     (∀ y t, ty.(ty_phys) y t = ty'.(ty_phys) y t) →
     (∀ y dd gg t, ty.(ty_ghox) y dd gg t ≡[<k]≡ ty'.(ty_ghox) y dd gg t) →
     (∀ y dd gg t,
       ty.(ty_gho_persx) y dd gg t ≡[<k]≡ ty'.(ty_gho_persx) y dd gg t) →
     st_ghox (shr_bor_st κ ty) x d g tid ≡[k]≡
       st_ghox (shr_bor_st κ ty') x d g tid.
   ```

   The two ghost components are needed only at `≡[<k]≡` - the recursive
   occurrence is *guarded* in the thesis's sense - and `ty_phys` is needed at
   plain equality, which `ty_phys_eq2` forces anyway.  `Print Assumptions`
   gives `Eq_rect_eq` and nothing else.

   Getting there took five changes, each of which is forced:

   1. both of `&shr`'s indices bounded, so weakening is widening a bound;
   2. `pers_fml` (`cif`'s `□`), so persistence is structural;
   3. a store world satisfaction, as a second `sinvGS` family beside the
      boxes', placed *inside* `verus_halt_WGuard`;
   4. `pstoreJT`/`pstoreCT` - `store_deriv.v`'s `cif_store` with the
      modality dropped, since the content is persistent;
   5. `ty_guard_proph` handing its conclusion out under `Wguard`, which is
      `rust_halt`'s `TyOpAt` shape, because reading a `cdom` child back needs
      the world satisfaction and building a guard does not supply it.

   ### Done: the fixpoint, in `typing/rec.v`

   `profix` over the data, with `Ty` transported by `ty_rec_unfold` and the
   prophecy law by depth induction:

   ```coq
   Definition ty_rec {𝔄} (F : tyd 𝔄 → tyd 𝔄) `{!Productive F} := profix F.
   Lemma ty_rec_Ty : (∀ T, Ty (F T)) → Ty (ty_rec F).
   Lemma ty_rec_TyProphAt lfts :
     (∀ T d, TyProphLt lfts T d → TyProphAt lfts (F T) d) →
     ∀ d, TyProphAt lfts (ty_rec F) d.
   ```

   and the composition that makes it usable - `μ X. G (&shr{κ} X)` for any
   *size-preserving* `G`, since `&shr{κ}` contributes the productivity and
   `Ty (shr_tyd κ T)` is unconditional:

   ```coq
   Lemma shr_rec_productive : Preserv' _ _ G → Productive' _ _ (λ T, G (shr_tyd κ T)).
   Lemma ty_rec_shr_Ty : (∀ U, Ty U → Ty (G U)) → Ty ty_rec_shr.
   ```

   That is the thesis's guardedness condition (§ 5.1) and `rust_halt`'s
   three-layer pattern: guarded formers unconditional, unguarded ones
   conditional, `ty_rec` asking for `∀ T, Ty (F T)`.  `Print Assumptions`
   gives `Eq_rect_eq` and nothing else, and the `Cofe (FML $oi Σ)` that
   `typing/fixpoint.v` assumes never appears.

   The file is in two sections, and the split is forced.  The laws live in
   an *abstract* `typeG` context, like `typing/shr_bor.v`'s, because with
   the model concrete Coq reduces `bor_sem` and the `AltSem` projections
   eagerly (they are primitive) and then none of the development's own
   lemmas can be applied by unification.  The `prost` lives in a *concrete*
   section, because `cif` is where it is.  `tydata 𝔄` (abstract) and
   `prost_car (tyd 𝔄)` (concrete) are the same type, which `tod` witnesses.

   ### Done too: the structural formers

   `prod_tyd` and `own_tyd` are `product.v`'s and `own.v`'s bodies with the
   record replaced by its data, with `Ty`/`TyProphAt` *conditional* on their
   arguments' - which is all `ty_rec_shr_Ty` asks, since in
   `μ X. G (&shr{κ} X)` the hole is already behind the guarded former.
   `ty_prod_ty` is conditional upstream for the same reason.

   Their `Preserv'` instances are what `shr_rec_productive` composes with,
   and they are free to mention the argument's physical contents and size:
   those sit in a constructor's *selector* and *data*, which `proeqv k`
   compares by equality at every level, and the discrete components of `tyd`
   supply exactly that.  Only the *guarded* former has to keep its argument
   out of those positions - which is what `&shr`'s `syn_phys` is about.
   `sum_tyd` and the rest are the same exercise, obligation for obligation.

   `TyProphAt_lfts` weakens the lifetime list, which composing formers
   needs: the hole's law arrives with the guarded former's lifetime
   prepended, and `TyProphAt` is antitone in that list.

   ### The thesis's method, and how `rec.v` corresponds to it

   Chapter 5 does recursive types without a metric at all.  Its syntax is

   >  `Typᵢ ∋ Tᵢ ::= … | ref°ₖ Tₖ | Tᵢ →ⱼ Uᵢ (j ≤ i) | rec Xⱼ. Tⱼ (j ≤ i) | Xⱼ`

   where every occurrence of a variable `Xⱼ` inside a type of level `i` is
   either **guarded** (`j = i`, and the occurrence under `ref°`) or
   **lower-level** (`j < i`).  The interpretation is then plain
   substitution:

   >  `⟦rec Xⱼ. Tⱼ⟧ᵢ v ≜ ⟦Tⱼ[rec Xⱼ.Tⱼ / Xⱼ]⟧ⱼ v`

   and it terminates for exactly two reasons: a guarded occurrence is
   *never semantically interpreted*, because (5.3)/(5.5) give `⟦ref°ₖ T⟧ᵢ`
   without ever mentioning `⟦T⟧ₖ`; and a lower-level occurrence recurses at
   a strictly smaller level.

   **That is the same condition `rec.v` enforces, in metric form.**  A
   `cifcon`'s `Ecsem` receives its `cdom` children as *formulas*, not as
   interpretations - the only thing it can do with one is hand it to `δ` as
   a judgment, or to an interpretation-free function like `dinv_tok`.  So
   "the argument occurs only under a `cdom` child", which is what
   `Productive` amounts to, *is* the thesis's "guarded by `ref`, whose
   interpretation does not depend on the body's".  `&shr{κ}` and `sown_tyd`
   are this port's `ref°`; `proeqv` plays the part of the level.  The
   correspondence is exact at the only point that matters, and it explains
   why the two guarded formers here are precisely the two whose semantics
   never interprets the argument.

   Where the port cannot follow the thesis is the refinement type.  The
   thesis has none - it is not a RustHorn-style system - so its `rec` is
   pure syntax and needs no solution to `𝔄 = F(𝔄)`.  `rust_halt` does have
   refinement types and uses `profix` with `listₓ`/`binₓ`, which is the
   route taken here.

   ### Done: subtyping of a recursive type, by induction not coinduction

   § 5.1 fn. 1 allows `≤-ref` to be used *coinductively*, and so derives
   `listᵢ T ≤ listⱼ U` from `T ≤ U`, `U ≤ T` and `i ≤ j`.  `rec.v` now has
   that rule for `ty_shr_list`, and the interesting part is that it needed
   **neither coinduction nor `Deriv`**:

   ```coq
   ty_rec_incl F G f P : (∀ d, P -∗ tyd_incl_lt (ty_rec F) (ty_rec G) f d -∗
                                 tyd_incl_at (F (ty_rec F)) (G (ty_rec G)) f d) →
                         ∀ d, P ⊢ tyd_incl_at (ty_rec F) (ty_rec G) f d
   ty_shr_list_subtype : lctx_lft_incl E L κ' κ → … →
     subtype E L (ty_shr_list κ T …) (ty_shr_list κ' U …) (shr_list_mapₛ f)
   ```

   Two reasons the thesis's device is not needed, and both are facts about
   the port rather than conveniences.

   * **The thesis's `rec` carries no index**, since it is plain
     substitution, so there is nothing to descend on and the loop has to be
     cut coinductively.  The port's guarded formers *do* carry one -
     `&shr{κ}`'s body is `[Ltx(d') := d] …`, i.e. `∃ d' < d` - so the loop
     is cut by well-founded induction on the depth, which is how
     `ty_rec_TyProphAt` and upstream's `ty_rec_ty_op` are already proved.
     What this took was a statement *indexed by `d`*: `type_incl`
     quantifies over the depth inside its `□`, so `tyd_incl_at` is the same
     pair of ghost components with `d` pulled out, and
     `type_incl_of_tyd_incl` puts it back.
   * **The quantification `Deriv_φ` would supply is already there.**  The
     thesis stores `□ δ(T ≤̇ U)`, a subtyping judgment at a derivability
     candidate; `type_incl` in this port is `□ ∀ sem, alt_sem sem → …`,
     i.e. quantified over every good candidate up front.  So the
     coinductive hypothesis has nowhere to live and nothing to do.

   The rest was congruences - `unit_tyd_incl`, `prod_tyd_incl`,
   `xsum2_tyd_incl`, `mod_tyd_incl` (which asks for a commuting square of
   the four maps, discharged by `unfoldshr_mapₛ`) and `shr_tyd_incl`, the
   only one that turns `tyd_incl_lt` into `tyd_incl_at`.  Its proof is
   `shr_bor.v`'s `shr_type_incl` with the depth exposed, and the backward
   direction of the ghost component is free because a shared borrow's
   ghost assertion is persistent - which is exactly what
   `type_incl_simple_type` exploits.

   The refinement type comes along: `prophecy/syn_type.v` gains
   `ptrlist_map`, `shr_list_mapₛ`/`own_list_mapₛ`, the two layout lemmas
   (`shr_list_size_eq`, `shr_list_phys_eq` - `ty_size_eq2`/`ty_phys_eq2`
   force a subtyping map to preserve both) and `unfoldshr_mapₛ`, the square
   that lets the rule be read off the body.  `Print Assumptions` on the
   rule gives `Eq_rect_eq` and `functional_extensionality_dep`, the latter
   only through `Isoₛ`.

   ### Done too: the same rule for `ty_own_list`, and what it cost

   `sown_tyd` used to hold its pointee behind `dinv_fml`, a bare invariant
   token, and that admitted **no** subtyping rule: a token names the
   formula it stores, so nothing turns `dinv_tok Px` into `dinv_tok Qx`.

   That is exactly the obstruction (5.5) exists to remove, and the port
   confirms the thesis's reading of it.  Its `ref°` stores a *different*
   type tied to `T` by two derivability assertions, and § 5.1 says the
   indirection is the only reason `≤-ref` is provable.  `&shr{κ}` here had
   the indirection already - its body is wrapped in a Leaf guard, and
   guards compose - which is why `shr_ghod_incl` can simply retarget it and
   why that former had a rule and the owning pointer did not.

   So `sown_persd` now holds `guard_fml empty_fml Px` in place of
   `dinv_fml Px`, and the trade is free:

   ```coq
   dinv_fml_guard_at (H : alt_sem sem) : sem (dinv_fml Px) ⊢
     (True &&{alt_WGuard sem}&&> sem Px)
   eguard_fml_alloc : bor_sem Px =[verus_halt_WGuard]=∗
     bor_sem (guard_fml empty_fml Px)
   ```

   The token is still how one is *allocated* - `dinv_fml_alloc` then
   `guard_fml_sem_2`, which needs the guard at every candidate the ambient
   interpretation maps into, hence `dinv_fml_guard_at` rather than
   `dinv_fml_guard`.  What is gained is that a guard *composes*, so
   `sown_tyd_incl` is `shr_tyd_incl` with one difference: the ghost
   component is not persistent (it carries the pointer and the deallocation
   permission), so the backward direction is not free - but it is still
   free of the argument's laws, because those two pieces are literally the
   same formula on both sides once `size_of 𝔄 = size_of 𝔅` and
   `syn_phys x = syn_phys (f x)` are used.

   `ty_own_list_subtype` is then `ty_shr_list_subtype` verbatim, minus the
   lifetime premise.  Both rest on `Eq_rect_eq` and
   `functional_extensionality_dep`, the latter only through `Isoₛ`.

   This did **not** fix the other half of the owning pointer: the pointee
   can still be borrowed and not moved out, for the reason recorded below -
   `ty_guard_proph` is guard-shaped and a `□` guard needs a *persistent*
   discriminator.  Subtyping and extraction are independent.

   For reference, (5.5) in full:

   >  `⟦ref°ₖ T⟧ᵢᵟ v ≜ ∃U, k' ≤ k. □ δ(T ≤̇ U) ∗ □ δ(U ≤̇ T) ∗ invₖ'ᴺ((ℓ+o) ↦ U)`

   `&shr{κ}` here puts that indirection in a guard and in
   `st_iff`/`inclJT` rather than in the type's own interpretation, which is
   why it needed no change.

   ### Done as well: a list

   `rec.v` ends with

   ```coq
   ty_shr_list κ T lfts E Hκ HT HP : type (shr_listₛ 𝔄)   (* μ X. Σ! [(); 𝔄 * &shr{κ} X] *)
   ```

   which is `rust_halt`'s `ty_list` with the one substitution this port
   forces - the shared reference in place of the owning pointer - and with
   it the recipe is closed end to end: a refinement type that is its own
   unfolding, the `ty_mod` bridge, structural formers for the body, the
   fixpoint, both law classes, and an actual `type` out the other end.
   `Eq_rect_eq` and `functional_extensionality`, the latter only because
   `SemiIso` is an equality of functions and every `Isoₛ` needs it.

   Three things it took.

   **A refinement type, `shr_listₛ`.**  `ty_rec` needs `F : tyd 𝔄 → tyd 𝔄` -
   the same refinement type in and out - and no former preserves it:
   `&shr{κ}` sends `𝔄` to `at_clocₛ 𝔄`, so a body's refinement is strictly
   bigger than its argument's and `𝔄 = F(𝔄)` has no solution in the grammar
   as it stood.  `rust_halt` solves this by choosing a refinement type whose
   unfolding matches the body's - `listₓ`, and `binₓ` for `mutlist`, because
   `ty_mutref` *doubles* the refinement - and bridging with `ty_mod` along an
   injective unwrap.  `shr_listₛ 𝔄` is that choice here, and
   `foldshrₛ`/`unfoldshrₛ` beside it are the unwrap.

   `listₛ` could not serve, and the reason is the one difference from
   upstream that matters.  `ty_mod` is free there because `ty_size` is
   unconstrained data; here `ty_size_eq2` and `ty_phys_eq2` tie a type to its
   refinement, so `Isoₛ` demands `size_of 𝔄 = size_of 𝔅` *and*
   `syn_phys x = syn_phys (f x)`.  `size_of (listₛ _) = 0` while the body is
   `xsumₛ`-shaped.  So `shr_listₛ`'s `size_of` and `syn_phys` clauses *are*
   the body's, written so the two sides are **convertible**:

   ```coq
   | shr_listₛ 𝔄₀ => S (list_max [0; size_of 𝔄₀ + 1])
   ```

   is `size_of (xsumₛ [(); 𝔄₀ * at_clocₛ (shr_listₛ 𝔄₀)])` with the `fmap`
   and the two `size_of`s already reduced - the recursive occurrence sits
   under `at_clocₛ`, whose size is `1` whatever is inside, so nothing has to
   recurse into the hole.  That one line is what makes `syn_iso_size_eq`
   `eq_refl` and, with it, every `pad` width in `syn_phys`; `shrlist_isoₛ` is
   then three `done`s and a case split.

   The cost was far lower than this plan estimated, for a reason worth
   recording: **`typing/syn_type.v` is dead.**  It is not in `_CoqProject`,
   has no `.vo`, and imports `nola.lrust`; the live grammar is
   `prophecy/syn_type.v` alone.  The estimate of "~10 fixpoints, and the same
   again in the copy" was therefore double.  The real blast radius of a new
   constructor is nine clauses in one file (`~~`, the prophecy
   interpretation, `syn_abstract`'s type, `syn_type_beq`, `vπ`, `ξl`,
   `size_of`, `syn_phys`, `syn_abstract`), three proof bullets
   (`syn_phys_size_eq`, `syn_abstract_phys_eq`, `prophecy.v`'s `syn_indep`),
   and nothing else in the tree - `inh_syn_type` and `blockedπ` have
   catch-alls, and the four `case: 𝔄` proofs in `of_just_and_neg_inh_syn_type`
   are closed by their `try by … exact inhabitant` as long as the new shape
   has an `Inhabited` instance, which `shrnil []` supplies.

   **A binary tagged sum at the data level, `xsum2_tyd`.**  `typing/sum.v`'s
   `xsum_ty` is the general one, over a heterogeneous list; two branches is
   all a list needs, and taking them one at a time means the `psum` is a
   plain `+` and every obligation is a case split rather than an induction
   over `𝔄l`.  `unit_tyd` beside it is the nil branch: no memory, no
   prophecies, `pure_fml True`.

   **And the lesson from the previous commit, applied.**  Every application
   in the section unfolds its abbreviation first.

   ### Done: the owning pointer, made productive

   `rec.v` also ends with

   ```coq
   ty_own_list n T lfts E HT HP : type (own_listₛ 𝔄)   (* μ X. Σ! [(); 𝔄 * own n X] *)
   ```

   which is `rust_halt`'s `ty_list` with *nothing* substituted.  Getting
   there needed one new piece of model, and the reason is worth stating
   exactly, because this plan had it wrong twice.

   **Nola's store is one-shot, and a Leaf guard cannot use it.**
   `nola/iris/store.v`:

   ```coq
   store_tok Px := ∃ γ, token γ ∗ dinv_tok (Px ∨ ▷ token γ)
   store_tok_acc : store_tok Px -∗[dinv_wsat ⟦⟧ᶜ(δ)]◇ ⟦ Px ⟧ᶜ(δ)
   ```

   Access deposits the token in the invariant, so the content never comes
   back.  Fine for `ty_box`, whose `ty_own` is consumed when the box is
   dereferenced.  Not fine for a guard: `guard_acc` is
   `Q ∗ (Q -∗ W ∗ T)`, so a guarded resource must be returnable.

   **But a plain simple invariant is exactly what is wanted.**
   `dinv_tok` is persistent and its accessor is *reversible*:

   ```coq
   dinv_tok_acc : dinv_tok Px -∗ dinv_wsat sm -∗ sm Px ∗ (sm Px -∗ dinv_wsat sm)
   ```

   so, with `dinv_wsat` sitting inside `verus_halt_WGuard` (it already did, for
   `pstore`), **an invariant is a guard** - three lines, no axioms:

   ```coq
   Lemma dinv_fml_guard {Px} :
     bor_sem (dinv_fml Px) ⊢ (True &&{verus_halt_WGuard}&&> bor_sem Px).
   Proof.
     iIntros "#i". iApply (guard_trans (Q:=verus_halt_store_wsat)).
     { iApply (guard_wsat_out (W':=verus_halt_store_wsat)). }
     iApply guard_intro. iIntros "!> W".
     rewrite /verus_halt_store_wsat.
     by iApply (dinv_fml_acc_at (alt_sem_any alt_here) with "i W").
   Qed.
   ```

   That is Leaf's central move, and it is the whole arc.  `dinvCT` in
   `model.v` is the constructor - one `cdom` child, so a former holding its
   argument behind it is `Productive`, and a semantics of `dinv_tok` that
   mentions no interpretation at all, so unlike `cif_pstore` and `cif_guard`
   it is an ordinary constructor with a `⊣⊢` at every candidate rather than
   a judgment.

   `sown_tyd` is then `own_tyd` with four forced changes, and its `Ty` comes
   out **unconditional**, which is the mark of a properly guarded former:

   * the pointee's ghost assertion behind `dinv_fml` rather than in hand;
   * both indices *bounded* (`Ltx`, `Lex`) rather than matched exactly,
     because an invariant holds a formula at one fixed depth and guard
     index and weakening cannot push them up - `rust_halt`'s `sty_shrref`
     carries `⌜d' < d⌝` for the same reason;
   * `size_of`/`syn_phys` in place of `tyd_size T`/`tyd_phys T`, because
     `proeqv 0` relates nothing in a discrete component, so a `Productive`
     former may not mention either - the same constraint `&shr` is under;
   * the stored part in the *persistent* component as well as the ghost one,
     because `ty_guard_proph` is handed that one directly while the guard it
     is handed cannot be opened, `guard_acc` wanting a left-hand side the
     law does not supply.

   `own_listₛ` beside `shr_listₛ` is the refinement type; the two differ
   only in the tail being a `loc` rather than a `cloc`, so the inductive is
   parameterised by it (`ptrlist L A`) and everything else is the same
   clauses twice.

   ### Done: the two owning pointers are one

   `sown_tyd`'s pointee could be *borrowed* - that is what a reversible
   accessor gives - but not moved out, so a recursive type was readable
   and not destructurable and the port carried two owning pointers:

   | | content | extractable | productive |
   |---|---|---|---|
   | `own_ptr` (`own.v`) | in hand | yes | no |
   | `sown_tyd` (`rec.v`) | in a simple invariant | **yes** | yes |

   The second row's middle column is now `yes`.  `sown_tyd_take` moves the
   pointee out for good and hands back the pointer and its deallocation
   permission untouched; `sown_tyd_alloc` is the other direction; `Ty` is
   still unconditional, `TyProphAt` and `sown_tyd_incl` still go through,
   and the former is still `Productive`.  All of it is closed under the
   global context.

   Getting there took two things, and the first of them this plan had
   wrong.

   **The interface is a judgment, not a token.**  The obvious merge is
   `store_tok`'s shape - hold an exclusive token and store `Px ∨ marker`,
   so the guard rules out the marker while extraction deposits it.  This
   plan recorded that as *structurally impossible*; it is not, and
   `nola/examples/rust_halt/box.v`'s `ty_box` is exactly that shape, with

   ```coq
   store_tok Px := ∃ γ, token γ ∗ dinv_tok (Px ∨ ▷ token γ)
   ```

   under it - the `▷` only because `cif` has no constructor for `token γ`
   and has to embed it, which a later-free port does not need.

   But that is only half.  An earlier version of this section answered the
   subtyping objection - "a token names the formula it stores" - with
   `st_iff`, the device a full borrow uses.  That is wrong: `st_iff` is an
   `iProp`, not a formula, so an `estore_at` built from it can never be a
   type's *ghost component*, which is `FML`-valued.  Both sources say what
   the answer is and they agree.  The thesis hits the objection head on
   (§ 5.2): its first model stores the reference's content in a bare
   invariant token and cannot prove `≤-ref` "because the proposition of
   the invariant token `inv N` cannot be directly changed"; the fix is
   derivability, giving (5.5)

   ```
   ⟦ref°ₖ T⟧ⁱδ v ≜ ∃U, k' ≤ k. □ δ (T ≤ U) ∗ □ δ (U ≤ T) ∗ inv (ℓ ↦ U)
   ```

   with `≤-ref` following from (5.8) and the transitivity (5.7).  And
   `ty_box` does the same: `cif_store` denotes `store_deriv.v`'s
   `store δ Px`, a derivability assertion - `store_tok` is only how one is
   **built**, and `store_wand` is what `subty_box` runs on.

   So the token is the realization and the judgment is the interface.
   `typing/model.v`'s `eownCT`/`eownJT` and `typing/ctx.v`'s `eown_fml`:

   ```coq
   ⟦ eown_fml γ Px ⟧(δ) := □ δ (eown_j γ Px)
   ⟦ eown_j γ Px ⟧(δ)   := (ts_full γ &&{W δ}&&> ⟦Px⟧(δ))        (* read, repeatably *)
                         ∗ □ (ts_full γ -∗ |=[W δ]=> ⟦Px⟧(δ))    (* take, once *)
   ```

   realized by one persistent `dinv_tok (ts_taken γ ∨ Px)` beside the held
   `ts_full γ`, which is the only owned part - one judgment, because two
   conjuncts would ask for two realizations of one `Px`.
   `nola/verus_halt/two_state.v`'s token is what makes the guard half go
   through: `guard_cancel_or` wants the *non-separating*
   `ts_full γ ∧ ts_taken γ ⊢ False`, which a plain `Excl ()` cannot give,
   `P ∧ P ⊣⊢ P`.  `eown_fml_map_at` is (5.7) and `store_wand`.

   **The token's name is in the refinement type.**  This is the part that
   took the longest to see, and it is where `TyProphAt` comes in rather
   than subtyping.  The law is *handed* a guard on the ghost component at
   a universally quantified `R`, and `@[κ]` is reachable only from that
   same `R`, so it can only ever compose - it can never open anything.
   Composing down to the pointee needs `R &&{W}&&> ts_full γ`, and with
   `γ` existentially quantified inside the ghost component nothing could
   reach it: guards do not commute with `∃`.  With `γ` read off the
   refinement value it is `sown_tyd_guard_tok`, two `guard_sep`
   projections, the token sitting outside both bounded existentials.
   (The bounds are forced too: widening one is the only weakening
   available to an *unconditional* `Ty`, which the fixpoint needs.)

   So `at_loctokₛ 𝔄 := at_locₛ (positiveₛ * 𝔄)` and `own_listₛ`'s tail is
   a `loc * gname` the way `shr_listₛ`'s is a `cloc`.  The device is the
   port's own: `invₛ` already interprets to `namespace * gname * ⟦𝔄₀⟧`,
   and `typing/atomic_inv.v` already runs this two-state trick off a `γ`
   taken from the data.  A pleasant consequence: subtyping needs only one
   direction of the thesis's premise, since the map is the identity on the
   name and the capability is persistent, so the backward direction of
   `tyd_incl_at` hands back the one it kept rather than inverting
   anything.

   `bi/guard.v` gained `guard_apply` and `guard_exist_pers` along the way.
   The second narrows a guard on an existential whose witness carries a
   persistent guard of its own; naming the token made it unnecessary here,
   and it is kept because it is the general form of the move.

   The list now has its own destructuring rules, which is the second of
   those and what `rust_halt`'s `verify/list.v` does with `ty_box`'s
   `Read`/`Write` instances: `ty_rec_own_unfold` unfolds the fixpoint
   once, and `own_list_tyd_cons_take` takes a cons cell apart into the
   head's ghost assertion, the tail pointer, its deallocation permission
   and the tail list - all in hand, at a strictly smaller depth.
   `own_list_tyd_cons_alloc` puts one back together and
   `own_list_tyd_nil` is the empty case; `ty_own_list_cons_take` and
   `ty_own_list_nil` are the same two at the level of `type`, which is
   what a typing rule sees.  The structural formers between the fixpoint
   and the pointer are all depth-transparent, so the only step that moves
   the depth is `sown_tyd`'s own `⌜d' < d⌝`.

   And the rules themselves are in `typing/own_rec.v`: `sown_ptr n ty`
   packages `sown_tyd n (ty_d ty)` as a `type` - its data *is* that, so
   every law comes from `rec.v` - and `read_sown_copy`, `read_sown_move`
   and `write_sown` are `own.v`'s three rules for it.  Each is `own.v`'s
   proof with one step in front, `sown_ptr_take_wsat`, which spends the
   token and brings the pointee into hand.

   Two things differ from `own_ptr`'s, and both come from the token.  The
   pointee's depth is only *bounded* by the pointer's rather than one
   below it exactly, so it is lifted with `ty_gho_depth_mono` - the same
   step `own.v` already takes to meet `typed_read`'s "same depth on both
   sides", starting one further down.  And closing allocates a **fresh**
   token, so the residual refinement's ghost name is not the one it
   started with - which is why `typed_read`'s `st` and `typed_write`'s are
   relations; they pin the location and the value and say nothing about
   the name.  `read_sown_move` leaves an ordinary `own_ptr`: the token is
   spent and nothing is left in the store that would need one.

   `sown_ptr_d`, `ty_d_type_of_tyd` and `sown_ptr_of_tyd` tie the two
   together: the slot a guarded recursion puts its hole in -
   `sown_tyd n Self` in `own_list_gen` - is exactly
   `sown_ptr n <what the fixpoint denotes>`, so the rules apply to a
   recursive type and not only to a standalone pointer.

   So the owning pointer is finished: one former, productive, extractable,
   with subtyping, a prophecy law, destructuring and the standard read and
   write rules.

   VerusBelt was no help: `fix_ty` has no client in
   `verus-belt/src/lambda_verus/typing/` at all, only `TypeContractive`
   instances for the formers.  The recipe followed is `rust_halt`'s.

   **The lifetimes** turned out not to be a gap.  `type_of_rec_shr` closes
   the loop: a guarded, structural body gives an actual `type`, with the
   lifetime list and the external context *supplied* rather than derived.
   `typing/fixpoint.v` derives them with `TypeLftMorphism` because its
   carrier is the whole record; here they were never in the carrier, so the
   only thing that constrains them is the prophecy law, and that is exactly
   the obligation `type_of_rec_shr` asks for.  `fixpoint.v`'s
   `Tn_ty_lft_const`/`Tn_ty_E_const` are therefore spare - useful if one
   ever wants the list derived rather than chosen, not needed to have
   recursive types.

   So the fixpoint cannot be taken over the whole record.  It should be
   taken over the two *ghost* components only,

   ```coq
   Definition ghostd 𝔄 : prost :=
     (~~𝔄) -pr> nat -pr> nat -pr> thread_id -pr> cifPR CON Σ.
   ```

   with `ty_size`/`ty_phys` supplied by `size_of`/`syn_phys` and
   `ty_lfts`/`ty_E` supplied the way the present `fixpoint.v` already does
   it - `TypeLftMorphism`, `Tn_ty_lft_const`, `Tn_ty_E_const`.  That half of
   `fixpoint.v` is sound as it stands and carries no laters; only the COFE
   limit on the ghost assertions is replaced by `profix`, and only that half
   needs `Productive`.  The `Cofe (FML $oi Σ)` assumption then disappears,
   which was the point.

   The second route - limit preservation for `proeqv` - has **no
   counterpart** in Nola, `rust_halt` or the thesis.  `nola/util/productive.v`
   has nothing of the kind, `Preserv` is declared for `cif`'s constructors
   and never for `Csem`, and there is no
   `proeqv k t t' → ⟦ t ⟧ᶜ(δ) ≡{k}≡ ⟦ t' ⟧ᶜ(δ)`.  It would be new work in
   Nola's core rather than a port.

   The branch `wip-type-split` holds a failed third attempt: abstracting the
   `prost` over a general `FML` as a class does not work either, because
   `Cprost` takes the whole `prost` record and one rebuilt from a class's
   fields will not unify with `citPR`, whose obligations are its own.  A
   recursion file would have to be specialised to `cif`, as `rust_halt/rec.v`
   is.

## Rules this port had to learn

Written out in `nola/verus_halt/typing/README.md`:

* a judgment can be eliminated at a candidate the ambient interpretation
  maps into, and introduced at every candidate from interpretation-free
  ghost state - but never *moved* between interpretations;
* anything to be *used* at a candidate must be the family of the things
  themselves, not of stored judgments (`fguardx`, `st_incl`, `st_iff`);
* a thing whose semantics ignores the candidate can be a formula with a
  `⊣⊢` at every candidate (`cif_idxbor`, `cif_incl`);
* a candidate is a *wrapped* `VerusHaltSem`: unwrapped it would shadow the
  ambient instance under every binder;
* `cif`'s own existential is capped at `cif_sel`'s universe, which is below
  the one `~~𝔄` lives in - hence `exs_fml` and its own constructor;
* seal anything that unfolds to `□ ∀ sem, …`, or typeclass search goes
  under the binder and build times go from seconds to minutes;
* ghost state is allocated before the interpretation and the interpretation
  handed in afterwards, because `bor_sem` is `⟦⟧ᶜ(der)` and its `Csem`
  mentions the ghost state;
* an allocation lemma should hand out the ghost *name*, not the record: a
  projection of an opaque record does not reduce, and the program logic has
  to recognise the instance it was given;
* **guards compose and never open**, so anything a guarded former's law
  has to reach must be reachable by `guard_sep`/`guard_trans` alone.  In
  particular guards do not commute with `∃`, so a per-value ghost name
  that a law must narrow by belongs in the *refinement type* - which is
  what `invₛ` does and what `at_loctokₛ` now does for the owning pointer;
* a *token* names the formula it stores, so a former holding one admits no
  subtyping rule.  Put the token behind a **judgment** and the relation to
  the wanted formula composes: this is the thesis's (5.5)/(5.7) and
  `rust_halt`'s `cif_store`/`store_wand`, and `eown_fml` here.
