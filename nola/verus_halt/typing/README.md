# `nola/verus_halt/typing` — port status

A later-free, total-correctness port of VerusBelt's
`src/lambda_verus/typing/` (MIT; Hance, Elbeheiry, Matsushita, Dreyer).

**The model is concrete.**  `typing/inst.v` builds a `CON`, a `JUDG` and
their semantics, so `typing/soundness.v`'s two theorems are not vacuous;
`verus_halt_type_soundness` and `verus_halt_type_safety` are the concrete forms, and
`Print Assumptions` gives only `Eq_rect_eq` for both.  Several sections
below were written while that was still open and described obstacles that
turned out to be artefacts of how a borrow was stored; each now says so
where it was wrong, rather than being deleted, since the wrong turn is the
useful part.

Two things change globally:

* **No `▷`.**  Ghost assertions are *formulas* (`FML $oi Σ`) interpreted by
  `bor_sem`, in the style of `nola/examples/rust_halt/type.v`.  The time
  receipts (`⧖`, `⧗`), later credits (`£`) and the guard indices
  (`leaf_goal laters to …`) that paid for the `▷`s are gone, and so is the
  depth arithmetic that sized them.
* **Total weakest precondition.**  `twpw` replaces `wpw`, so `iLöb` is not
  available and no loop that may fail to terminate can be given a proof.

36 of the 39 upstream files are ported in full.  Per-file deviations are
documented in each file's header.

## Not ported

### `spawn.v`

Blocked twice over.

* `lang/lib/spawn.v`'s `join_spec` is proved by `iLöb`: `join` re-invokes
  itself while the flag is `false`, i.e. it is a spin loop.  Under the total
  weakest precondition it has no specification.  (Upstream's `join_type` is
  already commented out for unrelated reasons, so only `spawn_type` would be
  gained.)
* `spawn_inv` stores an arbitrary `Ψ : val → iProp Σ` inside an Iris `inv`,
  and `typing/spawn.v` instantiates `Ψ` with `join_future`, which is built
  from `|={⊤}=>`, `∀ tid` and `⧖ d`.  Later-free, invariant contents must be
  formulas, so `Ψ` would have to become `val → FML $oi Σ` and `join_future`
  a formula - and `⧖ d` no longer exists.

### `protocol.v`

Depends on Leaf's `guarding/storage_protocol/protocol.v` (1272 lines) and
`base_storage_opt.v` (110 lines), plus `guarding/guard_later_pers.v`.  None
of these is ported; they live outside `typing/`, and `guard_later_pers` is
later-based by construction.  `own_and.v` - the one piece of that stack that
is already ported - is not enough on its own.

### `soundness.v`

The adequacy layer it needs is in place: `nola/verus_halt/lang/adequacy.v`
provides `lrust_adequacy` and, beyond what the original can state,
`lrust_total`.  Two things stand between that and the theorem.

1. **The world satisfaction cannot be allocated in the current order.**
   `llft_wsat_alloc` (`lifetime/lifetime_full.v:1934`) takes the client's
   guarding world satisfaction `WG : iProp Σ` as a *value*, but
   `verus_halt_WG` mentions `llctx_interp`, which needs the `llft_logicGS` that
   the call allocates.  The lemma frames `WG` once and never looks inside, so
   a variant that returns `llft_logicGS`, `sinvGS` and the share name first
   and takes `WG` afterwards breaks the cycle.  This part is routine.

2. **`bor_sem` has no definition.**  A concrete `FML` means a `cif` (see
   `nola/iris/cif.v`) with roughly 25 constructors - `gsrc`, `alive`,
   `dead`, `cmapstoany`, `cells`, `ccells`, `cellsvec`, `freeable`, `heap`,
   `vo`, `pc`, `ra`, `obs`, `handle`, the `cna_*` and `na_inv_*` family, … -
   together with their `Ecsem`.  Most of that is long but mechanical: those
   constructors' semantics mention their subformulas and nothing else.

   What is not mechanical is that **`bor_sem` would have to be defined in
   terms of itself at formulas that are not subformulas**, so it is not a
   structural recursion over the `cif`; and the self-reference sits on both
   sides of a `-∗` with no `▷`, so it is not a contractive fixpoint either.
   Three constructors do this:

   * `guard_fml Px Qx` (`ctx.v:596`), whose semantics is
     `bor_sem Px &&{Wguard}&&> bor_sem Qx`.  `Wguard = llft_wsatG =
     WG ∗ shr_wsat ∗ box_wsat bor_sem ∗ llft_inv_main`
     (`lifetime/lifetime_full.v:143`), and `shr_wsat` is
     `sinv_wsat (λ _ Qx, bor_sem Qx)`.
   * `idxbor_fml κ idx Px` (`ctx.v:626`): `idx_bor κ idx Px` is
     `κ ⊑ κ' ∗ ∃ Px', □ (bor_sem Px' ↔ bor_sem Px) ∗ sinv_tok sn Px'`
     (`lifetime_full.v:736`) — an `∃` over *arbitrary* formulas under
     `bor_sem`, and `κ ⊑ κ'` is itself a guard over `llft_wsatG`
     (`lifetime_full.v:249`).
   * `fn_fml fp spec x` (`function.v:113`), whose semantics is the
     function's whole `typed_body` judgment and so mentions `twpw` over
     `verus_halt_wsat`.

   The two *closers* used to belong on this list.  They no longer do: an
   opened invariant is now a token, `cna_otok` / `na_otok`, following Nola's
   `obor_tok` (`nola/iris/borrow.v:115`), which is plain CMRA ownership plus
   a lifetime-token fragment and mentions no interpretation at all.

   **Why Nola does not hit this and we do.**  Nola's borrow machinery is
   token-shaped throughout: `bor_tok α Px` is
   `own borrow_name (◯ {[i := (to_agree α, {[j := Excl (Px, Clsd)]}, ε)]})`,
   which carries `Px` as *data*, and `α ⊑□ β` is over lifetime ghost state
   only.  Neither mentions the interpretation, so `cif_bor` and friends are
   ordinary constructors.  Leaf's lifetime logic - which VerusBelt is built
   on, and which this port reimplements later-free - instead bakes the world
   satisfaction into the proposition: inclusion *is* a guard, and a shared
   borrow *is* a guard.

   Two ways forward.

   * **Magic derivability** (`nola/bi/deriv.v`).  This is Nola's own answer
     to storing a world-satisfaction-quantifying accessor in a formula:
     `inv_deriv.v` stores `inv_acsr sm N P :=
     ∀E, ⌜↑N⊆E⌝ → |=[inv_wsat sm]{E,E∖↑N}=> P ∗ (P =[inv_wsat sm]{E∖↑N,E}=∗ True)`
     as a *judgment*, with `inv' δ N Px := □ δ (inv_jacsr N Px)` and
     `invJT_sem δ J := inv_acsr ⟦⟧(δ) …`.  The knot is tied by
     `der = psg …`; elimination is `der_sound` (`invd_acc`), introduction is
     `Deriv_factor'` (`inv_acsr_inv'`).  Note what this does *not* give: a
     `⊣⊢` semantics is impossible, and `psg` yields only the post-fixpoint
     `der J ⊢ ⟦J⟧(der)`.  So `guard_fml_sem`, `idxbor_fml_sem` and
     `fn_fml_sem` split into an elimination at `der` and an introduction
     that must hold **uniformly in `δ'`** - which is exactly why every law
     of Nola's own `Ty` class is stated `∀ δ`
     (`nola/examples/rust_halt/type.v:128-145`).  Making this development
     `δ`-parametric is the price.  **This is the route that was taken**; see
     below.  The first two equations are gone and the third is split, so
     what the file list above describes as "three constructors that have no
     semantics" is now, concretely, one missing introduction rule,
     `fn_fml_sem_2`.
   * **Replace the lifetime logic with Nola's** (`nola/iris/borrow.v`,
     `nola/iris/lft.v`), so that inclusion and shared borrows are tokens and
     the guard disappears from the formulas.  `rust_halt` is that
     development: it uses no guards at all (`&&{` occurs nowhere in
     `nola/examples/rust_halt/`), and Nola's lifetime inclusion is either
     pure (`lft_incl`) or a persistent token (`⊑□`,
     `nola/iris/lft.v:343-437`).

     **This is explicitly not the route.**  The point of this development is
     to have Leaf's guarding logic *in* Nola - guards are what VerusBelt is
     built on, and they are what `pcell`, `atomic_inv` and the storage
     protocols need.  `nola/iris/guard.v` already provides the guard itself;
     what is being built here is the rest of Leaf's lifetime logic and
     VerusBelt's type system over it, later-free, using Nola's ideas for the
     parts that would otherwise need a `▷`.

   Either way, `fn_fml` needs derivability regardless: a function type's
   ghost assertion is its own typing judgment.  `rust_halt` has no function
   *type former* - its formers are `ty_box`, `ty_mutref`, `ty_shrref`,
   `ty_prod`, `ty_sum`, `ty_mod`, `ty_rec`, `ty_uninit`, the numeric ones,
   and `ty_list`/`ty_mutlist` in `verify/` - so a function value never gets
   a type at all.  Calls are beta, not lookup (`core.v:96`'s `type_call` is
   `AsRec` + `DoSubstL`), and higher-order code is parameterised by the
   callee's judgment at the meta level (`verify/list_more.v`'s
   `type_iter_list_mut` takes `(∀ q, type κ (q ◁ …) (f [q]) …)` as a Coq
   hypothesis).  So there is no worked example in Nola of a typing judgment
   stored inside a type.

## The route being taken

Nola's `deriv` ([`nola/bi/deriv.v`](../../bi/deriv.v)), as used by
`nola/iris/inv_deriv.v`.  The pieces, in order; each is meant to leave the
build green.

1. **Tokenise what can be tokenised.**  *Done.*  The two closers are now
   `cna_otok` / `na_otok`, after Nola's `obor_tok`.
2. **The `AltSem` interface.**  *Done.*  `ctx.v` carries `AltSem`:
   `alt_sem sem` says `sem` is a derivability candidate, `alt_WGuard sem` is
   the guarding world satisfaction at it, `alt_into sem sem'` is Nola's
   `dinto`, and the `_at` fields repeat the equations of the non-judgment
   constructors at an arbitrary candidate.  On top of it: `dguard Px Qx` (a
   guard held as a formula) with `dguard_sem` / `dguard_alive_sem{,'}` for
   elimination, `dguard_of_all` (`Deriv_factor'`) for introduction, and the
   combinators — `dguard_trans`, `dguard_{lhs,rhs}_iff`,
   `dguard_{lhs,rhs}_sep_{l,r}`, `dguard_and`, `dguard_intro`,
   `dguard_cloc_combine_fancy{,'}`, `dguard_cells_nil`, `dguard_depth_mono`,
   `dguard_and_own` — each of which is `Deriv_map` in the model; plus
   `dincl` and `dbasically_dead`.
3. **The type laws at a candidate.**  *Done.*  `ty_gho_depth_mono_at`,
   `ty_gho_pers_depth_mono_at` and `ty_gho_pers_pers_at` are record fields
   taking `sem` and `alt_sem sem`, proved for every type former; the ambient
   laws follow by `alt_here`.  `Sync` is candidate-indexed, and `type_incl`,
   `subtype`, `eqtype`, `elctx_elt_interp`, `lctx_lft_incl`, `lft_equiv` and
   `TypeLftMorphism` are stated with `dincl` and with their ghost components
   `∀ sem, alt_sem sem → …`.  This is the same shape as Nola's `Ty` class,
   whose laws are all `∀ δ`
   (`nola/examples/rust_halt/type.v:128-145`).
4. **Migrate the stored guards.**  *Done.*  `TypeFml.guard_fml_sem` — the
   equation that had no model — is **gone**.  A stored guard is only ever
   eliminated (`guard_fml_sem_into`) or introduced uniformly in the
   candidate (`guard_fml_sem_2`).  `shr_bor`, `uniq_bor`, `uniq_util`'s
   `basically_dead`, and `borrow.v`'s mid-formulas state their unfolding
   lemmas with `dguard`; the ~20 files downstream build their guards as
   stored guards and drop to a raw one (`dguard_alive_sem'`) only at the
   point where one is actually opened.

   Two places had to become sources of storable guards rather than
   consumers, because a *raw* guard can never be promoted — it holds at the
   ambient interpretation only, and nothing in it says it holds at the
   others:

   * `guard_fml_borrow_shared` (`llftl_borrow_shared`: the shared borrow it
     allocates is a `sinv_tok`, which mentions no interpretation), and
   * `guard_fml_of_bor` (`bor_to_guard`: a full borrow token is plain CMRA
     ownership, and `bor_to_guard`'s proof is parametric in `BorSem`).

   Everything else is built from those two, from `dincl_of_incl` /
   `dincl_eternalize` / `Ltok_guard_frac_at`, or out of other stored guards.
5. **The same for `idxbor_fml` and `fn_fml`.**
   * `idxbor_fml`: *done*.  `idxbor_fml_sem` is gone.  Elimination is
     `idxbor_fml_sem_1`, introduction is `idxbor_fml_of_bor` — splitting a
     full borrow into an index and a token, where the `iff` the indexed
     borrow carries is reflexivity and the token mentions no interpretation.
     `uniq_body_pers_component` is now `bor_sem (idxbor_fml …)` rather than
     `&{κ,idx} …`, and the transformations the development needs
     (`idxbor_fml_iff_at`, `idxbor_fml_shorten_at`, `idxbor_fml_into`,
     `idxbor_fml_guard_at`) are `Deriv_map` fields.
     `incl_uniq_body{,_pers_component}` are dropped: their premises — a raw
     inclusion and an ambient `↔` — cannot be stated any more, and
     `incl_uniq_body_pers_component_at` supersedes them.
   * `fn_fml`: *the derivability route is the wrong one for it.*  See
     "Why `fn` is stratified, not derived" below.  `fn_fml_sem` is currently
     split into `fn_fml_sem_1` (elimination, sound) and `fn_fml_sem_2`
     (introduction, **assumed**); `fn_fml_specialize_at` handles
     `fn_subtype_specialize` as a `Deriv_map`.  `fn_fml_sem_2` is used in
     exactly one place, `type_fn`, and is to be replaced by a stratified
     definition rather than discharged.

6. **The model.**  *In progress*, in [`model.v`](model.v).  What is there:

   * the `cif` constructor signature - about twenty *leaves*, whose
     semantics is a token (lifetime, dead lifetime, the two points-to
     forms, allocatedness, deallocation permission, value observer,
     prophecy controller, guard source, borrow state, heap cell, cell
     vector, the two "active" tokens, prophecy observation, lock handle,
     dead atom, cancellation token), and four constructors holding a
     *syntactic* sub-formula (the atomic and cancellable non-atomic
     invariants, open and closed), after `cif_inv` in
     `nola/iris/inv_deriv.v`.  The shared-borrow formula needed no
     constructor of its own: it is built from `cif_or`, `cif_sep`,
     `cif_ex` and two leaves.
   * `BorSem_at δ`, `BorStateFml_at δ`, `ShrBorSem_at δ`, `EmptySem_at δ`,
     hence `VerusHaltSem_at δ`, hence **`verus_halt_WGuard_at δ`** - the guarding
     world satisfaction at a candidate.  This is what the
     `verus_haltGS`/`VerusHaltSem` split was for, and it is Nola's
     `inv_wsat ⟦⟧(δ)` one level up.
   * the two judgments `guardJT` and `idxborJT` with their `Dsem`
     instances, and the constructors `cif_guard` / `cif_idxbor` whose
     meaning is `□ δ (…)`, after `inv'`.
   * the constraint classes `typingC` / `typingJ` / `typingCS` /
     `typingJS`, after `rust_haltC` and friends.
   * `bor_sem := ⟦⟧ᶜ(der)` as the ambient interpretation, and the
     `TypeFml`, `GsrcSem` and `HeapSem` instances at it.

   What is left: the `AltSem` instance, then `typeG`, then `PcellFml` /
   `AtomicInvFml` / `LocalInvFml` / `RaFml`, then the world-satisfaction
   allocation and `soundness.v`.

### What building the model showed about `AltSem`

**The rule.**  A stored guard lives at one interpretation and *cannot be
moved to another*: that would need `δ J ⊢ δ' J`, while `Deriv_factor'`
gives only `δ J ⊢ ⟦J⟧(δ')` (`Psgoidp_factor'` yields one conjunct of the
thesis's `δ ⇝ δ'`, not the `δ' J` one).  So anything that has to be
*usable while building* a stored guard at a candidate - and candidates
only ever arise from such a build - must be held as a **family**, one
member per candidate, from the moment it is created.

That is how stored *guards* work: `dguard_all Px Qx` is
`□ ∀ sem, alt_sem sem → sem (guard_fml Px Qx)`, created whole by
`guard_fml_borrow_shared` and `guard_fml_of_bor`, whose tokens mention no
interpretation.

`dincl` is a family too, and of a *stronger* shape: it is `st_incl`, the
raw family of guards

```coq
st_incl κ κ' := □ ∀ δ, @[κ] &&{verus_halt_WGuard_at δ}&&> @[κ']
```

over **every** interpretation, good or not.  It was briefly a token - a
covering set of eternalized lifetimes - on the grounds that a token needs
no `Deriv` to state and so does not drag `Jsem` into its own definition.
The second half of that is right and the first is not the way to get it:
dropping the `⌜Deriv ⊤ δ⌝` removes `Deriv` just as well, and keeps the
family.  The token lost `fn_incl_of_all` - the *semantic* inclusion
`type_call_iris'` manufactures for a call's own lifetime - which the
family gives back as `dincl_fguardx`.

**Resolved, and not by a family: the indexed borrow.**
`idxbor_fml_into : sem (idxbor_fml κ idx Px) ⊢ sem' (idxbor_fml κ idx Px)`
is indeed not realisable, for exactly the reason above - and the conclusion
drawn here, that the indexed borrow therefore had to become a family too,
was wrong.  What it had to become is the *relaxed* borrow (below): the
alteration read at the interpretation over an interpretation-free token.
`alt_into`'s borrow clause is then *eliminating* rather than *moving* -
`sem (idxbor_fml κ idx Px) ⊢ ∃ Px', □ (sem' Px' ↔ sem' Px) ∗ idx_bor κ idx Px'`
- which is all its one consumer, `dguard_inner_from_guard_uniq_body`, ever
needed.  `idxbor_fml_into` is gone.

**`alt_into` should be defined by what it is used for.**  In the model a
candidate is a function `FML $oi Σ → iProp Σ`, and nothing recovers the
`δ` behind it, so `alt_into` cannot be `dinto δ δ'` as written.  Both of
its uses are "a judgment stored at `sem` can be read at `sem'`", which
*is* a function of the two interpretations - so that is what it should be
defined as, with `dinto δ δ'` discharging it.  `alt_WGuard` had the same
problem and is solved: `verus_halt_WGuard_of` is `llft_wsatG`'s body with
`bor_sem` replaced by the argument, and agrees with both `verus_halt_WGuard`
and `verus_halt_WGuard_at δ` definitionally.

**A performance note.**  `dguard_all` is sealed and `Typeclasses Opaque`.
Unfolded it is a `□ ∀ sem` under a class binder, and with about a hundred
occurrences that sends every unification and every `Persistent` search
under the binder: `lft_contexts.v` alone went from 4s to over ten minutes
before sealing.  Any further family-shaped definition needs the same
treatment.



Trying to instantiate `AltSem` turned up two things the interface claimed
that Nola's `Deriv` cannot give.  The first is fixed; the second says how
the interface has to be reshaped.

1. **`alt_into_refl` was unsound.**  It said every candidate maps into
   itself, i.e. `dinto δ δ` - which is *soundness* of `δ`.
   `nola/bi/deriv.v` proves that for `der` alone (`der_sound`; thesis
   Theorem 4.3) and for no other member of `Deriv`.  It is now
   `alt_into_here : alt_into bor_sem bor_sem`, and the development turned
   out never to need more: `dguard_sem_at` and `dincl_sem_at` were only
   ever used at `alt_here`, so both are gone.  **A judgment can be
   eliminated at the ambient interpretation and nowhere else.**

2. **`alt_sem_into` and introduction-at-an-arbitrary-candidate are
   jointly unrealisable.**  Write `reach δ` for `dinto der δ`.
   `alt_sem_into` needs `reach` of every candidate in range; introduction
   at a candidate `δ` is `Deriv_factor'` at `δ`, whose binder gives
   `Deriv ih δ'`, `ih δ'` and `dinto δ δ'` - and `reach δ` together with
   `dinto δ δ'` does *not* give `reach δ'`, because that would need
   `⟦J⟧(δ) ⊢ δ J`.  Putting `reach` into Nola's induction hypothesis `ih`
   does not help either: then the binder does hand out `reach δ'`, but
   `alt_here` becomes `Deriv reach der`, and `nola/bi/deriv.v` gives only
   `der_Deriv : Deriv (λ _, True) der`.  Reachability has to be carried,
   not recovered.

   The shape that *is* realisable, and the next piece of work:

   * `alt_cand sem` - "`sem` is a derivability candidate", `Deriv ⊤ δ`.
     All the `_sem_at` equations, `guard_fml_pers_at`,
     `idxbor_fml_pers_at` and `guard_fml_sem_into` are stated at this.
   * `alt_sem sem` - "… and reachable from the ambient", `Deriv ⊤ δ ∧
     reach δ`.  `alt_here` holds (`der_Deriv` and `der_sound`),
     `alt_sem_into` is a projection, and this is what the type-record
     laws and `type_incl` quantify over, since they read stored guards
     that were made at the ambient interpretation.
   * **Introduction only at the ambient**: `guard_fml_sem_2` becomes
     `dguard_of_all`, whose binder gives `⌜alt_sem sem'⌝` - this is
     `Deriv_factor'` at `der`, which does give `dinto der δ'`.
   * The combinators that currently derive from `dguard_of_all_at` at a
     non-ambient candidate - `dguard_trans_at`, `dguard_intro_at`,
     `dguard_{lhs,rhs}_iff_at`, `dguard_{lhs,rhs}_sep_*_at`,
     `dguard_and_at`, `dincl_glb_at`, `idxbor_fml_iff_at`,
     `idxbor_fml_shorten_at`, about sixteen in all - become *fields*,
     realised by `Deriv_map` / `Deriv_map2`, whose binders give
     `⌜alt_cand sem''⌝` and `⌜alt_into sem sem''⌝`.  Their bodies never
     read an ambient guard, so that is enough.  Their users do not
     change.

   Two things found along the way, both now fixed or recorded:

   * `Default Proof Using "Type"` was making sealed definitions generalise
     over their whole section context, so a points-to *token* carried a
     `NaSem` - hence a `bor_sem` - that it never used.  Invisible while the
     interpretation was bundled into `verus_haltGS`; fatal once a
     constructor's semantics has to be written before the interpretation
     exists.  Fixed in `non_atomic_cell_map.v` and `lang/heap.v`.
   * `TypeFml` demanded `Cofe (FML $oi Σ)`, which **a `cif` does not
     satisfy**: Nola's `cit` is complete as a `prost`, not as an OFE
     (`nola/util/cit.v`'s `cit_prolimit`), and recursion over it goes
     through `profix` with `Productive`, as `rust_halt/rec.v`'s `ty_rec`
     does.  Only `typing/fixpoint.v` needs it - it builds a recursive type
     as the COFE limit `compl` of a chain of ghost assertions, the
     step-indexed idiom - so the assumption now lives there.  **It is no
     longer on any path**: `typing/rec.v` takes the fixpoint with `profix`
     instead, over a type's *data* rather than the whole record, with the
     laws split into an unconditional `Ty` and a depth-indexed
     `TyProphAt`.  `fixpoint.v` stays only for its `TypeLftMorphism` half,
     which is what supplies the lifetime list that `tyd` omits.

   The original sketch of this step read:  A `cif` with the remaining ~25 leaf constructors, a
   `JUDG`, `bor_sem := ⟦⟧ᶜ(der)`, the `AltSem` instance with
   `alt_sem := Deriv ih` and `alt_into := dinto`, and the
   world-satisfaction allocation (plus the `llft_wsat_alloc` reordering
   above).  Then `soundness.v`.

   `inv_deriv.v` is the template for the `JUDG` entries, and Nola's own
   borrow connectives are built the same way the port's now are
   (thesis § 6.4):

   > `⟦bor^α P⟧δ ≜ ∃Q. δ(P⇒Q) ∗ δ(Q⇒P) ∗ bor^α Q`,
   > `⟦lend^α P⟧δ ≜ ∃Q. δ(Q⇒P) ∗ lend^α Q`,
   > `⟦obor^α_q P⟧δ ≜ ∃Q. δ(P⇒Q) ∗ obor^α_q Q`

   with the single judgment `⟦P⇒Q⟧δ ≜ ⟦P⟧δ -∗ |⇛ ⟦Q⟧δ`, which is worth
   copying: one general-purpose judgment constructor rather than one per
   connective.  Note also that Nola's borrow *tokens* mention no
   interpretation at all, whereas Leaf's `idx_bor` carries `κ ⊑ κ'`, which
   is itself a guard - that is the only reason the port needs
   `guard_fml` as well.

## Why `fn` is stratified, not derived

Nola's own case study hits exactly this problem and does not solve it with
derivability.  Thesis chapter 5 verifies strong normalisation of a type
system with higher-order references, and its function type has the same
shape as ours - a *total* Hoare triple over a world satisfaction that
depends on the interpretation:

> `⟦T →ⱼ U⟧ⁱ_δ v ≜ ∀u. [⟦T⟧ⁱ_δ u] v(u) [⟦U⟧ⁱ_δ]_{N, ∗_{k<j} Winvₖ ⟦⟧*ₖ}`
> (thesis (5.4), p. 74)

The recursion is well-founded not because of a judgment but because of a
**level**: types are stratified `Typᵢ`, the function type `T →ⱼ U ∈ Typᵢ`
carries an execution level `j ≤ i`, and the world satisfaction it quantifies
is `∗_{k<j} Winvₖ ⟦⟧*ₖ` - the invariant world satisfactions of levels
*strictly below* `j`.  Each level has its own ghost state
(`Inv_{nProp₀}, Inv_{nProp₁}, …`, with a maximum level `L` fixed up front,
thesis p. 74 fn. 3).  Derivability is used in that development only for the
*subtyping* rule on references (`≤-ref`), which is semantic alteration -
precisely the role `guard_fml` and `idxbor_fml` play here.

The same chapter explains why this is a soundness requirement and not an
engineering convenience.  § 3.4.1's paradox is Landin's knot with
`ref (option (unit -> bot))`: a later-free invariant whose content mentions
the fancy update - "the shared invariant connective corresponds to `ref`,
the fancy update `|⇛` to the closure type `->`" (p. 55) - derives `⊥`.  A
function type whose interpretation is a Hoare triple over the world
satisfaction, stored unstratified in a borrow, is that shape.  So
`fn_fml_sem_2` must not be discharged as it stands; `fn_fml` must carry an
execution level and be interpreted with the world satisfaction of lower
levels.

What that costs here: `FML`, `bor_sem` and `verus_halt_wsat` become
level-indexed up to a fixed maximum `L`, and a `type` carries the level of
its ghost assertion.  The rest of the port needs no level reasoning,
because every *other* formula constructor's interpretation mentions only
its subformulas or a judgment - in particular `guard_fml` and `idxbor_fml`
are judgments and so, like `⟦ref^o_k T⟧`, do not depend on the
interpretation of their contents at all.

`typing/strat.v` now carries that construction out, on a self-contained
type system over `nola.lrust`: the interpretation as a level-indexed
family, (5.4) for the function type, (5.5) for the reference type, the
typing and subtyping rules, Corollary 5.3 and four closed terminating
programs, all axiom-free.  It is also where the cost is visible.  A single
`verus_halt_wsat`, however it is interpreted, will not do: a body at level `j`
that holds it can read its own `f : fn →ⱼ` back out of a borrow and call
it, because calling asks for the `lvs_below … j` the body already has.
What stops that in the thesis is that a reference at level `k` interprets
`fn →ⱼ` only for `j ≤ k`, so the borrow families themselves have to be
levelled.  Which part of them, exactly: `box_wsat bor_sem`, `shr_wsat`
**and `llft_inv_main`**.  The last is not interpretation-free, whatever an
earlier version of this file said: it is `outer_inv`, which is
`inner_inv`, which holds `box bor_sem (boxmap alive dead mbs) Ptotal` and
the formula map `mprops` beside `AuthBorState … mbs`, tied by
`dom mbs = dom mprops`.  Levelling the box therefore means levelling the
borrow bookkeeping, which used to sit at `llft_name` with the lifetime
tokens - and that is why `lifetime/ra.v`'s `LtRa` had to be split after
all.  It now is, and the split needed no new camera, because `lt_inv`'s
only cross term was `w ⊆ d` and `consistent_modulo` was always about the
borrow side's own copy of the dead set.

**Where that has got to.**  `bor_name` and `o_name` are now
`LlftBorNames`, a class of their own, so `llft_wsatG` is a function of
the level's borrow names; `llft_bor_wsat_alloc` builds a further level's
machinery against the lifetime logic that is already there, born at the
*empty* prefix of the kill order, which is sound because a level's dead
set and outlives relation may both lag the shared ones; and
`typing/level_ctx.v` allocates one `llft_logicGS` for the whole run with
a list of levels over it, so `@[κ]` is one proposition rather than one
per level.  `verus_halt_wsat_below P ns j` is `∗_{k<j} Winv_k` beside a
single shared copy.

`typed_body` is stated over a world satisfaction that is a *parameter*,
so `≤-→` is one `twpw_incl_fupd` (`typed_body_at_wsat`, and
`typed_body_lv_le` at the levels); every `type` carries a `ty_lev`, which
the structural formers compute; and `fn_params` carries `fp_lev`, with
`fn_fml_sem_1`/`fn_fml_sem_2` and `type_fn`'s premise stated at
`fn_wsat_lv (fp_lev …)` - the thesis's (5.4) rather than a body at the
ambient world.

What is still open is one thing: `fn_fml_sem_2` wants the body to be
**constant in the candidate interpretation**, and it is not, because the
body's types are interpreted by `bor_sem`, which is the ambient
`⟦⟧ᶜ(der)`, and a judgment's semantics may not mention `der`.  The level
breaks that only once the body's types are interpreted at a *lower
level's* package - which means `fn_params` must be a record at a lower
level's `typeG`.  That is "a level on every type former" in its strong
sense: the ghost state, not the `nat`.

`typing/strat_bor.v` then checks that the levelled design is *sound* with
borrows in it, which neither source establishes: the thesis's Chapter 5
has no lifetimes and no borrows, and `rust_halt` has no function type at
all - there is no `ty_fn` in `nola/examples/rust_halt/`.  Over Nola's
native `borrow.v` and `lft.v`, which already separate the borrow ghost
name from the lifetime tokens (`lftG` has no ghost name and no world
satisfaction, and `lft_end` is a bare `==∗`), it gives each execution
level its own borrowing machinery and proves `typed_call_borrowed`: a
closure of type `A →ⱼ B` stored in a borrow at slot level `k`, retrieved
at execution level `i` and called, with `j ≤ k < i` forced by the storing
and opening rules.  `knot_not_typable` is why no `j` closes the knot, and
`ex_borfn_total` runs such a program and proves it terminates.

It also locates the port's real obstacle, by being free of it.  Nola's
`lft_end` is `1.[α] ==∗ [†α]`, needing no world satisfaction at all, and
a dead lifetime's borrows are reclaimed lazily by the lender at its own
level - `typed_ex_endlft` runs the same program along that route.  The
port's `expire_lt.v` is not like that: `inner_kill_lt` runs under
`|=[box_wsat bor_sem]{…}=>`, because `inner_inv` is *indexed by the dead
set* and a death empties and fills that level's slices.  With one
`inner_inv` per level, killing would have to advance every level at once,
and a body at level `j` never holds the levels at or above `j`.

The split is what makes the way out expressible: each level keeps its own
`ModuloDead`, so it can hold its own `sd_k ⊆ sd` and catch up lazily the
next time its world satisfaction is held - sound because `inner_inv` now
carries `□ ∀ d ∈ dead, Dead llft_name d` persistently, which is what
replaced the camera-level coupling.

The one thing that could have sunk that design is checked rather than
assumed, in `lifetime/inv.v`: a lagging level can be *bounded* by a
persistent witness because death is persistent, but **aliveness is not**,
and `inner_inv` consults `alive` in three places.  It does not need to.
Each consults it only as `al ⊆ alive` for a borrow's own alive set, and
`map_wf` gives `al ∪ de ⊆ alive ∪ dead` with `alive ## dead`, so
`al ⊆ alive ↔ al ## dead` (`subseteq_alive_iff`); `boxmap_alive_free`,
`invalidated_alive_free` and `revalidated_alive_free` carry the
substitution out as equalities of the *boolean*, so they rewrite under
`boxmap` and `borrow_sum` without disturbing a proof.

`lifetime/level.v` is that design, built.  The change of variable is
`inner_inv_c created dead blocked := inner_inv (created ∖ dead) dead
blocked`, in which **death leaves `created` alone**, so both indices are
monotone and a level may lag in either.  Two expectations it corrected:

* a level's invariant has to be a **closed proposition** - it may not
  mention the shared `(sa, sd)`, since `∗_{k<j} Wbor_k` is held on its
  own - and that is affordable because what a lagging level actually
  wants is `lv_alive_disj_dead`, the level's own death witness against
  the lender's `Alive` token, rather than any arithmetic against the
  shared sets;
* **lifetime creation does not reach down the levels.**  A borrow of `κ`
  can be made at a level that has never heard of `κ`
  (`lv_borrow_ready`): the level creates `κ`'s atoms on the spot.  So
  giving a lifetime a level, which this file previously said was what
  would make the lag invisible, is not needed at all - lifetimes are not
  levelled, *borrows* are.

Catching up replays the shared kill order (`lv_catch_up`), which has to
be a list rather than a set (`no_greedy_kill_order` is the two-cycle that
shows consistency does not order it), and a past run stays valid as the
outlives relation grows (`kill_run_mono`), because
`llft_augment_outlives` only ever relates lifetimes that are alive.

`lifetime_full.v` runs that design.  Its `llft_inv_main` no longer ties
the borrow bookkeeping's indices to the shared `(sa, sd)`: the
bookkeeping keeps its own view and all fourteen rules are re-proved
against it, with the user-facing statements unchanged, so the whole of
`typing/` is untouched.  The invariant now carries a **kill order** (a
`mono_list` of the atoms in the order they died, of which a level's dead
set is a prefix) and a second half of the outlives relation so that the
order's well-formedness can be stated in one place; `Delayed` survives,
re-purposed to mark the one-atom gap between the shared dead set and the
order, which exists only inside the vacuous branch of `llftl_end`.

Two things only that integration could settle.  `guard_helper2` used to
ask for `set_map LtAtomSwell κ' ⊆ alive`, which no caller can produce
once the bookkeeping's dead set is its own; it now asks `## dead`, which
is the same thing by `subseteq_alive_iff` and is where the `alive`-free
lemmas earn their keep.  And `inner_borrow_create` threads an `LtState`
it never uses, so creating a borrow needs no agreement with the shared
lifetime state at all.

What is left is the family: `llft_inv_main` holds one `lv_inv`, and
holding `llft_lv_inv ls` instead is a change of that one conjunct -
but splitting `llft_wsatG` so that a body can hold `∗_{k<j} Wbor_k`
alone is what forces the level index into the user-facing rules.
PLAN.md item 2 has the order of work.

## What this means for the earlier plan

An earlier version of this file proposed making `typed_body` candidate-
indexed so that `fn_fml_sem_2` could be discharged by `Deriv_factor'`.
That is not Nola's design and it does not terminate: `Deriv_factor'` would
ask for the function body's typing at every candidate, which is a strictly
harder obligation than the stratified definition and still leaves the
paradox of § 3.4.1 unaddressed.  `rust_halt` keeps its typing judgment at
the ambient interpretation (`type_def` uses `WP[rust_halt_wsat]` with
`⟦⟧ᶜ = ⟦⟧ᶜ(der)`, `type.v:910-932`) precisely because it never stores one.

## The last obstacle in the model: a full borrow was not storable

Building the `AltSem` instance turns every field into one of two shapes.

*Elimination at a candidate* - `guard_fml_sem_into`, and the merged form
`idxbor_fml_guard_at` should take - is `dinto der δ'`, which `Deriv_factor'`
hands out: a judgment held at the ambient interpretation can be read as its
*semantics* at any candidate the ambient one maps into.  Every `dguard_*_at`
lemma in `ctx.v` is of this shape, and all of them are fine.

*Introduction at every candidate* - the families `dguard_all`,
`guard_fml_borrow_shared` - needs the ingredient to be
interpretation-independent.  `sinv_tok`, `eternal_tok` and `OwnBorState` are
plain ghost state, so those are fine too.  (`dincl` was listed here as a
family; it is a token now, which is the same observation taken further.)

Two fields are neither: `idxbor_fml_of_bor` and `guard_fml_of_bor` start
from a `full_bor κ Px`, and

```coq
full_bor_def κ Px := ∃ sn κ',
  κ ⊑ κ' ∗ (∃ Px', □ (bor_sem Px' ↔ bor_sem Px) ∗ sinv_tok sn Px')
  ∗ OwnBorState …
```

mentions the interpretation **twice** in a way that does not transport:
`κ ⊑ κ'` is `llft_incl`, a Leaf guard over `llft_wsatG`, which contains
`box_wsat bor_sem`; and the `□ (bor_sem Px' ↔ bor_sem Px)` is the borrow's
semantic alteration.  Neither is a judgment held at `der`, so `dinto der δ'`
does not move them, and neither is ghost state, so they do not hold at every
candidate either.

**Both are now fixed, by the same two observations Nola makes.**  In
`nola/iris/lft.v` lifetime inclusion is **pure** (`lft_incl`, inclusion of
multisets) or a **persistent token** (`lft_sincl`, `⊑□`); `st_incl` is now
the second of those, so the first occurrence is ghost state and holds at
every candidate.  And in `nola/iris/borrow_deriv.v` the alteration does not
sit inside the token at all - `bor_tok` carries the formula exactly, and
`bor δ` wraps it in two `□ δ (jbupd …)`; the stored indexed borrow is now
that relaxed form, so the second occurrence is a judgment read at `δ`.

Keeping Leaf's guarding logic therefore costs nothing here after all.  What
it did cost was the detour: a guard is not ghost state, so the first
instinct - hold the inclusion as a family over the candidates - looks right
and is what the rest of this file originally described.  It is a token that
was wanted.

### The fix: a storable inclusion and a storable alteration

Both occurrences are *parameters* of the lifetime logic, not things it
inspects: `lifetime_full.v` only ever uses `κ ⊑ κ'` through `guard_trans` /
`llftl_incl_glb` and the iff through `□ (bor_sem Px' ↔ bor_sem Px)`.  So
abstract them.  A class `StBor` supplies

```coq
st_incl : lft → lft → iProp Σ      st_iff : FML $oi Σ → FML $oi Σ → iProp Σ
```

with the closure properties the 18 `unseal_bor` sites use (`refl`, `trans`,
`glb`, the `bor_sep` congruence for `st_iff`) and, at each `BorSem`, the two
elimination rules `st_incl κ κ' ⊢ κ ⊑ κ'` and
`st_iff Px Qx ⊢ □ (bor_sem Px ↔ bor_sem Qx)`.  `idx_bor_def` and
`full_bor_def` use `st_incl`/`st_iff` in place of the two occurrences above.

Both were first given in the model as *families* over the good
interpretations:

```coq
st_incl κ κ' := □ ∀ δ' (_ : Deriv (λ _, True) δ'),
                  @[κ] &&{verus_halt_WGuard_at δ'}&&> @[κ']
st_iff Px Qx := □ ∀ δ' (_ : Deriv (λ _, True) δ'),
                  ⟦ Px ⟧ᶜ(δ') ∗-∗ ⟦ Qx ⟧ᶜ(δ')
```

**Both of those are gone, and for the same reason: they mention `Deriv`,
which is defined from `Jsem`, while `idx_bor` *is* `idxborJT_sem`.**  That
is what kept the model from being concrete, and closing it took two moves.

`st_incl` lost its `⌜Deriv ⊤ δ'⌝` and quantifies over every interpretation.
The cycle is the *restriction*, not the family: without the `Deriv` there is
nothing for `Jsem` to depend on, and nothing is lost, because every proof
the lifetime logic has about a guard is parametric in `BorSem` -
`st_sub_at`, `st_glb_at`, `eternal_incl_at` and `shr_tok_guard_at` all take
an arbitrary `δ` already.  (It was a *token* for one commit, as Nola's
`lft_sincl α β := [†α] ∨ [∞ lft_diff β α]` is.  That form survives as
`eternal_incl_cif`, which is what eternalizing a lifetime produces and
which implies the family, but it cannot express a semantic inclusion.)

`st_iff` lost its `Deriv` restriction, quantifying over every interpretation
instead.  That alone made `Jsem` definable, but it moved the cost to
introduction: `idxbor_fml_iff_at` then wanted its alteration off the
candidates, which no `eqtype` supplies.  So the *stored borrow* changed
shape instead - see "The relaxed borrow" below - and `idxbor_fml_iff_at` is
back to `Deriv_map`'s premise.

### The relaxed borrow

A stored indexed borrow is now what `nola/iris/borrow_deriv.v` calls the
relaxed borrower and what `nola/iris/pborrow_deriv.v` gives `cif_pbor` as
its `Ecsem` - the alteration as a judgment read *at* the interpretation,
over a judgment whose semantics is interpretation-free:

```coq
⟦ cif_idxbor κ idx Px ⟧ᶜ(δ) = ∃ Px', □ δ (iff_j Px' Px) ∗ □ δ (idxbor_j κ idx Px')
```

the thesis's § 6.4.  Changing the alteration is then `Deriv_map`, so
`idxbor_fml_iff_at` asks for the equivalence only at the candidates the
stored borrow maps into - which is exactly `rust_halt`'s
`subty_mutref`/`pbor_wand` premise - and `uniq_subtype` needs nothing beyond
an `eqtype`.  `uniq_uniq_subtype` is the nested case, which the previous
shape could not give at all.

The borrow API did **not** have to be restated wholesale, as upstream's
`borrow_deriv.v` does.  `dFullBor_exact` turns a relaxed full borrow back
into an exact one under an update - open it atomically, carry the contents
across the alteration, close at the formula wanted - so every existing
`full_bor` lemma applies unchanged, and only those consuming an `idx_bor`
directly needed transported forms (`dIdxBor_guard`, `dIdxBor_acc_guarded`,
`dIdxBor_shorten`, `dIdxBor_unnest`, `dIdxBor_to_full`, `dFullBor_idx`).

One rule was lost rather than transported: `alt_into`'s borrow clause is now
*eliminating* rather than *moving*, since a stored borrow cannot be carried
from one candidate to another.  `idxbor_fml_into` went with it, unused.

`llftl_bor_shorten` and `llftl_idx_shorten` take an `st_incl` after this
change; the one call site outside the lifetime logic (`borrow.v`) passes a
closed inclusion, which is storable.

### Done: the lifetime logic now carries both as parameters

`lifetime_full.v` is split in two sections.  The first ends once
`llft_wsatG`, the lifetime tokens and `llft_incl` are defined; between them
sits `StBor`, with `st_incl` and `st_iff` and their closure properties, and
the second section adds `StBorSem` - the two elimination rules at *this*
interpretation - and uses them in

```coq
idx_bor_def κ (sn, κ') Px := st_incl κ κ' ∗ ∃ Px', st_iff Px' Px ∗ sinv_tok sn Px'
```

With both abstracted, **`idx_bor` and `full_bor` no longer mention the
interpretation at all**; `idxborJT_sem` is constant in `δ`, and that is what
makes an indexed borrow storable.  `llftl_bor_shorten`, `llftl_idx_shorten`,
`llftl_reborrow`, `llftl_bor_iff` and `llftl_idx_bor_iff` take an `st_incl`
or an `st_iff`; `llftl_reborrow_meet` is the inclusion-free reborrow, whose
result lives at `κ ⊓ κ'`, for the one caller that has only an ambient
inclusion.

In the model `st_incl`/`st_iff` are the plain-`iProp` families over good
`δ`, and `StBorSem_at δ` instantiates each at `δ`.

### What this changed in the typing layer

Three notions now exist where there used to be one, and the difference is
exactly whether the thing can be *used* at a candidate or only *stored*:

| | lives at | use at a candidate | store in a formula |
|---|---|---|---|
| `dguard Px Qx` | the ambient `δ` | via `dinto der δ'` | it *is* a formula |
| `dguard_all Px Qx` | every `δ`, as judgments | no - reading gives a judgment | yes |
| `fguardx Px Qx` | every `δ`, as guards | yes | via `fguardx_dguard_all` |

`dincl κ κ'` is now `st_incl κ κ'`, i.e. the `fguardx` of two lifetime
tokens, and `incl_fml κ κ'` (the notation `κ ⊑x κ'`) is the formula for it.
`incl_fml` is a *third* judgment in the model (`inclJT`, `cif_incl`), with
the same shape as the indexed borrow: its semantics does not mention `δ`, so
`incl_fml_sem_at` is a `⊣⊢` at **every** candidate - reading it anywhere is
reading it at `der`.  That is what lets `&uniq{κ}`'s ghost assertion store an
inclusion that is later strong enough to shorten a borrow.
`basically_dead` holds a `dincl` for the same reason.

A general guard between two formulas cannot be treated this way: its
endpoints are interpreted, so `guard_fml` stays a judgment at one
interpretation, eliminated at candidates by `dinto der δ'`.

## Done: the model, and soundness

`model.v` gives the concrete interpretation (`FML := cifOF CON`,
`bor_sem := ⟦⟧ᶜ(der)`), `model_inst.v` bundles it into a `typeG`, and
`soundness.v` allocates the world satisfaction and proves that a closed,
semantically well-typed program **terminates**.  What the rest of this file
worked out along the way, in one list:

* **The family rule.**  A judgment is *eliminated* at a candidate the
  ambient interpretation maps into - `dinto der δ'`, which `Deriv_factor'`
  hands out - and *introduced* at every candidate from interpretation-free
  ghost state.  It is never *moved* from one interpretation to another.
* **Raw families.**  Anything that has to be *used* at a candidate cannot be
  a family of stored judgments: `fguardx` is the family of the guards
  themselves, and `st_incl`/`st_iff` are its lifetime and alteration cases.
  Abstracting those two out of `idx_bor` is what makes a borrow storable.
* **Interpretation-independent formulas.**  A thing whose semantics ignores
  the candidate has a `⊣⊢` at *every* candidate and can be a formula:
  `cif_idxbor` and `cif_incl`.
* **Candidates are records.**  The guarding world satisfaction is a function
  of the whole `VerusHaltSem`, not of `bor_sem`, so a candidate carries one -
  wrapped in `Cand`, because an unwrapped one would shadow the ambient
  instance under every binder.
* **Universes.**  `cif`'s own existential stores the index *type* in the
  formula's selector and so is capped at `cif_sel`'s universe, strictly
  below the one `~~𝔄` lives in; `exs_fml` and `exsCT` are the existential
  over a syntactic type's values.
* **Allocation order.**  The ghost state is allocated before the
  interpretation, which is handed in afterwards; and an allocation lemma
  hands out the ghost *name*, not the record, so that the program logic can
  recognise the instance it was given.

What is left is written in `PLAN.md`: `fn`'s stratification,
`fixpoint.v`'s move to `profix`, and a worked example.
