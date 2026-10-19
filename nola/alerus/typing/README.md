# `nola/alerus/typing` — port status

A later-free, total-correctness port of AlerusBelt/VerusBelt's
`src/lambda_verus/typing/` (MIT; Hance, Elbeheiry, Matsushita, Dreyer).

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

The adequacy layer it needs is in place: `nola/alerus/lang/adequacy.v`
provides `lrust_adequacy` and, beyond what the original can state,
`lrust_total`.  Two things stand between that and the theorem.

1. **The world satisfaction cannot be allocated in the current order.**
   `llft_wsat_alloc` (`lifetime/lifetime_full.v:1934`) takes the client's
   guarding world satisfaction `WG : iProp Σ` as a *value*, but
   `alerus_WG` mentions `llctx_interp`, which needs the `llft_logicGS` that
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
     `alerus_wsat`.

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

6. **The model.**  A `cif` with the remaining ~25 leaf constructors, a
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

What that costs here: `FML`, `bor_sem` and `alerus_wsat` become
level-indexed up to a fixed maximum `L`, and a `type` carries the level of
its ghost assertion.  The rest of the port needs no level reasoning,
because every *other* formula constructor's interpretation mentions only
its subformulas or a judgment - in particular `guard_fml` and `idxbor_fml`
are judgments and so, like `⟦ref^o_k T⟧`, do not depend on the
interpretation of their contents at all.

## What this means for the earlier plan

An earlier version of this file proposed making `typed_body` candidate-
indexed so that `fn_fml_sem_2` could be discharged by `Deriv_factor'`.
That is not Nola's design and it does not terminate: `Deriv_factor'` would
ask for the function body's typing at every candidate, which is a strictly
harder obligation than the stratified definition and still leaves the
paradox of § 3.4.1 unaddressed.  `rust_halt` keeps its typing judgment at
the ambient interpretation (`type_def` uses `WP[rust_halt_wsat]` with
`⟦⟧ᶜ = ⟦⟧ᶜ(der)`, `type.v:910-932`) precisely because it never stores one.
