# Porting AlerusBelt / VerusBelt into Nola, later-free

Branch `later-free-guard`.  Upstream: `verus-belt/src/`.  Keep Leaf's
guarding logic (`P &&{W}&&> Q`); drop `▷` and `iLöb`; use Nola's magic
derivability, `cif` formulas and explicit world satisfactions.  Replacing
the guards with Nola's own borrows is *not* the route.

Everything ported builds green (`make -f Makefile.coq -j4`).

## Where it stands

The model is **done**: `nola/alerus/typing/model.v` builds the `cif` model
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
semantics**, so neither theorem is vacuous; `alerus_type_soundness` and
`alerus_type_safety` are the concrete forms, and `Print Assumptions` gives
only `Eq_rect_eq` for those too.  Neither this development nor
`nola/examples/rust_halt/` had ever instantiated `sigTCT`/`sigTO` before.

`typing/rec.v` then builds recursive types by `profix`, as
`nola/examples/rust_halt/rec.v` does, so the `Cofe (FML $oi Σ)` that
`typing/fixpoint.v` assumes is no longer on any path.  `&shr{κ}` is the
guarded former and is *proved* productive; the owning pointer is
*also* productive, now that its pointee sits in a simple invariant; and
`ty_shr_list` and `ty_own_list` - `μ X. Σ! [(); 𝔄 * &shr{κ} X]` and
`μ X. Σ! [(); 𝔄 * own n X]` - are worked recursive types built from them.

One checkable statement fixes what is left:

* **`FnFml` is the only class in `typing/` with no instance anywhere.**  Its
  two fields, `fn_fml_sem_2` and `fn_incl_of_all`, are what an execution-level
  stratification has to supply - item 2 below.  (`TypeContractive` has none
  either, but it is superseded: `rec.v` uses `Productive` over `cif`'s
  `prost`, which is what the model actually has.)

File-by-file map to upstream: `nola/alerus/CORRESPONDENCE.md`.
Performance traps, four of which present as a hang: `nola/alerus/PERF.md`.

## Not ported

| upstream | lines | why |
|---|---|---|
| `guarding/storage_protocol/` | 1382 | only needed by `typing/protocol.v` |
| `guarding/lib/rwlock.v` | 518 | client of the above |
| `typing/protocol.v` | 1189 | needs `storage_protocol/` |
| `typing/spawn.v` | 394 | `join` is an `iLöb` spin loop - no later-free version |

The rest of `guarding/` is here; the line counts shrink because Leaf's
later/`iLöb`/`pers` machinery disappears.  Nothing in the tree waits on a
missing guarding lemma, so pull in `storage_protocol/` when starting
`protocol.v`, not before.

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

Both offenders are gone: `st_incl` is a token, and `st_iff` quantifies over
every interpretation rather than the good ones.  See step 0 below for what
that cost.

## Next

The model is closed and both of the blockers that were open after it are
gone; what is written up in `nola/alerus/typing/inst.v` is the record of
how.  What remains is one small item and two large ones, and the two large
ones are large for reasons now understood rather than guessed at.

1. **A worked example** - done.  `typing/examples/basic.v` types four
   programs against the rules, parametric in `CON`/`JUDG` exactly as
   `rust_halt/verify/` is: a binding, two bindings and an addition, a box
   allocated and freed, and a box allocated, *written* and freed - the last
   bringing `own_ptr`'s `typed_write` in through `write_own`.  Two subtyping
   facts exercise the relaxed borrow, including a unique borrow of a unique
   borrow, which is the case `uniq_subtype` could not state before.

   The traps are recorded in `nola/alerus/PERF.md` and each one bit here:
   `type_val` cannot be applied to a concrete program, `type_new`'s size
   must be passed rather than unified, transformers must be built forward
   into an evar, and `Closed` premises are discharged by resolution *before*
   the bracket list, which silently shifts every branch.

2. **`fn` must be stratified by an execution level** (thesis § 5).
   `FnFml`'s `fn_fml_sem_2` and `fn_incl_of_all` have no model, so `fn` is
   the one type former the model does not interpret - which is why
   `soundness.v` is stated about a typing judgment, as `rust_halt`'s adequacy
   is.

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
   once, for the store world satisfaction inside `alerus_WGuard` beside
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
   * **Not every world satisfaction need be levelled.**  The thesis levels
     only `Winv`, the thing a function body may access.  Here that is the
     borrow machinery; the lifetime machinery, which a body does not open,
     looks like it can stay single.  Which of `alerus_wsat`'s components
     must be per-level is the one genuinely open question left in this item.
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
      `alerusGS` and `alerus_wsat` (as they do `rust_haltGS`), a `storeCT`
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
   one constructor in `alerusCONF` and one judgment in `alerusJUDGF` - both
   of which `inst.v` already extends six and four times over.

   It is *dearer* than it sounds in another.  `dinvGS FML Σ` is
   definitionally `sinvGS FML Σ`, which `alerusGS` already carries - but
   that family is taken: `nola/alerus/boxes.v` defines
   `box_wsat sm := sinv_wsat (λ γ Px, slice_body sm γ Px)` on it, and
   `box_wsat bor_sem` is a conjunct of `alerus_WGuard`.  A `sinvGS` carries
   exactly one `sinv_name`, so the store needs a second family: a new
   `alerus_store_name : gname` field beside `alerus_shr_name` and
   `alerus_eternal_name`, a non-global `sinvGS` built from it, and care that
   `storeCT_ecsem` and `store_as_cif` resolve `dinvGS` to *that* one rather
   than the box's.  Then `dinv_wsat bor_sem` joins `alerus_wsat`, whose
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

   `typing/inst.v` now proves it, at the concrete `alerusCON` where the
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
      boxes', placed *inside* `alerus_WGuard`;
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
   eguard_fml_alloc : bor_sem Px =[alerus_WGuard]=∗
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

   so, with `dinv_wsat` sitting inside `alerus_WGuard` (it already did, for
   `pstore`), **an invariant is a guard** - three lines, no axioms:

   ```coq
   Lemma dinv_fml_guard {Px} :
     bor_sem (dinv_fml Px) ⊢ (True &&{alerus_WGuard}&&> bor_sem Px).
   Proof.
     iIntros "#i". iApply (guard_trans (Q:=alerus_store_wsat)).
     { iApply (guard_wsat_out (W':=alerus_store_wsat)). }
     iApply guard_intro. iIntros "!> W".
     rewrite /alerus_store_wsat.
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

   ### Still to do, and it is a genuine tension rather than a gap

   **Moving a pointee out.**  `sown_tyd`'s pointee can be *borrowed* - that
   is what the reversible accessor gives - but not moved out, so the list
   can be read and not destructured, and `typing/own.v`'s rules do not apply
   to it as they stand.  The port therefore has two owning pointers:

   | | content | extractable | productive |
   |---|---|---|---|
   | `own_ptr` (`own.v`) | in hand | yes | no |
   | `sown_tyd` (`rec.v`) | in a simple invariant | no | yes |

   The obvious merge is `store_tok`'s shape - hold an exclusive `token γ`
   and store `Px ∨ token γ`, so that the guard rules out the right disjunct
   while extraction deposits the token.  **It does not work, and the reason
   is structural.**  `guard W P Q` is

   ```coq
   □ ∀ T, P ∗ (P -∗ W ∗ T) -∗ Q ∗ (Q -∗ W ∗ T)
   ```

   - note the `□`.  Narrowing a guard on `Px ∨ token γ` to one on `Px` needs
   `guard_or_false` or `guard_cancel_or`, and both ask for a side condition
   that is *persistent*: `guard_or_false` wants `token γ &&{W}&&> False`,
   which a `□` body cannot prove while the only evidence is an owned token,
   and `guard_cancel_or` wants `Q ∧ R ⊢ False`, which two copies of the same
   exclusive resource do not give - `P ∧ P ⊣⊢ P`.  (`&uniq` can use
   `guard_or_false` because its discriminator, a lifetime being dead, *is*
   persistent.)

   And the general form of the obstruction is the same: whatever
   distinguishes "content still inside" from "content extracted" has to be
   persistent for a `□` guard to use it, yet it must be falsified by
   extraction.  So the two cannot be merged while `ty_guard_proph` is
   guard-shaped.

   The ways out, none of them small:

   1. reshape `ty_guard_proph` so its premise is ownership under the world
      satisfaction rather than a guard, which is `rust_halt`'s `TyOpAt`
      shape - its prophecy law is a fupd and it has no Leaf guards at all.
      This is the honest fix and it touches every type former.
   2. leave the two formers side by side, which is where the tree is: the
      recursion uses `sown_tyd` and the typing rules use `own_ptr`, and a
      recursive type is readable but not destructurable.
   3. give the list its own destructuring rules against `sown_tyd`
      directly, which is `verify/list.v`-level work and does not need
      `own_ptr` at all.

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

Written out in `nola/alerus/typing/README.md`:

* a judgment can be eliminated at a candidate the ambient interpretation
  maps into, and introduced at every candidate from interpretation-free
  ghost state - but never *moved* between interpretations;
* anything to be *used* at a candidate must be the family of the things
  themselves, not of stored judgments (`fguardx`, `st_incl`, `st_iff`);
* a thing whose semantics ignores the candidate can be a formula with a
  `⊣⊢` at every candidate (`cif_idxbor`, `cif_incl`);
* a candidate is a *wrapped* `AlerusSem`: unwrapped it would shadow the
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
  to recognise the instance it was given.
