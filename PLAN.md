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

Two checkable statements fix what is left:

* **`FnFml` is the only class in `typing/` with no instance anywhere.**  Its
  two fields, `fn_fml_sem_2` and `fn_incl_of_all`, are what an execution-level
  stratification has to supply - item 2 below.
* **`TypeContractive` has no instance either**, so `typing/fixpoint.v` is
  inert: it is a correct construction with nothing to apply it to, and its
  `Cofe (FML $oi Σ)` assumption is one the model cannot discharge - item 3.

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

1. **A worked example** (in progress).  `typing/examples/basic.v` types two
   small programs against the rules, parametric in `CON`/`JUDG` exactly as
   `rust_halt/verify/` is.  Worth extending to a program that allocates,
   writes and frees a box, which exercises `own_ptr`, `type_assign` and
   `type_deref`, and to one that uses `uniq_subtype`, which exercises the
   relaxed borrow.  Beware the two traps in `nola/alerus/PERF.md`:
   `type_val` cannot be applied to a concrete program, and transformers must
   be built forward into an evar.

2. **`fn` must be stratified by an execution level** (thesis § 5, and (5.4)).
   `FnFml`'s `fn_fml_sem_2` and `fn_incl_of_all` have no model, so `fn` is
   the one type former the model does not interpret - which is why
   `soundness.v` is stated about a typing judgment, as `rust_halt`'s adequacy
   is.

   The device, from § 5.2: types carry a level `i`, and the function type's
   interpretation is a total Hoare triple whose *world satisfaction mentions
   only lower levels*,

   > `⟦T →ⱼ U⟧ᵢ v ≜ ∀u. [⟦T⟧ᵢ u] v(u) [⟦U⟧ᵢ] ∗_{k<j} Winv_k ⟦⟧*_k`   (5.4)

   which is well-formed because `k < j ≤ i`, so the recursion on the level
   is well-founded.  That is exactly what `fn_fml_sem_2` lacks: `Deriv_factor'`
   asks for `typed_body` at every candidate, and `typed_body` is stated at the
   ambient interpretation.

   The cost is the whole ghost-state layer: one copy of the formula
   machinery (`sinv`, the box, the borrows) per level up to a fixed maximum
   `L` - the thesis parameterises by `L` for the same reason, that Coq's
   global camera is finite (§ 5.2 fn. 3) - plus `FML`, `bor_sem`,
   `alerus_wsat` and `typed_body` indexed by level, and a level on every
   type former.  This is weeks, not days.

3. **`typing/fixpoint.v`** builds a recursive type as a COFE limit; a `cif`
   is complete as a `prost`, not an OFE, so it must move to
   `profix`/`Productive`.  Until then it assumes `Cofe (FML $oi Σ)`, which
   the model cannot discharge.  The file is also inert - `TypeContractive`
   has no instance - so this buys recursive types rather than fixing a live
   path.

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

   ### Still to do

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
