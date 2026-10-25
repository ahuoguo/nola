# VerusBelt → Nola: file correspondence

Upstream is `~/Downloads/verus-belt/src/`.  `iris/` and `stdpp/` there are
vendored copies of Iris and std++; this port uses the ones Nola depends on,
so they have no entry below.

Line counts are upstream → here.  Where the port is smaller it is because
the later-, `iLöb`- and `pers`-specific machinery of Leaf disappears in a
later-free setting, or because only the part the typing layer calls was
carried over.  Where it is larger it is because the interpretation is now an
explicit parameter (`BorSem`, `NaSem`, …) and the world satisfactions are
threaded by hand rather than hidden in Iris invariants.

## `guarding/` → `nola/bi`, `nola/iris`, `nola/alerus`

| upstream | here | |
|---|---|---|
| `guard.v` (1503) | `nola/bi/guard.v` (303), `nola/iris/guard.v` (97), `nola/iris/point.v` (135) | the later-free fragment |
| `own_and.v` (303), `own_and_own_sep.v` (530) | `nola/alerus/own_and.v` (56), `auth_frag.v` (70) | |
| `internal/auth_frag_util.v` (320) | `nola/alerus/auth_frag.v` | folded in |
| `internal/na_invariants_fork.v` (136) | `nola/alerus/na_inv_fork.v` (163) | |
| `lib/boxes.v` (513) | `nola/alerus/boxes.v` (406) | |
| `lib/fractional.v` (494) | `nola/alerus/frac_guard.v` (391) | |
| `lib/cancellable.v` (221) | `nola/alerus/lifetime/ra.v` | folded in |
| `lib/lifetime.v` (884) | `nola/alerus/lifetime/` | see below |
| `lib/non_atomic_map.v` (679) | `nola/alerus/util/non_atomic_cell_map.v` (1464) | together with `lambda_verus/util/non_atomic_cell_map.v` |
| `factoring_props.v`, `guard_later_pers.v`, `tactics.v`, `internal/{factoring_upred,inved,misc_tactics,wsat_util}.v` | — | later/`pers` machinery, or subsumed by Nola's `modw`/`wsat` |
| `lib/rwlock.v` (518) | — | **not ported**, client of the storage protocol |
| `storage_protocol/base_storage_opt.v` (110), `storage_protocol/protocol.v` (1272) | — | **not ported**, needed only by `typing/protocol.v` |

Leaf's `guards_alloc`, which makes a guard persistent by allocating an Iris
invariant, has no later-free counterpart; `nola/alerus/eternal.v` (78, new)
replaces its one use with an authoritative set of eternalized keys.

## `lambda_verus/lang/` → `nola/alerus/lang/`

| upstream | here |
|---|---|
| `adequacy.v` (51) | `adequacy.v` (107) |
| `heap.v` (1658) | `heap.v` (1689) |
| `lang.v` (670) | `lang.v` (674) |
| `lib/memcpy.v` (105) | `lib/memcpy.v` (108) |
| `lib/new_delete.v` (52) | `lib/new_delete.v` (85) |
| `lifting.v` (867) | `lifting.v` (934) |
| `notation.v` (108) | `notation.v` (108) |
| `proofmode.v` (311) | `proofmode.v` (469) |
| `races.v` (298) | `races.v` (305) |
| `tactics.v` (288) | `tactics.v` (288) |
| `time.v` (427) | — | the time receipts `⧖`/`⧗` and `£` disappear with the laters |
| `lib/spawn.v` (144) | — | see `typing/spawn.v` |

Weakest preconditions are Nola's total `twpw` over an explicit world
satisfaction, not `wp`.

## `lambda_verus/lifetime/` → `nola/alerus/lifetime/`

`lifetime_internals/*.v` map one-to-one onto files of the same name
(`augment_outlives`, `expire_lt`, `iff`, `inv`, `join`, `new_lt`, `ra`,
`reborrow`, `split`, `unborrow`, `unnest`); `lifetime_full.v` (1942 → 2167)
keeps its name.

Three structural changes:

* the lifetime invariant and the box become **world satisfactions**
  (`llft_wsat = llft_wsatG ∗ llft_inv_other`) threaded explicitly, instead
  of Iris invariants at `↑Nmain`/`↑Nbox`;
* slices hold **formulas** interpreted by a `BorSem` parameter, not `iProp`s,
  so `inv.v` gains `BorSem`, `BorStateFml` and `ShrBorSem`;
* `idx_bor`/`full_bor` carry an abstract **`StBor`** (`st_incl`, `st_iff`)
  in place of the Leaf guard `κ ⊑ κ'` and the `□ (bor_sem Px' ↔ bor_sem Px)`,
  which is what makes a borrow storable in a formula.  `lifetime_full.v` is
  split in two sections around the declaration of that class.

## `lambda_verus/prophecy/`, `lambda_verus/util/` → same names

`prophecy/{prophecy,syn_type}.v`, `util/{atomic_lock_counter,basic,
cancellable_na_invariants,cellmap,discrete_fun,fancy_lists,
non_atomic_cell_map,vector}.v` port one-to-one.  `util/adequacy_util.v` and
`util/{cancellable,update}.v` are folded into `lang/adequacy.v`,
`lifetime/ra.v` and Nola's `modw`.

## `lambda_verus/typing/` → `nola/alerus/typing/`

One-to-one, same names, for: `atomic_inv`, `base`, `base_type`, `bool`,
`borrow`, `cont`, `cont_context`, `fixpoint`, `freeable_util`, `function`,
`ghost`, `int`, `inv_context`, `lft_contexts`, `lifetime`, `local_inv`,
`mod_ty`, `own`, `pcell`, `pptr`, `product`, `product_split`, `programs`,
`programs_util`, `programs_util_atomic`, `programs_util_own`, `ra`,
`shr_bor`, `sum`, `tracked`, `type`, `type_context`, `type_sum`, `uninit`,
`uniq_bor`, `uniq_cmra`, `uniq_util`.

`soundness.v` (100 upstream, 182 here) is ported, and proves *termination*
as well as the original's safety.

Eight files are new here:

| here | what |
|---|---|
| `ctx.v` (2120) | the interface the whole typing layer is parametric in: `alerusGS` (ghost state), `AlerusSem` (the interpretation), `TypeFml`, `GsrcSem`, `HeapSem`, `AltSem` - the rules for stored guards, indexed borrows and inclusions at a derivability candidate - and the relaxed borrow (`dFullBor`, `dIdxBor`, `dalter`) |
| `model.v` (1833) | the concrete model: `FML := cifOF CON`, `bor_sem := ⟦⟧ᶜ(der)`, the four judgments, and the instances of the classes above |
| `model_inst.v` (74) | the `typeG` bundle and the remaining formula-language classes |
| `inst.v` (364) | a concrete `CON` and `JUDG` with their semantics, and the two soundness theorems at them |
| `rec.v` (1661) | recursive types by `profix`: a type's data as a `prost`, the laws split into an unconditional `Ty` and a depth-indexed `TyProphAt`, **two** guarded formers proved `Productive` - `&shr{κ}` and the owning pointer, the latter with its pointee behind a stored guard - `ty_rec` with both laws, `xsum2_tyd`/`unit_tyd` for the body, the two worked recursive types `ty_shr_list` and `ty_own_list`, and their subtyping: `tyd_incl_at` (`type_incl` with the depth exposed), a congruence per former, and `ty_rec_incl` by depth induction |
| `levels.v` (261) | execution levels as *ghost names*, following the thesis's Chapter 5 but without its global maximum level: `lvs_names_alloc` (names first, interpretation after), `lvs_below` (the thesis's `∗_{k<j} Winv_k`), `lv_tok`/`lvs_below_acc`/`lvs_below_alloc` (a reference at level `k` is reachable from, and allocatable at, execution level `j > k`) and `twpw_lvs_le` (its `ty-lev`) |
| `strat.v` (1030) | the thesis's **Chapter 5 case study**, mechanized over `nola.lrust`: leveled types with `ref°ₖ`, `→ⱼ` and (5.1)'s `listₖ`, the interpretation as a level-indexed family *and* a derivability-indexed one ((5.4) and (5.5) both), the typing rules, the subtyping rules including `≤-ref` **used coinductively**, Corollary 5.3, § 5.1's closing iteration example and four closed terminating programs.  Not part of the port - it is what settles what the port's `fn` would need, and it is axiom-free |
| `syn_type.v` (942) | **dead**: not in `_CoqProject`, no `.vo`, imports `nola.lrust`.  A stale copy of `prophecy/syn_type.v`, which is the live grammar |

Two upstream files are missing:

| upstream | why |
|---|---|
| `protocol.v` (1189) | needs `guarding/storage_protocol/` |
| `spawn.v` (394) | `join` is a spin loop proved by `iLöb` |

`examples/` (`assert`, `list`, `pcell_example`) are not ported;
`typing/examples/basic.v` (111) is new here, and is the first worked example
in the tree.

### What changed inside the ported typing files

* A type's ghost assertion `ty_own` becomes a **formula** `ty_ghox` plus its
  interpretation, because it has to live inside a borrow.  `type.v` carries
  the `_at` versions of every ghost-assertion law, quantified over a
  candidate interpretation.
* `κ ⊑ κ'` as *data* becomes `dincl` (= `st_incl`, the family
  `□ ∀ δ, @[κ] &&{alerus_WGuard_at δ}&&> @[κ']` over *every*
  interpretation) and, as a formula, `incl_fml` (notation `κ ⊑x κ'`).
* An indexed borrow in a formula is `idxbor_fml`, a judgment; `&{κ,i} Px`
  itself no longer mentions the interpretation.
* `⧖d`/`⧗d`/`£n` and the steps that pay for laters are gone throughout; the
  depth indices `d`, `g` survive as plain numbers.

Performance traps this port hit, and why two of them do not arise
upstream: `nola/alerus/PERF.md`.
