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

## `guarding/` → `nola/bi`, `nola/iris`, `nola/verus_halt`

| upstream | here | |
|---|---|---|
| `guard.v` (1503) | `nola/bi/guard.v` (332), `nola/iris/guard.v` (97), `nola/iris/point.v` (135) | the later-free fragment |
| — | `nola/lrust/guard.v` (71, new) | `Heap-Read-Guarded` and its siblings for the *total* `twpw` |
| `own_and.v` (303), `own_and_own_sep.v` (530) | `nola/verus_halt/own_and.v` (56), `auth_frag.v` (70) | |
| `internal/auth_frag_util.v` (320) | `nola/verus_halt/auth_frag.v` | folded in |
| `internal/na_invariants_fork.v` (136) | `nola/verus_halt/na_inv_fork.v` (209) | |
| `lib/boxes.v` (513) | `nola/verus_halt/boxes.v` (406) | |
| `lib/fractional.v` (494) | `nola/verus_halt/frac_guard.v` (408) | |
| `lib/cancellable.v` (221) | `nola/verus_halt/lifetime/ra.v` | folded in |
| `lib/lifetime.v` (884) | `nola/verus_halt/lifetime/` | see below |
| `lib/non_atomic_map.v` (679) | `nola/verus_halt/util/non_atomic_cell_map.v` (1464) | together with `lambda_verus/util/non_atomic_cell_map.v` |
| `factoring_props.v`, `guard_later_pers.v`, `tactics.v`, `internal/{factoring_upred,inved,misc_tactics,wsat_util}.v` | — | later/`pers` machinery, or subsumed by Nola's `modw`/`wsat` |
| `lib/rwlock.v` (518) | — | **not ported**, client of the storage protocol |
| `storage_protocol/base_storage_opt.v` (110), `storage_protocol/protocol.v` (1272) | — | **not ported**, needed only by `typing/protocol.v` |

Leaf's `guards_alloc`, which makes a guard persistent by allocating an Iris
invariant, has no later-free counterpart; `nola/verus_halt/eternal.v` (78, new)
replaces its one use with an authoritative set of eternalized keys.

`nola/verus_halt/two_state.v` (166, new) is the other file with no upstream
counterpart: one exclusive token with two incomparable states, whose
*non-separating* contradiction `ts_and_false` is what
`nola/bi/guard.v`'s `guard_cancel_or` needs.  It is what makes the stored
owning pointer extractable as well as productive (`rec.v`'s
`sown_tyd_take`), and `frac_guard.v`'s death token is the same idea at a
fractional camera.

Nola proper gained six results for this port, in four files:

| file | what |
|---|---|
| `nola/iris/borrow.v` | `borrowGS_of`, `borrow_wsat_alloc_name` - the analogue of `sinv_wsat_alloc_name`, handing out a borrowing machinery's ghost *name* before the interpretation that mentions it is built.  Several machineries - one per execution level - need that order |
| `nola/iris/sinv.v` | `sinv_wsat_alloc_name` (a *second* `sinv_wsat` under the same ghost functor), `sinv_tok_agree` |
| `nola/iris/dinv.v` | `dinv_wsat_sinv`: a `dinv_wsat` is a `sinv_wsat` whose interpretation ignores the index |
| `nola/bi/deriv.v` | `Deriv_const`, `der_const`: a judgment whose semantics ignores the candidate *is* its body, in both directions.  This is what collapses `FnFml` to one equation |

## `lambda_verus/lang/` → `nola/verus_halt/lang/`

| upstream | here |
|---|---|
| `adequacy.v` (51) | `adequacy.v` (108) |
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

## `lambda_verus/lifetime/` → `nola/verus_halt/lifetime/`

`lifetime_internals/*.v` map one-to-one onto files of the same name
(`augment_outlives`, `expire_lt`, `iff`, `inv`, `join`, `new_lt`, `ra`,
`reborrow`, `split`, `unborrow`, `unnest`); `lifetime_full.v` (1942 → 3150)
keeps its name.  One file is new: `level.v` (1142), a per-level view of the dead
set - see PLAN.md item 2, step 3.  `lifetime_full.v`'s invariant is
*decoupled* from the borrow bookkeeping's view of the world: the
bookkeeping keeps its own created/dead/blocked, the invariant carries the
kill order those deads are a prefix of, and `Delayed` marks the one-atom
gap between the shared dead set and that order.

Four structural changes:

* the lifetime invariant and the box become **world satisfactions**
  (`llft_wsat = llft_wsatG ∗ llft_inv_other`) threaded explicitly, instead
  of Iris invariants at `↑Nmain`/`↑Nbox`;
* slices hold **formulas** interpreted by a `BorSem` parameter, not `iProp`s,
  so `inv.v` gains `BorSem`, `BorStateFml` and `ShrBorSem`;
* `LtRa`'s two halves sit at **two ghost names**: `llft_name` for the
  lifetime tokens (`LtState`, `Alive`, `Dead`), `bor_name` for the borrow
  bookkeeping (`AuthBorState`, `OwnBorState`, `ModuloDead`).  Upstream has
  one.  The camera is unchanged - `lt_inv`'s only cross term was `w ⊆ d`,
  and `modulo_dead` no longer contributes to the global dead set - and
  what the camera enforced is now `inner_inv`'s persistent
  `∀ d ∈ dead, Dead llft_name d`.  This is what lets one borrowing
  machinery per execution level sit over one lifetime algebra;
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

## `lambda_verus/typing/` → `nola/verus_halt/typing/`

One-to-one, same names, for: `atomic_inv`, `base`, `base_type`, `bool`,
`borrow`, `cont`, `cont_context`, `freeable_util`, `function`,
`ghost`, `int`, `inv_context`, `lft_contexts`, `lifetime`, `local_inv`,
`mod_ty`, `own`, `pcell`, `pptr`, `product`, `product_split`, `programs`,
`programs_util`, `programs_util_atomic`, `programs_util_own`, `ra`,
`shr_bor`, `sum`, `tracked`, `type`, `type_context`, `type_sum`, `uninit`,
`uniq_bor`, `uniq_cmra`, `uniq_util`.

`soundness.v` (100 upstream, 143 here) is ported, and proves *termination*
as well as the original's safety.

Ten files are new here:

| here | what |
|---|---|
| `ctx.v` (2388) | the interface the whole typing layer is parametric in: `verus_haltGS` (ghost state), `VerusHaltSem` (the interpretation), `TypeFml`, `GsrcSem`, `HeapSem`, `AltSem` - the rules for stored guards, indexed borrows and inclusions at a derivability candidate - and the relaxed borrow (`dFullBor`, `dIdxBor`, `dalter`) |
| `model.v` (2031) | the concrete model: `FML := cifOF CON`, `bor_sem := ⟦⟧ᶜ(der)`, the five judgments - the fifth being `eownJT`, the owning pointer's capability - and the instances of the classes above |
| `model_inst.v` (74) | the `typeG` bundle and the remaining formula-language classes |
| `inst.v` (544) | a concrete `CON` and `JUDG` with their semantics, the two soundness theorems at them, and `verus_halt_lvl_const`/`verus_halt_levels_alloc` - the first family of execution levels anything in the tree supplies, so that `level_ctx.v`'s apparatus is not vacuous at the concrete model |
| `rec.v` (1877) | recursive types by `profix`: a type's data as a `prost`, the laws split into an unconditional `Ty` and a depth-indexed `TyProphAt`, **two** guarded formers proved `Productive` - `&shr{κ}` and the owning pointer, the latter with its pointee behind `eown_fml`, so it is extractable as well (`sown_tyd_take`) and the list comes apart (`own_list_tyd_cons_take`) - `ty_rec` with both laws, `xsum2_tyd`/`unit_tyd` for the body, the two worked recursive types `ty_shr_list` and `ty_own_list`, and their subtyping: `tyd_incl_at` (`type_incl` with the depth exposed), a congruence per former, and `ty_rec_incl` by depth induction |
| `own_rec.v` (293) | the stored owning pointer as a `type`: `sown_ptr n ty`, whose data *is* `rec.v`'s `sown_tyd n (ty_d ty)`, with `own.v`'s three rules for it (`read_sown_copy`, `read_sown_move`, `write_sown`) and the bridge saying that a guarded recursion's hole is exactly one of these |
| `levels.v` (261) | execution levels as *ghost names*, following the thesis's Chapter 5 but without its global maximum level: `lvs_names_alloc` (names first, interpretation after), `lvs_below` (the thesis's `∗_{k<j} Winv_k`), `lv_tok`/`lvs_below_acc`/`lvs_below_alloc` (a reference at level `k` is reachable from, and allocatable at, execution level `j > k`) and `twpw_lvs_le` (its `ty-lev`) |
| `strat.v` (1034) | the thesis's **Chapter 5 case study**, mechanized over `nola.lrust`: leveled types with `ref°ₖ`, `→ⱼ` and (5.1)'s `listₖ`, the interpretation as a level-indexed family *and* a derivability-indexed one ((5.4) and (5.5) both), the typing rules, the subtyping rules including `≤-ref` **used coinductively**, Corollary 5.3, § 5.1's closing iteration example and four closed terminating programs.  Not part of the port - it is what settles what the port's `fn` would need, and it is axiom-free |
| `strat_bor.v` (658) | **levelled borrows**: the question `strat.v` leaves open and that neither source answers - the thesis's Chapter 5 has no borrows, `rust_halt` has no function type.  One borrowing machinery per execution level over *one* lifetime algebra, `typed_call_borrowed` (a closure stored in a borrow, retrieved and called, with `j ≤ k < i` forced), `knot_not_typable`, and a closed terminating program.  Not part of the port - it is what justifies the `lifetime/ra.v` refactor, and it is axiom-free |
| `level_ctx.v` (685) | the port's **execution levels**, over *one* lifetime logic: `verus_haltNames` (a level's own names - its borrows, box, shared-borrow family, invariants, store - with `llft_logicGS` shared for the whole run), `verus_haltGS_of` (the thesis's `verus_haltGS_at`), `verus_halt_names_alloc` and `verus_halt_names_alloc_more` (a further level against the state already there), the family `verus_halt_wsats`, `verus_halt_wsat_below` (`∗_{k<j} Winv_k` beside one shared copy), `ty-lev` as `twpw_verus_halt_le`, `typed_body_lv_le` (the thesis's `≤-→` for the judgment), and `verus_halt_wsat_below_acc` - the port's `bors_below_acc`, by which a body at execution level `j` reaches level `k < j`'s machinery and gets back *level `k`'s* world satisfaction |

Three upstream files are missing:

| upstream | why |
|---|---|
| `fixpoint.v` (494) | **superseded, and not portable as written**: it builds a recursive type as a COFE limit, so every result in it is under `Cofe (FML $oi Σ)` *and* `TypeContractive`, neither of which the `cif` model provides - a `cif` is complete as a `prost`, not an OFE.  `rec.v`'s `profix`/`Productive` construction is what replaces it.  A port of it did sit in the tree, compiling and imported by nothing; it was removed rather than left to look like coverage |
| `protocol.v` (1189) | needs `guarding/storage_protocol/` |
| `spawn.v` (394) | `join` is a busy-wait spin loop; see below |

**`spawn.v` is not a matter of technique.**  `join` is

```
rec: "join" ["c"] := if: !ˢᶜ"c" then (* read the result *) else "join" ["c"]
```

a spin loop with no decreasing measure, and upstream's `join_spec`
(`lang/lib/spawn.v`) is proved by `iLöb`.  Under a *total* weakest
precondition the specification is not merely unproved but **false**:
`twp` quantifies over every schedule with no fairness assumption, and a
scheduler that never runs the spawned thread makes `join` diverge.  So
this entry will not move without a fair-scheduling total weakest
precondition, which neither λRust's operational semantics nor Iris's
`twp` provides.  (`typing/spawn.v` itself contains no `iLöb`; it is the
client of the one in `lang/lib/spawn.v`.)

`examples/` (`assert`, `list`, `pcell_example`) are not ported;
`typing/examples/basic.v` (163) is new here, and is the first worked example
in the tree.

### What changed inside the ported typing files

* A type's ghost assertion `ty_own` becomes a **formula** `ty_ghox` plus its
  interpretation, because it has to live inside a borrow.  `type.v` carries
  the `_at` versions of every ghost-assertion law, quantified over a
  candidate interpretation.
* `κ ⊑ κ'` as *data* becomes `dincl` (= `st_incl`, the family
  `□ ∀ δ, @[κ] &&{verus_halt_WGuard_at δ}&&> @[κ']` over *every*
  interpretation) and, as a formula, `incl_fml` (notation `κ ⊑x κ'`).
* An indexed borrow in a formula is `idxbor_fml`, a judgment; `&{κ,i} Px`
  itself no longer mentions the interpretation.
* `⧖d`/`⧗d`/`£n` and the steps that pay for laters are gone throughout; the
  depth indices `d`, `g` survive as plain numbers.

Performance traps this port hit, and why two of them do not arise
upstream: `nola/verus_halt/PERF.md`.
