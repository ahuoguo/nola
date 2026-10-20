# Porting AlerusBelt / VerusBelt into Nola, later-free

Branch `later-free-guard`.  Upstream: `verus-belt/src/`.  Keep Leaf's
guarding logic (`P &&{W}&&> Q`); drop `▷` and `iLöb`; use Nola's magic
derivability, `cif` formulas and explicit world satisfactions.  Replacing
the guards with Nola's own borrows is *not* the route.

Everything ported builds green (`make -f Makefile.coq -j4`).

## Not ported

| upstream | lines | why |
|---|---|---|
| `guarding/storage_protocol/` | 1382 | only needed by `typing/protocol.v` |
| `guarding/lib/rwlock.v` | 518 | client of the above |
| `typing/protocol.v` | 1189 | needs `storage_protocol/` |
| `typing/spawn.v` | 394 | `join` is an `iLöb` spin loop - no later-free version |
| `typing/soundness.v` | 100 | needs the model |

The rest of `guarding/` is here (`nola/bi/guard.v`, `nola/iris/guard.v`,
`nola/alerus/{boxes,frac_guard,own_and,auth_frag,na_inv_fork}.v`,
`nola/alerus/lifetime/`, `nola/alerus/util/`); the line counts shrink because
Leaf's later/`iLöb`/`pers` machinery disappears.  Nothing in the tree is
waiting on a missing guarding lemma, so pull in `storage_protocol/` when
starting `protocol.v`, not before.

File-by-file map to upstream: `nola/alerus/CORRESPONDENCE.md`.

## Next: finish the model (`nola/alerus/typing/model.v`)

`typeG` has no instance yet, so the development is sound-but-vacuous.

Done: `alerusCT` leaves, the three judgments (`guard`, `idxbor`, `incl`),
`AlerusSem_at δ`, `alerus_WGuard_at δ`, `StBor`/`StBorSem_at δ`, `TypeFml`,
`GsrcSem`, `HeapSem`, and **`AltSem`**.

1. `PcellFml` / `AtomicInvFml` / `LocalInvFml` / `RaFml`, then `typeG`
2. world-satisfaction allocation and `typing/soundness.v`

## Separate work

* `typing/fixpoint.v` uses a COFE limit; a `cif` is complete as a `prost`,
  not an OFE, so it must move to `profix`/`Productive` (cf.
  `rust_halt/rec.v`).  Until then it assumes `Cofe (FML $oi Σ)`, which the
  model cannot discharge.
* `fn` must be stratified by an execution level (thesis (5.4), § 3.4.1).
  `fn_fml_sem_2` has no model and must not be discharged as it stands.

## Rules this port had to learn

Written out in `nola/alerus/typing/README.md`:

* a judgment can be eliminated at a candidate the ambient interpretation
  maps into, and introduced at every candidate from interpretation-free
  ghost state - but never *moved* between interpretations;
* anything to be *used* at a candidate must be the family of the things
  themselves, not of stored judgments (`fguardx`, `st_incl`, `st_iff`);
* a thing whose semantics ignores the candidate can be a formula with a
  `⊣⊢` at every candidate (`cif_idxbor`, `cif_incl`);
* seal anything that unfolds to `□ ∀ sem, …`, or typeclass search goes
  under the binder and build times go from seconds to minutes.
