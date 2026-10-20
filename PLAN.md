# Porting AlerusBelt / VerusBelt into Nola, later-free

Working branch: `later-free-guard`.  Upstream: `verus-belt/src/`.

The goal is a **later-free, total-correctness** version of VerusBelt's type
system: keep Leaf's *guarding* logic (`P &&{W}&&> Q`), but give it a
foundation that needs no `▷` and no `iLöb`, using Nola's machinery - magic
derivability (`nola/bi/deriv.v`), `cif` formulas (`nola/iris/cif.v`), and
world satisfactions threaded explicitly instead of Iris invariants.

Replacing the guarding logic with Nola's own borrow connectives is **not**
the route; see `nola/alerus/typing/README.md`.

## Where things stand

| upstream | here | state |
|---|---|---|
| `guarding/guard.v` (1503) | `nola/bi/guard.v`, `nola/iris/guard.v`, `nola/iris/point.v` (535) | the later-free fragment the port uses |
| `guarding/own_and*.v` (833) | `nola/alerus/own_and.v`, `auth_frag.v` (126) | ditto |
| `guarding/lib/boxes.v` (513) | `nola/alerus/boxes.v` (406) | done |
| `guarding/lib/fractional.v` (494) | `nola/alerus/frac_guard.v` (391) | done |
| `guarding/lib/cancellable.v` (221) | `nola/alerus/lifetime/ra.v` | folded in |
| `guarding/lib/lifetime.v` (884) | `nola/alerus/lifetime/` | done, later-free |
| `guarding/lib/non_atomic_map.v` (679) | `nola/alerus/util/non_atomic_cell_map.v` | done |
| `guarding/internal/na_invariants_fork.v` | `nola/alerus/na_inv_fork.v` | done |
| `guarding/lib/rwlock.v` (518) | — | **not ported** |
| `guarding/storage_protocol/` (1382) | — | **not ported** |
| `lambda_verus/typing/*.v` | `nola/alerus/typing/` | all but three files |
| `typing/protocol.v` (1189) | — | **not ported** (needs `storage_protocol/`) |
| `typing/spawn.v` (394) | — | **blocked**, see below |
| `typing/soundness.v` (100) | — | **next**, needs the model |

Everything that is ported builds: `make -f Makefile.coq -j4` is green.

### Do we need the whole `guarding/` directory?

No, and the table says why.  `guard.v`, `own_and*.v` and the `lib/` files are
already here in the form the port uses - the line counts shrink because the
later-, `iLöb`- and `pers`-specific machinery of Leaf disappears in a
later-free setting, and because only the lemmas the typing layer actually
calls were carried over.  Nothing currently in the tree is waiting on a
missing guarding lemma.

Two pieces are genuinely absent and are needed only for work that has not
started:

* `storage_protocol/base_storage_opt.v` + `storage_protocol/protocol.v`
  (1382 lines).  These are the prerequisite for `typing/protocol.v`; port
  them if and when `protocol.v` is taken on.
* `lib/rwlock.v` (518 lines), which is a client of the storage protocol.

So: pull in `storage_protocol/` **when** starting `protocol.v`, not before.
Porting it earlier buys nothing and has to be kept compiling meanwhile.

## The model: what is left

The typing layer is parametric in a formula language `FML` and an
interpretation; `nola/alerus/typing/model.v` builds the concrete one, with
`FML := cifOF CON` and `bor_sem := ⟦⟧ᶜ(der)`.  Until it is finished,
`typeG FML Σ` has no instance and the development is sound-but-vacuous.

Done in `model.v`:

* `alerusCT` - every token of the development as a `cif` leaf.
* the three judgments `guardJT`, `idxborJT`, `inclJT`, their constructors
  `cif_guard`, `cif_idxbor`, `cif_incl`, and the `typingC/J/CS/JS`
  constraint classes.
* `AlerusSem_at δ`, `alerus_WGuard_at δ` - the interpretation and its
  guarding world satisfaction at any derivability candidate.
* `StBor` / `StBorSem_at δ` - the storable inclusion and alteration.
* `TypeFml`, `GsrcSem`, `HeapSem`.
* the leaf equations at an arbitrary candidate, and the three judgment
  unfoldings (`alt_into_cif_here`, `cif_idxbor_sem`, `cif_incl_sem`).

Remaining, in order:

1. **`AltSem`** - the rest of the fields.  Each is one of
   * an equation at a candidate (rewrite with the candidate's `δ`);
   * `Deriv_factor'` / `der_sound` / `dinto` on one of the three judgments;
   * a lifetime-logic fact replayed at `AlerusSem_at δ` with
     `StBorSem_at δ`.

   The ones with real content are `guard_fml_sem_2`, `idxbor_fml_of_bor`,
   `idxbor_fml_guard_at`, `st_incl_eternalize`, `guard_fml_borrow_shared`
   and `guard_fml_of_bor`.
2. **`PcellFml` / `AtomicInvFml` / `LocalInvFml` / `RaFml`**, then `typeG`.
3. **World-satisfaction allocation** and `typing/soundness.v`, including the
   `llft_wsat_alloc` reordering described in `typing/README.md`.

## Separate pieces of work

* **`typing/fixpoint.v`**: it builds a recursive type as a COFE limit
  (`compl` of a chain).  A `cif` is complete as a **`prost`**
  (`nola/util/cit.v`'s `cit_prolimit`), not as an OFE, so this has to move
  to `profix`/`Productive`, the way `nola/examples/rust_halt/rec.v` defines
  `ty_rec F := profix F`.  Until then the file carries a local
  `Cofe (FML $oi Σ)` assumption, which the model cannot discharge.
* **`fn` must be stratified by an execution level** (thesis (5.4),
  § 3.4.1).  `FnFml`'s `fn_fml_sem_2` is the one rule with no model and must
  *not* be discharged as it stands.  `FML`, `bor_sem` and `alerus_wsat`
  become level-indexed up to a fixed maximum `L`, and a `type` carries the
  level of its ghost assertion.
* **`typing/spawn.v`**: `join` is a spin loop proved by `iLöb`.  There is no
  later-free, total-correctness version of it; it stays out.
* **`typing/protocol.v`**: ~1200 lines plus the 1382 of `storage_protocol/`.

## Rules of thumb this port has had to learn

They are written out in `nola/alerus/typing/README.md`; in one line each:

* A judgment can be **eliminated** at a candidate the ambient interpretation
  maps into (`dinto der δ'`, from `Deriv_factor'`), and **introduced** at
  every candidate from interpretation-free ghost state - but never *moved*
  from one interpretation to another.
* Anything that has to be *used* at a candidate (lifetime inclusion, a
  borrow's semantic alteration) must be the family of the things themselves,
  not the family of stored judgments: `fguardx`, `st_incl`, `st_iff`.
* A thing whose semantics does not mention the candidate at all can have a
  `⊣⊢` at *every* candidate, and so can be a formula: that is `cif_idxbor`
  and `cif_incl`.
* Definitions that unfold to `□ ∀ sem, …` must be sealed and
  `Typeclasses Opaque`, or typeclass search goes under the binder a hundred
  times per file and build times go from seconds to minutes.
