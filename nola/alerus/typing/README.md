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
   `vo`, `idxbor`, `ra`, `obs`, `handle`, the `cna_*` and `na_inv_*` family,
   … - together with their `Ecsem`.  That is long but mechanical, with one
   exception:

   `LocalInvFml.cna_closer_fml` (`local_inv.v:38`) and
   `AtomicInvFml.atomic_closer_fml` (`atomic_inv.v`) are formulas whose
   semantics is

   ```coq
   cna_closer alerus_wsat κ p N bor_sem Px
   ```

   i.e. a magic wand over `alerus_wsat`, which itself contains
   `cna_wsat alerus_WGuard bor_sem`.  Defining `bor_sem` therefore needs
   `bor_sem` applied to *arbitrary* formulas, not to subformulas, so it is
   not a structural recursion; and the occurrence sits on both sides of `-∗`
   with no `▷`, so it is not contractive either.  Storing a closer over the
   world satisfaction *inside* the world satisfaction is exactly the
   self-reference the later-free discipline rules out.

   Two ways out, neither of them local:

   * Hand back the closer's *resources* instead of the wand.  Concretely
     `cna_inv_acc` builds its closer out of `cna_inv γ p N Px`, a `cna_own`
     fragment and the half of the lifetime token that records `κ`
     (`util/cancellable_na_invariants.v:356`ff.).  Exposing those as a
     `cna_closer_res` predicate, with `cna_close` restated over it, makes the
     closer a composite of leaf constructors.  This touches
     `cancellable_na_invariants.v`, `na_inv_fork.v`, `local_inv.v` and
     `atomic_inv.v`.
   * Express the closer as a *judgment* and use Nola's derivability machinery
     (`nola/bi/deriv.v`, as `nola/iris/inv_deriv.v` does), so the semantics is
     parameterised by `δ` and the knot is tied by `der`.  This keeps the
     interfaces as they are but pulls the whole `Dsem`/`Csem`/`Jsem` layer
     into the development.
