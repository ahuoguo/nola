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
     `fn_fml_sem` would split into an elimination at `der` and an
     introduction that must hold **uniformly in `δ'`** - which is exactly why
     every law of Nola's own `Ty` class is stated `∀ δ`
     (`nola/examples/rust_halt/type.v:128-145`).  Making this development
     `δ`-parametric is the price.
   * **Replace the lifetime logic with Nola's** (`nola/iris/borrow.v`,
     `nola/iris/lft.v`), so that inclusion and shared borrows are tokens and
     the guard disappears from the formulas.  That is a different
     development - it is what `rust_halt` is - and it gives up the Leaf
     shape the port deliberately follows.

   Either way, `fn_fml` needs derivability regardless: a function type's
   ghost assertion is its own typing judgment, and `rust_halt` has no
   function type, so there is no worked precedent for it in Nola.

## The route being taken

Nola's `deriv` ([`nola/bi/deriv.v`](../../bi/deriv.v)), as used by
`nola/iris/inv_deriv.v`.  The pieces, in order; each is meant to leave the
build green.

1. **Tokenise what can be tokenised.**  *Done.*  The two closers are now
   `cna_otok` / `na_otok`, after Nola's `obor_tok`.
2. **The `AltSem` interface.**  *Done.*  `ctx.v` now carries `AltSem`:
   `alt_sem sem` says `sem` is a derivability candidate, `alt_WGuard sem` is
   the guarding world satisfaction at it, `alt_into sem` is Nola's
   `dinto bor_sem sem`, and the `_at` fields repeat the equations of the
   non-judgment constructors at an arbitrary candidate.  On top of it:
   `dguard Px Qx` (a guard held as a formula) with `dguard_sem` for
   elimination, `dguard_of_all` (`Deriv_factor'`) for introduction, and the
   combinators — `dguard_trans`, `dguard_{lhs,rhs}_iff`,
   `dguard_{lhs,rhs}_sep_{l,r}`, `dguard_and`, `dguard_intro`,
   `dguard_borrow_shared` — each of which is `Deriv_map` in the model; plus
   `dincl` and `dbasically_dead`.

   `TypeFml.guard_fml_sem` is **still there**, marked as having no model, so
   that the files that have not been migrated still build.  Everything that
   rests on it is exactly what steps 3–5 remove.
3. **`ty_gho_depth_mono` at a candidate.**  A guard's right-hand side is a
   type's ghost assertion, and the one thing the development does to it
   while rebuilding a guard is weaken its depth.  So the `type` record needs
   `ty_gho_depth_mono_at : ∀ sem, alt_sem sem → …`, proved for each type
   former (~30 of them); the ambient law then follows by `alt_here`.  This is
   the same shape as Nola's `Ty` class, whose laws are all `∀ δ`
   (`nola/examples/rust_halt/type.v:128-145`).
4. **Migrate the stored guards.**  `shr_bor`, `uniq_bor`, `uniq_util`'s
   `basically_dead`, and `borrow.v`'s mid-formulas state their unfolding
   lemmas with `dguard` instead of a raw guard; the ~20 files downstream use
   `dguard_*` where they currently use `guard_*` on a guard that is about to
   be stored, and `dguard_sem` where they actually open one.  Then
   `guard_fml_sem` goes.
5. **The same for `idxbor_fml` and `fn_fml`.**  `idx_bor` carries
   `□ (bor_sem Px' ↔ bor_sem Px)`, which is a judgment in the same sense -
   compare `nola/iris/borrow_deriv.v`.  `fn_fml` is the function type's own
   typing judgment; its introduction rule takes the body's typing at every
   candidate, which is how `soundness.v` already states its premise
   (`∀ `{!typeG Σ}, typed_val main main_type c`).
6. **The model.**  A `cif` with the remaining ~25 leaf constructors, a `JUDG`
   with the three judgments, `bor_sem := ⟦⟧ᶜ(der)`, the `AltSem` instance
   with `alt_sem := Deriv ih`, and the world-satisfaction allocation (plus
   the `llft_wsat_alloc` reordering above).  Then `soundness.v`.
