(** * Guarded heap access in a total weakest precondition

  The payoff of the later-free guard ([nola.bi.guard]): VerusBelt's
  [Heap-Read-Guarded] rule

    (G ↣ (ℓ ↦ v)) ⊢ {G} x := *ℓ {(x = v) ∗ G}

  holds for Nola's *total* weakest precondition, with no later credits and no
  [▷].  In Leaf and VerusBelt the same rule can only be had for a partial
  weakest precondition, because opening the guard hands back [▷ (ℓ ↦ v)] and a
  later has to be stripped by a program step.

  Here the points-to lives in the world satisfaction [W] that [twpw] threads
  through every step, so the guard is opened and closed within the step
  itself. *)

From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From nola.bi Require Export guard.
From nola.lrust Require Export lifting.
From nola.lrust Require Import tactics.
From iris.proofmode Require Import proofmode.
Import WpwNotation GuardNotation.

(** [nola.lrust.lifting] keeps these hints local, so we repeat them *)
Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (base_reducible_no_obs _ _) => eexists _, _, _; simpl
  : core.
Local Hint Constructors base_step : core.
Local Hint Resolve to_of_val : core.

Section guard_lifting.
  Context `{!lrustGS_gen hlc Σ}.
  Implicit Type (W G : iProp Σ) (l : loc) (q : Qp).

  (** Read a location guarded by [G], under a total weakest precondition *)
  Lemma twp_read_sc_guard {W G s E l q v} :
    (G &&{W}&&> l ↦{q} v) -∗
    [[{ G }]][W] Read ScOrd (Lit $ LitLoc l) @ s; E [[{ RET v; G }]].
  Proof.
    iIntros "#g" (Φ) "!> G →Φ".
    iApply twp_lift_atomic_base_step_no_fork; [done|].
    iIntros (????) "[W σ]".
    iDestruct (guard_acc with "g G W") as "[↦ toW]".
    iDestruct (heap_read with "σ ↦") as %[??].
    iModIntro. iSplit; [by eauto|]. iIntros (?????) "!>". inv_base_step.
    iDestruct ("toW" with "↦") as "[$ G]". do 2 (iSplit=> //). iFrame "σ".
    by iApply "→Φ".
  Qed.

  (** Write to a location whose points-to is guarded by [G]

    The guarded proposition must not pin the stored value, since the guard has
    to be closed with the *same* proposition it was opened with.  Pinning the
    value as well needs the points-to cell logic, where the guard sits on the
    immutable location-to-cell link. *)
  Lemma twp_write_sc_guard {W G s E l e v} :
    IntoVal e v → (G &&{W}&&> ∃ w, l ↦ w) -∗
    [[{ G }]][W] Write ScOrd (Lit $ LitLoc l) e @ s; E
    [[{ RET LitV LitPoison; G }]].
  Proof.
    iIntros (<-). iIntros "#g" (Φ) "!> G →Φ".
    iApply twp_lift_atomic_base_step_no_fork; [done|].
    iIntros (????) "[W σ]".
    iDestruct (guard_acc with "g G W") as "[[%w ↦] toW]".
    iDestruct (heap_read_1 with "σ ↦") as %?.
    iMod (heap_write _ _ _ v with "σ ↦") as "[σ ↦]".
    iModIntro. iSplit; [by eauto|]. iIntros (?????) "!>". inv_base_step.
    iDestruct ("toW" with "[↦]") as "[$ G]"; [by iExists _|].
    do 2 (iSplit=> //). iFrame "σ". by iApply "→Φ".
  Qed.
End guard_lifting.
