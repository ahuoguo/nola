(** * Non-atomic ("thread-local") invariants, later-free

  Ported from VerusBelt's [guarding/internal/na_invariants_fork.v] (itself a
  fork of Iris's [base_logic/lib/na_invariants.v]), MIT.

  The token machinery ([na_own] and friends) is reused verbatim from Iris.
  What changes is the invariant itself: the original wraps the content in an
  Iris invariant, so opening it yields [▷ P].  Here the content is a syntactic
  formula held by a *simple* invariant ([nola.iris.sinv]) whose world
  satisfaction is threaded explicitly, so opening yields [sm Px] with no later
  and no fancy update -- [na_inv_tok_acc] is a plain entailment. *)

From nola.bi Require Export modw.
From nola.iris Require Export sinv.
From iris.base_logic.lib Require Export na_invariants.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import gset coPset.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
Import iPropAppNotation ModwNotation.

Section na_inv.
  Context `{!sinvGS FML Σ, !na_invG Σ}.
  Local Existing Instance na_inv_inG.
  Implicit Type (p : na_inv_pool_name) (i : positive) (Px : FML $oi Σ).

  (** Access lock of a non-atomic invariant *)
  Local Definition na_lock p i : iProp Σ := own p (ε, GSet {[i]}).

  (** Allocate a lock with an index fresh for both [N] and a given set *)
  Local Lemma na_lock_alloc p N (I : gset positive) :
    ⊢ |==> ∃ i, ⌜i ∈ (↑N:coPset) ∧ i ∉ I⌝ ∧ na_lock p i.
  Proof.
    iMod (own_unit (prodUR coPset_disjUR (gset_disjUR positive)) p) as "ε".
    iMod (own_updateP with "ε") as ([m1 m2]) "[%cond l]".
    { apply prod_updateP'.
      - apply cmra_updateP_id, (reflexivity (R:=eq)).
      - apply (gset_disj_alloc_empty_updateP_strong'
          (λ i, i ∈ (↑N:coPset) ∧ i ∉ I))=> E.
        destruct (fresh_inv_name (E ∪ I) N) as [i [??]].
        exists i. set_solver. }
    move: cond=>/=[<-[i[->?]]]. iModIntro. iExists i. by iSplit.
  Qed.

  (** Access [na_own] *)
  Lemma na_own_subset {p E F} : F ⊆ E →
    na_own p E ⊣⊢ na_own p F ∗ na_own p (E∖F).
  Proof.
    move=> ?. rewrite {1}(union_difference_L F E); [|done].
    by rewrite na_own_union; [|set_solver].
  Qed.
  Lemma na_own_in {p i E} : i ∈ E →
    na_own p E ⊣⊢ na_own p {[i]} ∗ na_own p (E∖{[i]}).
  Proof. move=> ?. apply na_own_subset. set_solver. Qed.

  (** [na_lock] is exclusive *)
  Local Lemma na_lock_2_no {p i} : na_lock p i -∗ na_lock p i -∗ False.
  Proof.
    iIntros "l l'". iCombine "l l'" gives %[_ Hval%gset_disj_valid_op].
    set_solver.
  Qed.

  (** What is kept in the simple invariant: either the content together with
    the lock, or the thread-local token saying the invariant is closed. *)
  Definition na_body p (sm : FML $oi Σ → iProp Σ) i Px : iProp Σ :=
    sm Px ∗ na_lock p i ∨ na_own p {[i]}.

  (** World satisfaction for non-atomic invariants *)
  Definition na_inv_wsat p sm : iProp Σ := sinv_wsat (na_body p sm).

  (** Token for a non-atomic invariant *)
  Definition na_inv_tok p N Px : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ sinv_tok i Px.

  #[export] Instance na_inv_tok_persistent {p N Px} :
    Persistent (na_inv_tok p N Px).
  Proof. exact _. Qed.
  #[export] Instance na_inv_tok_ne {p N} : NonExpansive (na_inv_tok p N).
  Proof. solve_proper. Qed.

  (** Allocate a non-atomic invariant *)
  Lemma na_inv_tok_alloc {p sm} Px N :
    sm Px -∗ |=[na_inv_wsat p sm]=> na_inv_tok p N Px.
  Proof.
    rewrite /modw /na_inv_wsat. iIntros "Px W".
    iDestruct (sinv_tok_alloc_suspend (sm := na_body p sm) Px with "W")
      as (I) "→".
    iMod (na_lock_alloc p N I) as (i [??]) "lock".
    iMod ("→" $! i with "[//]") as "[#tok →W]".
    iModIntro. iSplitL.
    - iApply "→W". rewrite /na_body. iLeft. iFrame.
    - iExists i. by iSplit.
  Qed.

  (** Access a non-atomic invariant.  The original needed
    [={E}=∗ ▷ P ∗ … ∗ (▷ P ∗ … ={E}=∗ …)]; here there is neither later nor
    update, only the world satisfaction being passed in and out. *)
  Lemma na_inv_tok_acc {p sm N F Px} : ↑N ⊆ F →
    na_inv_tok p N Px -∗ na_own p F -∗ na_inv_wsat p sm -∗
      sm Px ∗ na_own p (F ∖ ↑N) ∗ na_inv_wsat p sm ∗
      (sm Px -∗ na_own p (F ∖ ↑N) -∗ na_inv_wsat p sm -∗
         na_own p F ∗ na_inv_wsat p sm).
  Proof.
    move=> NF. iIntros "[%i[%iN #tok]] F W". rewrite /na_inv_wsat.
    rewrite (na_own_subset NF) (na_own_in iN).
    iDestruct "F" as "[[i rest] $]".
    iDestruct (sinv_tok_acc with "tok W") as "[body →W]".
    rewrite {1}/na_body. iDestruct "body" as "[[$ lock]|i']"; last first.
    { iDestruct (na_own_disjoint with "i i'") as %?. set_solver. }
    iDestruct ("→W" with "[i]") as "$". { rewrite /na_body. iRight. iFrame. }
    iIntros "Px rest' W".
    iDestruct (sinv_tok_acc with "tok W") as "[body →W]".
    rewrite {1}/na_body. iDestruct "body" as "[[_ lock']|i]".
    { iDestruct (na_lock_2_no with "lock lock'") as "[]". }
    iDestruct ("→W" with "[Px lock]") as "$".
    { rewrite /na_body. iLeft. iFrame. }
    iFrame.
  Qed.
End na_inv.
