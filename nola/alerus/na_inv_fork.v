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

(** The ghost state.

  The simple-invariant family is given by a *name* beside the pre-ghost
  state rather than by an ambient [sinvGS]: the lifetime logic's box uses an
  [sinvGS] of its own, and two [sinv_wsat]s over the same family would each
  claim the authoritative map.  Making this a class of its own keeps the
  client's notation unchanged and the two families apart. *)
Class naInvGS (FML : oFunctor) Σ : Type := NaInvGS {
  #[global] na_inv_sinvG :: sinvGpreS FML Σ;
  #[global] na_inv_invG :: na_invG Σ;
  na_inv_name : gname;
}.

Section na_inv.
  Context `{!naInvGS FML Σ}.
  #[local] Instance naSinvGS : sinvGS FML Σ :=
    SinvGS FML Σ na_inv_sinvG na_inv_name.
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

  (** Non-expansiveness of the body, for allocating the world satisfaction *)
  Lemma na_body_ne {p sm} :
    internal_ne (PROP:=iProp Σ) sm -∗ ∀ i, internal_ne (na_body p sm i).
  Proof.
    iIntros "#Ne" (i). rewrite /internal_ne /na_body. iIntros (Px Qx) "eq".
    iDestruct ("Ne" $! Px Qx with "eq") as "eq'". by iRewrite "eq'".
  Qed.

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

  (** Token for an *open* non-atomic invariant.

    Nola represents an opened borrow by a token made of plain ghost ownership
    ([nola.iris.borrow]'s [obor_tok]) rather than by a closing wand, so that
    it can be stored in a formula.  This does the same for an opened
    invariant: it holds exactly what the closer of [na_inv_tok_acc] used to
    capture - the simple invariant, its lock, and the part of the pool
    outside the invariant's own index. *)
  Definition na_otok p N Px : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ sinv_tok i Px ∗ na_lock p i ∗
      na_own p ((↑N:coPset) ∖ {[i]}).

  #[export] Instance na_otok_ne {p N} : NonExpansive (na_otok p N).
  Proof. solve_proper. Qed.
  #[export] Instance na_otok_proper {p N} : Proper ((≡) ==> (⊣⊢)) (na_otok p N).
  Proof. apply ne_proper, _. Qed.

  (** Open a non-atomic invariant.  The original needed
    [={E}=∗ ▷ P ∗ … ∗ (▷ P ∗ … ={E}=∗ …)]; here there is neither later nor
    update, only the world satisfaction being passed in and out - and the
    closer is a token rather than a wand. *)
  Lemma na_inv_tok_open {p sm N F Px} : ↑N ⊆ F →
    na_inv_tok p N Px -∗ na_own p F -∗ na_inv_wsat p sm -∗
      sm Px ∗ na_own p (F ∖ ↑N) ∗ na_otok p N Px ∗ na_inv_wsat p sm.
  Proof.
    move=> NF. iIntros "[%i[%iN #tok]] F W". rewrite /na_inv_wsat.
    rewrite (na_own_subset NF) (na_own_in iN).
    iDestruct "F" as "[[i rest] $]".
    iDestruct (sinv_tok_acc with "tok W") as "[body →W]".
    rewrite {1}/na_body. iDestruct "body" as "[[$ lock]|i']"; last first.
    { iDestruct (na_own_disjoint with "i i'") as %?. set_solver. }
    iDestruct ("→W" with "[i]") as "$". { rewrite /na_body. iRight. iFrame. }
    iExists i. iSplit; [done|]. iFrame "tok lock rest".
  Qed.

  (** Close a non-atomic invariant with its open token *)
  Lemma na_inv_tok_close {p sm N F Px} :
    na_otok p N Px -∗ sm Px -∗ na_own p F -∗ na_inv_wsat p sm -∗
      ⌜F ## ↑N⌝ ∗ na_own p (F ∪ ↑N) ∗ na_inv_wsat p sm.
  Proof.
    iIntros "[%i[%iN (#tok & lock & rest)]] Px F W". rewrite /na_inv_wsat.
    iDestruct (sinv_tok_acc with "tok W") as "[body →W]".
    rewrite {1}/na_body. iDestruct "body" as "[[_ lock']|i]".
    { iDestruct (na_lock_2_no with "lock lock'") as "[]". }
    iDestruct ("→W" with "[Px lock]") as "$".
    { rewrite /na_body. iLeft. iFrame. }
    iAssert (na_own p (↑N:coPset)) with "[i rest]" as "N".
    { rewrite (na_own_in (p:=p) (E:=(↑N:coPset)) iN). iFrame. }
    iDestruct (na_own_disjoint with "F N") as %?. iSplit; [done|].
    rewrite na_own_union; [|done]. iFrame.
  Qed.

  (** The wand form, as before, derived from the two *)
  Lemma na_inv_tok_acc {p sm N F Px} : ↑N ⊆ F →
    na_inv_tok p N Px -∗ na_own p F -∗ na_inv_wsat p sm -∗
      sm Px ∗ na_own p (F ∖ ↑N) ∗ na_inv_wsat p sm ∗
      (sm Px -∗ na_own p (F ∖ ↑N) -∗ na_inv_wsat p sm -∗
         na_own p F ∗ na_inv_wsat p sm).
  Proof.
    move=> NF. iIntros "inv F W".
    iDestruct (na_inv_tok_open NF with "inv F W") as "($ & $ & o & $)".
    iIntros "Px rest W".
    iDestruct (na_inv_tok_close with "o Px rest W") as "(_ & F & $)".
    have ->: ((F ∖ ↑N) ∪ ↑N) = F.
    { rewrite difference_union_L union_comm_L.
      by apply subseteq_union_1_L. }
    iFrame "F".
  Qed.
End na_inv.

(** The same with the ghost state given, so that the record is a
  constructor application and its fields reduce.  A client that has to
  compare the [na_invG] it allocated with the one it started from - the
  program logic's [lrustGS_gen] does - needs that. *)
Lemma na_inv_wsat_alloc_name `{!sinvGS FML Σ, na_invG0 : !na_invG Σ} :
  ⊢ |==> ∃ γ : gname, ∀ p sm, internal_ne (PROP:=iProp Σ) sm -∗
    @na_inv_wsat FML Σ (NaInvGS FML Σ sinvGS_pre na_invG0 γ) p sm.
Proof.
  iMod (sinv_wsat_alloc_name (FML:=FML)) as (γ) "W". iModIntro.
  iExists γ. iIntros (p sm) "Ne". rewrite /na_inv_wsat /naSinvGS.
  iApply "W". by iApply na_body_ne.
Qed.

(** Allocate the world satisfaction for non-atomic invariants *)
Lemma na_inv_wsat_alloc `{!sinvGpreS FML Σ, !na_invG Σ} :
  ⊢ |==> ∃ _ : naInvGS FML Σ, ∀ p sm,
    internal_ne (PROP:=iProp Σ) sm -∗ na_inv_wsat p sm.
Proof.
  iMod (sinv_wsat_alloc (FML:=FML)) as ([pre γ]) "W". iModIntro.
  iExists (NaInvGS FML Σ pre _ γ). iIntros (p sm) "Ne".
  rewrite /na_inv_wsat /naSinvGS. iApply "W". by iApply na_body_ne.
Qed.
