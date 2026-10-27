(** * Invariant contexts

  Ported from VerusBelt ([typing/inv_context.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).  Mechanical: [↑NllftG] becomes [Wguard], Leaf's
  [guards_refl]/[guards_transitive] become nola's [guard_refl]/[guard_trans],
  and the cancellable non-atomic invariant API keeps its [cna_] names. *)

From iris.proofmode Require Import proofmode.
From nola.verus_halt.util Require Import basic cancellable_na_invariants
  atomic_lock_counter.
From nola.verus_halt.typing Require Export base ctx lifetime lft_contexts
  uniq_cmra.
From nola.verus_halt.prophecy Require Import syn_type.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Inductive invctx_elt : Type :=
  | InvCtx_open (κ: lft).

Inductive invctx_atomic_state : Type :=
  | AtomicOpen (n: nat)
  | AtomicClosed.

Inductive invctx : Type :=
  | InvCtx (l: list invctx_elt) (ϝ: lft) (𝛼: invctx_atomic_state) : invctx.

Local Definition thread_id := gname.

Section inv_contexts.
  Context `{!verus_haltGS FML Σ, !VerusHaltSem FML Σ, !HeapSem FML Σ, !GsrcSem FML Σ, !TypeFml FML Σ,
    StBor0 : !StBor FML Σ, StBorSem0 : !StBorSem, !AltSem FML Σ}.
  Implicit Type (κ: lft).

  Definition ATOMIC_POOL : na_inv_pool_name := atomic_threadpool.

  Definition invctx_elt_unwrap (elt: invctx_elt) : lft :=
      match elt with InvCtx_open κ => κ end.

  Definition invctx_to_multiset (ictx: list invctx_elt) : gmultiset lft :=
    list_to_set_disj (fmap invctx_elt_unwrap ictx).

  Definition atomic_ctx (mask: Mask) (𝛼: invctx_atomic_state) : iProp Σ :=
      match 𝛼 with
          | AtomicClosed => ⌜mask = ⊤⌝
          | AtomicOpen n =>
              atomic_lock_ctr atomic_lock_ctr_name n mask ∗
                na_own ATOMIC_POOL mask
      end.

  Definition invctx_interp (tid: thread_id) (mask: Mask) (iκs: list lft)
      (ictx: invctx) : iProp Σ :=
      match ictx with
        InvCtx ictx_elts ϝ 𝛼 =>
          ∃ (na_mask at_mask : coPset),
              ⌜na_mask ∪ at_mask = ⊤ ∧ na_mask ∩ at_mask = mask⌝
                ∗ (cna_lifetimes tid
                    (invctx_to_multiset ictx_elts ⊎ (list_to_set_disj iκs))
                    ∗ ϝ ⊑ lft_intersect_list iκs)
                ∗ cna_own tid na_mask
                ∗ atomic_ctx at_mask 𝛼
      end.

  Definition invctx_equiv (I1 I2: invctx) :=
      match I1, I2 with
        InvCtx l1 ϝ1 astate1, InvCtx l2 ϝ2 astate2 =>
          l1 ≡ₚ l2 ∧ ϝ1 = ϝ2 ∧ astate1 = astate2
      end.

  Global Instance invctx_interp_permut tid mask iκs :
    Proper ((invctx_equiv) ==> (⊣⊢)) (invctx_interp tid mask iκs).
  Proof.
    intros [l1 ϝ1 astate1] [l2 ϝ2 astate2] [Eq1 [-> ->]]. unfold invctx_interp.
    do 7 f_equiv. unfold invctx_to_multiset, invctx_elt_unwrap.
    setoid_rewrite Eq1. done.
  Qed.

  Definition lctx_ictx_alive (E: elctx) (L: llctx) (I: invctx) : Prop :=
      match I with
        InvCtx ictx_elts ϝ astate =>
          lctx_lft_alive E L ϝ ∧
          ∀ κ : lft, κ ∈ (fmap invctx_elt_unwrap ictx_elts) →
            lctx_lft_alive E L κ
      end.

  Lemma lctx_ictx_alive_nil (E: elctx) (L: llctx) ϝ 𝛼 :
      lctx_lft_alive E L ϝ → lctx_ictx_alive E L (InvCtx [] ϝ 𝛼).
  Proof.
    unfold lctx_ictx_alive. intros. split; trivial. intros. set_solver.
  Qed.

  Lemma lctx_ictx_alive_cons (E: elctx) (L: llctx) (I: list invctx_elt) ϝ 𝛼
      (κ: lft) :
      lctx_ictx_alive E L (InvCtx I ϝ 𝛼)
        → lctx_lft_alive E L κ
        → lctx_ictx_alive E L (InvCtx (InvCtx_open κ :: I) ϝ 𝛼).
  Proof.
      unfold lctx_ictx_alive. intros [Hϝ Hl] H1. split; trivial. intros κ0 Ha.
      simpl in Ha. rewrite elem_of_cons in Ha. destruct Ha as [->|?]; auto.
  Qed.

  Lemma lctx_ictx_alive_L_guards_ϝ E L Il ϝ 𝛼 :
      lctx_ictx_alive E L (InvCtx Il ϝ 𝛼) →
      llctx_interp L -∗ elctx_interp E -∗
        (llctx_interp L &&{Wguard}&&> @[ϝ]).
  Proof.
      intros [Alvϝ _]. iIntros "L E". iApply (Alvϝ with "L E").
  Qed.

  Lemma lctx_ictx_alive_L_guards_list E L Il ϝ 𝛼 :
      lctx_ictx_alive E L (InvCtx Il ϝ 𝛼) →
      llctx_interp L -∗ elctx_interp E -∗
        (llctx_interp L &&{Wguard}&&>
          @[lft_intersect_list (fmap invctx_elt_unwrap Il)]).
  Proof.
      intros [_ AlvList]. rewrite <- Forall_forall in AlvList.
      have AlvAll := (lctx_lft_alive_tok_list _ _ _ AlvList).
      iIntros "L E". iApply (AlvAll with "L E").
  Qed.

  Lemma lctx_ictx_alive_all_guards E L Il ϝ 𝛼 iκs :
    lctx_ictx_alive E L (InvCtx Il ϝ 𝛼) →
    llctx_interp L -∗ elctx_interp E -∗
    (ϝ ⊑ lft_intersect_list iκs) -∗
    ∀ κ : lft,
      ⌜κ ∈ invctx_to_multiset Il ⊎ list_to_set_disj iκs⌝ -∗
        llctx_interp L &&{Wguard}&&> @[κ].
  Proof.
    iIntros (Alv) "L E #Incl". iIntros (κ) "%Hin".
    rewrite gmultiset_elem_of_disj_union in Hin.
    destruct Alv as [Alv1 Alv2]. destruct Hin as [Hin|Hin].
     - unfold invctx_to_multiset in Hin. rewrite elem_of_list_to_set_disj in Hin.
       iApply (Alv2 κ Hin with "L E").
     - iDestruct (Alv1 with "L E") as "#G1".
       iDestruct (fguard_here with "Incl") as "#Inclh".
       iApply (guard_trans with "G1 []"). iApply (guard_trans with "Inclh []").
       iApply fguard_here. iApply lft_intersect_list_elem_of_incl.
       by rewrite elem_of_list_to_set_disj in Hin.
  Qed.

  Lemma invctx_alloc mask :
    ⊢ |==> ∃ tid, invctx_interp tid mask [] (InvCtx [] static AtomicClosed).
  Proof.
      iIntros. iMod cna_pool_alloc as (tid) "[na_own multi]".
      iModIntro. iExists tid. iExists mask, ⊤.
      iSplit; first by (iPureIntro; set_solver).
      unfold invctx_to_multiset. simpl.
      rewrite gmultiset_disj_union_right_id. iFrame.
      iSplit. { iApply fguard_refl. }
      iSplit; last by done.
      replace (⊤) with (mask ∪ (⊤ ∖ mask)).
       - rewrite cna_own_union. { iDestruct "na_own" as "[$ _]". } set_solver.
       - apply set_eq. intros x. destruct (decide (x ∈ mask)); set_solver.
  Qed.
End inv_contexts.
