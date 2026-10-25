(** * Ported from VerusBelt ([lifetime/lifetime_internals/augment_outlives.v], MIT,
  Hance, Elbeheiry, Matsushita, Dreyer), with the laters removed; see
  [nola.alerus.lifetime.inv] for the design. *)

From nola.alerus Require Import boxes.
From nola.alerus.lifetime Require Import ra.
From nola.alerus.lifetime Require Import inv.

Require Import stdpp.base.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From nola.iris Require Export iprop sinv.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import proofmode.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants.
Import GuardNotation ModwNotation iPropAppNotation.

Section FullBorrows.
  Context {Σ: gFunctors} {FML : oFunctor}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS_gen hlc Σ}.
  Context `{!boxG Σ, !sinvGS FML Σ, !BorSem FML Σ}.
  
  (** The lifetime tokens' ghost name, and - separately - the borrow
    bookkeeping's.  See the head of [nola/alerus/lifetime/inv.v]. *)
  Context (γlt: gname).
  Context (γ: gname).
  Context (γo: gname).
  Context (γd: gname).
  
  Implicit Types (mprops: gmap_props FML Σ).

 
  Lemma outlives_consistent_mono dead outlives outlives' :
    outlives ⊆ outlives' →
    outlives_consistent dead outlives' →
    outlives_consistent dead outlives.
  Proof.
    unfold outlives_consistent. intros Hsub Hoc.
    intros o. have Ho := Hoc o. set_solver.
  Qed.
  
  Lemma future_vs_augment_outlives alive dead outlives outlives' mbs mprops :
    outlives ⊆ outlives' →
    future_vs γlt γ alive dead outlives mbs mprops ⊢
    future_vs γlt γ alive dead outlives' mbs mprops.
  Proof using γlt invGS_gen0 Σ γ γd γo.
    intros Hc.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead) "Hvs".
    rewrite future_vs_def.
    rewrite (future_vs_def γlt γ my_alive).
    
    iIntros (k) "%Hin_my_alive Dead". iSplit.
      { iIntros "NotSwell". iDestruct ("Hvs" $! k with "[] Dead") as "[Hvs _]".
        { iPureIntro. destruct Hin_my_alive. split; trivial.
          apply (outlives_consistent_mono _ _ outlives'); trivial.
        }
        iApply IH. { intuition. }
        iFrame "#". iApply "Hvs". iFrame.
      }
    iIntros "inval".
    iDestruct ("Hvs" $! k with "[] Dead") as "[_ Hvs]".
        { iPureIntro. destruct Hin_my_alive. split; trivial.
          apply (outlives_consistent_mono _ _ outlives'); trivial.
        }
    iMod ("Hvs" with "[inval]") as "[reval Hvs]".
    { iFrame. }
    iModIntro. iFrame "reval".
    iApply IH; trivial. intuition.
  Qed.
  
  Lemma map_wf_augment_outlives alive dead blocked outlives outlives' mbs :
    (∀ o , o ∈ outlives' → o.1 ⊆ alive ∪ dead ∧ o.2 ∈ alive ∪ dead) →
    outlives ⊆ outlives' →
    inv.map_wf alive dead blocked outlives mbs →
    inv.map_wf alive dead blocked outlives' mbs.
  Proof.
    unfold inv.map_wf.
    intros Ho Hsub [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]]. 
    split; trivial.
    split; trivial.
    split; trivial.
    split. {
      intros sn bs Hmbssn. have Hf := Hf1 sn bs Hmbssn. destruct bs; trivial. set_solver.
    }
    split; trivial.
  Qed.

  Lemma inner_augment_outlives alive dead blocked outlives outlives' :
    (∀ o , o ∈ outlives' → o.1 ⊆ alive ∪ dead ∧ o.2 ∈ alive ∪ dead) →
    (outlives ⊆ outlives') →
    (outlives_consistent dead outlives') →
      (inner_inv γlt γ γo alive dead blocked) ∗ Outlives γo outlives
    ==∗ (inner_inv γlt γ γo alive dead blocked) ∗ Outlives γo outlives'.
  Proof using γlt invGS_gen0 Σ γ γd γo.
    intros Ho Hsub Hc.
    iIntros "[Inv Outlives]".
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives2) "[auth [Modulo [#DeadsLt [box [vs [%pures [#slices outlives]]]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives2.
    
    iMod (outlives_update γo outlives outlives outlives' with "[outlives Outlives]") as "[outlives Outlives]". { iFrame. }
    
    iModIntro. iSplitR "Outlives"; last by iFrame "Outlives".
    iExists mbs. iExists mprops. iExists Ptotal. iExists outlives'.
    iFrame "auth". iFrame "box". iFrame "outlives". iFrame "Modulo".
    iFrame "DeadsLt".
    iDestruct (future_vs_augment_outlives alive dead outlives outlives' mbs mprops with "vs") as "vs"; trivial.
    iFrame "vs".
    iSplitL. {
      destruct pures as [Hdom [Hwf Hoc]].
      iPureIntro. split; trivial. split; trivial.
      apply (map_wf_augment_outlives alive dead blocked outlives outlives'); trivial.
    }
    iFrame "slices".
  Qed.
  
  Lemma outer_augment_outlives alive dead blocked outlives outlives' :
    (∀ o , o ∈ outlives' → o.1 ⊆ alive ∪ dead ∧ o.2 ∈ alive ∪ dead) →
    (outlives ⊆ outlives') →
    (outlives_consistent dead outlives') →
      Delayed γd None ∗ (outer_inv γlt γ γo γd alive dead blocked) ∗ Outlives γo outlives
    ==∗ Delayed γd None ∗ (outer_inv γlt γ γo γd alive dead blocked) ∗
      Outlives γo outlives'.
  Proof.
    intros Howf Hosub Hc.
    iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iDestruct (inner_augment_outlives alive dead blocked outlives outlives' with "[H Inv]") as "X"; trivial. { iFrame. }
    iMod "X" as "[Inv H]".
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
End FullBorrows.
