(** * Ported from VerusBelt ([lifetime/lifetime_internals/new_lt.v], MIT,
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
  
  Lemma outlives_consistent_okay_on_kill_fresh alive dead blocked outlives m my_dead k_new :
      k_new ∉ alive →
      k_new ∉ dead →
      inv.map_wf alive dead blocked outlives m →
      outlives_consistent (my_dead ∪ {[k_new]}) outlives →
      outlives_consistent my_dead outlives.
  Proof.
      unfold outlives_consistent, inv.map_wf.
      intros Hal Hde Hwf Hoc o Ho_in_outlives. have Ho := Hoc o Ho_in_outlives.
      destruct Hwf as [Ha [Hb [Hc [Hforall [Hforall2 Hforall3]]]]].
      have Hr := Hoc o Ho_in_outlives. set_solver.
  Qed.
  
  Lemma set_lemma3 (k_new : lt_atom) (alive dead al de : gset lt_atom) :
      k_new ∉ alive →
      k_new ∉ dead →
      al ∪ de ⊆ alive ∪ dead →
      k_new ∉ al.
  Proof. set_solver. Qed.

  Lemma set_lemma4 (k: lt_atom) (my_alive my_dead : gset lt_atom) :
      (k ∈ my_alive) →
      my_alive ∖ {[k]} ∪ (my_dead ∪ {[k]}) = my_alive ∪ my_dead. 
  Proof.
    intros k_in. apply set_eq. intro x. destruct (decide (x = k)); set_solver.
  Qed.
 
  
  Lemma llfb_fb_vs_for_new_lt' alive dead blocked outlives my_alive my_dead mbs mprops k_new :
    inv.map_wf alive dead blocked outlives mbs →
    my_alive ∪ my_dead = alive ∪ dead →
    my_alive ## my_dead →
    k_new ∉ alive →
    k_new ∉ dead →
    future_vs γlt γ (my_alive) my_dead outlives mbs mprops 
    ⊢ future_vs γlt γ (my_alive) (my_dead ∪ {[k_new]}) outlives mbs mprops.
  Proof.
    intros Hwf.
    generalize my_dead. clear my_dead.
    induction my_alive as [my_alive IH] using set_ind_strong. 
    intros my_dead Hsame Hdisj Hknew_alive Hknew_dead.
    iIntros "Hvs".
    rewrite future_vs_def.
    rewrite (future_vs_def γlt γ my_alive).
    iIntros (k) "%Hin_my_alive Dead".
    destruct (decide (k = k_new)).
    - subst k_new. exfalso. set_solver.
    -   iSplit.
          { iIntros "NotSwell". iDestruct ("Hvs" $! k with "[] Dead") as "[Hvs _]".
            { iPureIntro. split; intuition.
              apply (outlives_consistent_okay_on_kill_fresh alive dead blocked outlives mbs (my_dead ∪ {[k]}) k_new); trivial.
              replace ((my_dead ∪ {[k]} ∪ {[k_new]})) with 
                  (my_dead ∪ {[k_new]} ∪ {[k]}) by set_solver.
              intuition.
            }
            replace ((my_dead ∪ {[k_new]} ∪ {[k]})) with 
                (my_dead ∪ {[k]} ∪ {[k_new]}) by set_solver.
            iApply IH. { intuition. } { rewrite <- Hsame. apply set_lemma4. set_solver. }
            { set_solver. } { set_solver. } { set_solver. }
            iApply "Hvs". iFrame.
          }
        iIntros "inval".
        iDestruct ("Hvs" $! k with "[] Dead") as "[_ Hvs]".
          { iPureIntro. split. { intuition. }
          apply (outlives_consistent_okay_on_kill_fresh alive dead blocked outlives mbs (my_dead ∪ {[k]}) k_new); trivial.
          replace ((my_dead ∪ {[k]} ∪ {[k_new]})) with 
              (my_dead ∪ {[k_new]} ∪ {[k]}) by set_solver.
          intuition.
        }
        iMod ("Hvs" with "[inval]") as "[reval Hvs]". {
          unfold full_borrows_invalidated_via.
          iApply (borrow_sum_equiv _ (invalidated (my_alive) (my_dead ∪ {[k_new]}) k)).
          { intros sn bs. unfold invalidated.
            destruct bs as [al de|bl al de].
            - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true. set_solver.
            - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true. set_solver.
          }
          iFrame.
        }
        iModIntro. iSplitL "reval".
        {
          unfold full_borrows_invalidated_via.
          iApply (borrow_sum_equiv _ (revalidated my_alive my_dead k)).
          { intros sn bs Hmbssn.
            destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
            have Hf := Hforall sn bs. unfold revalidated.
            destruct bs as [al de|bl al de].
              - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true.
                intros [Hx [Hy Hz]]. split.
                + have Hf2 := Hf Hmbssn. destruct Hf2 as [Hf2 _].
                  have Hg := (set_lemma3 k_new alive dead al de Hknew_alive Hknew_dead Hf2).
                  set_solver.
                + set_solver.
              - intros; trivial.
          }
          iFrame "reval".
        }
        iDestruct (IH with "Hvs") as "Hvs"; trivial.
          { set_solver. }
          { rewrite <- Hsame. apply set_lemma4. set_solver. }
          { set_solver. }
          replace ((my_dead ∪ {[k]} ∪ {[k_new]})) with 
              (my_dead ∪ {[k_new]} ∪ {[k]}) by set_solver.
          iFrame.
  Qed.
 
  Lemma set_lemma5 (k k_new: lt_atom) (my_alive : gset lt_atom) :
    (k ≠ k_new) →
    (my_alive ∖ {[k]} ∪ {[k_new]}) = (my_alive ∪ {[k_new]}) ∖ {[k]}.
  Proof.
    intros Hne. apply set_eq. intro x. destruct (decide (x = k)); set_solver.
  Qed.
    
  Lemma llfb_fb_vs_for_new_lt alive dead blocked outlives my_alive my_dead mbs mprops k_new :
    inv.map_wf alive dead blocked outlives mbs →
    my_alive ∪ my_dead = alive ∪ dead →
    my_alive ## my_dead →
    k_new ∉ alive →
    k_new ∉ dead →
    future_vs γlt γ (my_alive) my_dead outlives mbs mprops 
    ⊢ future_vs γlt γ (my_alive ∪ {[k_new]}) (my_dead) outlives mbs mprops.
  Proof.
    intros Hwf.
    generalize my_dead. clear my_dead.
    induction my_alive as [my_alive IH] using set_ind_strong. 
    intros my_dead Hsame Hdisj Hknew_alive Hknew_dead.
    iIntros "Hvs".
    rewrite (future_vs_def γlt γ (my_alive ∪ {[k_new]})).
    iIntros (k) "%Hin_my_alive Dead".
    destruct (decide (k = k_new)).
      - subst k_new.
        iSplit. {
          iIntros "NotSwell".
          replace ((my_alive ∪ {[k]}) ∖ {[k]}) with my_alive.
          2: { apply set_eq. intros x. destruct (decide (x = k)); set_solver. }
          iApply (llfb_fb_vs_for_new_lt' alive dead blocked outlives my_alive my_dead mbs mprops k); trivial.
        }
        iIntros "inval".
        iModIntro.
        iSplitR. {
          iApply borrow_sum_empty. intros sn bs Hmbssn. unfold revalidated.
          destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
          have Hf := Hforall sn bs.
          destruct bs as [al de|]; trivial. rewrite bool_decide_eq_false.
          set_solver.
        }
        replace ((my_alive ∪ {[k]}) ∖ {[k]}) with my_alive.
          + iApply (llfb_fb_vs_for_new_lt' alive dead blocked outlives my_alive my_dead mbs mprops k); trivial.
          + apply set_eq. intros x. destruct (decide (x = k)); set_solver.
      - rewrite future_vs_def.
        iSplit. {
          iIntros "NotSwell".
          iDestruct ("Hvs" $! k with "[] Dead") as "[Hvs _]". { iPureIntro; intuition. set_solver. }
          iDestruct ("Hvs" with "NotSwell") as "Hvs".
          iDestruct (IH with "Hvs") as "Hvs"; trivial.
          { set_solver. }
          { rewrite <- Hsame. apply set_lemma4. set_solver. }
          { set_solver. }
          rewrite set_lemma5; trivial.
        }
        iIntros "inval".
        iDestruct ("Hvs" $! k with "[] Dead") as "[_ Hvs]".
          { iPureIntro. split. { set_solver. } intuition. }
        iMod ("Hvs" with "[inval]") as "[reval Hvs]".
        { unfold full_borrows_invalidated_via.
          iApply (borrow_sum_equiv _ (invalidated (my_alive ∪ {[k_new]}) my_dead k)).
          { intros sn bs. unfold invalidated.
            destruct bs as [al de|bl al de].
            - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true. set_solver.
            - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true. set_solver.
          }
          iFrame.
        }
        iModIntro. iSplitL "reval".
        {
          unfold full_borrows_invalidated_via.
          iApply (borrow_sum_equiv _ (revalidated my_alive my_dead k)).
          { intros sn bs Hmbssn.
            destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
            have Hf := Hforall sn bs. unfold revalidated.
            destruct bs as [al de|bl al de].
              - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true.
                intros [Hx [Hy Hz]]. split.
                + have Hf2 := Hf Hmbssn. destruct Hf2 as [Hf2 _].
                  have Hg := (set_lemma3 k_new alive dead al de Hknew_alive Hknew_dead Hf2).
                  set_solver.
                + set_solver.
              - intros; trivial.
          }
          iFrame "reval".
        }
        iDestruct (IH with "Hvs") as "Hvs"; trivial.
          { set_solver. }
          { rewrite <- Hsame. apply set_lemma4. set_solver. }
          { set_solver. }
          rewrite set_lemma5; trivial.
  Qed.
   
  Lemma inner_new_lt alive dead blocked k :
    (k ∉ alive ∪ dead) →
    (inner_inv γlt γ γo alive dead blocked) -∗ |=[box_wsat bor_sem]=> (inner_inv γlt γ γo (alive ∪ {[ k ]}) dead blocked).
  Proof.
    intros Hk_fresh.
    iIntros "Inv".
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [Modulo [#DeadsLt [box [vs [%pures [#slices outlives]]]]]]]".
    
    iDestruct (llfb_fb_vs_for_new_lt alive dead blocked outlives alive dead mbs mprops k with "vs") as "vs"; trivial.
      { intuition. }
      { unfold inv.map_wf in pures. intuition. }
      { set_solver. }
      { set_solver. }
    
    iModIntro. iExists mbs. iExists mprops. iExists Ptotal. iExists outlives.
    iFrame "auth". iFrame "Modulo". iFrame "DeadsLt".
    destruct pures as [Hdom [Hwf Hoc]].
    try iFrame "DeadsLt". iSplitL "box". {
      replace (boxmap (alive ∪ {[k]}) dead mbs) with (boxmap alive dead mbs). { iFrame. }
      unfold boxmap. apply map_eq. intros sn.
      rewrite lookup_fmap. rewrite lookup_fmap.
      destruct (mbs !! sn) as [[al de|bl al de]|] eqn:Hmbssn.
      - rewrite Hmbssn. simpl. f_equiv. apply bool_decide_equiv.
        destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
        have Hf2 := Hforall sn (Borrow al de). set_solver.
      - rewrite Hmbssn. simpl. trivial.
      - rewrite Hmbssn. trivial.
    }
    iFrame "vs".
    iSplitR. { iPureIntro.
      split; trivial. split; trivial.
      apply map_wf_new_lt; trivial.
    }
    iFrame "slices". iFrame "outlives".
  Qed.
          
  Lemma outer_new_lt alive dead blocked k :
    (k ∉ alive ∪ dead) →
    (outer_inv γlt γ γo γd alive dead blocked) ∗ Delayed γd None -∗ |=[box_wsat bor_sem]=>
    (outer_inv γlt γ γo γd (alive ∪ {[ k ]}) dead blocked) ∗ Delayed γd None.
  Proof.
    intros Had.
    iIntros "[Inv Delayed]". iDestruct "Inv" as (opt_k) "[D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_new_lt alive dead blocked k with "Inv") as "Inv"; trivial.
    iModIntro. iFrame. iFrame.
  Qed.

End FullBorrows.
