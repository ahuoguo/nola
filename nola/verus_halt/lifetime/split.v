(** * Ported from VerusBelt ([lifetime/lifetime_internals/split.v], MIT,
  Hance, Elbeheiry, Matsushita, Dreyer), with the laters removed; see
  [nola.verus_halt.lifetime.inv] for the design. *)

From nola.verus_halt Require Import boxes.
From nola.verus_halt.lifetime Require Import ra.
From nola.verus_halt.lifetime Require Import inv.

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
    bookkeeping's.  See the head of [nola/verus_halt/lifetime/inv.v]. *)
  Context (γlt: gname).
  Context (γ: gname).
  Context (γo: gname).
  Context (γd: gname).
  
  Implicit Types (mprops: gmap_props FML Σ).
  
  Lemma full_borrows_invalidated_preserved_in_split
    sn sn1 sn2 mbs mprops Px Qx alive dead k bs
    :
      (delete sn mbs !! sn1 = None) →
      (delete sn mbs !! sn2 = None) →
      (sn1 ≠ sn2) →
      (mbs !! sn = Some bs) →
      (mprops !! sn ≡ Some (bor_sep Px Qx)) ∗
          full_borrows_invalidated_via alive dead k
                (<[sn2:=bs]> (<[sn1:=bs]> (delete sn mbs)))
                (<[sn2:=Qx]> (<[sn1:=Px]> (delete sn mprops)))
      ⊢ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof using γlt invGS_gen0 Σ γ.
    intros Hsn1 Hsn2 Hne Hmbssn. iIntros "[#Heq inval]".
    destruct (invalidated alive dead k bs) eqn:Hinvbool.
    - iDestruct (full_borrows_invalidated_via_insert with "inval") as "[q inval]".
        { rewrite lookup_insert_ne; trivial. } { trivial. }
      iDestruct (full_borrows_invalidated_via_insert with "inval") as "[p inval]".
        { trivial. } { trivial. }
      iDestruct (full_borrows_invalidated_via_delete with "[inval p q]") as "inval".
        { apply Hmbssn. } { iFrame "Heq". iFrame "inval". rewrite bor_sep_sem. iFrame. }
      iFrame.
    - iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
        { rewrite lookup_insert_ne; trivial. }
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
        { trivial. }
      iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
        { apply Hmbssn. } { trivial. } { iFrame "inval". }
  Qed.
  
  Lemma full_borrows_revalidated_preserved_in_split
    sn sn1 sn2 mbs mprops Px Qx alive dead k bs
    :
      (delete sn mbs !! sn1 = None) →
      (delete sn mbs !! sn2 = None) →
      (sn1 ≠ sn2) →
      (mbs !! sn = Some bs) →
      (mprops !! sn ≡ Some (bor_sep Px Qx)) ∗
      full_borrows_revalidated_via alive dead k mbs mprops
      ⊢ full_borrows_revalidated_via alive dead k
                (<[sn2:=bs]> (<[sn1:=bs]> (delete sn mbs)))
                (<[sn2:=Qx]> (<[sn1:=Px]> (delete sn mprops))).
  Proof using γlt invGS_gen0 Σ γ.
    intros Hsn1 Hsn2 Hne Hmbssn. iIntros "[#Heq inval]".
    destruct (revalidated alive dead k bs) eqn:Hinvbool.
    - iAssert (full_borrows_revalidated_via alive dead k (delete sn mbs) (delete sn mprops)
        ∗ (bor_sem Px ∗ bor_sem Qx))%I with "[inval]" as "[inval [P Q]]".
        { rewrite -bor_sep_sem.
          iApply full_borrows_revalidated_via_delete. { apply Hmbssn. } { trivial. } iFrame. iFrame "#". }
      iApply full_borrows_revalidated_via_insert.
      { rewrite lookup_insert_ne; trivial. } iFrame.
      iApply full_borrows_revalidated_via_insert.
      { trivial. } iFrame.
    - iApply full_borrows_revalidated_via_insert_false.
      { rewrite lookup_insert_ne; trivial. } { trivial. }
      iApply full_borrows_revalidated_via_insert_false.
      { trivial. } { trivial. }
      iApply full_borrows_revalidated_via_delete_false.
      { apply Hmbssn. } iFrame.
  Qed.

  Lemma llfb_fb_vs_split sn sn1 sn2 (mbs : gmap_bor_state) alive dead al de outlives mprops Px Qx
  :
    (delete sn mbs !! sn1 = None) →
    (delete sn mbs !! sn2 = None) →
    (sn1 ≠ sn2) →
    (mbs !! sn = Some (Borrow al de)) →
    (future_vs γlt γ alive dead outlives mbs mprops
        ∗ (mprops !! sn ≡ Some (bor_sep Px Qx)))
    ⊢
      future_vs γlt γ alive dead outlives
        (<[sn2:=Borrow al de]> (<[sn1:=Borrow al de]> (delete sn mbs)))
        (<[sn2:=Qx]> (<[sn1:=Px]> (delete sn mprops))).
  Proof using γlt invGS_gen0 Σ γ γd γo.
    intros Hdel1 Hdel2 Hne Hmbssn. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead) "[Hvs #Heq]".
    rewrite future_vs_def.
    rewrite (future_vs_def _ _ _ _ _ (<[sn2:=Borrow al de]> (<[sn1:=Borrow al de]> (delete sn mbs)))).
    iIntros  (k) "%Hin_my_alive Dead". iSplit.
      { iIntros "NotSwell". iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[Hvs _]".
        iApply IH. { intuition. }
        iFrame "#". iApply "Hvs". iFrame.
      }
    iIntros "inval".
    iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[_ Hvs]".
    iMod ("Hvs" with "[inval]") as "[reval Hvs]".
    { iFrame.
      iDestruct (full_borrows_invalidated_preserved_in_split sn sn1 sn2 mbs mprops Px Qx my_alive my_dead k (Borrow al de) Hdel1 Hdel2 Hne Hmbssn with "[inval]") as "inval". { iFrame. iFrame "Heq". }
      iFrame.
    }
    iModIntro.
    iSplitL "reval".
    { iDestruct (full_borrows_revalidated_preserved_in_split sn sn1 sn2 mbs mprops Px Qx my_alive my_dead k (Borrow al de) Hdel1 Hdel2 Hne Hmbssn with "[reval]") as "reval". { iFrame. iFrame "Heq". } iFrame. }
    destruct Hin_my_alive.
    iApply IH; trivial. iFrame. iFrame "#".
  Qed.
            
  Lemma inner_split alive dead blocked sn al de Px Qx :
    (inner_inv γlt γ γo alive dead blocked)
      ∗ OwnBorState γ sn (Borrow al de) ∗ sinv_tok sn (bor_sep Px Qx)
      ⊢ |=[box_wsat bor_sem]=> ∃ sn1 sn2, (inner_inv γlt γ γo alive dead blocked)
        ∗ OwnBorState γ sn1 (Borrow al de) ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ sinv_tok sn1 Px ∗ sinv_tok sn2 Qx.
  Proof using γlt invGS_gen0 Σ γ γd γo.
    iIntros "[Inv [OwnBor #slice]]".
    destruct (decide (al ## dead)) as [Hdisj|Hnot_disj].
    
    2: {
      unfold inner_inv.
      iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [Modulo [#DeadsLt [box [vs [#pures [#slices outlives]]]]]]]".
      iMod (inner_fake γ alive dead blocked al de Px Hnot_disj with "Modulo")
          as (sn1) "[Modulo [Ob2 Slice2]]".
      iMod (inner_fake γ alive dead blocked al de Qx Hnot_disj with "Modulo")
          as (sn2) "[Modulo [Ob3 Slice3]]".
      iModIntro. iExists sn1. iExists sn2. iFrame. iFrame "#".
    }
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [Modulo [#DeadsLt [box [vs [%pures [#slices outlives]]]]]]]".
    iDestruct (agree_bor_state_borrow_lts γ sn mbs dead al de Hdisj
        with "[Modulo auth OwnBor]") as (de') "[%Hmbs_sn %Hrel_de]". { iFrame. }
    
    iMod (slice_split (f := boxmap alive dead mbs) (P := Ptotal) (γ := sn)
        (b := bool_decide (al ⊆ alive ∧ ¬ de' ## dead))
        (Qx := bor_sep Px Qx) (Qx1 := Px) (Qx2 := Qx)
        with "slice box") as (sn1 sn2) "[%Hmd1 [%Hmd2 [%Hne [#slice1 [#slice2 box]]]]]".
      { unfold boxmap. rewrite lookup_fmap. rewrite Hmbs_sn. trivial. }
      { apply bor_sep_sem. }
    
    assert (delete sn mbs !! sn1 = None) as Hdel1
      by ( apply (delete_boxmap_implies_delete_original_is_none _ _ _ _ _ Hmd1) ).
    assert (delete sn mbs !! sn2 = None) as Hdel2
      by ( apply (delete_boxmap_implies_delete_original_is_none _ _ _ _ _ Hmd2) ).
      
    iMod (delete_bor_state_borrow_lts γ sn mbs dead al de Hdisj with 
        "[Modulo auth OwnBor]") as "[Modulo auth]". { iFrame. }
    iMod (alloc_bor_state2 γ sn1 (delete sn mbs) dead al de de' with "[Modulo auth]") as "[Modulo [auth own1]]"; trivial. { iFrame. }
    iMod (alloc_bor_state2 γ sn2 (<[sn1:=Borrow al de']> (delete sn mbs)) dead al de de' with "[Modulo auth]") as "[Modulo [auth own2]]".
      { rewrite lookup_insert_ne; trivial. } { trivial. } { iFrame. }
    
    iDestruct ((llfb_fb_vs_split sn sn1 sn2 mbs alive dead al de' outlives mprops Px Qx Hdel1 Hdel2 Hne Hmbs_sn) with "[vs]") as "vs".
    { iFrame. destruct pures as [Hdom Hrest].
      iApply (agree_slice_with_map mbs mprops sn _ (bor_sep Px Qx) Hdom Hmbs_sn). iFrame "#".
    }
      
    iModIntro. iExists sn1, sn2.
    iFrame "auth". iFrame "own1". iFrame "own2".
    iFrame "slice1". iFrame "slice2". iFrame "Modulo". iFrame "DeadsLt".
    iExists (<[ sn2 := Qx ]> (<[ sn1 := Px ]> (delete sn mprops))).
    iExists Ptotal, outlives.
    try iFrame "DeadsLt". iSplitL "box". { 
      rewrite boxmap_insert_Borrow. rewrite boxmap_insert_Borrow.
      rewrite boxmap_delete. iFrame.
    }
    iFrame "vs". iFrame "outlives".
    
    destruct pures as [Hdom [Hwf Hoc]].
    assert (al ∪ de' ⊆ alive ∪ dead) as Hwfalde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      apply (Hforall sn (Borrow al de') Hmbs_sn).
    }
    iSplitL. { iPureIntro. 
      split. { rewrite dom_insert_L. rewrite dom_insert_L. rewrite dom_insert_L.
        rewrite dom_insert_L. rewrite dom_delete_L. rewrite dom_delete_L.
        rewrite Hdom. trivial. }
      split. { apply map_wf_insert; trivial.
          { apply (swell_set_of_map_wf _ _ _ _ _ _ _ _ Hwf Hmbs_sn). }
          { apply (swell_set_of_map_wf_de _ _ _ _ _ _ _ _ Hwf Hmbs_sn). }
          apply map_wf_insert; trivial.
          { apply (swell_set_of_map_wf _ _ _ _ _ _ _ _ Hwf Hmbs_sn). }
          { apply (swell_set_of_map_wf_de _ _ _ _ _ _ _ _ Hwf Hmbs_sn). }
          apply map_wf_delete; trivial. }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice2".
      iApply big_sepM_insert_1. iFrame "slice1".
      rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm. intuition.
    }
  Qed. 
 
  
  Lemma outer_split alive dead blocked sn al de Px Qx :
      Delayed γd None
      ∗ (outer_inv γlt γ γo γd alive dead blocked)
      ∗ OwnBorState γ sn (Borrow al de) ∗ sinv_tok sn (bor_sep Px Qx)
      ⊢ |=[box_wsat bor_sem]=> ∃ sn1 sn2,
      Delayed γd None
        ∗ (outer_inv γlt γ γo γd alive dead blocked)
        ∗ OwnBorState γ sn1 (Borrow al de) ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ sinv_tok sn1 Px ∗ sinv_tok sn2 Qx.
  Proof.
    iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_split alive dead blocked sn al de Px Qx with "[H Inv]") as (sn1 sn2) "[Inv H]". { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
End FullBorrows.
