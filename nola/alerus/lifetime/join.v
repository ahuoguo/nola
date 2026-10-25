(** * Ported from VerusBelt ([lifetime/lifetime_internals/join.v], MIT,
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
      
  Lemma full_borrows_invalidated_preserved_in_join
    sn1 sn2 sn mbs mprops Px Qx alive dead k al de de1' de2'
    :
      (delete sn2 (delete sn1 mbs) !! sn = None) →
      (sn1 ≠ sn2) →
      (mbs !! sn1 = Some (Borrow al de1')) →
      (mbs !! sn2 = Some (Borrow al de2')) →
      (de = de1' ∨ ¬ de1' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
      (de = de2' ∨ ¬ de2' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
      (mprops !! sn1 ≡ Some Px) ∗
      (mprops !! sn2 ≡ Some Qx) ∗
          full_borrows_invalidated_via alive dead k
                (<[sn:=Borrow al de]> (delete sn2 (delete sn1 mbs)))
                (<[sn:=bor_sep Px Qx]> (delete sn2 (delete sn1 mprops)))
      ⊢ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof using γlt invGS_gen0 Σ γ.
    intros Hdel Hne Hmbssn1 Hmbssn2 Hrel_de1 Hrel_de2. iIntros "[#Heq1 [#Heq2 inval]]".
    destruct (invalidated alive dead k (Borrow al de)) eqn:Hinvbool.
    - iDestruct (full_borrows_invalidated_via_insert with "inval") as "[pq inval]".
        { trivial. } { trivial. }
      rewrite bor_sep_sem. iDestruct "pq" as "[p q]".
      iDestruct (full_borrows_invalidated_via_delete alive dead k sn2 (delete sn1 mbs) (delete sn1 mprops) (Borrow al de2') Qx with "[inval q]") as "inval".
        { rewrite lookup_delete_ne; trivial. } { rewrite lookup_delete_ne; trivial. iFrame "Heq2". iFrame "inval". iFrame "q". }
      iDestruct (full_borrows_invalidated_via_delete alive dead k sn1 mbs mprops (Borrow al de1') Px with "[inval p]") as "inval".
        { trivial. } { iFrame "Heq1". iFrame "inval". iFrame "p". }
      iFrame.
    - iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
        { trivial. }
      iDestruct (full_borrows_invalidated_via_delete_false alive dead k sn2 (delete sn1 mbs) (delete sn1 mprops) with "[inval]") as "inval".
        { rewrite lookup_delete_ne; trivial. apply Hmbssn2. }
        { rewrite bool_decide_eq_false. rewrite bool_decide_eq_false in Hinvbool. set_solver. }
        { iFrame "inval". }
      iDestruct (full_borrows_invalidated_via_delete_false alive dead k sn1 mbs mprops with "[inval]") as "inval".
        { apply Hmbssn1. }
        { rewrite bool_decide_eq_false. rewrite bool_decide_eq_false in Hinvbool. set_solver. }
        { iFrame "inval". }
      iFrame.
  Qed.
  
  Lemma full_borrows_revalidated_preserved_in_join
    sn sn1 sn2 mbs mprops Px Qx alive dead k al de de1' de2'
    :
      (delete sn2 (delete sn1 mbs) !! sn = None) →
      (sn1 ≠ sn2) →
      (mbs !! sn1 = Some (Borrow al de1')) →
      (mbs !! sn2 = Some (Borrow al de2')) →
      (de = de1' ∨ ¬ de1' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
      (de = de2' ∨ ¬ de2' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
      (mprops !! sn1 ≡ Some Px) ∗
      (mprops !! sn2 ≡ Some Qx) ∗
      full_borrows_revalidated_via alive dead k mbs mprops
      ⊢ full_borrows_revalidated_via alive dead k
            (<[sn:=Borrow al de]> (delete sn2 (delete sn1 mbs)))
            (<[sn:=bor_sep Px Qx]> (delete sn2 (delete sn1 mprops))).
  Proof using γlt invGS_gen0 Σ γ.
    intros Hdel Hne Hmbssn1 Hmbssn2 Hrel_de1 Hrel_de2. iIntros "[#Heq1 [#Heq2 inval]]".
    destruct (revalidated alive dead k (Borrow al de)) eqn:Hinvbool.
    - iAssert (full_borrows_revalidated_via alive dead k (delete sn1 mbs) (delete sn1 mprops)
        ∗ bor_sem Px)%I with "[inval]" as "[inval P]".
        { iApply full_borrows_revalidated_via_delete. { apply Hmbssn1. }
          { rewrite bool_decide_eq_true. rewrite bool_decide_eq_true in Hinvbool. set_solver. }
          iFrame. iFrame "#". }
      iAssert (full_borrows_revalidated_via alive dead k (delete sn2 (delete sn1 mbs)) (delete sn2 (delete sn1 mprops))
        ∗ bor_sem Qx)%I with "[inval]" as "[inval Q]".
        { iApply full_borrows_revalidated_via_delete. { rewrite lookup_delete_ne; trivial. apply Hmbssn2. }
          { rewrite bool_decide_eq_true. rewrite bool_decide_eq_true in Hinvbool. set_solver. }
          iFrame. iFrame "#". rewrite lookup_delete_ne; trivial. }
      iApply full_borrows_revalidated_via_insert.
      { trivial. } rewrite bor_sep_sem. iFrame.
    - iApply full_borrows_revalidated_via_insert_false.
      { trivial. } { trivial. }
      iApply full_borrows_revalidated_via_delete_false.
      { rewrite lookup_delete_ne; trivial. apply Hmbssn2. } iFrame.
      iApply full_borrows_revalidated_via_delete_false.
      { apply Hmbssn1. } iFrame.
  Qed.

  Lemma llfb_fb_vs_join sn sn1 sn2 (mbs : gmap_bor_state) alive dead al de de1' de2' outlives mprops Px Qx
  :
    (delete sn2 (delete sn1 mbs) !! sn = None) →
    (sn1 ≠ sn2) →
    (mbs !! sn1 = Some (Borrow al de1')) →
    (mbs !! sn2 = Some (Borrow al de2')) →
    (de = de1' ∨ ¬ de1' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
    (de = de2' ∨ ¬ de2' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
    (future_vs γlt γ alive dead outlives mbs mprops
        ∗ (mprops !! sn1 ≡ Some Px)
        ∗ (mprops !! sn2 ≡ Some Qx))
    ⊢
      future_vs γlt γ alive dead outlives
        (<[sn:=Borrow al de]> (delete sn2 (delete sn1 mbs)))
        (<[sn:=bor_sep Px Qx]> (delete sn2 (delete sn1 mprops))).
  Proof using γlt invGS_gen0 Σ γ.
    intros Hdel Hne Hmbssn1 Hmbssn2 Hrel_de1 Hrel_de2.
    generalize Hrel_de1. generalize Hrel_de2. generalize dead.
    clear Hrel_de1. clear Hrel_de2. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hrel_de2 Hrel_de1) "[Hvs [#Heq1 #Heq2]]".
    rewrite future_vs_def.
    rewrite (future_vs_def γlt γ my_alive).
    iIntros  (k) "%Hin_my_alive Dead". iSplit.
      { iIntros "NotSwell". iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[Hvs _]".
      destruct Hin_my_alive. iApply IH; trivial; clear IH.
      - replace (my_alive ∖ {[k]} ∪ (my_dead ∪ {[k]})) with (my_alive ∪ my_dead).
        + set_solver.
        + apply set_eq. intros x. destruct (decide (x = k)); set_solver.
      - replace (my_alive ∖ {[k]} ∪ (my_dead ∪ {[k]})) with (my_alive ∪ my_dead).
        + set_solver.
        + apply set_eq. intros x. destruct (decide (x = k)); set_solver.
      - iFrame "#". iApply "Hvs". iFrame.
    }
    iIntros "inval".
    iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[_ Hvs]".
    iMod ("Hvs" with "[inval]") as "[reval Hvs]".
    { iFrame.
      iDestruct (full_borrows_invalidated_preserved_in_join sn1 sn2 sn mbs mprops Px Qx my_alive my_dead k al de de1' de2' Hdel Hne Hmbssn1 Hmbssn2 Hrel_de1 Hrel_de2 with "[inval]") as "inval". { iFrame. iFrame "#". }
      iFrame.
    }
    iModIntro.
    iSplitL "reval".
    { iDestruct (full_borrows_revalidated_preserved_in_join sn sn1 sn2 mbs mprops Px Qx my_alive my_dead k al de de1' de2' Hdel Hne Hmbssn1 Hmbssn2 Hrel_de1 Hrel_de2 with "[reval]") as "reval". { iFrame. iFrame "#". } iFrame. }
    destruct Hin_my_alive.
    iApply IH; trivial. 
    - replace (my_alive ∖ {[k]} ∪ (my_dead ∪ {[k]})) with (my_alive ∪ my_dead).
      + set_solver.
      + apply set_eq. intros x. destruct (decide (x = k)); set_solver.
    - replace (my_alive ∖ {[k]} ∪ (my_dead ∪ {[k]})) with (my_alive ∪ my_dead).
      + set_solver.
      + apply set_eq. intros x. destruct (decide (x = k)); set_solver.
    - iFrame. iFrame "#".
  Qed.
  
  Lemma inner_join alive dead blocked sn1 sn2 al de Px Qx :
    swell_set de →
    (de ⊆ alive ∪ dead) →
    (inner_inv γlt γ γo alive dead blocked)
        ∗ OwnBorState γ sn1 (Borrow al de) ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ sinv_tok sn1 Px ∗ sinv_tok sn2 Qx
      ⊢ |=[box_wsat bor_sem]=> ∃ sn, (inner_inv γlt γ γo alive dead blocked)
        ∗ OwnBorState γ sn (Borrow al de) ∗ sinv_tok sn (bor_sep Px Qx).
  Proof using γlt invGS_gen0 Σ γ γd γo.
    intros swell_de Hwfde.
    iIntros "[Inv [OwnBor1 [OwnBor2 [#slice1 #slice2]]]]".
    destruct (decide (al ## dead)) as [Hdisj|Hnot_disj].
    2: {
      unfold inner_inv.
      iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [Modulo [#DeadsLt [box [vs [#pures [#slices outlives]]]]]]]".
      iMod (inner_fake γ alive dead blocked al de (bor_sep Px Qx) Hnot_disj with "Modulo")
          as (sn) "[Modulo [Ob Slice]]".
      iModIntro. iExists sn. iFrame. iFrame "#".
    }
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [Modulo [#DeadsLt [box [vs [%pures [#slices outlives]]]]]]]".
    iDestruct (agree_bor_state_borrow_lts γ sn1 mbs dead al de Hdisj
        with "[Modulo auth OwnBor1]") as (de1') "[%Hmbs_sn1 %Hrel_de1]". { iFrame. }
    iDestruct (agree_bor_state_borrow_lts γ sn2 mbs dead al de Hdisj
        with "[Modulo auth OwnBor2]") as (de2') "[%Hmbs_sn2 %Hrel_de2]". { iFrame. }
    iDestruct (distinct_bor_state_borrow_borrow_lts γ sn1 sn2 al de al de dead
        with "[Modulo OwnBor1 OwnBor2]") as "%Hne"; trivial. { iFrame. }
    
    iMod (slice_combine (f := boxmap alive dead mbs) (P := Ptotal)
        (Qx := bor_sep Px Qx) (Qx1 := Px) (Qx2 := Qx) (γ1 := sn1) (γ2 := sn2)
        (b := bool_decide (al ⊆ alive ∧ ¬ de ## dead))
        with "slice1 slice2 box") as (sn) "[%Hmd [#slice box]]".
      { trivial. }
      { unfold boxmap. rewrite lookup_fmap. rewrite Hmbs_sn1. simpl. f_equiv.
        apply bool_decide_equiv. set_solver. }
      { unfold boxmap. rewrite lookup_fmap. rewrite Hmbs_sn2. simpl. f_equiv.
        apply bool_decide_equiv. set_solver. }
      { apply bor_sep_sem. }
    
    assert (delete sn2 (delete sn1 mbs) !! sn = None) as Hdel
      by ( apply (delete_delete_boxmap_helper4 sn sn1 sn2 alive dead mbs Hmd) ).

    iMod (delete_bor_state_borrow_lts γ sn1 mbs dead al de Hdisj with 
        "[Modulo auth OwnBor1]") as "[Modulo auth]". { iFrame. }
    iMod (delete_bor_state_borrow_lts γ sn2 (delete sn1 mbs) dead al de Hdisj with 
        "[Modulo auth OwnBor2]") as "[Modulo auth]". { iFrame. }
        
    iMod (alloc_bor_state2 γ sn (delete sn2 (delete sn1 mbs)) dead al de de with "[Modulo auth]") as "[Modulo [auth own]]"; trivial. { set_solver. } { iFrame. }
    
    assert (de = de1' ∨ ¬ de1' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) as Hrel_de1'.
      { intuition. }
    assert (de = de2' ∨ ¬ de2' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) as Hrel_de2'.
      { intuition. }
    
    iDestruct ((llfb_fb_vs_join sn sn1 sn2 mbs alive dead al de de1' de2' outlives mprops Px Qx Hdel Hne Hmbs_sn1 Hmbs_sn2 Hrel_de1' Hrel_de2') with "[vs]") as "vs".
    { iFrame. destruct pures as [Hdom Hrest]. iSplitL.
      { iApply (agree_slice_with_map mbs mprops sn1 _ Px Hdom Hmbs_sn1). iFrame "#". }
      { iApply (agree_slice_with_map mbs mprops sn2 _ Qx Hdom Hmbs_sn2). iFrame "#". }
    }
      
    iModIntro. iExists sn.
    iFrame "auth". iFrame "own".
    iFrame "Modulo". iFrame "slice". iFrame "DeadsLt".
    iExists (<[ sn := bor_sep Px Qx ]> (delete sn2 (delete sn1 mprops))).
    iExists Ptotal, outlives.
    try iFrame "DeadsLt". iSplitL "box". { 
      rewrite boxmap_insert_Borrow. rewrite boxmap_delete.
      rewrite boxmap_delete. iFrame.
    }
    iFrame "vs". iFrame "outlives".
    
    destruct pures as [Hdom [Hwf Hoc]].
    assert (al ∪ de ⊆ alive ∪ dead) as Hwfalde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn1 (Borrow al de1') Hmbs_sn1.
      set_solver.
    }
    iSplitL. { iPureIntro. 
      split. { rewrite dom_insert_L. rewrite dom_insert_L. rewrite dom_delete_L.
        rewrite dom_delete_L. rewrite dom_delete_L. rewrite dom_delete_L.
        rewrite Hdom. trivial. }
      split. { apply map_wf_insert; trivial.
          { apply (swell_set_of_map_wf _ _ _ _ _ _ _ _ Hwf Hmbs_sn1). }
          apply map_wf_delete; trivial.
          apply map_wf_delete; trivial. }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice".
      rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro.
      rewrite lookup_delete_Some in Dm.
      rewrite lookup_delete_Some in Dm. intuition.
    }
  Qed.
    
  Lemma outer_join alive dead blocked sn1 sn2 al de Px Qx :
      swell_set de →
      (de ⊆ alive ∪ dead) →
      Delayed γd None
        ∗ (outer_inv γlt γ γo γd alive dead blocked)
        ∗ OwnBorState γ sn1 (Borrow al de) ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ sinv_tok sn1 Px ∗ sinv_tok sn2 Qx
      ⊢ |=[box_wsat bor_sem]=> ∃ sn,
      Delayed γd None
        ∗ (outer_inv γlt γ γo γd alive dead blocked)
        ∗ OwnBorState γ sn (Borrow al de) ∗ sinv_tok sn (bor_sep Px Qx).
  Proof.
    intros swell_de Hdewf. iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_join alive dead blocked sn1 sn2 al de Px Qx swell_de Hdewf with "[H Inv]") as (sn) "[Inv H]". { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
End FullBorrows.
