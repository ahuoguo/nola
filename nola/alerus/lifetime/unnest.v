(** * Ported from VerusBelt ([lifetime/lifetime_internals/unnest.v], MIT,
  Hance, Elbeheiry, Matsushita, Dreyer), with the laters removed; see
  [nola.alerus.lifetime.inv] for the design. *)

From nola.alerus Require Import boxes.
From nola.alerus.lifetime Require Import ra.
From nola.alerus.lifetime Require Import inv.
From nola.alerus.lifetime Require Import reborrow.

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
  
  Context (γ: gname).
  Context `{!BorStateFml γ}.
  Context (γo: gname).
  Context (γd: gname).
  
  Implicit Types (mprops: gmap_props FML Σ).
 
  Lemma set_lemma1 (x y z w : gset lt_atom) : x ∪ y ⊆ z ∪ w → x ## w → x ⊆ z.
  Proof. set_solver. Qed.
      
  Lemma llfb_fb_vs_for_delete_already_dead alive dead outlives mbs mprops sn al dd :
    alive ## dead →
    ¬(al ## dead) →
    (mbs !! sn = Some (Borrow al dd)) →
      future_vs γ alive dead outlives mbs mprops
      ⊢
      future_vs γ alive dead outlives (delete sn mbs) (delete sn mprops).
  Proof using invGS_gen0 Σ γ γd γo.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdisj Hdead Hmbssn) "Hvs".
    
    rewrite future_vs_def.
    rewrite (future_vs_def γ my_alive).
    iIntros (k) "%Hin_my_alive Dead". iSplit.
      { iIntros "NotSwell". iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[Hvs _]".
        iApply IH. { intuition. } { set_solver. } { set_solver. }
        { trivial. }
        iFrame "#". iApply "Hvs". iFrame.
      }
    iIntros "inval".
    iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "Hvs".
    destruct Hin_my_alive as [Hin_my_alive Hoc].

     iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hmbssn. }
      { unfold invalidated.  rewrite bool_decide_eq_false. set_solver. }
      
      iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hmbssn. }
          iFrame.
      }
      
      iApply IH; trivial. { set_solver. } { set_solver. }
  Qed.
  
  Local Instance modulo_dead_pers γ1 k : Persistent (ModuloDeadPers γ1 k).
  Proof. apply own_core_persistent. unfold CoreId. trivial. Qed.
    
  Lemma llfb_fb_vs_for_unnest alive dead outlives mbs mprops sn sn' al al' dd dd' :
    (mbs !! sn' = Some (Borrow al' dd')) →
    alive ## dead →
    ¬(dd ## dead) →
    al' ⊆ alive →
    swell_set al' →
    (future_vs γ alive dead outlives mbs mprops
      ∗ (∀ d, ⌜d ∈ dead⌝ -∗ ModuloDeadPers γ d)
      ∗ OwnBorState γ sn (Borrow al al')
      ∗ (mprops !! sn' ≡ Some (bor_state_fml sn (Borrow al dd)))
      ⊢ 
      future_vs γ alive dead outlives (delete sn' mbs) (delete sn' mprops))%I.
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hmbssn'.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    intros my_dead Hdisj Hdd Halal' swell_al'.
    iIntros "[Hvs [#Halldead [OwnBor #Heq]]]".
    
    rewrite future_vs_def.
    rewrite (future_vs_def γ my_alive).
    iIntros (k) "%Hin_my_alive #Dead".
    
    iAssert (∀ d : lt_atom, ⌜d ∈ (my_dead ∪ {[ k ]})⌝ -∗ ModuloDeadPers γ d)%I as "#Halldead2".
      { iIntros (d) "%Hdin". rewrite elem_of_union in Hdin. destruct Hdin as [Hdin1|Hdin2].
        - iApply "Halldead". iPureIntro; trivial.
        - rewrite elem_of_singleton in Hdin2. subst k. iApply "Dead".
      }
    
    destruct (decide (k ∈ al')) as [Hin|Hout].
    - iSplit.
      { iIntros "%Hnotswell". exfalso. apply Hnotswell. apply swell_al'. apply Hin. }
      assert (dd ∩ my_dead ≠ ∅) as Hdisj2. { set_solver. }
      assert (∃ x , x ∈ (dd ∩ my_dead)) as Hex_x. { apply set_choose_L; trivial. }
      destruct Hex_x as [x Hex_d].
      iMod (update_bor_state_borrow_fix_dead γ sn al al' dd k x with "[OwnBor]") as "OwnBor".
        { trivial. } { set_solver. } {
          iFrame.  iFrame "Dead".
          iApply "Halldead". iPureIntro. set_solver.
        }
      
      iIntros "inval".
      iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "Hvs".
      
      iDestruct (full_borrows_invalidated_via_delete with "[inval OwnBor]") as "inval".
        { apply Hmbssn'. }
        { iFrame "Heq". iFrame "inval". rewrite bor_state_fml_sem. iFrame "OwnBor". }
        
      iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }
        
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hmbssn'. }
          iFrame "reval".
      }
      
      iApply (llfb_fb_vs_for_delete_already_dead _ _ outlives mbs mprops sn' al' dd').
        { set_solver. } { set_solver. } { trivial. }
      iFrame "vs".
      
    - iSplit.
     { iIntros "NotSwell". iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[Hvs _]".
        iApply IH. { intuition. } { set_solver. } { set_solver. } { set_solver. } { trivial. }
        iFrame "#". iFrame.
        iApply "Hvs". iFrame.
      }
     iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[_ Hvs]".
     iIntros "inval".

     iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hmbssn'. }
      { unfold invalidated.  rewrite bool_decide_eq_false. set_solver. }
      
      iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hmbssn'. }
          iFrame.
      }
      
      iApply IH; trivial. { set_solver. } { set_solver. } { set_solver. } { set_solver. }
      iFrame. iFrame "#".
  Qed.
        
  Lemma inner_unnest alive dead blocked sn sn' al al' Px :
    (inner_inv γ γo alive dead blocked)
        ∗ sinv_tok sn Px
        ∗ OwnBorState γ sn' (Borrow al' {[ default_dead ]})
        ∗ sinv_tok sn' (bor_state_fml sn (Borrow al {[ default_dead ]}))
      -∗ |=[box_wsat bor_sem]=> ∃ sn2,
    (inner_inv γ γo alive dead blocked)
        ∗ OwnBorState γ sn2 (Borrow (al ∪ al') {[ default_dead ]})
        ∗ sinv_tok sn2 Px.
  Proof using invGS_gen0 Σ γ γd γo.
    iIntros "[Inv [#sliceP [OwnBor' #sliceBorrow]]]".
    destruct (decide ((al ∪ al') ## dead)) as [Hdisj|Hndisj].
      2: {
        iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [Modulo [box [vs [#pures [#slices outlives]]]]]]".
        iMod (inner_fake γ alive dead blocked (al ∪ al') {[default_dead]} Px with "Modulo") as (sn2) "[Modulo A]"; trivial. iModIntro. iExists sn2. iFrame. iFrame "#".
      }
    
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [Modulo [box [vs [%pures [#slices outlives]]]]]]".
    
    assert (al ## dead) as Hdisj_al_dead. { unfold inv.map_wf in pures; set_solver. }
    assert (al' ## dead) as Hdisj_al'_dead. { unfold inv.map_wf in pures; set_solver. }
    assert (alive ## {[default_dead]}) as Hdisj_alive_dd. { unfold inv.map_wf in pures. set_solver. }
    assert (alive ## dead) as Halive_disj_dead. { unfold inv.map_wf in pures. intuition. }
    assert (default_dead ∈ dead) as Hdd. { unfold inv.map_wf in pures. intuition. }
    
    iDestruct (agree_bor_state_borrow_lts γ sn' mbs dead al' {[default_dead]}
        with "[Modulo auth OwnBor']") as (dd') "[%Hmbssn' %Hrel_dd']". { set_solver. } { iFrame. }
    
    assert (al' ⊆ alive) as Hal'_sub_alive. {
      destruct pures as [Hp [[Ha [Hb [Hc [Hforall Hforall2]]]] Hrest]]. 
      have Hforsn' := Hforall sn' _ Hmbssn'. destruct Hforsn' as [Hforsn' _].
      apply (set_lemma1 _ _ _ _ Hforsn' Hdisj_al'_dead).
    }
    
    assert (boxmap alive dead mbs !! sn' = Some true) as Hboxmap_true'.
      { unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn'. simpl.
        f_equiv. rewrite bool_decide_eq_true. 
        split. { set_solver. } unfold inv.map_wf in pures. set_solver.
      }
    
    iMod (slice_delete_full (f := boxmap alive dead mbs) (P := Ptotal)
        (Px := bor_state_fml sn (Borrow al {[default_dead]})) (γ := sn')
        with "sliceBorrow box") as (Ptotal') "[OwnBor [Ptotaleq box]]"; trivial.
    rewrite bor_state_fml_sem.
        
    iDestruct (agree_bor_state_borrow_lts γ sn mbs dead al {[default_dead]}
        with "[Modulo auth OwnBor]") as (dd) "[%Hmbssn %Hrel_dd]". { set_solver. } { iFrame. }
        
    assert (al ⊆ alive) as Hal_sub_alive. {
      destruct pures as [Hp [[Ha [Hb [Hc [Hforall Hforall2]]]] Hrest]]. 
      have Hforsn := Hforall sn _ Hmbssn. destruct Hforsn as [Hforsn _].
      apply (set_lemma1 _ _ _ _ Hforsn Hdisj_al_dead).
    }
    assert (dd ⊆ alive ∪ dead) as Hdd_sub_alive. {
      destruct pures as [Hp [[Ha [Hb [Hc [Hforall Hforall2]]]] Hrest]]. 
      have Hforsn := Hforall sn _ Hmbssn.
      set_solver.
    }
    assert (al ∪ al' ⊆ alive) as HalUal' by set_solver.
    assert (¬(dd ## dead)) as Hdddead. { set_solver. }
    assert (¬({[default_dead]} ## dead)) as Hdefaultdead. { set_solver. }
    
    assert (boxmap alive dead mbs !! sn = Some true) as Hboxmap_true.
      { unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. simpl.
        f_equiv. rewrite bool_decide_eq_true. 
        split. { set_solver. } unfold inv.map_wf in pures. set_solver.
      }
    
    iDestruct (distinct_bor_state_borrow_borrow_lts γ sn' sn al' {[default_dead]} al {[default_dead]} dead with "[Modulo OwnBor OwnBor']") as "%Hne"; trivial.
    { iFrame. }
    
    iMod (delete_bor_state_borrow_lts γ sn' mbs dead al' {[default_dead]} Hdisj_al'_dead
        with "[Modulo auth OwnBor']") as "[Modulo auth]". { iFrame. }
        
    iMod (update_bor_state_borrow_lts γ sn (delete sn' mbs) dead al {[default_dead]} (Borrow al al') Hdisj_al_dead
        with "[Modulo auth OwnBor]") as "[Modulo [auth OwnBor]]". { iFrame. }
    
    iMod (slice_empty (f := delete sn' (boxmap alive dead mbs)) (P := Ptotal')
        (Px := Px) (γ := sn) with "sliceP box") as "[P box]".
      { rewrite lookup_delete_ne; trivial. }
    
    iMod (slice_insert_full
        (f := <[sn:=false]> (delete sn' (boxmap alive dead mbs))) (P := Ptotal')
        Px with "P box") as (sn2) "[%Hsn2None [#slice2 box]]".
    
    iMod (alloc_bor_state2 γ sn2 (<[sn:=Borrow al al']> (delete sn' mbs)) dead (al ∪ al') {[default_dead]} dd with "[Modulo auth]") as "[Modulo [auth OwnBor2]]".
      { eapply lookup_insert_delete_boxmap_helper. apply Hsn2None. }
      { apply Hrel_dd. } { iFrame. }
      
    iDestruct (get_all_modulo_dead_pers with "Modulo") as "[Modulo #Halldeadspers]".
    
    assert (sn ≠ sn2) as Hne2.
      { intro Heq. subst sn2. rewrite lookup_insert_eq in Hsn2None. discriminate. }
    
    destruct pures as [Hdom [Hwf Hoc]].
    have swell_al := swell_set_of_map_wf _ _ _ _ _ _ _ _ Hwf Hmbssn.
    have swell_dd := swell_set_of_map_wf_de _ _ _ _ _ _ _ _ Hwf Hmbssn.
    have swell_al' := swell_set_of_map_wf _ _ _ _ _ _ _ _ Hwf Hmbssn'.
    have swell_dd' := swell_set_of_map_wf_de _ _ _ _ _ _ _ _ Hwf Hmbssn'.
    have swell_al_al' := swell_set_union _ _ swell_al swell_al'.
    
    iDestruct ((llfb_fb_vs_for_unnest alive dead outlives mbs mprops sn sn' al al' {[default_dead]} dd' Hmbssn' Halive_disj_dead Hdefaultdead Hal'_sub_alive swell_al') with "[vs OwnBor]") as "vs".
     { iDestruct (agree_slice_with_map mbs mprops sn' _
          (bor_state_fml sn (Borrow al {[default_dead]})) with "[]") as "EqSlice".
        { intuition. } { apply Hmbssn'. } { iFrame "#". }
       iFrame. iFrame "#".
     }
     
    assert (delete sn' mbs !! sn2 = None) as Hdelsn'. {
      eapply lookup_insert_delete_boxmap_helper2. apply Hsn2None.
    }
     
    iDestruct ((llfb_fb_vs_for_reborrow γ γo γd alive dead outlives
        (delete sn' mbs) _ sn sn2 al al' dd Px Hne2 Halive_disj_dead Hdddead _ _ Hdelsn') with "[vs]") as "vs".
     { iFrame "vs". iDestruct (agree_slice_with_map mbs mprops sn _ Px with "[]") as "EqSlice".
        { intuition. } { apply Hmbssn. } { iFrame "#". }
       rewrite lookup_delete_ne; trivial. }
      
    iModIntro. iExists sn2.
    iFrame "OwnBor2". iFrame "slice2". iFrame "Modulo".
    iExists (<[sn2:=Borrow (al ∪ al') dd]> (<[sn:=Borrow al al']> (delete sn' mbs))).
    iExists (<[sn2:=Px]> (<[sn:=Px]> (delete sn (delete sn' mprops)))).
    iExists (bor_sem Px ∗ Ptotal')%I.
    iExists outlives.
    iFrame "auth". iFrame "outlives". iFrame "vs".
    iSplitL "box". {
        rewrite boxmap_insert_Borrow. rewrite boxmap_insert_Borrow. rewrite boxmap_delete.
        rewrite bool_decide_eq_true_2.
        2: { split.  { set_solver. } unfold inv.map_wf in Hwf. set_solver. }
        rewrite bool_decide_eq_false_2. 
        2: { intuition. }
        iFrame "box".
    }
    iSplitL. { iPureIntro. 
      split. { rewrite dom_insert_L. rewrite dom_insert_L. rewrite dom_insert_L.
        rewrite dom_insert_L. rewrite dom_delete_L. rewrite dom_delete_L.
        rewrite dom_delete_L.
        rewrite Hdom.
        apply set_eq. intros x.
        destruct (decide (x = sn')); destruct (decide (x = sn)); set_solver.
      }
      split. {
        apply map_wf_insert; trivial. 2: { set_solver. }
        apply map_wf_insert; trivial. 2: { set_solver. }
        apply map_wf_delete; trivial.
      }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice2".
      iApply big_sepM_insert_1. iFrame "sliceP".
      rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm.
      rewrite lookup_delete_Some in Dm. intuition. }
    Unshelve.
    { set_solver. }
    rewrite lookup_delete_ne; trivial.
  Qed.
    
  Lemma outer_unnest alive dead blocked sn sn' al al' Px :
    Delayed γd None
        ∗ (outer_inv γ γo γd alive dead blocked)
        ∗ sinv_tok sn Px
        ∗ OwnBorState γ sn' (Borrow al' {[ default_dead ]})
        ∗ sinv_tok sn' (bor_state_fml sn (Borrow al {[ default_dead ]}))
      -∗ |=[box_wsat bor_sem]=> ∃ sn2,
    Delayed γd None
        ∗ (outer_inv γ γo γd alive dead blocked)
        ∗ OwnBorState γ sn2 (Borrow (al ∪ al') {[ default_dead ]})
        ∗ sinv_tok sn2 Px.
  Proof.
    iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_unnest alive dead blocked sn sn' al al' Px with "[H Inv]") as (sn2) "[Inv H]". { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.

End FullBorrows.
