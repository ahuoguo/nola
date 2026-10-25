(** * Ported from VerusBelt ([lifetime/lifetime_internals/reborrow.v], MIT,
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
  
 
  Lemma future_vs_create_empty alive dead outlives mbs mprops sn Px dd :
  ¬(dd ## dead) →
  (mbs !! sn = None) →
  future_vs γlt γ alive dead outlives mbs mprops
  ⊢ future_vs γlt γ alive dead outlives (<[sn:=Borrow ∅ dd]> mbs) (<[sn:=Px]> mprops).
  Proof using γlt invGS_gen0 Σ γ γd γo.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdd Hmbssn) "Hvs".
    
    rewrite future_vs_def.
    rewrite (future_vs_def γlt γ my_alive).
    
    iIntros (k) "%Hin_my_alive #Dead". iSplit.
      { iIntros "NotSwell". iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[Hvs _]".
        iApply IH. { intuition. } { set_solver. } { trivial. }
        iApply "Hvs". iFrame.
      }
    iIntros "inval".
    iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[_ Hvs]".
    
    iDestruct (full_borrows_invalidated_via_insert_false my_alive my_dead k sn mbs mprops (Borrow ∅ dd) Px with "inval") as "inval"; trivial.
    
    iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }
    
    iModIntro.
    
    iSplitL "reval". {
      iApply full_borrows_revalidated_via_insert_false; trivial.
      unfold revalidated. rewrite bool_decide_eq_false. set_solver.
    }
    
    iApply IH; trivial. { set_solver. } { set_solver. }
  Qed.
  
  Lemma inner_borrow_create_empty alive dead blocked Px :
      (inner_inv γlt γ γo alive dead blocked) ∗ (bor_sem Px)
        -∗ |=[box_wsat bor_sem]=>
        ∃ sn , (inner_inv γlt γ γo alive dead blocked)
            ∗ OwnBorState γ sn (Borrow ∅ {[ default_dead ]})
            ∗ sinv_tok sn Px.
  Proof using γlt invGS_gen0 Σ γ γd γo.
    iIntros "[Inv P]".
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [Modulo [#DeadsLt [box [vs [%pures [#slices outlives]]]]]]]".
    
    iMod (slice_insert_full (f := boxmap alive dead mbs) (P := Ptotal) Px with "P box") as (sn) "[%Hisnone [#slice box]]".
    assert (mbs !! sn = None) as Hmbssn. {
      destruct (mbs !! sn) eqn:Heqn; trivial.
      rewrite lookup_fmap in Hisnone. rewrite Heqn in Hisnone. discriminate.
    }
    iMod (alloc_bor_state γ sn mbs (Borrow ∅ {[ default_dead ]}) with "auth") as "[auth OwnBor]"; trivial.
    
    assert (default_dead ∈ dead) as Hdd. { unfold inv.map_wf in pures. intuition. }
    assert (¬({[default_dead]} ## dead)) as Hdd2. { set_solver. }
    
    iDestruct ((future_vs_create_empty alive dead outlives mbs mprops sn Px {[default_dead]} Hdd2 Hmbssn) with "vs") as "vs".
    
    iModIntro. iExists sn. iFrame "OwnBor". iFrame "slice". iFrame "Modulo".
    iExists (<[sn:=Borrow ∅ {[default_dead]}]> mbs).
    iExists (<[sn:=Px]> mprops).
    iExists (bor_sem Px ∗ Ptotal)%I.
    iExists outlives.
    iFrame "auth".
    try iFrame "DeadsLt". iSplitL "box". { 
      rewrite boxmap_insert_Borrow.
      rewrite bool_decide_eq_true_2. { iFrame. }
      set_solver.
    }
    iFrame "vs". iFrame "outlives".
    
    destruct pures as [Hdom [Hwf Hoc]].
    
    iSplitL. { iPureIntro. 
      split. { rewrite dom_insert_L. rewrite dom_insert_L. rewrite Hdom. trivial. }
      split. { apply map_wf_insert; trivial. { done. } { apply swell_set_default_dead. } set_solver. }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice".
      rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro. trivial. }
  Qed.
  
    
  Lemma llfb_fb_vs_for_reborrow1 alive dead al al' sn sn2 mbs mprops Px k dd :
    (sn ≠ sn2) →
    alive ## dead →
    ¬(dd ## dead) →
    (al' ⊆ alive ∪ dead) →
    mbs !! sn = Some (Borrow al dd) →
    mbs !! sn2 = None →
  full_borrows_invalidated_via alive dead k
                (<[sn2:=Borrow (al ∪ al') dd]> (<[sn:=Borrow al al']> (delete sn mbs)))
                (<[sn2:=Px]> (<[sn:=Px]> (delete sn mprops)))
      ∗ (mprops !! sn ≡ Some Px)
  ⊢ full_borrows_invalidated_via alive dead k mbs mprops
      ∗ (⌜ al ⊆ alive ∧ k ∉ al ∧ al' ⊆ alive ∧ k ∈ al' ⌝ -∗ bor_sem Px).
  Proof using γlt invGS_gen0 Σ γ γd γo.
    iIntros (Hne Hdisj Halive Hdead Hmbssn Hmbssn2) "[inval #Heq]".
    destruct (decide (k ∈ al ∧ al ⊆ alive)) as [Hin|Hout].
    
    - destruct (decide (al' ⊆ alive)) as [Hsub|Hnotsub].
      + 
      iDestruct (full_borrows_invalidated_via_insert with "inval") as "[P inval]".
      { rewrite lookup_insert_ne; trivial. rewrite lookup_delete_ne; trivial. }
      { unfold invalidated. rewrite bool_decide_eq_true. set_solver. }
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { apply lookup_delete_eq. }
      iDestruct (full_borrows_invalidated_via_delete with "[P inval]") as "inval".
        { apply Hmbssn. } { iFrame "Heq". iFrame "inval". iFrame "P". }
      iFrame. iIntros "%t". exfalso. set_solver.
      +
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { rewrite lookup_insert_ne; trivial. rewrite lookup_delete_ne; trivial. }
      iDestruct (full_borrows_invalidated_via_insert with "inval") as "[P inval]".
      { apply lookup_delete_eq. }
      { unfold invalidated. rewrite bool_decide_eq_true. set_solver. }
      iDestruct (full_borrows_invalidated_via_delete with "[P inval]") as "inval".
        { apply Hmbssn. } { iFrame "Heq". iFrame "inval". iFrame "P". }
      iFrame. iIntros "%t". exfalso. set_solver.
      
    - destruct (decide (al ⊆ alive ∧ k ∉ al ∧ al' ⊆ alive ∧ k ∈ al')) as [Hx|Hy].
      +
      iDestruct (full_borrows_invalidated_via_insert with "inval") as "[P inval]".
      { rewrite lookup_insert_ne; trivial. rewrite lookup_delete_ne; trivial. }
      { unfold invalidated. rewrite bool_decide_eq_true. set_solver. }
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { apply lookup_delete_eq. }
      iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hmbssn. } { unfold invalidated. rewrite bool_decide_eq_false. set_solver. }
      iFrame. iIntros "%Ht". done.
      +
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { rewrite lookup_insert_ne; trivial. rewrite lookup_delete_ne; trivial. }
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { apply lookup_delete_eq. }
      iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hmbssn. } { unfold invalidated. rewrite bool_decide_eq_false. set_solver. }
      iFrame. iIntros "%Ht". exfalso. set_solver.
  Qed.
  
  Lemma llfb_fb_vs_for_reborrow2 alive dead al al' sn sn2 mbs mprops Px k dd :
    (sn ≠ sn2) →
    alive ## dead →
    ¬(dd ## dead) →
    (al' ⊆ alive ∪ dead) →
    mbs !! sn = Some (Borrow al dd) →
    mbs !! sn2 = None →
    full_borrows_revalidated_via alive dead k mbs mprops
      ∗ (mprops !! sn ≡ Some Px)
      ∗ (⌜ al ⊆ alive ∧ k ∉ al ∧ al' ⊆ alive ∧ k ∈ al' ⌝ -∗ bor_sem Px)
    ⊢
    full_borrows_revalidated_via alive dead k
        (<[sn2:=Borrow (al ∪ al') dd]> (<[sn:=Borrow al al']> (delete sn mbs)))
        (<[sn2:=Px]> (<[sn:=Px]> (delete sn mprops))).
  Proof using γlt invGS_gen0 Σ γ γd γo.
    iIntros (Hdisj Halive Hdead Hwfal' Hmbssn Hmbssn2) "[reval [#Heq P]]".
    
    iApply full_borrows_revalidated_via_insert_false.
      { rewrite lookup_insert_ne; trivial. rewrite lookup_delete_ne; trivial. }
      { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
    
    destruct (decide (al ⊆ alive ∧ k ∉ al ∧ al' ⊆ alive ∧ k ∈ al')) as [Ha|Hb].
    - iDestruct ("P" with "[%]") as "P"; trivial.
    
      iApply full_borrows_revalidated_via_insert.
        { rewrite lookup_delete_eq; trivial. } iFrame.
        
      iApply full_borrows_revalidated_via_delete_false.
        { apply Hmbssn. } iFrame.
    -
      iApply full_borrows_revalidated_via_insert_false.
        { rewrite lookup_delete_eq; trivial. } 
        { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
        
      iApply full_borrows_revalidated_via_delete_false.
        { apply Hmbssn. } iFrame.
   Qed.
          
  Lemma llfb_fb_vs_for_reborrow alive dead outlives mbs mprops sn sn2 al al' dd Px :
    (sn ≠ sn2) →
    alive ## dead →
    ¬(dd ## dead) →
    (al' ⊆ alive ∪ dead) →
    mbs !! sn = Some (Borrow al dd) →
    mbs !! sn2 = None →
    future_vs γlt γ alive dead outlives mbs mprops
      ∗ (mprops !! sn ≡ Some Px)
    ⊢ 
    future_vs γlt γ alive dead outlives
      (<[sn2:=Borrow (al ∪ al') dd]> (<[sn:=Borrow al al']> mbs))
      (<[sn2:=Px]> (<[sn:=Px]> (delete sn mprops))).
  Proof using γlt invGS_gen0 Σ γ γd γo.
    replace (<[sn:=Borrow al al']> mbs) with (<[sn:=Borrow al al']> (delete sn mbs)).
      2: { apply map_eq. { intros i. destruct (decide (sn = i)).
          - subst sn. rewrite lookup_insert_eq. rewrite lookup_insert_eq. trivial.
          - rewrite lookup_insert_ne; trivial. rewrite lookup_insert_ne; trivial.
              rewrite lookup_delete_ne; trivial. } }
  
    intros Hne.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdisj Hdead Hwfal Hmbssn Hmbssn2) "[Hvs #Heq]".
    
    rewrite future_vs_def.
    rewrite (future_vs_def γlt γ my_alive).
    iIntros (k) "%Hin_my_alive Dead". iSplit.
      { iIntros "NotSwell". iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[Hvs _]".
        iApply IH. { intuition. } { set_solver. } { set_solver. }
        { intro x. destruct (decide (x = k)); set_solver. }
        { trivial. } { trivial. }
        iFrame "#". iApply "Hvs". iFrame.
      }
    iIntros "inval".

    iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "Hvs".
    destruct Hin_my_alive as [Hin_my_alive Hoc].
    
    iDestruct (llfb_fb_vs_for_reborrow1 my_alive my_dead al al' sn sn2 mbs mprops Px k dd with "[inval]") as "[inval P]"; trivial. { iFrame. iFrame "Heq". }
     
    iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }

    iModIntro.
    
    iSplitL "P reval". { iApply llfb_fb_vs_for_reborrow2; trivial. iFrame. iFrame "Heq". }
    
    iApply IH; trivial. { set_solver. } { set_solver. }
      { intro x. destruct (decide (x = k)); set_solver. }
    iFrame. iFrame "#".
  Qed.
  
  Lemma lemma_set5 (al dd' alive dead : gset lt_atom) :
    al ∪ dd' ⊆ alive ∪ dead →
    al ## dead →
    al ⊆ alive. Proof. set_solver. Qed.
    
  Lemma lemma_set6 (al' dd' alive dead : gset lt_atom) :
    al'  ⊆ alive ∪ dead →
    al' ## dead →
    al' ⊆ alive. Proof. set_solver. Qed.
            
  Lemma inner_reborrow alive dead blocked Px sn al al' :
      swell_set al' →
      (al' ⊆ alive ∪ dead) →
      (inner_inv γlt γ γo alive dead blocked)
        ∗ OwnBorState γ sn (Borrow al {[default_dead]})
        ∗ sinv_tok sn Px
        -∗ |=[box_wsat bor_sem]=> ∃ sn1 sn2,
      (inner_inv γlt γ γo alive dead blocked)
        ∗ OwnBorState γ sn1 (Borrow (al ∪ al') {[default_dead]})
        ∗ OwnBorState γ sn2 (Borrow al al')
        ∗ sinv_tok sn1 Px
        ∗ sinv_tok sn2 Px.
  Proof using γlt invGS_gen0 Σ γ γd γo.
    intros swell_al' Hal'wf.
    iIntros "[Inv [OwnBor #sliceP]]".
    destruct (decide (al ## dead)) as [Hdisj|Hndisj].
    2: {
      iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [Modulo [#DeadsLt [box [vs [#pures [#slices outlives]]]]]]]".
      iMod (inner_fake γ alive dead blocked (al ∪ al') {[default_dead]} Px with "Modulo") as (sn1) "[Modulo [A Aslice]]". { set_solver. }
      iMod (inner_fake γ alive dead blocked al al' Px with "Modulo") as (sn2) "[Modulo [B Bslice]]". { set_solver. }
      iModIntro. iExists sn1. iExists sn2. iFrame. iFrame "#".
    }
    
    destruct (decide (al' ## dead)) as [Hdisj'|Hndisj].
    2: {
      iDestruct (inv_get_dead with "Inv") as "%Hdd".
      iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [Modulo [#DeadsLt [box [vs [#pures [#slices outlives]]]]]]]".
      iMod (inner_fake γ alive dead blocked (al ∪ al') {[default_dead]} Px with "Modulo") as (sn1) "[Modulo [A Aslice]]". { set_solver. }
      
      assert (∃ x , x ∈ al' ∩ dead) as Hex_x. { apply set_choose_L; set_solver. }
      destruct Hex_x as [x Hex].
      iDestruct (get_all_modulo_dead_pers γlt γ dead with "DeadsLt Modulo") as "[Modulo #Deads]".
      iMod (update_bor_state_borrow_fix_dead' γlt γ sn al {[default_dead]} al' default_dead x with "[OwnBor]") as "OwnBor2"; trivial. { set_solver. } { set_solver. } {
        iFrame. iSplitL.
          { iApply "Deads". iPureIntro. trivial. }
          { iApply "Deads". iPureIntro. set_solver. }
      }
      
      iModIntro. iExists sn1. iExists sn. iFrame. iFrame "#".
    }
   
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [Modulo [#DeadsLt [box [vs [%pures [#slices outlives]]]]]]]".
    
    iDestruct (agree_bor_state_borrow_lts γ sn mbs dead al {[default_dead]}
        with "[Modulo auth OwnBor]") as (dd') "[%Hmbssn %Hrel_dd]". { set_solver. } { iFrame.    }
        
    destruct pures as [Hdom [Hwf Houtlives]].
    assert (alive ## dead) as Halive_disj_dead. { unfold inv.map_wf in Hwf. intuition. }
    assert (default_dead ∈ dead) as Hdddead. { unfold inv.map_wf in Hwf. intuition. }
    assert (¬ dd' ## dead) as Hdd'dead. { set_solver. }
    assert (al ⊆ alive) as Halalive. { unfold inv.map_wf in Hwf.
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. destruct Hf as [Hf _].
      apply (lemma_set5 al dd' alive dead); trivial.
    }
    assert (al' ⊆ alive) as Hal'alive. { apply (lemma_set6 al' dd' alive dead); trivial. }
    assert (dd' ⊆ alive ∪ dead) as Hdd'wf. { 
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn.
      set_solver.
    }
    have swell_al := swell_set_of_map_wf _ _ _ _ _ _ _ _ Hwf Hmbssn.
    have swell_dd' := swell_set_of_map_wf_de _ _ _ _ _ _ _ _ Hwf Hmbssn.
    have swell_al_al' := swell_set_union _ _ swell_al swell_al'.
        
    iMod (slice_empty (f := boxmap alive dead mbs) (P := Ptotal) (Px := Px) (γ := sn) with "sliceP box")
      as "[P box]"; trivial.
    {
      unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. simpl. f_equiv.
      rewrite bool_decide_eq_true. set_solver.
    }
        
    iMod (slice_insert_full (f := <[sn:=false]> (boxmap alive dead mbs)) (P := Ptotal) Px with "P box")
      as (sn2) "[%Hlookup_sn2 [#slice box]]".
    
    destruct (lookup_insert_boxmap_helper3 sn false alive dead mbs sn2 Hlookup_sn2) as [Hmbssn2 Hne].
    iMod (update_bor_state_borrow_lts γ sn _ dead al {[default_dead]} (Borrow al al') with "[Modulo auth OwnBor]") as "[Modulo [auth OwnBor]]". { set_solver. } { iFrame "auth". iFrame. }
    
    iMod (alloc_bor_state γ sn2 (<[sn:=Borrow al al']> mbs) (Borrow (al ∪ al') dd') with "[auth]") as "[auth OwnBor2]"; trivial. { rewrite lookup_insert_ne; trivial. }
    iMod (update_bor_state_borrow_fix_dead_lts γ dead sn2 (al ∪ al') dd' {[default_dead]} with "[Modulo OwnBor2]") as "[Modulo OwnBor2]". { set_solver. } { set_solver. } { iFrame. }
    
    iDestruct ((llfb_fb_vs_for_reborrow alive dead outlives mbs mprops sn sn2 al al' dd' Px Hne Halive_disj_dead Hdd'dead Hal'wf Hmbssn Hmbssn2)
     with "[vs]") as "vs"; trivial. { iFrame. iDestruct (agree_slice_with_map mbs mprops sn _ Px with "[]") as "EqSlice"; trivial.
      { apply Hmbssn. } iFrame "#". }
        
    iModIntro.
    iExists sn2. iExists sn.
    iFrame "OwnBor". iFrame "OwnBor2". iFrame "slice". iFrame "sliceP". iFrame "Modulo".
    iExists (<[sn2:=Borrow (al ∪ al') dd']> (<[sn:=Borrow al al']> mbs)).
    iExists (<[sn2:=Px]> (<[sn:=Px]> (delete sn mprops))).
    iExists (bor_sem Px ∗ Ptotal)%I.
    iExists outlives.
    iFrame "outlives". iFrame "auth".
    try iFrame "DeadsLt". iSplitL "box". {
      rewrite boxmap_insert_Borrow.
      rewrite boxmap_insert_Borrow.
      rewrite bool_decide_eq_true_2.
      - rewrite bool_decide_eq_false_2.
        + iFrame "box". 
        + set_solver.
      - set_solver.
    }
    iFrame "vs".
    iSplitL. { iPureIntro. 
      split. { rewrite dom_insert_L. rewrite dom_insert_L. rewrite dom_insert_L.
      rewrite dom_insert_L. rewrite dom_delete_L. rewrite Hdom.
        apply set_eq. intros x.
        destruct (decide (x = sn2)); destruct (decide (x = sn)); set_solver.
      }
      split. {
        apply map_wf_insert; trivial. 2: { set_solver. }
        apply map_wf_insert; trivial. set_solver.
      }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice".
      iApply big_sepM_insert_1. iFrame "sliceP".
      rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm. intuition.
    }
   Qed.
 
  
   Lemma inner_borrow_create alive dead blocked lt Px :
      swell_set lt →
      (lt ⊆ alive ∪ dead) →
      (inner_inv γlt γ γo alive dead blocked)
        ∗ LtState γlt alive dead
        ∗ (bor_sem Px)
        -∗ |=[box_wsat bor_sem]=>
        ∃ sn sn2, (inner_inv γlt γ γo alive dead blocked)
            ∗ LtState γlt alive dead
            ∗ OwnBorState γ sn (Borrow lt {[ default_dead ]})
            ∗ OwnBorState γ sn2 (Borrow ∅ lt)
            ∗ sinv_tok sn Px
            ∗ sinv_tok sn2 Px.
  Proof using γlt invGS_gen0 Σ γ γd γo.
    intros swell_lt Hlt. iIntros "[Inv [LtState P]]".
    iMod (inner_borrow_create_empty alive dead blocked Px with "[Inv P]") as (sn) "[Inv [OwnBor #slice]]". { iFrame. }
    iMod (inner_reborrow alive dead blocked Px sn ∅ lt swell_lt Hlt with "[Inv OwnBor]") as (sn1 sn2) "[Ha [Hb [Hd [He Hf]]]]".
      { iFrame. iFrame "#". }
    iModIntro. iExists sn1. iExists sn2. iFrame. replace (∅ ∪ lt) with lt by set_solver.
    iFrame.
  Qed.

  Lemma outer_borrow_create alive dead blocked lt Px :
      swell_set lt →
      (lt ⊆ alive ∪ dead) →
      Delayed γd None
        ∗ (outer_inv γlt γ γo γd alive dead blocked)
        ∗ LtState γlt alive dead
        ∗ (bor_sem Px)
        -∗ |=[box_wsat bor_sem]=>
      Delayed γd None ∗
      ∃ sn sn2, (outer_inv γlt γ γo γd alive dead blocked)
          ∗ LtState γlt alive dead
          ∗ OwnBorState γ sn (Borrow lt {[ default_dead ]})
          ∗ OwnBorState γ sn2 (Borrow ∅ lt)
          ∗ sinv_tok sn Px
          ∗ sinv_tok sn2 Px.
  Proof.
    intros swell_lt Hlt. iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_borrow_create alive dead blocked lt Px swell_lt Hlt with "[H Inv]") as (sn sn2) "[Inv H]". { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
      
  Lemma outer_reborrow alive dead blocked Px sn al al' :
      swell_set al' →
      (al' ⊆ alive ∪ dead) →
      Delayed γd None
       ∗ (outer_inv γlt γ γo γd alive dead blocked)
        ∗ OwnBorState γ sn (Borrow al {[default_dead]})
        ∗ sinv_tok sn Px
        -∗ |=[box_wsat bor_sem]=> ∃ sn1 sn2,
      Delayed γd None
        ∗ (outer_inv γlt γ γo γd alive dead blocked)
        ∗ OwnBorState γ sn1 (Borrow (al ∪ al') {[default_dead]})
        ∗ OwnBorState γ sn2 (Borrow al al')
        ∗ sinv_tok sn1 Px
        ∗ sinv_tok sn2 Px.
  Proof.
    intros swell_al' Hal.
    iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_reborrow alive dead blocked Px sn al al' swell_al' Hal with "[H Inv]") as (sn1 sn2) "[P H]"; trivial. { iFrame. }
    iModIntro. iExists sn1. iExists sn2.
    iFrame "Delayed". iFrame "H". iExists None. iFrame.
  Qed.
End FullBorrows.
