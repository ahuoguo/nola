(** * Permission cells

  Ported from VerusBelt ([typing/pcell.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer).

  The [▷]s in front of the inner type's ghost assertion and the credits and
  time receipts that strip them are gone; the depth arithmetic that sized
  them (the [leaf_goal laters to …] steps) goes with them.  The ghost
  assertions are formulas, so the one piece of ghost state they name -
  ownership of a vector of cells - is asked for as [PcellFml]. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.lang.lib Require Import memcpy.
From nola.alerus.lang Require Import heap.
From nola.alerus.typing Require Export type own product sum shr_bor uniq_bor
  uniq_util int bool.
From nola.alerus.typing Require Import uninit type_context programs
  programs_util programs_util_atomic tracked freeable_util lft_contexts ctx.
From nola.alerus.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation WpwNotation.

Implicit Type 𝔄 𝔅: syn_type.

Section pcell.
  Context `{!typeG FML Σ}.

  (** Ownership of a vector of cells, as a formula *)
  Class PcellFml := {
    cellsvec_fml : list cell_id → list fancy_val → FML $oi Σ;
    cellsvec_fml_sem cs fv :
      bor_sem (cellsvec_fml cs fv) ⊣⊢ cs ^↦!∗ fv;
    (** The constructor means the same at every candidate interpretation;
      see [AltSem] in [typing/ctx.v]. *)
    cellsvec_sem_at {sem} : alt_sem sem → ∀ cs fv,
      sem (cellsvec_fml cs fv) ⊣⊢ cs ^↦!∗ fv;
  }.
  Context `{!PcellFml}.

  (** [guard_cloc_combine_fancy'] for stored guards *)
  Lemma dguard_cloc_combine_fancy' {Px} (l : cloc) (γs : list cell_id)
      (fv : list fancy_val) :
    dguard Px (cells_fml l.1 l.2 (FCell <$> γs)) -∗
    dguard Px (cellsvec_fml γs fv) -∗
    dguard Px (cells_fml (cloc_flat_insert l γs).1
                 (cloc_flat_insert l γs).2 fv).
  Proof.
    have ? := guard_fml_pers_at alt_here.
    iIntros "#g1 #g2". iApply dguard_of_all. iIntros (sem' Hs Hi).
    iDestruct (guard_fml_sem_into alt_here Hs Hi with "g1") as "#G1".
    iDestruct (guard_fml_sem_into alt_here Hs Hi with "g2") as "#G2".
    iDestruct (guard_rhs_iff (cells_sem_at Hs _ _ _) with "G1") as "#G1'".
    iDestruct (guard_rhs_iff (cellsvec_sem_at Hs _ _) with "G2") as "#G2'".
    have Heq : (cloc_flat_insert l γs).1 ↦[^ (cloc_flat_insert l γs).2 ]!∗ fv
      ⊣⊢ sem' (cells_fml (cloc_flat_insert l γs).1
                 (cloc_flat_insert l γs).2 fv).
    { by rewrite (cells_sem_at Hs). }
    iApply (guard_rhs_iff Heq).
    iApply (guard_cloc_combine_fancy' with "G1' G2'").
  Qed.

  Program Definition pcell_ty n : type (pcellₛ n) :=
    {| ty_size := n;
       ty_lfts := [];
       ty_E := [];
       ty_ghox x _ _ _ := pure_fml (length x = n);
       ty_gho_persx x _ _ _ := pure_fml (length x = n);
       ty_phys (cell_ids: ~~ (pcellₛ n)) _ := pad (FCell <$> cell_ids) n;
    |}.
  Next Obligation. move=> n v tid. by rewrite length_pad. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move=> ? sem Hsm *. by iIntros "$". Qed.
  Next Obligation. move=> ? sem Hsm *. by iIntros "$". Qed.
  Next Obligation. iIntros "* _ _ _ _ _ !>" (ξ) "%Hin". set_solver. Qed.
  Next Obligation. move=> ? sem Hsm *. rewrite (pure_sem_at Hsm). exact _. Qed.
  Next Obligation. move=> *. by iIntros "$". Qed.

  Lemma pcell_ty_gho n x d g tid :
    ty_gho (pcell_ty n) x d g tid ⊣⊢ ⌜length x = n⌝.
  Proof. apply pure_fml_sem. Qed.
  Lemma pcell_ty_gho_pers n x d g tid :
    ty_gho_pers (pcell_ty n) x d g tid ⊣⊢ ⌜length x = n⌝.
  Proof. apply pure_fml_sem. Qed.

  Global Instance pcell_send n: Send (pcell_ty n).
  Proof.
    split.
    - move=> tid tid' x x' /= ->. done.
    - move=> tid tid' x d g G κs. iIntros "_ _ lfts _ G gho $ !>".
      iExists x, 0%nat. rewrite Nat.add_0_r. by iFrame "lfts G gho".
  Qed.

  Global Instance pcell_sync n: Sync (pcell_ty n).
  Proof. move=> *. split; [done|]. split; reflexivity. Qed.
End pcell.

Global Hint Rewrite @pcell_ty_gho @pcell_ty_gho_pers : fml_sem.

Section points_to.
  Context `{!typeG FML Σ, !PcellFml}.

  Program Definition cell_points_to_ty {𝔄} (ty: type 𝔄)
      : type (trackedₛ (pcellₛ (ty.(ty_size)) * 𝔄)) :=
    {| ty_size := 0%nat;
       ty_lfts := ty.(ty_lfts);
       ty_E := ty.(ty_E);
       ty_ghox x d g tid := [Sx(d') := d]
         (cellsvec_fml x.1 (ty.(ty_phys) x.2 tid) ∗
          ty.(ty_ghox) x.2 d' g tid)%FML;
       ty_gho_persx x d g tid := [Sx(d') := d]
         (pure_fml (length x.1 = ty_size ty) ∗
          ty.(ty_gho_persx) x.2 d' g tid)%FML;
       ty_phys _ _ := [];
    |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> ? ty sem Hsm d g d' g' x tid ??.
    destruct d as [|d0]; [rewrite /= (false_sem_at Hsm); by iIntros "[]"|].
    destruct d' as [|d0']; [lia|]. rewrite /= !(sep_sem_at Hsm).
    iIntros "[$ gho]".
    iApply (ty_gho_depth_mono_at ty sem Hsm with "gho"); lia.
  Qed.
  Next Obligation.
    move=> ? ty sem Hsm d g d' g' x tid ??.
    destruct d as [|d0]; [rewrite /= (false_sem_at Hsm); by iIntros "[]"|].
    destruct d' as [|d0']; [lia|]. rewrite /= !(sep_sem_at Hsm).
    iIntros "[$ gho]".
    iApply (ty_gho_pers_depth_mono_at ty sem Hsm with "gho"); lia.
  Qed.
  Next Obligation.
    move=> ? ty κ x d g tid R. rewrite !by_succx_sem.
    destruct d as [|d']; [by iIntros "_ _ []"|].
    rewrite /= !bor_sep_sem.
    iIntros "#LFT #Incl [_ Pers] #Gk #Ggho".
    iApply (ty_guard_proph _ ty κ x.2 d' g tid R with "LFT Incl Pers Gk").
    iApply (guard_rhs_sep_r with "Ggho").
  Qed.
  Next Obligation.
    move=> ? ty sem Hsm x d g tid.
    apply (by_succx_persistent_at Hsm)=> d'.
    have ? := pure_pers_at Hsm. have ? := sep_pers_at Hsm.
    have ? := ty_gho_pers_pers_at ty sem Hsm. exact _.
  Qed.
  Next Obligation.
    move=> ? ty x d g tid. rewrite !by_succx_sem.
    destruct d as [|d']; [by iIntros "[]"|]. rewrite /= !bor_sep_sem.
    iIntros "[A1 A2]".
    iDestruct (cellsvec_fml_sem with "A1") as "A1".
    iDestruct (cells_points_to_fancy_vec_length_eq with "A1") as %Hlen.
    rewrite (ty_size_eq ty) in Hlen.
    iSplitR; [by iApply pure_fml_sem_2|].
    by iApply ty_gho_pers_impl.
  Qed.

  Lemma cell_points_to_gho {𝔄} (ty: type 𝔄) x d g tid :
    ty_gho (cell_points_to_ty ty) x d g tid ⊣⊢ [S(d') := d]
      (x.1 ^↦!∗ ty_phys ty x.2 tid ∗ ty_gho ty x.2 d' g tid).
  Proof.
    rewrite /ty_gho by_succx_sem. destruct d as [|d']; [done|].
    by rewrite /= bor_sep_sem cellsvec_fml_sem.
  Qed.
  Lemma cell_points_to_gho_pers {𝔄} (ty: type 𝔄) x d g tid :
    ty_gho_pers (cell_points_to_ty ty) x d g tid ⊣⊢ [S(d') := d]
      (⌜length x.1 = ty_size ty⌝ ∗ ty_gho_pers ty x.2 d' g tid).
  Proof.
    rewrite /ty_gho_pers by_succx_sem. destruct d as [|d']; [done|].
    by rewrite /= bor_sep_sem pure_fml_sem.
  Qed.

  Global Instance cell_points_to_send {𝔄} (ty: type 𝔄) :
    Send ty → Send (cell_points_to_ty ty).
  Proof.
    move=> [Hphys Hgho]. split; [done|].
    move=> tid tid' x d g G κs. iIntros "LFT UNIQ lfts #gs G gho W".
    rewrite cell_points_to_gho.
    destruct d as [|d]; [by iDestruct "gho" as "[]"|].
    iDestruct "gho" as "[Hown gho]".
    iMod (Hgho with "LFT UNIQ lfts gs G gho W")
      as "(W & %x' & %off & gho & %Habs & lfts & G)".
    iModIntro. iFrame "W". iExists (x.1, x'), off. iFrame "lfts G".
    rewrite cell_points_to_gho /=.
    rewrite -(Hphys tid tid' x.2 x' (eq_sym Habs)). iFrame "Hown gho".
    iPureIntro. simpl. by rewrite Habs.
  Qed.

  Global Instance cell_points_to_sync {𝔄} (ty: type 𝔄) :
    Sync ty → Sync (cell_points_to_ty ty).
  Proof.
    move=> HSync tid tid' x d g. split; [done|].
    destruct d as [|d']; [done|].
    have [Hp [Hg Hgp]] := HSync tid tid' x.2 d' g.
    split=>/=; [rewrite Hp Hg|rewrite Hgp]; done.
  Qed.
End points_to.

Section typing.
  Context `{!typeG FML Σ, !PcellFml}.

  Definition PCellFromOwn : val := (λ: ["p"], "p")%V.

  Lemma typed_pcell_from_own {𝔄} (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ own_ptr (ty_size ty) ty] (PCellFromOwn [p])
      (λ v, +[v ◁ own_ptr (ty_size ty)
                 (prod_ty (pcell_ty (ty_size ty)) (cell_points_to_ty ty))])
      (λ post '-[(l, x)], λ mask π, ∀ cell_ids : list positive,
        post -[(l, (cell_ids, (cell_ids, x)))] mask π).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #PROPH #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [[l x][]]. iDestruct "TY" as "(TY & _)".
    iDestruct "TY" as (pl d Heval) "[Hown %Hphys]".
    simpl in Hphys. inversion Hphys; subst pl.
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite own_ptr_gho /=. iDestruct "Hown" as "(Hl & Hfree & Hgho)".
    iApply twpw_fupdw_nonval; [done|].
    wp_bind p. iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    wp_rec. iIntros "W".
    iMod (cell_alloc2 with "Hl") as (γs Hlen) "H↦".
    iDestruct (bi.equiv_entails_1_1 _ _
      (heap_mapsto_cells_to_complete_mapsto_fancy_vec
         (l, (λ γ : cell_id, [γ]) <$> γs) (ty_phys ty x tid)) with "H↦")
      as "[Hchain Htail]".
    iDestruct (bi.equiv_entails_1_1 _ _ (heap_complete_mapsto_vec_eq l γs)
      with "Hchain") as "Hchain".
    iDestruct (bi.equiv_entails_1_1 _ _
      (heap_complete_mapsto_fancy_val_vec_eq' l γs (ty_phys ty x tid))
      with "Htail") as "Htail".
    rewrite ty_size_eq in Hlen.
    iModIntro. iFrame "W L I". iExists -[(l, (γs, (γs, x)))].
    iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> ? Ha. apply Ha. }
    iSplit; [|done]. iExists #l, (S (S d)). iSplit; [done|].
    rewrite /ty_own own_ptr_gho /= prod_ty_gho /= pcell_ty_gho
      cell_points_to_gho /= Nat.add_0_r app_nil_r.
    rewrite (pad_length' (FCell <$> γs) (ty_size ty));
      [|by rewrite length_fmap Hlen].
    iDestruct (ty_gho_depth_mono ty d (S d) d (S (S d)) x tid with "Hgho")
      as "Hgho"; [lia|lia|].
    iFrame "Hchain Hfree Htail Hgho". by iSplit.
  Qed.

  Definition PCell2Own : val := (λ: ["pcell"; "perm"], "pcell")%V.

  Lemma typed_pcell_to_own {𝔄} (perm pcell : path) (ty : type 𝔄) E L I :
    typed_instr E L I
      +[pcell ◁ own_ptr (ty_size ty) (pcell_ty (ty_size ty));
        perm ◁ own_ptr 0 (cell_points_to_ty ty)]
      (PCell2Own [pcell; perm]) (λ v, +[v ◁ own_ptr (ty_size ty) ty])
      (λ post '-[(l, γs); (_, (γs', x))], λ mask π,
        γs = γs' ∧ post -[(l, x)] mask π).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #PROPH #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [[l γs] [[l' [γs' x]] []]].
    iDestruct "TY" as "(Hpcell & Hperm & _)".
    iDestruct "Hpcell" as (pl d Heval) "[Hown %Hphys]".
    iDestruct "Hperm" as (pl' d' Heval') "[Hown' %Hphys']".
    simpl in Hphys, Hphys'. inversion Hphys; subst pl.
    inversion Hphys'; subst pl'.
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    destruct d' as [|d'];
      [by iDestruct (false_fml_sem_1 with "Hown'") as "[]"|].
    rewrite own_ptr_gho /= pcell_ty_gho.
    iDestruct "Hown" as "(H↦ & Hfree & %Hlen)".
    rewrite own_ptr_gho /=. iDestruct "Hown'" as "(_ & _ & Hown')".
    rewrite cell_points_to_gho.
    destruct d' as [|d''];
      [by iDestruct "Hown'" as "[]"|].
    iDestruct "Hown'" as "[H↦' Hgho]".
    iApply twpw_fupdw_nonval; [done|].
    wp_bind pcell. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_bind perm.
    iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    wp_rec. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [<- _]]; [solve_ndisj|].
    rewrite (pad_length' (FCell <$> γs) (ty_size ty));
      [|by rewrite length_fmap Hlen].
    iDestruct (bi.equiv_entails_1_2 _ _
      (heap_complete_mapsto_fancy_val_vec_eq' l γs (ty_phys ty x tid))
      with "H↦'") as "H↦'".
    iMod (heap_delete_cell with "H↦ H↦'") as "H↦".
    iModIntro. iFrame "W L I". iExists -[(l, x)].
    iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> ? [_ Ha]. apply Ha. }
    iSplit; [|done]. iExists #l, (S (S d'')). iSplit; [done|].
    rewrite /ty_own own_ptr_gho /=.
    iDestruct (ty_gho_depth_mono ty d'' (S (S d'')) (S d'') (S (S d'')) x tid
      with "Hgho") as "Hgho"; [lia|lia|].
    by iFrame "H↦ Hfree Hgho".
  Qed.

  Lemma pcell_ty_gho_phys n (γs : ~~(pcellₛ n)) tid :
    length γs = n →
    ∀ (l : cloc), (l.1 ↦[^ l.2 ]!∗ ty_phys (pcell_ty n) γs tid) ⊣⊢
      (l.1 ↦[^ l.2 ]!∗ (FCell <$> γs)).
  Proof.
    move=> Hlen l. rewrite /= (pad_length' (FCell <$> γs) n) //.
    by rewrite length_fmap Hlen.
  Qed.

  Definition PCellBorrow : val := (λ: ["pcell_ref"; "perm_ref"], "pcell_ref")%V.

  (** The original splits into two symmetric branches on which of the two
    depths is larger, because it has to pick the receipt that pays for the
    [▷]s in front of the shared ghost assertions.  There are none here, so
    one branch does. *)
  Lemma typed_pcell_borrow {𝔄} κ (pcell_ref perm_ref : path) (ty : type 𝔄)
      E L I :
    typed_instr E L I
      +[pcell_ref ◁ shr_bor κ (pcell_ty (ty_size ty));
        perm_ref ◁ shr_bor κ (cell_points_to_ty ty)]
      (PCellBorrow [pcell_ref; perm_ref]) (λ v, +[v ◁ shr_bor κ ty])
      (λ post '-[(l, γs); (_, (γs', x))], λ mask π,
        γs = γs' ∧ post -[(cloc_flat_insert l γs, x)] mask π).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #PROPH #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [[l γs] [[l' [γs' x]] []]].
    iDestruct "TY" as "(Hcell & Hperm & _)".
    iDestruct "Hcell" as (pl d Heval) "[Hshr %Hphys]".
    iDestruct "Hperm" as (pl' d' Heval') "[Hshr' %Hphys']".
    simpl in Hphys, Hphys'. inversion Hphys; subst pl.
    inversion Hphys'; subst pl'.
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd0 gg0 Hdd0 Hgg0)
      "#(Hpt & _ & Hst0)".
    iDestruct (shr_bor_gho_elim with "Hshr'") as (dd1 gg1 Hdd1 Hgg1)
      "#(_ & Hghoshr & Hst1)".
    iApply twpw_fupdw_nonval; [done|].
    wp_bind pcell_ref. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_bind perm_ref.
    iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    wp_rec. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [<- _]]; [solve_ndisj|].
    (* Both shared borrows keep their persistent part behind a judgment, so
       they are opened here, where the world satisfaction is at hand. *)
    iDestruct (wsat_split (W:=alerus_wsat) (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (store_fml_acc with "Hst0") as "#Acc0".
    iDestruct ("Acc0" with "Wg") as "[Wg #Hlen0]".
    rewrite pure_fml_sem. iDestruct "Hlen0" as %Hlen.
    iDestruct (store_fml_acc with "Hst1") as "#Acc1".
    iDestruct ("Acc1" with "Wg") as "[Wg #Hpers0]".
    rewrite by_succx_sem.
    destruct dd1 as [|d2]; [by iDestruct "Hpers0" as "[]"|]. simpl.
    rewrite bor_sep_sem pure_fml_sem. iDestruct "Hpers0" as "[_ Hpers]".
    iMod (store_ty_gho_pers ty x d2 gg1 tid with "Hpers Wg") as "[Wg #St]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iDestruct (dguard_rhs_sep_l with "Hghoshr") as "#Hcells".
    iDestruct (dguard_rhs_sep_r with "Hghoshr") as "#Hgho".
    iModIntro. iFrame "W L I". iExists -[(cloc_flat_insert l γs, x)].
    iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> ? [_ Ha]. apply Ha. }
    iSplit; [|done]. iExists #l.1, (S (d2 + gg1)). iSplit; [done|].
    rewrite /ty_own. iSplit; [|done].
    iApply (shr_bor_gho_intro_st κ ty (cloc_flat_insert l γs, x) _ _ d2 gg1);
      [lia|lia| | |].
    { have Hph : ∀ sem', alt_sem sem' →
        sem' (cells_fml l.1 l.2 (ty_phys (pcell_ty (ty_size ty)) γs tid)) ⊣⊢
        sem' (cells_fml l.1 l.2 (FCell <$> γs)).
      { move=> sem' Hs. rewrite !(cells_sem_at Hs).
        apply (pcell_ty_gho_phys (ty_size ty) γs tid Hlen l). }
      iDestruct (dguard_rhs_iff Hph with "Hpt") as "#Hpt2".
      iApply (dguard_cloc_combine_fancy' with "Hpt2 Hcells"). }
    { iApply "Hgho". }
    { iApply "St". }
  Qed.

  (** The physical footprint of a permission cell, re-read as the flat
    locations the cells stand for *)
  Lemma pcell_phys_to_flat n (γs : ~~(pcellₛ n)) (cl : cloc) tid :
    length γs = n → length cl.2 = n →
    (cl.1 ↦[^ cl.2 ]!∗ ty_phys (pcell_ty n) γs tid) ⊣⊢
      cloc_flat_insert cl γs #↦∗_.
  Proof.
    move=> Hlen Hlen2. rewrite (pcell_ty_gho_phys n γs tid Hlen cl).
    rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
    rewrite (heap_complete_mapsto_combine γs cl); [done|].
    by rewrite Hlen2 Hlen.
  Qed.

  Definition PCellMutBorrow : val :=
    (λ: ["pcell_ref"; "perm_mut_ref"], "pcell_ref")%V.

  (** As in [typed_pcell_borrow], the original's symmetric case split on which
    of the two depths is the larger only picked the time receipt that paid for
    the [▷]s in front of the shared ghost assertions; one branch does here. *)
  Lemma typed_pcell_borrow_mut {𝔄} κ (pcell_ref perm_mut_ref : path)
      (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[pcell_ref ◁ shr_bor κ (pcell_ty (ty_size ty));
        perm_mut_ref ◁ &uniq{κ} (cell_points_to_ty ty)]
      (PCellMutBorrow [pcell_ref; perm_mut_ref]) (λ v, +[v ◁ &uniq{κ} ty])
      (λ post '-[(cl, γs); m], λ mask π,
        let '(cl', (γs', x), ξi, d, g, idx) := m in γs = γs' ∧ ∀ m',
          uniq_bor_current m' = x →
          uniq_bor_future m' π = (uniq_bor_future m π).2 →
          (uniq_bor_future m π).1 = γs →
          uniq_bor_loc m' = cloc_flat_insert cl γs →
          post -[m'] mask π).
  Proof.
    move=> Alv tid post mask iκs vπl.
    iIntros "#LFT #PROPH #UNIQ #E L I TY #Obs"=>/=.
    iDestruct (Alv with "L E") as "#Alv".
    destruct vπl as [[cl γs] [u []]].
    destruct u as [[[[[cl' [γs' x]] ξi] d] g] ξidx].
    iDestruct "TY" as "(Hcell & Hperm & _)".
    iDestruct "Hcell" as (pl d0 Heval) "[Hshr %Hphys]".
    iDestruct "Hperm" as (pl' d'' Heval') "[Huniq %Hphys']".
    simpl in Hphys, Hphys'. inversion Hphys; subst pl.
    inversion Hphys'; subst pl'.
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd0 gg0 Hdd0 Hgg0)
      "#(Hpt & _ & Hst0)".
    rewrite uniq_bor_gho.
    iDestruct "Huniq" as "(#Incl & %Hineq & UniqBody & #PtBase & #Pers)".
    iApply twpw_fupdw_nonval; [done|].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    (* The shared borrow's persistent part is behind a judgment, so the
       length is read off it here, where the world satisfaction is at hand. *)
    iDestruct (wsat_split (W:=alerus_wsat) (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (store_fml_acc with "Hst0") as "#Acc0".
    iDestruct ("Acc0" with "Wg") as "[Wg #Hlen0]".
    rewrite pure_fml_sem. iDestruct "Hlen0" as %Hlen.
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & [#key f])]".
    iDestruct (Ltok_guard_frac with "key") as "#Gfrac".
    iAssert (frac_tok γ 1 &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "Gfrac Alv"). }
    (* read the length of the cell list off the shared points-to, giving the
      guard back right away *)
    iDestruct (dguard_alive_sem' (cells_fml_sem _ _ _) with "Hpt") as "#Hpt0".
    iDestruct (guard_trans with "Gκ Hpt0") as "#Gpt".
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "Gpt f Wg") as "[pt back]".
    iDestruct (heap_fancy_mapsto_cells_length with "pt") as %Hlen'.
    iDestruct ("back" with "pt") as "[Wg f]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    rewrite /= length_pad in Hlen'.
    iDestruct "Pers" as "[Dead|#Pers]".
    { iDestruct "Dead" as (κ'') "[#Incl0 #Dead']".
      iDestruct (dincl_sem with "Incl0") as "#Incl'".
      iDestruct (guard_trans with "Gκ Incl'") as "#G3".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg' Wr']".
      iDestruct (guard_acc with "G3 f Wg'") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    rewrite cell_points_to_gho_pers /=.
    destruct d as [|d]; [by iDestruct "Pers" as "[]"|].
    iDestruct "Pers" as "[_ Pers']".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [<- _]]; [solve_ndisj|].
    destruct cl' as [cl'1 cs']. destruct cs' as [|cs'0 cs']; last first.
    { (* the permission's own cell list is empty, so this cannot happen *)
      iDestruct "UniqBody" as "(ξVo & ξTok & #ξBor)".
      iDestruct (idxbor_fml_to_full with "ξBor ξTok") as "Bor0".
      iDestruct (dFullBor_exact (E:=⊤) with "LFT Bor0") as "Ex";
        [set_solver|].
      iDestruct (fupdw_incl (W:=alerus_wsat) with "Ex") as "Ex'".
      iMod ("Ex'" with "W") as "[W Bor]".
      iAssert (bor_sem (gsrc_fml (GFrac γ 1)) &&{Wguard}&&> @[κ])%I as "#Gκx".
      { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γ 1))). iApply "Gκ". }
      iDestruct (llftl_bor_acc_guarded ⊤ (gsrc_fml (GFrac γ 1)) κ
        with "LFT Bor Gκx [f]") as "A";
        [by iApply (gsrc_fml_sem_2 (s := GFrac γ 1))|].
      iDestruct (fupdw_incl (W:=alerus_wsat) with "A") as "A'".
      iMod ("A'" with "W") as "[W [P' _]]".
      iEval (rewrite uniq_body_fml_sem) in "P'".
      iDestruct "P'" as (???) "(_ & _ & Hfalse)".
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Hfalse")
        as %Hfalse. by simpl in Hfalse. }
    iDestruct "UniqBody" as "(ξVo & ξTok & #ξBor)".
    have Hinj : Inj eq eq ((!ₛ) (pair_with_cell_idsₛ (𝔄:=𝔄) (ty_size ty) γs))
      by move=> ??[=].
    have Hmask : (↑Nllft ∪ ↑prophN ∪ ↑uniqN : coPset) ⊆ ⊤ by set_solver.
    have Hcl : length cl.2 = length γs by rewrite Hlen' Hlen.
    iMod (uniq_body_transform (cell_points_to_ty ty) ty (γs, x) x (S d) g ξi
      ξidx κ tid (cl'1, []) (cloc_flat_insert cl γs) ⊤ γ L 1
      (pair_with_cell_idsₛ (ty_size ty) γs) Hinj Hmask
      with "LFT PROPH UNIQ [] Gκ [$key $f] [$ξVo $ξTok $ξBor] W")
      as "[W (%ζi & %ζidx & #Obs2 & UniqBody & tok)]".
    { iIntros "[gho pt]". rewrite cell_points_to_gho /=.
      iDestruct "gho" as "(cells & gho)".
      iDestruct (ty_gho_depth_mono ty d g (S d) g x tid with "gho")
        as "gho"; [lia|lia|]. iModIntro.
      iEval (rewrite (heap_complete_mapsto_fancy_val_vec_eq''
        γs cl (ty_phys ty x tid) Hcl)) in "cells".
      iFrame "gho cells". iIntros (y e h) "[gho2 pt2]". iModIntro.
      iExists (S e), h. rewrite cell_points_to_gho /=.
      iEval (rewrite -(heap_complete_mapsto_fancy_val_vec_eq''
        γs cl (ty_phys ty y tid) Hcl)) in "pt2".
      iFrame "pt gho2 pt2". }
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    wp_bind pcell_ref. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_bind perm_mut_ref.
    iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->). wp_rec.
    iModIntro.
    iExists -[(cloc_flat_insert cl γs, x, ζi, S d, g, ζidx)].
    iFrame "L I". iSplit; last first.
    { iCombine "Obs Obs2" as "#Obs3".
      iApply (proph_obs_impl with "Obs3")=> π [[_ Ha] Hb].
      apply Ha; [done| | |done]; rewrite /uniq_bor_future /= Hb //. }
    iSplit; [|done]. iExists #cl.1, d''. iSplit; [done|].
    rewrite /ty_own uniq_bor_gho. iSplit; [|done].
    iSplitR; [iApply "Incl"|]. iSplitR; [iPureIntro; lia|].
    iFrame "UniqBody". iSplitR.
    { have Hfl : ∀ sem', alt_sem sem' →
        sem' (cells_fml cl.1 cl.2 (ty_phys (pcell_ty (ty_size ty)) γs tid))
          ⊣⊢ sem' (cmapstoany_fml (cloc_flat_insert cl γs)).
      { move=> sem' Hs. rewrite (cells_sem_at Hs) (cmapstoany_sem_at Hs).
        apply (pcell_phys_to_flat (ty_size ty) γs cl tid Hlen Hlen'). }
      iApply (dguard_rhs_iff Hfl with "Hpt"). }
    iRight. iApply (ty_gho_pers_depth_mono with "Pers'"); lia.
  Qed.

  (** ** Atomic operations on a one-cell permission cell *)

  Definition AtomicLoad : val :=
    (λ: ["pcell_ref"; "perm_ref"], !ˢᶜ "pcell_ref")%V.

  Lemma typed_pcell_atomic_load κ (pcell_ref perm_ref : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[pcell_ref ◁ shr_bor κ (pcell_ty 1);
        perm_ref ◁ shr_bor κ (cell_points_to_ty int)]
      (AtomicLoad [pcell_ref; perm_ref]) (λ v, +[v ◁ int])
      (λ post '-[(cl, γs); (_, (γs', n))], λ mask π,
        γs = γs' ∧ post -[n] mask π).
  Proof.
    move=> Alv tid post mask iκs vπl.
    iIntros "#LFT #PROPH #UNIQ #E L I TY #Obs"=>/=.
    iDestruct (Alv with "L E") as "#Alv".
    destruct vπl as [[cl γs] [[cl' [γs' n]] []]].
    iDestruct "TY" as "(Hcell & Hperm & _)".
    iDestruct "Hcell" as (pl d0 Heval) "[Hshr %Hphys]".
    iDestruct "Hperm" as (pl' d1 Heval') "[Hint %Hphys']".
    simpl in Hphys, Hphys'. inversion Hphys; subst pl.
    inversion Hphys'; subst pl'.
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd0 gg0 Hdd0 Hgg0)
      "#(Hcells & _ & Hst0)".
    iDestruct (shr_bor_gho_elim with "Hint") as (dd1 gg1 Hdd1 Hgg1)
      "#(_ & H↦ & _)".
    iApply twpw_fupdw_nonval; [done|].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    (* The shared borrow's persistent part is behind a judgment, so the
       length is read off it here, where the world satisfaction is at hand. *)
    iDestruct (wsat_split (W:=alerus_wsat) (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (store_fml_acc with "Hst0") as "#Acc0".
    iDestruct ("Acc0" with "Wg") as "[Wg #Hlen0]".
    rewrite pure_fml_sem. iDestruct "Hlen0" as %Hlen.
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [<- _]]; [solve_ndisj|].
    iMod (Ltok_alloc with "L W") as "[W (%γl & [#key f])]".
    iDestruct (Ltok_guard_frac with "key") as "#Gfrac".
    iAssert (frac_tok γl 1 &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "Gfrac Alv"). }
    (* the permission's ghost assertion is [False] at depth zero *)
    destruct dd1 as [|d2].
    { iDestruct (dguard_alive_sem with "H↦") as "#H↦0".
      iDestruct (guard_trans with "Gκ H↦0") as "#G0".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G0 f Wg") as "[gho _]".
      by iDestruct (false_fml_sem_1 with "gho") as "[]". }
    destruct γs as [|γ [|γ2 γs2]]; simpl in Hlen; [done| |done].
    (* read the length of the permission cell's cell list off the shared
      points-to, giving the guard back right away *)
    iDestruct (dguard_alive_sem' (cells_fml_sem _ _ _) with "Hcells")
      as "#Hcells0".
    iDestruct (guard_trans with "Gκ Hcells0") as "#Gpt".
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "Gpt f Wg") as "[pt back]".
    iDestruct (heap_fancy_mapsto_cells_length with "pt") as %Hlen'.
    iDestruct ("back" with "pt") as "[Wg f]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    rewrite /= ?length_pad in Hlen'.
    destruct cl as [cll cls]=>/=. simpl in Hlen', Heval.
    destruct cls as [|cs1 [|??]]; simpl in Hlen'; [done| |done].
    (* assemble the guard the atomic read runs under *)
    have Hph1 : ∀ sem', alt_sem sem' →
      sem' (cells_fml (cll, [cs1]).1 (cll, [cs1]).2
              (ty_phys (pcell_ty 1) [γ] tid)) ⊣⊢
      sem' (cells_fml (cll, [cs1]).1 (cll, [cs1]).2 (FCell <$> [γ])).
    { move=> sem' Hs. rewrite !(cells_sem_at Hs).
      apply (pcell_ty_gho_phys 1 [γ] tid Hlen (cll, [cs1])). }
    iDestruct (dguard_rhs_iff Hph1 with "Hcells") as "#Hcells2".
    iDestruct (dguard_rhs_sep_l with "H↦") as "#H2".
    iDestruct (dguard_cloc_combine_fancy' (cll, [cs1]) [γ] [FVal #n]
      with "Hcells2 H2") as "#Hread".
    iDestruct (dguard_alive_sem' (cells_fml_sem _ _ _) with "Hread")
      as "#Hread0".
    iDestruct (guard_rhs_iff (heap_mapsto_singleton cll (cs1 ++ [γ]) (FVal #n))
      with "Hread0") as "#Hread2".
    iDestruct (guard_trans with "Gκ Hread2") as "#Gread".
    iModIntro. iFrame "W".
    wp_bind pcell_ref. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_bind perm_ref.
    iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->). wp_rec.
    iApply (twp_read_sc_guarded_cells _ _ cll (cs1 ++ [γ]) #n
      (frac_tok γl 1) with "[f]").
    { iFrame "f". iApply "Gread". }
    iIntros "f W". iMod (Ltok_withdraw with "[$key $f] W") as "[W L]".
    iModIntro. iFrame "W". iExists -[n]. iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> ? [_ Hpost]. apply Hpost. }
    iSplit; [|done]. rewrite tctx_hasty_val. iExists 0%nat.
    iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  (** A one-cell permission cell's contents, read as the single flat cell the
    atomic operations act on *)
  Lemma pcell1_cell_mapsto (γ : cell_id) (cll : loc) (cs : list cell_id)
      (v : val) :
    [γ] ^↦!∗ [FVal v] ⊣⊢ ((cll, cs ++ [γ]) #↦ v).
  Proof.
    rewrite (heap_complete_mapsto_fancy_val_vec_eq'' [γ] (cll, [cs])) //=.
    by rewrite -heap_complete_mapsto_val_singleton
      -(heap_complete_mapsto_fancy_fmap_eq _ [v]).
  Qed.
  Lemma pcell1_phys_to_cell (γ : cell_id) (cll : loc) (cs : list cell_id) tid :
    (cll ↦[^ [cs] ]!∗ ty_phys (pcell_ty 1) [γ] tid) ⊣⊢ ((cll, cs ++ [γ]) #↦_).
  Proof.
    rewrite (pcell_phys_to_flat 1 [γ] (cll, [cs]) tid) //=.
    apply heap_complete_mapsto_singleton.
  Qed.

  Definition AtomicStore : val :=
    (λ: ["pcell_ref"; "perm_mut_ref"; "new"], "pcell_ref" <-ˢᶜ "new")%V.

  Lemma typed_pcell_atomic_store κ (pcell_ref perm_mut_ref new : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[pcell_ref ◁ shr_bor κ (pcell_ty 1);
        perm_mut_ref ◁ &uniq{κ} (cell_points_to_ty int); new ◁ int]
      (AtomicStore [pcell_ref; perm_mut_ref; new]) (λ _, +[])
      (λ post '-[(cl, γs); m; n'], λ mask π,
        let '(cl', (γs', n), ξi, d, g, idx) := m in γs = γs' ∧
          (uniq_bor_future m π = (γs', n') → post -[] mask π)).
  Proof.
    move=> Alv tid post mask iκs vπl.
    iIntros "#LFT #PROPH #UNIQ #E L I TY #Obs"=>/=.
    iDestruct (Alv with "L E") as "#Alv".
    destruct vπl as [[cl γs] [u [n' []]]].
    destruct u as [[[[[cl' [γs' x]] ξi] di] gi] ξidx].
    iDestruct "TY" as "(Hcell & Hperm & Hn & _)".
    iDestruct "Hcell" as (pl d0 Heval) "[Hshr %Hphys]".
    iDestruct "Hperm" as (pl' d1 Heval') "[Huniq %Hphys']".
    iDestruct "Hn" as (pl'' d2 Heval'') "[_ %Hphys'']".
    simpl in Hphys, Hphys', Hphys''.
    inversion Hphys; subst pl. inversion Hphys'; subst pl'.
    inversion Hphys''; subst pl''.
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd0 gg0 Hdd0 Hgg0)
      "#(Hcells & _ & Hst0)".
    rewrite uniq_bor_gho.
    iDestruct "Huniq" as "(#Incl & %Hineq & UniqBody & #PtBase & #Pers)".
    iApply twpw_fupdw_nonval; [done|].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    (* The shared borrow's persistent part is behind a judgment, so the
       length is read off it here, where the world satisfaction is at hand. *)
    iDestruct (wsat_split (W:=alerus_wsat) (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (store_fml_acc with "Hst0") as "#Acc0".
    iDestruct ("Acc0" with "Wg") as "[Wg #Hlen0]".
    rewrite pure_fml_sem. iDestruct "Hlen0" as %Hlen.
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [<- _]]; [solve_ndisj|].
    iMod (Ltok_alloc with "L W") as "[W (%γl & tok)]".
    iDestruct (Ltok_split_1 with "tok") as "[[#key fa] [_ fb]]".
    iDestruct (Ltok_guard_frac with "key") as "#Gfrac".
    iAssert (frac_tok γl (1/2) &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "Gfrac Alv"). }
    iAssert (bor_sem (gsrc_fml (GFrac γl (1/2))) &&{Wguard}&&> @[κ])%I
      as "#Gκ'".
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γl (1/2)))). iApply "Gκ". }
    iDestruct (dincl_incl with "Incl") as "#Incls".
    iDestruct "Pers" as "[Dead|#Pers]".
    { iDestruct "Dead" as (κ'') "[#Incl0 #Dead']".
      iDestruct (dincl_sem with "Incl0") as "#Incl'".
      iDestruct (guard_trans with "Gκ Incl'") as "#G3".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G3 fb Wg") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    rewrite (cell_points_to_gho_pers int (γs, x) di gi tid).
    destruct di as [|di]; [by iDestruct "Pers" as "[]"|].
    destruct γs as [|γ [|??]]; simpl in Hlen; [done| |done].
    (* read off the length of the permission cell's cell list *)
    iDestruct (dguard_alive_sem' (cells_fml_sem _ _ _) with "Hcells")
      as "#Hcells0".
    iDestruct (guard_trans with "Gκ Hcells0") as "#Gpt".
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "Gpt fb Wg") as "[pt back]".
    iDestruct (heap_fancy_mapsto_cells_length with "pt") as %Hlen'.
    iDestruct ("back" with "pt") as "[Wg fb]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    rewrite /= ?length_pad in Hlen'.
    destruct cl as [cll cls]. simpl in Hlen', Heval.
    destruct cls as [|cs1 [|??]]; simpl in Hlen'; [done| |done].
    (* open the unique borrow over the permission *)
    iDestruct "UniqBody" as "(ξVo & ξTok & #ξBor)".
    iDestruct (idxbor_fml_sem_1 with "ξBor") as "#ξBor1".
    iDestruct (dIdxBor_acc_guarded (E:=⊤) (Gx:=gsrc_fml (GFrac γl (1/2)))
      (κ:=κ) (idx:=ξidx)
      with "LFT ξBor1 ξTok Gκ' [fa]") as "A".
    { by iApply (gsrc_fml_sem_2 (s := GFrac γl (1/2))). }
    iDestruct (fupdw_incl (W:=alerus_wsat) with "A") as "A'".
    iMod ("A'" with "W") as "[W [Inner Back]]".
    rewrite uniq_body_fml_sem.
    iDestruct "Inner" as (y d3 g3) "(ξPc & Gho & Phys)".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
    subst d3 g3. iSimpl in "Phys".
    rewrite (cell_points_to_gho int ([γ], x) (S di) gi tid).
    iDestruct "Gho" as "[Hcellpt _]".
    iEval (rewrite (pcell1_cell_mapsto γ cll cs1 #x)) in "Hcellpt".
    (* the guard the atomic write runs under *)
    iDestruct (guard_rhs_iff (pcell1_phys_to_cell γ cll cs1 tid)
      with "Hcells0") as "#Hcells2".
    iDestruct (guard_trans with "Gκ' Hcells2") as "#Gwrite".
    iModIntro. iFrame "W".
    wp_bind pcell_ref. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_bind perm_mut_ref.
    iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    wp_bind new. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_rec.
    iApply (twp_write_sc_guarded _ _ cll (cs1 ++ [γ]) _ _ #x
      (gsrc_fml (GFrac γl (1/2))) with "[fb Hcellpt]").
    { iFrame "Gwrite Hcellpt".
      by iApply (gsrc_fml_sem_2 (s := GFrac γl (1/2))). }
    iIntros "[Hcellpt fb] W".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γl (1/2)) with "fb") as "fb".
    iEval (rewrite -(pcell1_cell_mapsto γ cll cs1 #n')) in "Hcellpt".
    iMod (uniq_update (PrVar ((trackedₛ (pcellₛ (ty_size int) * Zₛ))%ST
        ↾ prval_to_inh (@vπ (trackedₛ (pcellₛ (ty_size int) * Zₛ))
          ([γ], x))) ξi)
      ([γ], n')
      (@vπ (trackedₛ (pcellₛ (ty_size int) * Zₛ)) ([γ], n')) (S di, gi)
      with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; [solve_ndisj|].
    iDestruct ("Back" with "[ξPc Hcellpt Phys]") as "B".
    { iExists ([γ], n'), (S di), gi.
      iFrame "ξPc". rewrite (cell_points_to_gho int ([γ], n') (S di) gi tid).
      iSplitR "Phys"; [|iExact "Phys"].
      iFrame "Hcellpt". by iApply empty_fml_sem_2. }
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "B") as "B'";
      [done|].
    iMod ("B'" with "W") as "[W [ξTok fa]]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γl (1/2)) with "fa") as "fa".
    rewrite (uniq_body_pers_component_irrel (cell_points_to_ty int) ([γ], x)
      ([γ], n') ξi (S di) gi (S di) gi ξidx κ tid cl' (proof_irrel _ _))
      (proof_irrel (prval_to_inh
        (@vπ (trackedₛ (pcellₛ (ty_size int) * Zₛ)) ([γ], x)))
       (prval_to_inh
        (@vπ (trackedₛ (pcellₛ (ty_size int) * Zₛ)) ([γ], n')))).
    iMod (resolve_uniq_body (cell_points_to_ty int) ([γ], n') ξi (S di) gi
      ξidx κ tid cl' E L γl (1/2) ⊤
      with "LFT PROPH UNIQ Incls E [$key $fa] [$ξVo $ξTok $ξBor] W")
      as "[W (#Hrslv & fa & _)]"; [done|solve_ndisj|].
    iDestruct (Ltok_split_2 with "fa [$key $fb]") as "tok".
    iMod (Ltok_withdraw with "tok W") as "[W L]".
    iModIntro. iFrame "W". iExists -[]. iFrame "L I". iSplit; [done|].
    iDestruct (proph_obs_and with "Hrslv Obs") as "Obs2".
    iApply (proph_obs_impl with "Obs2")=> π [Hrsv [_ Hpost]].
    apply Hpost. rewrite /uniq_bor_future /=.
    rewrite (proof_irrel (prval_to_inh _)
      (@to_inh_syn_type (trackedₛ (pcellₛ 1 * Zₛ)) ([γ], x))) in Hrsv.
    by rewrite Hrsv.
  Qed.

  Definition AtomicCAS : val :=
    (λ: ["pcell_ref"; "perm_mut_ref"; "n1"; "n2"],
      CAS "pcell_ref" "n1" "n2")%V.

  Lemma typed_pcell_atomic_CAS κ (pcell_ref perm_mut_ref p1 p2 : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[pcell_ref ◁ shr_bor κ (pcell_ty 1);
        perm_mut_ref ◁ &uniq{κ} (cell_points_to_ty int); p1 ◁ int; p2 ◁ int]
      (AtomicCAS [pcell_ref; perm_mut_ref; p1; p2]) (λ v, +[v ◁ int])
      (λ post '-[(cl, γs); m; n1; n2], λ mask π,
        let '(cl', (γs', n), ξi, d, g, idx) := m in γs = γs' ∧
          if decide (n = n1)
          then uniq_bor_future m π = (γs', n2) → post -[1%Z] mask π
          else uniq_bor_future m π = (γs', n) → post -[0%Z] mask π).
  Proof.
    move=> Alv tid post mask iκs vπl.
    iIntros "#LFT #PROPH #UNIQ #E L I TY #Obs"=>/=.
    iDestruct (Alv with "L E") as "#Alv".
    destruct vπl as [[cl γs] [u [n1 [n2 []]]]].
    destruct u as [[[[[cl' [γs' x]] ξi] di] gi] ξidx].
    iDestruct "TY" as "(Hcell & Hperm & Hn1 & Hn2 & _)".
    iDestruct "Hcell" as (pl d0 Heval) "[Hshr %Hphys]".
    iDestruct "Hperm" as (pl' d1 Heval') "[Huniq %Hphys']".
    iDestruct "Hn1" as (q1 e1 Hpath1) "[_ %Hphys1]".
    iDestruct "Hn2" as (q2 e2 Hpath2) "[_ %Hphys2]".
    simpl in Hphys, Hphys', Hphys1, Hphys2.
    inversion Hphys; subst pl. inversion Hphys'; subst pl'.
    inversion Hphys1; subst q1. inversion Hphys2; subst q2.
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd0 gg0 Hdd0 Hgg0)
      "#(Hcells & _ & Hst0)".
    rewrite uniq_bor_gho.
    iDestruct "Huniq" as "(#Incl & %Hineq & UniqBody & #PtBase & #Pers)".
    iApply twpw_fupdw_nonval; [done|].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    (* The shared borrow's persistent part is behind a judgment, so the
       length is read off it here, where the world satisfaction is at hand. *)
    iDestruct (wsat_split (W:=alerus_wsat) (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (store_fml_acc with "Hst0") as "#Acc0".
    iDestruct ("Acc0" with "Wg") as "[Wg #Hlen0]".
    rewrite pure_fml_sem. iDestruct "Hlen0" as %Hlen.
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [<- _]]; [solve_ndisj|].
    iMod (Ltok_alloc with "L W") as "[W (%γl & tok)]".
    iDestruct (Ltok_split_1 with "tok") as "[[#key fa] [_ fb]]".
    iDestruct (Ltok_guard_frac with "key") as "#Gfrac".
    iAssert (frac_tok γl (1/2) &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "Gfrac Alv"). }
    iAssert (bor_sem (gsrc_fml (GFrac γl (1/2))) &&{Wguard}&&> @[κ])%I
      as "#Gκ'".
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γl (1/2)))). iApply "Gκ". }
    iDestruct (dincl_incl with "Incl") as "#Incls".
    iDestruct "Pers" as "[Dead|#Pers]".
    { iDestruct "Dead" as (κ'') "[#Incl0 #Dead']".
      iDestruct (dincl_sem with "Incl0") as "#Incl'".
      iDestruct (guard_trans with "Gκ Incl'") as "#G3".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G3 fb Wg") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    rewrite (cell_points_to_gho_pers int (γs, x) di gi tid).
    destruct di as [|di]; [by iDestruct "Pers" as "[]"|].
    destruct γs as [|γ [|??]]; simpl in Hlen; [done| |done].
    iDestruct (dguard_alive_sem' (cells_fml_sem _ _ _) with "Hcells")
      as "#Hcells0".
    iDestruct (guard_trans with "Gκ Hcells0") as "#Gpt".
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "Gpt fb Wg") as "[pt back]".
    iDestruct (heap_fancy_mapsto_cells_length with "pt") as %Hlen'.
    iDestruct ("back" with "pt") as "[Wg fb]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    rewrite /= ?length_pad in Hlen'.
    destruct cl as [cll cls]. simpl in Hlen', Heval.
    destruct cls as [|cs1 [|??]]; simpl in Hlen'; [done| |done].
    iDestruct "UniqBody" as "(ξVo & ξTok & #ξBor)".
    iDestruct (idxbor_fml_sem_1 with "ξBor") as "#ξBor1".
    iDestruct (dIdxBor_acc_guarded (E:=⊤) (Gx:=gsrc_fml (GFrac γl (1/2)))
      (κ:=κ) (idx:=ξidx)
      with "LFT ξBor1 ξTok Gκ' [fa]") as "A".
    { by iApply (gsrc_fml_sem_2 (s := GFrac γl (1/2))). }
    iDestruct (fupdw_incl (W:=alerus_wsat) with "A") as "A'".
    iMod ("A'" with "W") as "[W [Inner Back]]".
    rewrite uniq_body_fml_sem.
    iDestruct "Inner" as (y d3 g3) "(ξPc & Gho & Phys)".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
    subst d3 g3. iSimpl in "Phys".
    rewrite (cell_points_to_gho int ([γ], x) (S di) gi tid).
    iDestruct "Gho" as "[Hcellpt _]".
    iEval (rewrite (pcell1_cell_mapsto γ cll cs1 #x)) in "Hcellpt".
    iDestruct (guard_rhs_iff (pcell1_phys_to_cell γ cll cs1 tid)
      with "Hcells0") as "#Hcells2".
    iDestruct (guard_trans with "Gκ' Hcells2") as "#Gwrite".
    iModIntro. iFrame "W".
    wp_bind pcell_ref. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_bind perm_mut_ref.
    iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    wp_bind p1. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_bind p2.
    iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->). wp_rec.
    destruct (decide (x = n1)) as [->|NE].
    - (* the compare-and-swap succeeds *)
      iApply (twp_cas_int_suc_guarded _ _ cll (cs1 ++ [γ]) n1 _ _
        (gsrc_fml (GFrac γl (1/2))) with "[fb Hcellpt]").
      { iFrame "Gwrite Hcellpt".
        by iApply (gsrc_fml_sem_2 (s := GFrac γl (1/2))). }
      iIntros "[fb Hcellpt] W".
      iDestruct (gsrc_fml_sem_1 (s := GFrac γl (1/2)) with "fb") as "fb".
      iEval (rewrite -(pcell1_cell_mapsto γ cll cs1 #n2)) in "Hcellpt".
      iMod (uniq_update (PrVar ((trackedₛ (pcellₛ (ty_size int) * Zₛ))%ST
          ↾ prval_to_inh (@vπ (trackedₛ (pcellₛ (ty_size int) * Zₛ))
            ([γ], n1))) ξi)
        ([γ], n2)
        (@vπ (trackedₛ (pcellₛ (ty_size int) * Zₛ)) ([γ], n2)) (S di, gi)
        with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; [solve_ndisj|].
      iDestruct ("Back" with "[ξPc Hcellpt Phys]") as "B".
      { iExists ([γ], n2), (S di), gi. iFrame "ξPc".
        rewrite (cell_points_to_gho int ([γ], n2) (S di) gi tid).
        iSplitR "Phys"; [|iExact "Phys"].
        iFrame "Hcellpt". by iApply empty_fml_sem_2. }
      iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "B") as "B'";
        [done|].
      iMod ("B'" with "W") as "[W [ξTok fa]]".
      iDestruct (gsrc_fml_sem_1 (s := GFrac γl (1/2)) with "fa") as "fa".
      rewrite (uniq_body_pers_component_irrel (cell_points_to_ty int)
        ([γ], n1) ([γ], n2) ξi (S di) gi (S di) gi ξidx κ tid cl'
        (proof_irrel _ _))
        (proof_irrel (prval_to_inh
          (@vπ (trackedₛ (pcellₛ (ty_size int) * Zₛ)) ([γ], n1)))
         (prval_to_inh
          (@vπ (trackedₛ (pcellₛ (ty_size int) * Zₛ)) ([γ], n2)))).
      iMod (resolve_uniq_body (cell_points_to_ty int) ([γ], n2) ξi (S di) gi
        ξidx κ tid cl' E L γl (1/2) ⊤
        with "LFT PROPH UNIQ Incls E [$key $fa] [$ξVo $ξTok $ξBor] W")
        as "[W (#Hrslv & fa & _)]"; [done|solve_ndisj|].
      iDestruct (Ltok_split_2 with "fa [$key $fb]") as "tok".
      iMod (Ltok_withdraw with "tok W") as "[W L]".
      iModIntro. iFrame "W". iExists -[1%Z]. iFrame "L I".
      iSplit; last first.
      { iDestruct (proph_obs_and with "Hrslv Obs") as "Obs2".
        iApply (proph_obs_impl with "Obs2")=> π [Hrsv [_ Hpost]].
        case_decide as Hd; [|done]. apply Hpost.
        rewrite /uniq_bor_future /=.
        rewrite (proof_irrel (prval_to_inh _)
          (@to_inh_syn_type (trackedₛ (pcellₛ 1 * Zₛ)) ([γ], n1))) in Hrsv.
        by rewrite Hrsv. }
      iSplit; [|done]. rewrite tctx_hasty_val. iExists 0%nat.
      iSplit; [by iApply empty_fml_sem_2|done].
    - (* the compare-and-swap fails; the permission is unchanged *)
      have Hne : n1 ≠ x := λ H, NE (eq_sym H).
      iApply (twp_cas_int_fail_guarded _ _ cll (cs1 ++ [γ]) n1 _ _ x
        (gsrc_fml (GFrac γl (1/2))) _ Hne with "[fb Hcellpt]").
      { iFrame "Gwrite Hcellpt".
        by iApply (gsrc_fml_sem_2 (s := GFrac γl (1/2))). }
      iIntros "[fb Hcellpt] W".
      iDestruct (gsrc_fml_sem_1 (s := GFrac γl (1/2)) with "fb") as "fb".
      iEval (rewrite -(pcell1_cell_mapsto γ cll cs1 #x)) in "Hcellpt".
      iDestruct ("Back" with "[ξPc Hcellpt Phys]") as "B".
      { iExists ([γ], x), (S di), gi. iFrame "ξPc".
        rewrite (cell_points_to_gho int ([γ], x) (S di) gi tid).
        iSplitR "Phys"; [|iExact "Phys"].
        iFrame "Hcellpt". by iApply empty_fml_sem_2. }
      iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "B") as "B'";
        [done|].
      iMod ("B'" with "W") as "[W [ξTok fa]]".
      iDestruct (gsrc_fml_sem_1 (s := GFrac γl (1/2)) with "fa") as "fa".
      iMod (resolve_uniq_body (cell_points_to_ty int) ([γ], x) ξi (S di) gi
        ξidx κ tid cl' E L γl (1/2) ⊤
        with "LFT PROPH UNIQ Incls E [$key $fa] [$ξVo $ξTok $ξBor] W")
        as "[W (#Hrslv & fa & _)]"; [done|solve_ndisj|].
      iDestruct (Ltok_split_2 with "fa [$key $fb]") as "tok".
      iMod (Ltok_withdraw with "tok W") as "[W L]".
      iModIntro. iFrame "W". iExists -[0%Z]. iFrame "L I".
      iSplit; last first.
      { iDestruct (proph_obs_and with "Hrslv Obs") as "Obs2".
        iApply (proph_obs_impl with "Obs2")=> π [Hrsv [_ Hpost]].
        case_decide as Hd; [done|]. apply Hpost.
        rewrite /uniq_bor_future /=.
        rewrite (proof_irrel (prval_to_inh _)
          (@to_inh_syn_type (trackedₛ (pcellₛ 1 * Zₛ)) ([γ], x))) in Hrsv.
        by rewrite Hrsv. }
      iSplit; [|done]. rewrite tctx_hasty_val. iExists 0%nat.
      iSplit; [by iApply empty_fml_sem_2|done].
  Qed.
End typing.
