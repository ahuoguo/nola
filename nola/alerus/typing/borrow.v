(** * Borrowing and dereferencing borrowed pointers

  Ported from VerusBelt ([typing/borrow.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  The arbitrary [Timeless G] with [G &&{↑NllftG}&&> llctx_interp L] that the
  original halves with [frac_split_guard_in_half] is an [Ltok γ L q] here,
  allocated out of [llctx_interp L] with [Ltok_alloc] and given back with
  [Ltok_withdraw]; the credits [⧗ ⧗' £] that the original's [Share] and
  [UniqBor] instructions mint go with the time receipts. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.typing Require Export uniq_bor shr_bor own uniq_util.
From nola.alerus.typing Require Import lft_contexts type_context programs
  programs_util.
From nola.alerus.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Implicit Type 𝔄 𝔅: syn_type.

Section borrow.
  Context `{!typeG FML Σ}.


  (** Creating a unique borrow out of an owning pointer.

    The original's [⧖]/[⧗]/[£] and the [▷]s they pay for are gone. *)
  Lemma type_uniqbor_instr {𝔄} E L I p n (ty: type 𝔄) κ :
    lctx_lft_alive E L κ →
    elctx_sat E L (ty_outlives_E ty κ) →
    typed_instr E L I +[p ◁ own_ptr n ty] UniqBor
      (const +[p ◁ &uniq{κ} ty;
               p ◁{κ} blocked_type_ctor _ (own_ptr n ty)])
      (λ post '-[a], λ mask π,
        ∀ (m: ~~(uniq_borₛ 𝔄)) (b: ~~(blockedₛ (at_locₛ 𝔄))),
          of_cloc (uniq_bor_loc m) = a.1 →
          uniq_bor_current m = a.2 →
          (blockedπ b π).2 = (vπ m π).2 →
          (blockedπ b π).1 = a.1 →
          post -[m; b] mask π).
  Proof.
    move=> Alv Out. apply typed_instr_of_skip.
    move=> [l x] v d tid post mask iκs.
    iIntros "#LFT #PROPH #UNIQ #E L I %Hp own #Obs W".
    iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#Inκ".
    iDestruct "own" as "[gho %phys]".
    destruct d as [|d']; [by iDestruct (false_fml_sem_1 with "gho") as "[]"|].
    rewrite own_ptr_gho /=.
    iDestruct "gho" as "(pt & freeable & gho)".
    iDestruct (ty_gho_pers_impl with "gho") as "#Pers".
    have Hmask : (↑Nllft ∪ ↑prophN ∪ ↑uniqN : coPset) ⊆ ⊤ by set_solver.
    iMod (alloc_uniq_body ty x d' (S d') κ tid
      (l, repeat [] (length (ty_phys ty x tid))) ⊤ Hmask
      with "LFT PROPH UNIQ gho [pt] W")
      as "[W (%ξi & %ζi & %idx & UniqBody & #Obsξζ & Back)]".
    { by rewrite -heap_cloc_mapsto_fancy_empty. }
    iModIntro. iFrame "W L I".
    iExists -[((l, repeat [] (length (ty_phys ty x tid))), x, ξi, d', S d', idx);
               ((l, x), ζi, ζi)].
    iSplit; last first.
    { iCombine "Obs Obsξζ" as "#Obs1".
      iApply (proph_obs_impl with "Obs1")=> π [Hm Hk]. apply Hm; [done|done|..].
      - by rewrite /= Hk.
      - by rewrite /= Hk. }
    iSplitL "UniqBody".
    { iExists v, (S (S d')). iSplit; [done|].
      rewrite /ty_own uniq_bor_gho. iSplitL; [|by rewrite /= -phys].
      iSplitR; [iApply "Inκ"|]. iSplitR; [iPureIntro; lia|].
      iFrame "UniqBody". iSplitR.
      { iApply dguard_cmapstoany_nil. }
      by iRight. }
    iSplit; [|done]. rewrite /tctx_elt_interp /=. iExists v.
    iSplit; [done|]. iIntros "†κ W".
    iMod ("Back" with "†κ W") as "[W Body]".
    iEval (rewrite uniq_body_fml_sem) in "Body".
    iDestruct "Body" as (x'' d'' g'') "(pc & gho2 & pt2)".
    iModIntro. iFrame "W". iExists (l, x''), (S d'' `max` g'').
    destruct (S d'' `max` g'') as [|d1] eqn:Hd1; [lia|].
    iSplitL "pc".
    { iDestruct (proph_ctrl_eqz with "PROPH pc") as "Eqz".
      iApply proph_eqz_modify;
        [|iApply (proph_eqz_constr (λ t, (l, t)) with "Eqz")].
      iApply (proph_obs_impl with "Obsξζ")=> π Ha. by rewrite /= -Ha. }
    rewrite /ty_own own_ptr_gho /=. iSplit; [|by rewrite /= -phys].
    rewrite heap_cloc_mapsto_fancy_empty !ty_size_eq.
    iFrame "pt2 freeable".
    iDestruct (ty_gho_depth_mono ty d'' g'' d1 (S d1) x'' tid with "gho2")
      as "[$ _]"; lia.
  Qed.

  (** Turning a unique borrow into a shared one.

    The original's [⧖]/[⧗]/[£] are gone, and the three guard indices it
    juggles with [leaf_goal laters to …] with them. *)
  Lemma type_share_instr {𝔄} p κ (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ &uniq{κ} ty] Share (const +[p ◁ &shr{κ} ty])
      (λ post '-[m], λ mask π, (vπ m π).1 = (vπ m π).2 →
        post -[(uniq_bor_loc m, uniq_bor_current m)] mask π).
  Proof.
    move=> Alv. apply typed_instr_of_skip.
    move=> [[[[[l x0] ξi] d'] g'] idx] v d tid post mask iκs.
    iIntros "#LFT #PROPH #UNIQ #E L I %Hp [gho %Phys] #Obs W".
    rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Hle & UniqBody & #PtBase & #Pers)".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct "Pers" as "[Dead|#Pers2]".
    { (* [κ] is already dead, so the lifetime context is contradictory *)
      iDestruct "Dead" as (κ') "[#Incl0 #Dead']".
      iDestruct (dincl_sem with "Incl0") as "#Incl'".
      iDestruct (guard_trans with "Alv Incl'") as "#G3".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G3 L Wg") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]".
    iDestruct (dincl_sem with "Incl") as "#Incl'".
    iMod (resolve_uniq_body ty x0 ξi d' g' idx κ tid l E L γ 1 ⊤
      with "LFT PROPH UNIQ Incl' E tok UniqBody W")
      as "[W (#Obs2 & tok & #ShrGuard)]"; [done|done|].
    iMod (Ltok_withdraw with "tok W") as "[W L]".
    iModIntro. iFrame "W L I". iExists -[(l, x0)].
    inversion Phys as [Eqv]. iSplit.
    { iSplit; [|done]. iExists v, (S d). iSplit; [done|].
      rewrite /ty_own shr_bor_gho /=. iSplit; [|by rewrite -Eqv].
      iDestruct (dguard_rhs_sep_l with "ShrGuard") as "#ShrGho".
      iDestruct (dguard_rhs_sep_r with "ShrGuard") as "#ShrPt".
      iSplit.
      { by iApply (dguard_cloc_combine_fancy with "PtBase ShrPt"). }
      iSplit.
      { iApply (dguard_depth_mono ty d' g' d (S d) x0 tid with "ShrGho");
          lia. }
      iApply (ty_gho_pers_depth_mono ty d' g' d (S d) x0 tid with "Pers2");
        lia. }
    iCombine "Obs Obs2" as "#Obs3".
    iApply (proph_obs_impl with "Obs3")=>/= π [Himpl Heq].
    apply Himpl. by rewrite Heq.
  Qed.

  Lemma type_share {𝔄 𝔅l ℭl 𝔇} p κ (ty: type 𝔄) (T: tctx 𝔅l) (T' : tctx ℭl)
      trx tr e E L I (C: cctx 𝔇) :
    Closed [] e → tctx_extract_ctx E L +[p ◁ &uniq{κ} ty] T T' trx →
    lctx_lft_alive E L κ →
    typed_body E L I C (p ◁ &shr{κ} ty +:: T') e tr -∗
    typed_body E L I C T (Share;; e) (trx ∘
      (λ post '(m -:: bl), λ mask π, (vπ m π).1 = (vπ m π).2 →
        tr post ((uniq_bor_loc m, uniq_bor_current m) -:: bl) mask π))%type.
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_seq; [by eapply type_share_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=> ??. apply Htrx. by case.
  Qed.

  (** The intermediate borrow that [tctx_reborrow_uniq] lends to [κ']: the
    old value observer paired with the new prophecy controller.  The
    original's [⧖(S d' `max` g')] inside it goes with the time receipts. *)
  Definition reborrow_mid_fml {𝔄} (x0: ~~𝔄) (ξi ζi: positive) : FML $oi Σ :=
    ex_fml (λ x' : ~~𝔄, ex_fml (λ d' : nat, ex_fml (λ g' : nat,
      (.VOx[PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ξi] x' (d', g') ∗
       .PCx[PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ζi] x' (vπ x') (d', g'))%FML))).

  Lemma reborrow_mid_fml_sem {𝔄} (x0: ~~𝔄) ξi ζi :
    bor_sem (reborrow_mid_fml x0 ξi ζi) ⊣⊢
      ∃ (x': ~~𝔄) (d' g': nat),
        .VO[PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ξi] x' (d', g') ∗
        .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ζi] x' (vπ x') (d', g').
  Proof.
    rewrite /reborrow_mid_fml ex_fml_sem. apply bi.exist_proper=> x'.
    rewrite ex_fml_sem. apply bi.exist_proper=> d'.
    rewrite ex_fml_sem. apply bi.exist_proper=> g'.
    by rewrite bor_sep_sem vo_fml_sem pc_fml_sem.
  Qed.

  (** Reborrowing a unique borrow for a shorter lifetime.

    The original's [⧖]/[⧗]/[£] and the laters they pay for are gone, and with
    them the [leaf_goal laters to …] steps; what is left is the skeleton -
    mint a fresh prophecy [ζ], reborrow the contents to [κ'], lend [κ'] the
    pair of [.VO[ξ]] and [.PC[ζ]], and merge the two borrows into one
    [uniq_body] for [ζ]. *)
  Lemma tctx_reborrow_uniq {𝔄} E L I p (ty: type 𝔄) κ κ' :
    lctx_lft_incl E L κ' κ →
    typed_instr E L I +[p ◁ &uniq{κ} ty] ReBor
      (const +[p ◁ &uniq{κ'} ty;
               p ◁{κ'} blocked_type_ctor _ (&uniq{κ} ty)])
      (λ post '-[m], λ mask π,
        ∀ (m': ~~(uniq_borₛ 𝔄)) (b: ~~(blockedₛ (uniq_borₛ 𝔄))),
          uniq_bor_loc m' = uniq_bor_loc m →
          uniq_bor_current m' = uniq_bor_current m →
          blockedπ b π = (uniq_bor_future m' π, uniq_bor_future m π) →
          post -[m'; b] mask π)%type.
  Proof.
    move=> In. apply typed_instr_of_skip.
    move=> [[[[[l x0] ξi] d'] g'] idx] v d tid post mask iκs.
    iIntros "#LFT #PROPH #UNIQ #E L I %Hp [gho %phys] #Obs W".
    iDestruct (In with "L E") as "#Inκ'κ".
    rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Hle & UniqBody & #PtBase & #Pers)".
    iDestruct "UniqBody" as "(ξVo & ξTok & #ξBor)".
    iMod (uniq_intro x0 (vπ x0) (d', g') with "PROPH UNIQ") as (ζi) "[ζVo ζPc]";
      [set_solver|].
    set ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ξi.
    set ζ := PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ζi.
    iDestruct (dguard_trans with "Inκ'κ Incl") as "#Inclκ'".
    iDestruct (dguard_trans with "Inκ'κ PtBase") as "#PtBase'".
    iDestruct (dincl_sem with "Inκ'κ") as "#Inκ'κs".
    iDestruct "Pers" as "[Dead|#Pers2]".
    { (* [κ] is already dead, so everything can be faked. *)
      iDestruct "Dead" as (κ3) "[#Incl3 #Dead3]".
      iDestruct (dincl_sem with "Incl3") as "#Incl3s".
      iDestruct (llftl_incl_dead_implies_dead ⊤ κ κ3 with "LFT Incl3s Dead3")
        as "A".
      iDestruct (fupdw_incl (W:=alerus_wsat) with "A") as "A'".
      iMod ("A'" with "W") as "[W #†κ]".
      iDestruct (llftl_incl_dead_implies_dead ⊤ κ' κ with "LFT Inκ'κs †κ")
        as "B".
      iDestruct (fupdw_incl (W:=alerus_wsat) with "B") as "B'".
      iMod ("B'" with "W") as "[W #†κ']".
      iDestruct (llftl_bor_fake ⊤ κ' (uniq_body_fml ty x0 ζi tid l)
        with "LFT †κ'") as "C".
      iDestruct (fupdw_incl (W:=alerus_wsat) with "C") as "C'".
      iMod ("C'" with "W") as "[W Fake]".
      rewrite idxbor_fml_of_bor.
      iDestruct "Fake" as (fidx) "[#FBor FTok]".
      iModIntro. iFrame "W L I".
      iExists -[(l, x0, ζi, d', g', fidx); ((l, x0, ζi, d', g', idx), ζi, ξi)].
      iSplit; last first.
      { iApply (proph_obs_impl with "Obs")=> π Ha. by apply Ha. }
      iSplitL "ζVo FTok".
      { iExists v, (S d). iSplit; [done|].
        rewrite /ty_own uniq_bor_gho. iSplit; [|by rewrite /= -phys].
        iSplitR; [by iApply "Inclκ'"|]. iSplitR; [iPureIntro; lia|].
        iFrame "ζVo FTok FBor". iSplitR; [by iApply "PtBase'"|].
        iLeft. iExists κ. by iFrame "Inκ'κ †κ". }
      iSplit; [|done]. rewrite /tctx_elt_interp /=. iExists v.
      iSplit; [done|]. iIntros "_ W". iModIntro. iFrame "W".
      iExists (l, x0, ξi, d', g', idx), (S d).
      iSplitL "ζPc".
      { iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
        iApply (proph_eqz_prod with "[Eqz]");
          [iFrame "Eqz"|iApply proph_eqz_refl]. }
      rewrite /ty_own uniq_bor_gho. iSplit; [|by rewrite /= -phys].
      iSplitR; [iApply "Incl"|]. iSplitR; [iPureIntro; lia|].
      iFrame "ξVo ξTok ξBor". iSplitR; [iApply "PtBase"|].
      iLeft. iExists κ. iFrame "†κ". iApply dincl_refl. }
    (* The main case. *)
    iDestruct (idxbor_fml_to_full with "ξBor ξTok") as "ξBor2".
    iDestruct (llftl_reborrow ⊤ κ κ' (uniq_body_fml ty x0 ξi tid l)
      with "LFT Inκ'κs ξBor2") as "A".
    iDestruct (fupdw_incl (W:=alerus_wsat) with "A") as "A'".
    iMod ("A'" with "W") as "[W [ξBor3 ToξBor]]".
    iDestruct (llftl_borrow κ' (reborrow_mid_fml x0 ξi ζi)
      with "LFT [ξVo ζPc]") as "B".
    { rewrite reborrow_mid_fml_sem. iExists x0, d', g'. iFrame. }
    iDestruct (bupdw_incl (W:=alerus_wsat) with "B") as "B'".
    iMod ("B'" with "W") as "[W [ζBor ToζBig]]".
    iDestruct (llftl_sep_join ⊤ _ _ κ' with "LFT ξBor3 ζBor") as "C".
    iDestruct (fupdw_incl (W:=alerus_wsat) with "C") as "C'".
    iMod ("C'" with "W") as "[W Bor]".
    (* Merge the two borrows into one [uniq_body] for [ζ].  The original
      opens the joined borrow atomically because [κ'] need not be alive. *)
    iAssert (|=[alerus_wsat]{⊤}=> &{κ'} (uniq_body_fml ty x0 ζi tid l))%I
      with "[Bor]" as "Merge".
    { iIntros "W". iDestruct (wsat_split (W':=llft_wsat) with "W") as "[Wl Wr]".
      iMod (llftl_bor_acc_atomic ⊤ _ κ' with "LFT Bor Wl")
        as "[[P Back]|[Wl #†κ']]"; last first.
      { iDestruct (wsat_join (W:=alerus_wsat) with "Wl Wr") as "W".
        iDestruct (llftl_bor_fake ⊤ κ' (uniq_body_fml ty x0 ζi tid l)
          with "LFT †κ'") as "D".
        iDestruct (fupdw_incl (W:=alerus_wsat) with "D") as "D'".
        iApply ("D'" with "W"). }
      iEval (rewrite bor_sep_sem uniq_body_fml_sem reborrow_mid_fml_sem) in "P".
      iDestruct "P" as "[(%x1 & %d1 & %g1 & ξPc1 & Gho1 & Pt1)
                        (%x2 & %d2 & %g2 & ξVo2 & ζPc2)]".
      iDestruct (uniq_agree with "ξVo2 ξPc1") as %[<- Heq]. inversion Heq.
      subst d2 g2.
      iMod ("Back" $! (uniq_body_fml ty x0 ζi tid l)
        with "[ξVo2 ξPc1] [ζPc2 Gho1 Pt1]") as "[Wl $]"; last first.
      { iDestruct (wsat_join (W:=alerus_wsat) with "Wl Wr") as "$". done. }
      { rewrite uniq_body_fml_sem. iExists x2, d1, g1. iFrame. }
      iIntros "[Body #†κ']". iEval (rewrite uniq_body_fml_sem) in "Body".
      iDestruct "Body" as (x3 d3 g3) "(ζPc3 & Gho3 & Pt3)".
      iMod (uniq_update ξ x3 (vπ x3) (d3, g3) with "UNIQ ξVo2 ξPc1")
        as "[ξVo4 ξPc4]"; [solve_ndisj|].
      iModIntro. rewrite bor_sep_sem uniq_body_fml_sem reborrow_mid_fml_sem.
      iSplitR "ξVo4 ζPc3"; [iExists x3, d3, g3; iFrame|].
      iExists x3, d3, g3. iFrame. }
    iMod ("Merge" with "W") as "[W ζBor2]".
    rewrite (idxbor_fml_of_bor (κ:=κ') (Px:=uniq_body_fml ty x0 ζi tid l)).
    iDestruct "ζBor2" as (ζidx) "[#ζBor3 ζTok]".
    iModIntro. iFrame "W L I".
    iExists -[(l, x0, ζi, d', g', ζidx); ((l, x0, ζi, d', g', idx), ζi, ξi)].
    iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Ha. by apply Ha. }
    iSplitL "ζVo ζTok".
    { iExists v, (S d). iSplit; [done|].
      rewrite /ty_own uniq_bor_gho. iSplit; [|by rewrite /= -phys].
      iSplitR; [by iApply "Inclκ'"|]. iSplitR; [iPureIntro; lia|].
      iFrame "ζVo ζTok ζBor3". iSplitR; [by iApply "PtBase'"|].
      by iRight. }
    iSplit; [|done]. rewrite /tctx_elt_interp /=. iExists v.
    iSplit; [done|]. iIntros "#†κ' W".
    iDestruct ("ToξBor" with "†κ'") as "A".
    iDestruct (bupdw_incl (W:=alerus_wsat) with "A") as "A'".
    iMod ("A'" with "W") as "[W ξBor4]".
    iDestruct ("ToζBig" with "†κ'") as "B".
    iDestruct (bupdw_incl (W:=alerus_wsat) with "B") as "B'".
    iMod ("B'" with "W") as "[W Mid]".
    iEval (rewrite reborrow_mid_fml_sem) in "Mid".
    iDestruct "Mid" as (x'' d'' g'') "[ξVo ζPc']".
    iDestruct (llftl_bor_pers_from_wand2 ⊤ κ _
      (ty_gho_pers ty x'' d'' g'' tid) with "LFT ξBor4 [] ξVo") as "C".
    { iIntros "ξVo Body". iEval (rewrite uniq_body_fml_sem) in "Body".
      iDestruct "Body" as (y e h) "(ξPc & Gho & _)".
      iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
      subst e h. iApply (ty_gho_pers_impl with "Gho"). }
    iDestruct (fupdw_incl (W:=alerus_wsat) with "C") as "C'".
    iMod ("C'" with "W") as "[W (ξBor5 & #Pers'' & ξVo)]".
    rewrite (idxbor_fml_of_bor (κ:=κ) (Px:=uniq_body_fml ty x0 ξi tid l)).
    iDestruct "ξBor5" as (ξidx) "[#ξBor6 ξTok]".
    iModIntro. iFrame "W".
    iExists (l, x'', ξi, d'', g'', ξidx), (d `max` S d'' `max` g'').
    have Hirr : prval_to_inh (vπ x'') = prval_to_inh (vπ x0).
    { apply proof_irrel. }
    have Hirr' : to_inh_syn_type (@vπ 𝔄 x'' inhabitant)
               = to_inh_syn_type (@vπ 𝔄 x0 inhabitant).
    { apply proof_irrel. }
    iSplitL "ζPc'".
    { iDestruct (proph_ctrl_eqz with "PROPH ζPc'") as "Eqz".
      iApply (proph_eqz_prod with "[Eqz]"); [iFrame "Eqz"|].
      rewrite /= Hirr'. iApply proph_eqz_refl. }
    rewrite /ty_own uniq_bor_gho. iSplit; [|by rewrite /= -phys].
    iSplitR; [iApply "Incl"|]. iSplitR; [iPureIntro; lia|].
    rewrite /uniq_body /uniq_body_pers_component
      (uniq_body_fml_irrel ty x'' x0 ξi tid l Hirr) Hirr.
    iFrame "ξVo ξTok ξBor6". iSplitR; [iApply "PtBase"|].
    iDestruct "Pers''" as "[Pers''|Dead]"; [by iRight|].
    iLeft. iExists κ. iFrame "Dead". iApply dincl_refl.
  Qed.

  (** [type_deref_uniq_own_instr]'s guard source.  The original's is
    [llctx_interp L ∗ .VO[ξ] … ∗ idx_bor_tok ξidx]; here it has to be a
    formula, so the context is banked as an [Ltok] and the two pieces of
    ghost state are named by [vo_fml] and [idx_bor_tok_fml]. *)
  Definition deref_uniq_own_src (γ: gname) (ξ: proph_var)
    (x: ~~ (`ξ.(pv_ty))) (d g: nat) (idx: Idx) : FML $oi Σ :=
    (gsrc_fml (GFrac γ 1) ∗ .VOx[ξ] x (d, g) ∗ idx_bor_tok_fml idx)%FML.

  Lemma deref_uniq_own_src_sem γ ξ x d g idx :
    bor_sem (deref_uniq_own_src γ ξ x d g idx) ⊣⊢
      frac_tok γ 1 ∗ .VO[ξ] x (d, g) ∗ idx_bor_tok idx.
  Proof.
    rewrite /deref_uniq_own_src !bor_sep_sem (gsrc_fml_sem (GFrac γ 1))
      vo_fml_sem idx_bor_tok_fml_sem //.
  Qed.

  (** Dereferencing a unique borrow of an owning pointer.

    The original's [⧗]/[⧖]/[£] and the laters they strip are gone; so is the
    [llctx_interp_make_guarded] halving, replaced by one [Ltok]. *)
  Lemma type_deref_uniq_own_instr {𝔄} κ p n (ty: type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr_ty E L I +[p ◁ &uniq{κ} (own_ptr n ty)] (!p) (&uniq{κ} ty)
      (λ post '-[m], λ mask π, ∀ m',
        uniq_bor_current m' = (uniq_bor_current m).2 →
        uniq_bor_future m' π = (uniq_bor_future m π).2 →
        of_cloc (uniq_bor_loc m') = (uniq_bor_current m).1 →
        of_cloc (uniq_bor_loc m') = (uniq_bor_future m π).1 →
        post m' mask π)%type.
  Proof.
    move=> Alv. apply typed_instr_of_memload_with_cumutime1.
    move=> [[[[[l [l1 x1]] ξi] d'] g'] ξidx] v d tid post mask.
    iIntros "#LFT #PROPH #UNIQ #E L %Hp [gho %Phys] #Obs W".
    iDestruct (Alv with "L E") as "#Alv".
    rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Hle & UniqBody & #PtBase & #Pers)".
    inversion Phys as [Eqv].
    iDestruct "Pers" as "[Dead|#Pers2]".
    { (* [κ] is already dead, so the lifetime context is contradictory *)
      iDestruct "Dead" as (κ'') "[#Incl0 #Dead']".
      iDestruct (dincl_sem with "Incl0") as "#Incl'".
      iDestruct (guard_trans with "Alv Incl'") as "#G3".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G3 L Wg") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    destruct d' as [|d''].
    { rewrite own_ptr_gho_pers /=. by iDestruct "Pers2" as "[]". }
    iDestruct "UniqBody" as "(ξVo & ξTok & #ξBor)".
    set ξ := PrVar (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l1, x1))) ξi.
    have Hinj : Inj eq eq ((!ₛ) (pair_with_locₛ (𝔄:=𝔄) l1)) by move=> ??[=].
    have Hmask : (↑Nllft ∪ ↑prophN ∪ ↑uniqN : coPset) ⊆ ⊤ by set_solver.
    iMod (Ltok_alloc with "L W") as "[W (%γ & #key & f)]".
    iDestruct (Ltok_guard_frac with "key") as "#Gfrac".
    iAssert (frac_tok γ 1 &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "Gfrac Alv"). }
    set Px := (frac_tok γ 1 ∗ .VO[ξ] (l1, x1) (S d'', g') ∗
               idx_bor_tok ξidx)%I.
    iAssert (Px &&{Wguard}&&> @[κ])%I as "#GPκ".
    { iApply (guard_lhs_sep_l with "Gκ"). }
    iAssert (Px &&{Wguard}&&> idx_bor_tok ξidx)%I as "#GPtok".
    { iApply guard_intro. iIntros "!> (f & vo & tok)". iFrame "tok".
      iIntros "tok". iFrame. }
    iDestruct (idxbor_fml_sem_1 with "ξBor") as "#ξBor1".
    iDestruct (llftl_idx_bor_guard' κ ξidx _ Px with "LFT ξBor1 GPκ GPtok")
      as "#Gexists".
    iDestruct (uniq_guards_get_guards_pt (own_ptr n ty) (frac_tok γ 1) (@[κ])
      (idx_bor_tok ξidx) (l1, x1) (S d'') g' ξi tid l with "Gexists")
      as "#Gpt".
    iAssert (Px &&{Wguard}&&> l #↦∗_)%I as "#GPtBase".
    { iApply (guard_trans with "GPκ []").
      iApply (guard_rhs_iff (cmapstoany_fml_sem l)).
      iApply (dguard_alive_sem with "PtBase"). }
    iDestruct (guard_cloc_combine_fancy with "GPtBase Gpt") as "#Gfull".
    iModIntro. iFrame "W".
    iExists l, l1, (deref_uniq_own_src γ ξ (l1, x1) (S d'') g' ξidx).
    iSplit; [done|].
    iSplitL "f ξVo ξTok".
    { rewrite deref_uniq_own_src_sem. iFrame. }
    iSplit.
    { iApply (guard_lhs_iff (deref_uniq_own_src_sem γ ξ (l1, x1) (S d'') g'
        ξidx)).
      rewrite /= -heap_mapsto_cells_fancy_fmap_eq. iApply "Gfull". }
    iIntros "H W". iEval (rewrite deref_uniq_own_src_sem) in "H".
    iDestruct "H" as "(f & ξVo & ξTok)".
    iMod (uniq_body_transform (own_ptr n ty) ty (l1, x1) x1 (S d'') g' ξi ξidx
      κ tid l (l1, repeat [] (length (ty_phys ty x1 tid))) ⊤ γ L 1
      (pair_with_locₛ l1) Hinj Hmask
      with "LFT PROPH UNIQ [] Gκ [$key $f] [$ξVo $ξTok $ξBor] W")
      as "[W (%ζi & %ζidx & #Obs2 & UniqBody & tok)]".
    { iIntros "[gho pt]". rewrite own_ptr_gho /=.
      iDestruct "gho" as "(phys & free & gho)".
      iDestruct (ty_gho_depth_mono ty d'' g' (S d'') g' x1 tid with "gho")
        as "[gho _]"; [lia|lia|]. iModIntro.
      rewrite -heap_cloc_mapsto_fancy_empty. iFrame "gho phys".
      iIntros (y e h) "[gho2 pt2]". iModIntro. iExists (S e), h.
      rewrite own_ptr_gho /=. iFrame "pt gho2 free".
      rewrite (_ : length (ty_phys ty x1 tid) = length (ty_phys ty y tid));
        [|by rewrite !ty_size_eq].
      by rewrite -heap_cloc_mapsto_fancy_empty. }
    iMod (Ltok_withdraw with "tok W") as "[W L]".
    iModIntro. iFrame "W".
    iExists ((l1, repeat [] (length (ty_phys ty x1 tid))), x1, ζi, S d'', g',
      ζidx).
    iFrame "L". iSplit; last first.
    { iCombine "Obs Obs2" as "#Obs3".
      iApply (proph_obs_impl with "Obs3")=> π [Ha Hb]. apply Ha; [done|..].
      - rewrite /uniq_bor_future /= Hb //.
      - done.
      - rewrite /uniq_bor_future /= Hb //. }
    rewrite /ty_own uniq_bor_gho. iSplit; [|done].
    iSplitR; [iApply "Incl"|]. iSplitR; [iPureIntro; lia|].
    iFrame "UniqBody". iSplitR.
    { iApply dguard_cmapstoany_nil. }
    iRight. rewrite own_ptr_gho_pers /=.
    iApply (ty_gho_pers_depth_mono ty d'' g' (S d'') g' x1 tid with "Pers2");
      lia.
  Qed.

  Lemma type_deref_uniq_own {𝔄 𝔅l ℭl 𝔇} κ x p e n (ty: type 𝔄)
      (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L I (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (own_ptr n ty)] T T' trx →
    lctx_lft_alive E L κ →
    (∀v: val, typed_body E L I C (v ◁ &uniq{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e) (trx ∘
      (λ post '(m -:: bl), λ mask π, ∀ m',
        uniq_bor_current m' = (uniq_bor_current m).2 →
        uniq_bor_future m' π = (uniq_bor_future m π).2 →
        of_cloc (uniq_bor_loc m') = (uniq_bor_current m).1 →
        of_cloc (uniq_bor_loc m') = (uniq_bor_future m π).1 →
        tr post (m' -:: bl) mask π))%type.
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_let; [by eapply type_deref_uniq_own_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=> ??. apply Htrx. by case.
  Qed.

  (** Dereferencing a shared borrow of an owning pointer.

    The original's guard source is [llctx_interp L] itself; here it has to be
    a formula, so the context is turned into an [Ltok] for the duration of
    the read and withdrawn afterwards.  Its [£] and the guard indices it
    sizes with [leaf_goal laters to …] are gone. *)
  Lemma type_deref_shr_own_instr {𝔅} {E L I} κ p n (ty : type 𝔅) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L I +[p ◁ &shr{κ} (own_ptr n ty)] (!p) (&shr{κ} ty)
      (λ post '-[(l1, (l2, a))], λ mask π,
        ∀ l2', of_cloc l2' = l2 → post (l2', a) mask π).
  Proof.
    move=> Alv. apply typed_instr_of_memload.
    move=> [l1 [l2 x2]] v d tid post mask.
    iIntros "#LFT #PROPH #UNIQ #E L %Hp own #Obs W".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct "own" as "[gho %phys]".
    destruct d as [|d']; [by iDestruct (false_fml_sem_1 with "gho") as "[]"|].
    rewrite shr_bor_gho /=. iDestruct "gho" as "#(Gp & Ggho & pers)".
    destruct d' as [|d''].
    { rewrite own_ptr_gho_pers /=. by iDestruct "pers" as "[]". }
    iMod (Ltok_alloc with "L W") as "[W (%γ & [#key f])]".
    iAssert (frac_tok γ 1 &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "[] Alv"). iApply (Ltok_guard_frac with "key"). }
    iModIntro. iFrame "W". iExists l1, l2, (gsrc_fml (GFrac γ 1)).
    inversion phys. iSplit; [done|].
    iSplitL "f"; [by iApply (gsrc_fml_sem_2 (s := GFrac γ 1))|].
    iSplit.
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γ 1))).
      rewrite /= -heap_mapsto_cells_fancy_fmap_eq.
      iDestruct (dguard_alive_sem' (cells_fml_sem _ _ _) with "Gp") as "#Gp0".
      iApply (guard_trans with "Gκ Gp0"). }
    iIntros "f W".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ 1) with "f") as "f".
    iMod (Ltok_withdraw with "[$key $f] W") as "[W L]".
    iModIntro. iFrame "W".
    iExists ((l2, repeat [] (length (ty_phys ty x2 tid))), x2). iFrame "L".
    iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Ha. by apply Ha. }
    rewrite /ty_own shr_bor_gho /=. iSplit; [|done].
    iSplit.
    { iApply (dguard_trans with "Ggho []"). iApply dguard_intro.
      iIntros (sem' Hs) "!> g".
      rewrite !(sep_sem_at Hs) /mapsto_fml !(cells_sem_at Hs)
        (freeable_sem_at Hs).
      iDestruct "g" as "(pt & free & gho)".
      rewrite -heap_mapsto_cells_fancy_empty. iFrame "pt".
      iIntros "pt". iFrame. }
    iSplit.
    { iApply (dguard_trans with "Ggho []"). iApply dguard_intro.
      iIntros (sem' Hs) "!> g".
      rewrite !(sep_sem_at Hs) /mapsto_fml (cells_sem_at Hs)
        (freeable_sem_at Hs).
      iDestruct "g" as "(pt & free & gho)".
      iDestruct (ty_gho_depth_mono_at ty sem' Hs d'' (S (S d'')) (S (S d''))
        (S (S (S d''))) x2 tid with "gho") as "[gho back]"; [lia|lia|].
      iSplitL "gho"; [iExact "gho"|]. iIntros "gho".
      iDestruct ("back" with "gho") as "$". iFrame. }
    rewrite own_ptr_gho_pers /=.
    iApply (ty_gho_pers_depth_mono ty d'' (S (S d'')) (S (S d''))
      (S (S (S d''))) x2 tid with "pers"); lia.
  Qed.

  Lemma type_deref_shr_own {𝔄 𝔅l ℭl 𝔇} κ x p e n (ty: type 𝔄)
      (T: tctx 𝔅l) (T': tctx ℭl) trx tr E I L (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (own_ptr n ty)] T T' trx →
    lctx_lft_alive E L κ →
    (∀v: val, typed_body E L I C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e) (trx ∘
      (λ post '((l1, (l2, a)) -:: bl), λ mask π,
        ∀ l2', of_cloc l2' = l2 → tr post ((l2', a) -:: bl) mask π))%type.
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_let; [by eapply type_deref_shr_own_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=> ??. apply Htrx. by case.
  Qed.

  (** A fraction of the local context paired with a borrow token, as a
    formula.  The original's guard sources are plain [iProp]s; here every
    guard source that goes into the Points-To Cell Logic must be named. *)
  Definition frac_idx_src (γ: gname) (q: Qp) (idx: Idx) : FML $oi Σ :=
    (gsrc_fml (GFrac γ q) ∗ idx_bor_tok_fml idx)%FML.

  Lemma frac_idx_src_sem γ q idx :
    bor_sem (frac_idx_src γ q idx) ⊣⊢ frac_tok γ q ∗ idx_bor_tok idx.
  Proof.
    rewrite /frac_idx_src bor_sep_sem (gsrc_fml_sem (GFrac γ q))
      idx_bor_tok_fml_sem //.
  Qed.
  Lemma frac_idx_src_sem_1 γ q idx :
    bor_sem (frac_idx_src γ q idx) ⊢ frac_tok γ q ∗ idx_bor_tok idx.
  Proof. by rewrite frac_idx_src_sem. Qed.
  Lemma frac_idx_src_sem_2 γ q idx :
    frac_tok γ q ∗ idx_bor_tok idx ⊢ bor_sem (frac_idx_src γ q idx).
  Proof. by rewrite frac_idx_src_sem. Qed.

  (** What [type_deref_uniq_uniq_instr] leaves in the outer borrow while the
    inner one is in use: the inner borrow's value observer, the outer one's
    prophecy controller, and the inner type's persistent part. *)
  Definition deref_uniq_uniq_mid_fml {𝔄} (ty: type 𝔄) (x0: ~~ (uniq_borₛ 𝔄))
      (ξi ωi: positive) (ωidx: Idx) (κ': lft) (tid: thread_id) (l1: cloc)
      : FML $oi Σ :=
    ex_fml (λ x' : ~~𝔄, ex_fml (λ d' : nat, ex_fml (λ g' : nat,
      (.VOx[PrVar (𝔄 ↾ prval_to_inh (vπ (uniq_bor_current x0))) ωi]
         x' (d', g') ∗
       .PCx[PrVar (uniq_borₛ 𝔄 ↾ prval_to_inh (vπ x0)) ξi]
         (l1, x', ωi, d', g', ωidx)
         (@vπ (uniq_borₛ 𝔄) (l1, x', ωi, d', g', ωidx)) (S d', g') ∗
       guard_fml (alive_fml κ') (cmapstoany_fml l1) ∗
       (basically_dead_fml κ' ∨ ty.(ty_gho_persx) x' d' g' tid))%FML))).

  Lemma deref_uniq_uniq_mid_fml_sem {𝔄} (ty: type 𝔄) x0 ξi ωi ωidx κ' tid l1 :
    bor_sem (deref_uniq_uniq_mid_fml ty x0 ξi ωi ωidx κ' tid l1) ⊣⊢
      ∃ (x': ~~𝔄) (d' g': nat),
        .VO[PrVar (𝔄 ↾ prval_to_inh (vπ (uniq_bor_current x0))) ωi]
          x' (d', g') ∗
        .PC[PrVar (uniq_borₛ 𝔄 ↾ prval_to_inh (vπ x0)) ξi]
          (l1, x', ωi, d', g', ωidx)
          (@vπ (uniq_borₛ 𝔄) (l1, x', ωi, d', g', ωidx)) (S d', g') ∗
        dguard (alive_fml κ') (cmapstoany_fml l1) ∗
        (basically_dead κ' ∨ ty_gho_pers ty x' d' g' tid).
  Proof.
    rewrite /deref_uniq_uniq_mid_fml ex_fml_sem. apply bi.exist_proper=> x'.
    rewrite ex_fml_sem. apply bi.exist_proper=> d'.
    rewrite ex_fml_sem. apply bi.exist_proper=> g'.
    rewrite !bor_sep_sem vo_fml_sem pc_fml_sem or_fml_sem
      basically_dead_fml_sem //.
  Qed.

  (** Dereferencing a unique borrow of a unique borrow.

    The original's two halves of [llctx_interp L] are the two halves of one
    [Ltok]; its [⧗]/[⧖]/[£] and all the laters they strip are gone. *)
  Lemma type_deref_uniq_uniq_instr {𝔄 E L I} κ κ' p (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L I +[p ◁ &uniq{κ} (&uniq{κ'} ty)] (!p) (&uniq{κ} ty)
      (λ post '-[m], λ mask π, ∀ m',
        uniq_bor_loc m' = uniq_bor_loc (uniq_bor_current m) →
        uniq_bor_current m' = uniq_bor_current (uniq_bor_current m) →
        uniq_bor_future m' π = (uniq_bor_future m π).1 →
        uniq_bor_future (uniq_bor_current m) π = (uniq_bor_future m π).2 →
        post m' mask π)%type.
  Proof.
    move=> Alv. apply typed_instr_of_memload_with_cumutime1.
    move=> [[[[[l [[[[[l1 x1] ωi] d1] g1] ωidx]] ξi] d0] g0] ξidx]
      v d tid post mask.
    iIntros "#LFT #PROPH #UNIQ #E L %Hp [gho %Phys] #Obs W".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]".
    iDestruct (Ltok_split_1 with "tok") as "[[#key f1] [_ f2]]".
    iDestruct (Ltok_guard_frac with "key") as "#Gfrac".
    iAssert (frac_tok γ (1/2) &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "Gfrac Alv"). }
    rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Ineqs & UniqBody & #PtBase & #Pers)".
    iDestruct "UniqBody" as "(ξVo & ξTok & #ξBor)".
    iDestruct (dincl_sem with "Incl") as "#Incls".
    iDestruct (dincl_trans with "Incl []") as "#Inκκ'd";
      [iApply dincl_intersect_l|].
    iDestruct (dincl_trans with "Incl []") as "#Inκrestd";
      [iApply dincl_intersect_r|].
    iAssert (κ ⊑ κ')%I as "#Inκκ'".
    { iApply (guard_trans with "Incls []"). iApply llftl_intersect_incl_l. }
    iAssert (κ ⊑ ty_lft ty)%I as "#Inκrest".
    { iApply (guard_trans with "Incls []"). iApply llftl_intersect_incl_r. }
    iAssert (frac_tok γ (1/2) &&{Wguard}&&> @[κ'])%I as "#Gκ'".
    { iApply (guard_trans with "Gκ Inκκ'"). }
    iDestruct "Pers" as "[Dead|#Pers]".
    { (* [κ] is already dead, so the lifetime context is contradictory *)
      iDestruct "Dead" as (κ'') "[#Incl0 #Dead']".
      iDestruct (dincl_sem with "Incl0") as "#Incl'".
      iDestruct (guard_trans with "Gκ Incl'") as "#G3".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G3 f1 Wg") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    (* Open the outer borrow. *)
    iDestruct (idxbor_fml_to_full with "ξBor ξTok") as "ξBorFull".
    iAssert (bor_sem (gsrc_fml (GFrac γ (1/2))) &&{Wguard}&&> @[κ])%I
      as "#Gκx".
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γ (1/2)))). iApply "Gκ". }
    iDestruct (llftl_bor_acc_guarded ⊤ (gsrc_fml (GFrac γ (1/2))) κ
      with "LFT ξBorFull Gκx [f1]") as "A";
      [by iApply (gsrc_fml_sem_2 (s := GFrac γ (1/2)))|].
    iDestruct (fupdw_incl (W:=alerus_wsat) with "A") as "A'".
    iMod ("A'" with "W") as "[W [Inner Hclose]]".
    iEval (rewrite uniq_body_fml_sem) in "Inner".
    iDestruct "Inner" as (x'' d'' g'') "(ξPc & Gho' & Pt')".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
    subst d'' g''.
    rewrite (uniq_bor_gho κ' ty l1 x1 ωi d1 g1 ωidx d0 g0 tid).
    iDestruct "Gho'" as "(#Incl2 & %Ineqs2 & UniqBody2 & #PtBase2 & #Pers2)".
    iMod (uniq_body_mono_upd ty x1 ωi d1 g1 d1 g0 ωidx κ' tid l1 γ L (1/2) ⊤
      with "LFT UNIQ Gκ' [$key $f2] UniqBody2 W")
      as "[W [[_ f2] UniqBody2]]"; [set_solver|lia|lia|].
    iDestruct "UniqBody2" as "(ωVo & ωTok & #ωBor)".
    set ξ := PrVar (uniq_borₛ 𝔄 ↾
      prval_to_inh (@vπ (uniq_borₛ 𝔄) (l1, x1, ωi, d1, g1, ωidx))) ξi.
    set ω := PrVar (𝔄 ↾ prval_to_inh (vπ x1)) ωi.
    iMod (uniq_update ξ (l1, x1, ωi, d1, g0, ωidx)
      (@vπ (uniq_borₛ 𝔄) (l1, x1, ωi, d1, g0, ωidx)) (S d1, g0)
      with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; [solve_ndisj|].
    (* Hand the outer borrow its new, frozen contents. *)
    set Mid := deref_uniq_uniq_mid_fml ty (l1, x1, ωi, d1, g1, ωidx) ξi ωi
      ωidx κ' tid l1.
    iDestruct ("Hclose" $! (ccells_fml l [FVal (LitV l1.1)] ∗ Mid ∗
      idx_bor_tok_fml ωidx)%FML with "[] [Pt' ωVo ξPc ωTok]") as "B".
    { iIntros "Big". rewrite !bor_sep_sem ccells_fml_sem
        deref_uniq_uniq_mid_fml_sem idx_bor_tok_fml_sem.
      iDestruct "Big" as "(pt & (%y & %e & %h & ωVo & ξPc & #Pt2 & #P2) & tk)".
      iModIntro. rewrite uniq_body_fml_sem.
      iExists (l1, y, ωi, e, h, ωidx), (S e), h. iFrame "ξPc".
      rewrite (uniq_bor_gho κ' ty l1 y ωi e h ωidx (S e) h tid).
      iFrame "P2 pt Incl2 Pt2". iSplitR; [iPureIntro; lia|].
      rewrite /uniq_body /uniq_body_pers_component
        (uniq_body_fml_irrel ty y x1 ωi tid l1 (proof_irrel _ _))
        (proof_irrel (prval_to_inh (vπ y)) (prval_to_inh (vπ x1))).
      iFrame "ωVo tk ωBor". }
    { rewrite !bor_sep_sem ccells_fml_sem deref_uniq_uniq_mid_fml_sem
        idx_bor_tok_fml_sem. iFrame "Pt' ωTok".
      iExists x1, d1, g0. iFrame "ωVo ξPc PtBase2".
      iDestruct "Pers2" as "[#Dead|#P2]"; [by iLeft|iRight].
      iApply (ty_gho_pers_depth_mono ty d1 g1 d1 g0 x1 tid with "P2"); lia. }
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "B") as "B'";
      [set_solver|].
    iMod ("B'" with "W") as "[W [Bor f1]]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ (1/2)) with "f1") as "f1".
    (* Split the frozen contents back apart. *)
    iDestruct (llftl_sep_split ⊤ (ccells_fml l [FVal (LitV l1.1)])
      (Mid ∗ idx_bor_tok_fml ωidx)%FML κ with "LFT Bor") as "C".
    iDestruct (fupdw_incl (W:=alerus_wsat) with "C") as "C'".
    iMod ("C'" with "W") as "[W [BorPt Bor]]".
    iDestruct (llftl_sep_split ⊤ Mid (idx_bor_tok_fml ωidx) κ
      with "LFT Bor") as "C2".
    iDestruct (fupdw_incl (W:=alerus_wsat) with "C2") as "C2'".
    iMod ("C2'" with "W") as "[W [BorMid BorTok]]".
    iDestruct (idxbor_fml_sem_1 with "ωBor") as "#ωBor1".
    iDestruct (llftl_idx_bor_unnest ⊤ κ' κ ωidx (uniq_body_fml ty x1 ωi tid l1)
      with "LFT ωBor1 BorTok") as "D".
    iDestruct (fupdw_incl (W:=alerus_wsat) with "D") as "D'".
    iMod ("D'" with "W") as "[W BorInner]".
    rewrite (idxbor_fml_of_bor (κ:=κ) (Px:=ccells_fml l [FVal (LitV l1.1)])).
    iDestruct "BorPt" as (idxpt) "[#BorPt Tokpt]".
    (* The guard the load runs under. *)
    iAssert (bor_sem (frac_idx_src γ (1/2) idxpt) &&{Wguard}&&> @[κ])%I
      as "#GHκ".
    { iApply (guard_lhs_iff (frac_idx_src_sem γ (1/2) idxpt)).
      iApply (guard_lhs_sep_l with "Gκ"). }
    iAssert (bor_sem (frac_idx_src γ (1/2) idxpt) &&{Wguard}&&>
      idx_bor_tok idxpt)%I as "#GHtok".
    { iApply (guard_lhs_iff (frac_idx_src_sem γ (1/2) idxpt)).
      iApply guard_sep_r. }
    iDestruct (idxbor_fml_sem_1 with "BorPt") as "#BorPt1".
    iDestruct (llftl_idx_bor_guard' κ idxpt _
      (bor_sem (frac_idx_src γ (1/2) idxpt)) with "LFT BorPt1 GHκ GHtok")
      as "#G1".
    iDestruct (guard_rhs_sep_r with "G1") as "#G2".
    iDestruct (guard_rhs_iff (ccells_fml_sem l [FVal (LitV l1.1)]) with "G2")
      as "#G3".
    iDestruct (dguard_alive_sem' (cmapstoany_fml_sem l) with "PtBase")
      as "#PtBase0".
    iDestruct (guard_trans with "GHκ PtBase0") as "#G4".
    iDestruct (guard_cloc_combine_fancy with "G4 G3") as "#Gfull".
    inversion Phys as [Eqv].
    iModIntro. iFrame "W". iExists l, l1.1, (frac_idx_src γ (1/2) idxpt).
    iSplit; [done|].
    iSplitL "f1 Tokpt"; [iApply frac_idx_src_sem_2; iFrame|].
    iSplit.
    { rewrite /= -heap_mapsto_cells_fancy_fmap_eq. iApply "Gfull". }
    iIntros "H W". iDestruct (frac_idx_src_sem_1 with "H") as "[f1 _]".
    (* Merge the frozen observer with the inner borrow and open it. *)
    iDestruct (llftl_bor_shorten (κ' ⊓ κ) κ with "[] BorInner") as "BorInner".
    { iApply llftl_incl_glb; [iApply "Inκκ'"|iApply lft_incl_refl]. }
    iDestruct (llftl_sep_join ⊤ Mid (uniq_body_fml ty x1 ωi tid l1) κ
      with "LFT BorMid BorInner") as "F".
    iDestruct (fupdw_incl (W:=alerus_wsat) with "F") as "F'".
    iMod ("F'" with "W") as "[W Bor2]".
    iDestruct (llftl_bor_acc_guarded ⊤ (gsrc_fml (GFrac γ (1/2))) κ
      with "LFT Bor2 Gκx [f1]") as "G";
      [by iApply (gsrc_fml_sem_2 (s := GFrac γ (1/2)))|].
    iDestruct (fupdw_incl (W:=alerus_wsat) with "G") as "G'".
    iMod ("G'" with "W") as "[W [Both Hclose2]]".
    iEval (rewrite bor_sep_sem deref_uniq_uniq_mid_fml_sem uniq_body_fml_sem)
      in "Both".
    iDestruct "Both" as "[(%y & %e & %h & ωVo & ξPc & _ & _)
                          (%y' & %e' & %h' & ωPc & gho & pt)]".
    iDestruct (uniq_agree with "ξVo ξPc") as %[Heq2 Heq3].
    inversion Heq2. inversion Heq3. subst y e h.
    iDestruct (uniq_agree with "ωVo ωPc") as %[<- Heq4]. inversion Heq4.
    subst e' h'.
    (* Mint the result's prophecy and resolve the old one against it. *)
    iMod (uniq_intro x1 (vπ x1) (d1, g0) with "PROPH UNIQ") as (ζi) "[ζVo ζPc]";
      [set_solver|].
    set ζ := PrVar (𝔄 ↾ prval_to_inh (vπ x1)) ζi.
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ToζPc)".
    iDestruct (uniq_proph_tok with "ωVo ωPc") as "(ωVo & ω & ToωPc)".
    iMod (uniq_preresolve ξ [ζ; ω] (λ π, (π ζ, π ω))
      with "UNIQ PROPH ξVo ξPc [$ζ $ω]") as "(#Hobs & (ζ & ω & _) & Heqz)";
      [set_solver|apply (proph_dep_prod [_] [_]); apply proph_dep_one|done|].
    iDestruct ("ToζPc" with "ζ") as "ζPc".
    iDestruct ("ToωPc" with "ω") as "ωPc".
    iDestruct ("Hclose2" $! (uniq_body_fml ty x1 ζi tid l1)
      with "[Heqz ωVo ωPc] [ζPc gho pt]") as "H".
    { iIntros "Body". iEval (rewrite uniq_body_fml_sem) in "Body".
      iDestruct "Body" as (y e h) "(ζPc & Gho & Pt)".
      iMod (uniq_update ω y (vπ y) (e, h) with "UNIQ ωVo ωPc")
        as "[ωVo ωPc]"; [solve_ndisj|].
      iDestruct (ty_gho_pers_impl with "Gho") as "#GhoPers".
      iModIntro.
      rewrite bor_sep_sem deref_uniq_uniq_mid_fml_sem uniq_body_fml_sem.
      iSplitR "ωPc Gho Pt"; last first.
      { iExists y, e, h. iFrame "ωPc Gho Pt". }
      iExists y, e, h. iFrame "PtBase2".
      iFrame "ωVo". iSplitL "Heqz ζPc"; last by iRight.
      iApply "Heqz".
      iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
      iApply (proph_eqz_prod with "[Eqz]"); [iFrame "Eqz"|].
      rewrite /= (proof_irrel (to_inh_syn_type (@vπ 𝔄 y inhabitant))
        (prval_to_inh (vπ x1))). iApply proph_eqz_refl. }
    { rewrite uniq_body_fml_sem. iExists x1, d1, g0. iFrame "ζPc pt".
      iDestruct (ty_gho_depth_mono ty d1 g0 d1 g0 x1 tid with "gho")
        as "[$ _]"; lia. }
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "H") as "H'";
      [set_solver|].
    iMod ("H'" with "W") as "[W [Bor3 f1]]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ (1/2)) with "f1") as "f1".
    rewrite (idxbor_fml_of_bor (κ:=κ) (Px:=uniq_body_fml ty x1 ζi tid l1)).
    iDestruct "Bor3" as (ζidx) "[#ζBor ζTok]".
    iDestruct (Ltok_split_2 with "[$key $f1] [$key $f2]") as "tok".
    iMod (Ltok_withdraw with "tok W") as "[W L]".
    iModIntro. iFrame "W". iExists (l1, x1, ζi, d1, g0, ζidx). iFrame "L".
    iSplit; last first.
    { iCombine "Obs Hobs" as "#Obs2".
      iApply (proph_obs_impl with "Obs2")=> π [Ha Hb]. apply Ha; [done|done|..].
      - rewrite /uniq_bor_future /= Hb //.
      - rewrite /uniq_bor_future /= Hb //. }
    rewrite /ty_own (uniq_bor_gho κ ty l1 x1 ζi d1 g0 ζidx d d tid).
    iSplit; [|done].
    iSplitR; [iApply "Inκrestd"|]. iSplitR; [iPureIntro; lia|].
    iFrame "ζVo ζTok ζBor". iSplitR.
    { iApply (dguard_trans with "Inκκ'd PtBase2"). }
    iDestruct "Pers2" as "[Dead|#P2]".
    { iLeft. iApply (basically_dead_incl with "Inκκ'd Dead"). }
    iRight.
    iApply (ty_gho_pers_depth_mono ty d1 g1 d1 g0 x1 tid with "P2"); lia.
  Qed.

  Lemma type_deref_uniq_uniq {𝔄 𝔅l ℭl 𝔇} κ κ' x p e (ty: type 𝔄)
      (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L I (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (&uniq{κ'} ty)] T T' trx →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀v: val, typed_body E L I C (v ◁ &uniq{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e) (trx ∘
      (λ post '(m -:: bl), λ mask π, ∀ m',
        uniq_bor_loc m' = uniq_bor_loc (uniq_bor_current m) →
        uniq_bor_current m' = uniq_bor_current (uniq_bor_current m) →
        uniq_bor_future m' π = (uniq_bor_future m π).1 →
        uniq_bor_future (uniq_bor_current m) π = (uniq_bor_future m π).2 →
        tr post (m' -:: bl) mask π))%type.
  Proof.
    iIntros. iApply typed_body_tctx_incl; [done|].
    by iApply type_let;
      [by eapply type_deref_uniq_uniq_instr|solve_typing| |done].
  Qed.

  (** Dereferencing a shared borrow of a unique borrow.

    The original buys [d*(g+1)] later credits out of [⧖] to strip the [▷]s
    in front of the borrow's ghost assertion; there are none here.  What is
    left is one [guard_acc] against the local context, needed because the
    guard to [l1 #↦∗_] sits inside that ghost assertion. *)
  Lemma type_deref_shr_uniq_instr {𝔄} {E L I} κ κ' p (ty : type 𝔄) :
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    typed_instr_ty E L I +[p ◁ &shr{κ} (&uniq{κ'} ty)] (!p) (&shr{κ} ty)
      (λ post '-[(l, m)], λ mask π,
        post (uniq_bor_loc m, uniq_bor_current m) mask π).
  Proof.
    move=> Alv In. apply typed_instr_of_memload.
    move=> [l [[[[[l1 x1] ξi] d1] g1] ξidx]] v d tid post mask.
    iIntros "#LFT #PROPH #UNIQ #E L %Hp [gho %phys] #Obs W".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (In with "L E") as "#Incl".
    destruct d as [|d'];
      [by iDestruct (false_fml_sem_1 with "gho") as "[]"|].
    rewrite shr_bor_gho /=. iDestruct "gho" as "#(G↦ & Ggho & Pers)".
    rewrite (uniq_bor_gho_pers κ' ty l1 x1 ξi d1 g1 ξidx d' (S d') tid).
    iDestruct "Pers" as "(%Hineq & #InnerPers & #UBPers)".
    (* The guard to [l1 #↦∗_] lives inside the borrow's ghost assertion, so
      the only way to it is to open the outer guard once. *)
    iDestruct (dguard_alive_sem with "Ggho") as "#Ggho0".
    iDestruct (guard_trans with "Alv Ggho0") as "#Lgho".
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "Lgho L Wg") as "[H Lback]".
    iAssert (dguard (alive_fml κ') (cmapstoany_fml l1)) as "#InnerPtBase".
    { iEval (rewrite !bor_sep_sem) in "H".
      by iDestruct "H" as "(_ & _ & _ & $ & _)". }
    iDestruct ("Lback" with "H") as "[Wg L]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & [#key f])]".
    iAssert (frac_tok γ 1 &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "[] Alv"). iApply (Ltok_guard_frac with "key"). }
    inversion phys.
    iModIntro. iFrame "W". iExists l, l1.1, (gsrc_fml (GFrac γ 1)).
    iSplit; [done|].
    iSplitL "f"; [by iApply (gsrc_fml_sem_2 (s := GFrac γ 1))|].
    iSplit.
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γ 1))).
      rewrite /= -heap_mapsto_cells_fancy_fmap_eq.
      iDestruct (dguard_alive_sem' (cells_fml_sem _ _ _) with "G↦") as "#G↦0".
      iApply (guard_trans with "Gκ G↦0"). }
    iIntros "f W".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ 1) with "f") as "f".
    iMod (Ltok_withdraw with "[$key $f] W") as "[W L]".
    iDestruct "InnerPers" as "[Dead|#InnerPers2]".
    { (* [κ'] is already dead, but [κ ⊑ κ'] is alive *)
      iDestruct (dincl_sem with "Incl") as "#Incls".
      iDestruct (guard_trans with "Alv Incls") as "#Alv'".
      iDestruct "Dead" as (κ'') "[#Incl0 #Dead']".
      iDestruct (dincl_sem with "Incl0") as "#Incl'".
      iDestruct (guard_trans with "Alv' Incl'") as "#G2".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G2 L Wg") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    iDestruct (dguard_rhs_sep_r with "Ggho") as "#Ggho3".
    iDestruct (dguard_rhs_sep_r with "Ggho3") as "#Ggho4".
    iDestruct (dguard_rhs_sep_l with "Ggho4") as "#GUB".
    iDestruct (dguard_inner_from_guard_uniq_body ty x1 ξi d1 g1 ξidx κ' tid l1
      (alive_fml κ) with "UBPers GUB Incl") as "#Gghopt".
    iDestruct (dguard_rhs_sep_l with "Gghopt") as "#Ggho5".
    iDestruct (dguard_rhs_sep_r with "Gghopt") as "#Gpt1".
    iModIntro. iFrame "W". iExists (l1, x1). iFrame "L". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Ha. exact Ha. }
    rewrite /ty_own shr_bor_gho /=. iSplit; [|done].
    iSplit.
    { iApply dguard_cloc_combine_fancy; [|iApply "Gpt1"].
      iApply (dguard_trans with "Incl InnerPtBase"). }
    iSplit.
    { iApply (dguard_depth_mono ty d1 g1 (S d') (S (S d')) x1 tid
        with "Ggho5"); lia. }
    iApply (ty_gho_pers_depth_mono ty d1 g1 (S d') (S (S d')) x1 tid
      with "InnerPers2"); lia.
  Qed.

  Lemma type_deref_shr_uniq {𝔄 𝔅l ℭl 𝔇} κ κ' x p e (ty: type 𝔄)
      (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L I (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (&uniq{κ'} ty)] T T' trx →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀v: val, typed_body E L I C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e) (trx ∘
      (λ post '((l, m) -:: bl), λ mask π,
        tr post ((uniq_bor_loc m, uniq_bor_current m) -:: bl) mask π))%type.
  Proof.
    iIntros. iApply typed_body_tctx_incl; [done|].
    iApply type_let;
      [by eapply type_deref_shr_uniq_instr|apply tctx_incl_refl| |done].
    by move=>/= ?[[??]?].
  Qed.
End borrow.
