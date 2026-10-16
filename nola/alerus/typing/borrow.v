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
      { rewrite -heap_cloc_mapsto_empty. iApply guard_true. }
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
      iDestruct "Dead" as (κ') "[#Incl' #Dead']".
      iDestruct (guard_trans with "Alv Incl'") as "#G3".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G3 L Wg") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]".
    iMod (resolve_uniq_body ty x0 ξi d' g' idx κ tid l E L γ 1 ⊤
      with "LFT PROPH UNIQ Incl E tok UniqBody W")
      as "[W (#Obs2 & tok & #ShrGuard)]"; [done|done|].
    iMod (Ltok_withdraw with "tok W") as "[W L]".
    iModIntro. iFrame "W L I". iExists -[(l, x0)].
    inversion Phys as [Eqv]. iSplit.
    { iSplit; [|done]. iExists v, (S d). iSplit; [done|].
      rewrite /ty_own shr_bor_gho /=. iSplit; [|by rewrite -Eqv].
      iDestruct (guard_rhs_sep_l with "ShrGuard") as "#ShrGho".
      iDestruct (guard_rhs_sep_r with "ShrGuard") as "#ShrPt".
      iSplit.
      { by iApply (guard_cloc_combine_fancy with "PtBase ShrPt"). }
      iSplit.
      { iApply (guard_trans with "ShrGho []"). iApply guard_intro.
        iIntros "!> G".
        iApply (ty_gho_depth_mono ty d' g' d (S d) x0 tid with "G"); lia. }
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
End borrow.
