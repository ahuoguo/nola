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
