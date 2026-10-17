(** * Shared borrows

  Ported from VerusBelt ([typing/shr_bor.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  [&shr{κ} ty] is LeLiLo's shared borrow: a *guard* from the lifetime token
  [@[κ]] to the borrowed contents.  The original takes those guards at index
  [g+1] and puts [▷^(g+1)] in front of the persistent ghost part, because
  opening a guard at index [n] costs [n] laters.  Later-free the indices and
  the [▷^(g+1)] both go.

  The price is [TypeContractive].  VerusBelt gets it from
  [guards_contractive_right_if_n_ge_1]: a guard at index ≥ 1 is contractive in
  its right-hand side exactly because opening it introduces a later.  Nola's
  guard introduces none, so it is merely non-expansive, and [&shr{κ}] is only
  [TypeNonExpansive].  Recursive types through a shared borrow are therefore
  out of reach here; see [typing/fixpoint.v]. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.typing Require Import programs.
From nola.alerus.typing Require Export type ctx.
From nola.alerus.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Implicit Type 𝔄 𝔅: syn_type.

Section shr_bor.
  Context `{!typeG FML Σ}.

  Program Definition shr_bor_st {𝔄} (κ: lft) (ty: type 𝔄)
    : simple_type (at_clocₛ 𝔄) := {|
    st_size := 1;
    st_lfts := κ :: ty.(ty_lfts);
    st_E := ty.(ty_E) ++ ty_outlives_E ty κ;

    st_ghox x d g tid := [Sx(d') := d]
      (guard_fml (alive_fml κ)
         ((x.1).1 ↦[^ (x.1).2 ]!∗ ty.(ty_phys) (snd x) tid) ∗
       guard_fml (alive_fml κ) (ty.(ty_ghox) (snd x) d' g tid) ∗
       ty.(ty_gho_persx) (snd x) d' g tid)%FML;

    st_phys x tid := [FVal (LitV (x.1).1)];
  |}.
  Next Obligation.
    move=> ?? ty sem H x d g tid.
    apply (by_succx_persistent_at H)=> d'.
    have ? := guard_fml_pers_at H. have ? := ty_gho_pers_pers_at ty sem H.
    rewrite !(sep_sem_at H). exact _.
  Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> ?? ty sem H d g d' g' x tid ??.
    destruct d as [|d0]=>/=; [rewrite (false_sem_at H); by iIntros "[]"|].
    destruct d' as [|d'0]; [lia|]=>/=.
    have ? := guard_fml_pers_at H. have ? := ty_gho_pers_pers_at ty sem H.
    rewrite !(sep_sem_at H). iIntros "#A".
    iDestruct "A" as "(#Phys & #Gho & #Pers)". iFrame "Phys". iSplit.
    - iApply (dguard_trans_at H with "Gho"). iApply (dguard_intro_at H).
      iIntros (sem' Hs) "!> gho".
      iApply (ty_gho_depth_mono_at ty sem' Hs with "gho"); lia.
    - iApply (ty_gho_pers_depth_mono_at ty sem H with "Pers"); lia.
  Qed.
  Next Obligation.
    move=> ?? ty κ0 x d g tid ξ R Hin.
    destruct d as [|d0]=>/=; [rewrite false_fml_sem; by iIntros "_ _ []"|].
    fml_simpl. iIntros "#LFT #Incl #A".
    iDestruct "A" as "(_ & #Gho & #Pers)". iIntros "#Rk _".
    iApply (ty_guard_proph _ ty κ0 (snd x) d0 g tid ξ R with
      "LFT [] Pers Rk"); [done|..].
    { iApply (llftl_incl_trans with "Incl []"). iApply llftl_intersect_incl_r. }
    iApply (guard_trans with "Rk"). iApply (guard_trans with "Incl").
    iApply (guard_trans with "[] Gho"). iApply llftl_intersect_incl_l.
  Qed.
  Next Obligation. done. Qed.

  (** [&shr{κ} ty] is a simple type; naming it lets its ghost assertion be
    unfolded by [shr_bor_st_gho] below. *)
  Definition shr_bor {𝔄} (κ: lft) (ty: type 𝔄) : type (at_clocₛ 𝔄) :=
    ty_of_st (shr_bor_st κ ty).

  Lemma shr_bor_st_gho {𝔄} κ (ty: type 𝔄) x d g tid :
    st_gho (shr_bor_st κ ty) x d g tid ⊣⊢ [S(d') := d]
      ((@[κ] &&{Wguard}&&> ((x.1).1 ↦[^ (x.1).2 ]!∗ ty.(ty_phys) (snd x) tid)) ∗
       (@[κ] &&{Wguard}&&> ty_gho ty (snd x) d' g tid) ∗
       ty_gho_pers ty (snd x) d' g tid).
  Proof.
    rewrite /st_gho. destruct d as [|d']; [apply false_fml_sem|].
    by rewrite /= !bor_sep_sem !guard_fml_sem !alive_fml_sem cells_fml_sem.
  Qed.

  Lemma shr_bor_gho {𝔄} κ (ty: type 𝔄) x d g tid :
    ty_gho (shr_bor κ ty) x d g tid ⊣⊢ [S(d') := d]
      ((@[κ] &&{Wguard}&&> ((x.1).1 ↦[^ (x.1).2 ]!∗ ty.(ty_phys) (snd x) tid)) ∗
       (@[κ] &&{Wguard}&&> ty_gho ty (snd x) d' g tid) ∗
       ty_gho_pers ty (snd x) d' g tid).
  Proof. apply shr_bor_st_gho. Qed.
  Lemma shr_bor_gho_pers {𝔄} κ (ty: type 𝔄) x d g tid :
    ty_gho_pers (shr_bor κ ty) x d g tid ⊣⊢ [S(d') := d]
      ((@[κ] &&{Wguard}&&> ((x.1).1 ↦[^ (x.1).2 ]!∗ ty.(ty_phys) (snd x) tid)) ∗
       (@[κ] &&{Wguard}&&> ty_gho ty (snd x) d' g tid) ∗
       ty_gho_pers ty (snd x) d' g tid).
  Proof. apply shr_bor_gho. Qed.

  Global Instance into_sep_shr_bor_gho {𝔄} κ (ty: type 𝔄) x d' g tid :
    IntoSep (ty_gho (shr_bor κ ty) x (S d') g tid)
      (@[κ] &&{Wguard}&&> ((x.1).1 ↦[^ (x.1).2 ]!∗ ty.(ty_phys) (snd x) tid))
      ((@[κ] &&{Wguard}&&> ty_gho ty (snd x) d' g tid) ∗
        ty_gho_pers ty (snd x) d' g tid).
  Proof. rewrite /IntoSep shr_bor_gho /=. by iIntros "$". Qed.
  Global Instance from_sep_shr_bor_gho {𝔄} κ (ty: type 𝔄) x d' g tid :
    FromSep (ty_gho (shr_bor κ ty) x (S d') g tid)
      (@[κ] &&{Wguard}&&> ((x.1).1 ↦[^ (x.1).2 ]!∗ ty.(ty_phys) (snd x) tid))
      ((@[κ] &&{Wguard}&&> ty_gho ty (snd x) d' g tid) ∗
        ty_gho_pers ty (snd x) d' g tid).
  Proof. rewrite /FromSep shr_bor_gho /=. by iIntros "$". Qed.

  Global Instance shr_ne {𝔄} κ : NonExpansive (@shr_bor 𝔄 κ).
  Proof. solve_ne_type. Qed.
End shr_bor.

Global Hint Rewrite @shr_bor_gho_pers @shr_bor_gho : fml_sem.

Notation "&shr{ κ }" := (shr_bor κ) (format "&shr{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG FML Σ}.

  (** The original proves [TypeContractive]; see the header for why only
    non-expansiveness survives. *)
  Global Instance shr_type_ne {𝔄} κ : TypeNonExpansive (@shr_bor _ _ _ 𝔄 κ).
  Proof.
    split; [by apply (type_lft_morphism_add_one κ)|done| | |done].
    - move=>/= n ty ty' ?? _ Eq Eq' Eqp x d g tid. rewrite /by_succx.
      destruct d as [|d']=>//. f_equiv; [|f_equiv].
      + by rewrite Eqp.
      + f_equiv. apply Eq.
      + apply Eq'.
    - move=>/= n ty ty' ?? _ Eq Eq' Eqp x d g tid. rewrite /by_succx.
      destruct d as [|d']=>//. f_equiv; [|f_equiv].
      + by rewrite Eqp.
      + f_equiv. apply Eq.
      + apply Eq'.
  Qed.

  Lemma shr_copy {𝔄} κ (ty: type 𝔄) : Copy (&shr{κ} ty).
  Proof. split. - typeclasses eauto. - iIntros. iPureIntro. done. Qed.

  Lemma shr_stack_okay {𝔄} κ (ty: type 𝔄) : StackOkay (&shr{κ} ty).
  Proof. done. Qed.

  Global Instance shr_sync {𝔄} κ (ty: type 𝔄) : Sync ty → Sync (&shr{κ} ty).
  Proof.
    move=> Hsync tid tid' x d g. split; [done|]. split.
    - rewrite !shr_bor_gho. destruct d as [|d]; [reflexivity|]=>/=.
      destruct (Hsync tid tid' (snd x) d g) as [phys [gho pers]].
      by rewrite gho phys pers.
    - rewrite !shr_bor_gho_pers. destruct d as [|d]; [reflexivity|]=>/=.
      destruct (Hsync tid tid' (snd x) d g) as [phys [gho pers]].
      by rewrite gho phys pers.
  Qed.

  (** The original's [⧖ d0] and its [|={…}▷=>^d] are gone with the time
    receipts; changing the thread id of a shared borrow needs no step. *)
  Global Instance shr_send {𝔄} κ (ty: type 𝔄) : Sync ty → Send (&shr{κ} ty).
  Proof.
    move=> Hsync. split.
    - move=> ?? [??] [??] Ha. by inversion Ha.
    - move=> tid tid' x d g G κs.
      have [_ [Hg _]] := shr_sync κ ty Hsync tid tid' x d g.
      iIntros "_ _ lfts _ K A $ !>". iExists x, 0. rewrite Nat.add_0_r.
      iFrame "lfts K". iSplit; [|done]. by iApply (iff_1 Hg).
  Qed.

  Global Instance shr_just_loc {𝔄} κ (ty: type 𝔄) : JustLoc (&shr{κ} ty).
  Proof. iIntros (x d g tid) "A". by iExists _. Qed.

  Lemma shr_resolve {𝔄} κ (ty: type 𝔄) E L :
    resolve E L (&shr{κ} ty) (const (const True)).
  Proof. apply resolve_just. Qed.

  Lemma shr_type_incl {𝔄 𝔅} κ κ' (f: 𝔄 →ₛ 𝔅) ty ty' :
    κ' ⊑ κ -∗ type_incl ty ty' f -∗
      type_incl (&shr{κ} ty) (&shr{κ'} ty') (at_cloc_mapₛ f).
  Proof.
    iIntros "#Incl". iDestruct 1 as "(_ & #Incl2 & #Sub & #SubPers & %Phys)".
    iApply (@type_incl_simple_type _ _ _ (at_clocₛ 𝔄) (at_clocₛ 𝔅) _ _).
    - done.
    - rewrite /ty_lfts /ty_of_st /st_lfts. by iApply lft_intersect_mono.
    - setoid_rewrite shr_bor_st_gho. iIntros "!>" (x d g tid) "A".
      destruct x as [l x]. destruct d as [|d]; [done|]. rewrite /by_succ /=.
      iDestruct "A" as "(#Hphys & #Hgho & #Hpers)". iSplit.
      { rewrite Phys. iApply (guard_trans with "Incl Hphys"). }
      iSplit.
      + iApply (guard_trans with "Incl"). iApply (guard_trans with "Hgho").
        iApply guard_intro. iIntros "!> gho". by iApply "Sub".
      + by iApply "SubPers".
    - iPureIntro. by move=> [l x].
  Qed.

  Lemma shr_subtype {𝔄 𝔅} E L κ κ' (f: 𝔄 →ₛ 𝔅) ty ty' :
    lctx_lft_incl E L κ' κ → subtype E L ty ty' f →
    subtype E L (&shr{κ} ty) (&shr{κ'} ty') (at_cloc_mapₛ f).
  Proof.
    move=> In Sub. iIntros "L". iDestruct (In with "L") as "#In".
    iDestruct (Sub with "L") as "#Sub". iIntros "!> #?".
    iApply shr_type_incl; by [iApply "In"|iApply "Sub"].
  Qed.

  Lemma shr_eqtype {𝔄 𝔅} E L κ κ' (f: 𝔄 →ₛ 𝔅) g ty ty' :
    lctx_lft_eq E L κ κ' → eqtype E L ty ty' f g →
    eqtype E L (&shr{κ} ty) (&shr{κ'} ty') (at_cloc_mapₛ f) (at_cloc_mapₛ g).
  Proof. move=> [??] [??]. split; by apply shr_subtype. Qed.

  (** Reading out of a shared borrow.

    The original hands [typed_read] its own arbitrary [H], namely the [G] that
    guards [llctx_interp L], and spends [£(d+1)] stripping the laters of the
    guard it opens.  Here the guard source has to be a *formula* - the
    Points-To Cell Logic parks it in its read bank - and the one we have is the
    fractional share inside [Ltok]: [gsrc_fml (GFrac γ q)]. *)
  Lemma read_shr {𝔄} (ty: type 𝔄) κ E L :
    Copy ty → lctx_lft_alive E L κ →
    typed_read E L (&shr{κ} ty) ty (&shr{κ} ty) snd (=).
  Proof.
    move=> Hcopy Alv x [|d'] v tid γ q; iIntros "#LFT #E tok T W";
      iDestruct "T" as "[gho %phys]";
      [by iDestruct (false_fml_sem_1 with "gho") as "[]"|].
    iEval (rewrite shr_bor_gho /=) in "gho".
    iDestruct "gho" as "#(A & B & C)".
    (* Open the share once, to read off the aliveness guard. *)
    iDestruct (Ltok_acc with "tok W") as "[L →W]".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct ("→W" with "L") as "[W [#key tok]]".
    (* Compose: the share guards [llctx_interp L], which guards [@[κ]], which
      guards both the physical contents and the inner ghost state. *)
    iAssert (frac_tok γ q &&{Wguard}&&> @[κ])%I as "#G1".
    { iApply (guard_trans with "[] Alv"). iApply Ltok_guard_frac. iFrame "key". }
    iDestruct (guard_trans with "G1 A") as "#GA".
    iDestruct (guard_trans with "G1 B") as "#GB".
    (* The inner ghost state is persistent, so opening its guard once is
      enough to keep it. *)
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "GB tok Wg") as "[#T →Wg]".
    iDestruct ("→Wg" with "T") as "[Wg tok]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iDestruct (copy_concrete with "T") as "%Conc".
    iModIntro. iFrame "W".
    iExists (fst x), (to_concrete (ty_phys ty (snd x) tid)),
      (ty_phys ty (snd x) tid), (gsrc_fml (GFrac γ q)).
    inversion phys. iSplit; [done|].
    iSplit; [iPureIntro; apply length_to_concrete|].
    iSplitL "tok". { by iApply gsrc_fml_sem_2. }
    iSplit.
    { rewrite /= gsrc_fml_sem /=.
      iApply (guard_rhs_iff with "GA").
      rewrite -heap_mapsto_cells_fancy_fmap_eq fmap_to_concrete //. }
    iSplitR.
    { iIntros (l₁ c₁) "↦". rewrite -heap_complete_mapsto_fancy_fmap_eq.
      rewrite (fmap_to_concrete _ Conc). by iFrame. }
    iSplit. { iPureIntro=> _. rewrite fmap_to_concrete //. }
    (* [T] is the inner ghost state at the shared borrow's depth [d'];
      the read hands it out at the outer depth [S d'].  The original needs a
      [▷] here, which the depth-monotonicity accessor replaces. *)
    iSplitR.
    { iSplit; [|done]. iDestruct (ty_gho_depth_mono with "T") as "[$ _]"; lia. }
    iIntros "f W". iModIntro. iFrame "W". iExists x. iSplit; [done|].
    iSplitL "f".
    { rewrite /Ltok. iFrame "key". by iApply (gsrc_fml_sem_1 (s := GFrac γ q)). }
    iSplit; [|done]. rewrite shr_bor_gho /=. by iFrame "A B C".
  Qed.
End typing.

Global Hint Resolve shr_resolve shr_subtype shr_eqtype read_shr : lrust_typing.
