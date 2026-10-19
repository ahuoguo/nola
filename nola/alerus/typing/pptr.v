(** * Raw pointers and points-to permissions

  Ported from VerusBelt ([typing/pptr.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer).

  [tracked_ty_with_prop] carried an arbitrary [P : iProp Σ] inside the ghost
  assertion; ghost assertions are formulas here, so it carries a
  [Px : FML $oi Σ] instead.  (It is unused upstream as well.)  The receipts
  the permission operations mint and the [▷]s they strip are gone. *)

From nola.alerus.lang.lib Require Import memcpy.
From nola.alerus.typing Require Export type tracked own product sum uniq_bor
  uniq_util shr_bor.
From nola.alerus.typing Require Import uninit type_context programs
  programs_util freeable_util lft_contexts.
From nola.alerus.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation WpwNotation.

Implicit Type 𝔄 𝔅: syn_type.

Section ptr.
  Context `{!typeG FML Σ}.

  Program Definition ptr_ty : type locₛ :=
    {| pt_size := 1;
       pt_ghox (l: ~~locₛ) _ := empty_fml;
       pt_phys (l: ~~locₛ) _ := [ FVal (LitV (LitLoc l)) ];
    |}.
  Next Obligation. move=> sem H *. rewrite (empty_sem_at H). exact _. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.

  Lemma ptr_gho l d g tid : ty_gho ptr_ty l d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.
  Lemma ptr_gho_pers l d g tid : ty_gho_pers ptr_ty l d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.

  Global Instance ptr_copy: Copy ptr_ty.
  Proof. split; [apply _|]. iIntros. iPureIntro. done. Qed.

  Lemma ptr_stack_okay : StackOkay ptr_ty.
  Proof. done. Qed.

  Global Instance ptr_send: Send ptr_ty.
  Proof.
    intros. split; trivial.
    - intros. unfold syn_abstract in H. by subst x'.
    - iIntros (tid tid' x0 d g G κs) "_ _ lfts _ tok _ $ !>".
      iExists x0, 0%nat. iFrame "lfts tok".
      iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Global Instance ptr_sync: Sync ptr_ty.
  Proof. move=> *. split; [done|]. split; reflexivity. Qed.

  Lemma ptr_resolve E L : resolve E L ptr_ty (const (const True)).
  Proof. apply resolve_just. Qed.
End ptr.

Global Hint Rewrite @ptr_gho @ptr_gho_pers : fml_sem.

Section points_to.
  Context `{!typeG FML Σ}.

  (** The original's [P] is an arbitrary [iProp Σ]; a ghost assertion is a
    formula here, so [Px] is one. *)
  Program Definition tracked_ty_with_prop {𝔄} (ty: type 𝔄) (Px : FML $oi Σ)
      : type (trackedₛ 𝔄) := {|
    ty_size := 0;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_ghox x d g tid := (Px ∗ ty.(ty_ghox) x d g tid)%FML;
    ty_gho_persx x d g tid := ty.(ty_gho_persx) x d g tid;
    ty_phys x tid := [];
  |}%I.
  Next Obligation. intros; done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> ? ty Px sem H *. rewrite !(sep_sem_at H). iIntros "[HP gho]".
    iDestruct (ty_gho_depth_mono_at ty sem H with "gho") as "[gho wand]";
      [done|done|].
    iFrame "HP gho". iIntros "[$ ?]". by iApply "wand".
  Qed.
  Next Obligation.
    move=> ? ty Px sem H *. by apply (ty_gho_pers_depth_mono_at ty sem H).
  Qed.
  Next Obligation.
    move=> *. iIntros "LFT Incl Pers Rk Rg".
    iDestruct (guard_rhs_iff (bor_sep_sem _ _) with "Rg") as "Rg'".
    iDestruct (guard_rhs_sep_r with "Rg'") as "Rg2".
    by iApply (ty_guard_proph with "LFT Incl Pers Rk Rg2").
  Qed.
  Next Obligation.
    move=> ? ty Px sem H *. by apply (ty_gho_pers_pers_at ty sem H).
  Qed.
  Next Obligation.
    move=> *. rewrite bor_sep_sem. iIntros "[_ gho]".
    by iApply ty_gho_pers_impl.
  Qed.

  Definition points_to_ty {𝔄} ty :=
    tracked_ty (@own_ptr _ _ _ 𝔄 (ty_size ty) ty).

  Global Instance points_to_ne {𝔄} : NonExpansive (@points_to_ty 𝔄).
  Proof.
    rewrite /points_to_ty=> m ty1 ty2 Eq. apply tracked_ne.
    destruct Eq as [Hsz ?]. rewrite Hsz. by apply own.own_ne.
  Qed.

  Lemma points_to_stack_okay {𝔄} (ty: type 𝔄) : StackOkay (points_to_ty ty).
  Proof. done. Qed.

  Global Instance points_to_send {𝔄} (ty: type 𝔄) :
    Send ty → Send (points_to_ty ty).
  Proof. exact _. Qed.

  Global Instance points_to_sync {𝔄} (ty: type 𝔄) :
    Sync ty → Sync (points_to_ty ty).
  Proof. exact _. Qed.

  Lemma points_to_resolve {𝔄} E L (ty: type 𝔄) Φ :
    resolve E L ty Φ → resolve E L (points_to_ty ty) (λ '(l, s), Φ s).
  Proof. move=> Rslv. apply tracked_resolve. by eapply own_resolve. Qed.

  Lemma points_to_type_incl {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) ty1 ty2 :
    type_incl ty1 ty2 f -∗
      type_incl (points_to_ty ty1) (points_to_ty ty2)
        (tracked_mapₛ (at_loc_mapₛ f)).
  Proof.
    iIntros "Hincl". iApply tracked_type_incl.
    iDestruct "Hincl" as "(%Hsz & ?)". rewrite Hsz.
    iApply own_type_incl. by iFrame.
  Qed.

  Lemma points_to_subtype {𝔄 𝔅} E L (f: 𝔄 →ₛ 𝔅) ty ty' :
    subtype E L ty ty' f →
    subtype E L (points_to_ty ty) (points_to_ty ty')
      (tracked_mapₛ (at_loc_mapₛ f)).
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iApply points_to_type_incl; by [|iApply "Incl"].
  Qed.
End points_to.

Section typing.
  Context `{!typeG FML Σ}.

  Definition PPtr2Own : val := (λ: ["ptr"; "perm"], "ptr")%V.

  Lemma typed_pptr_to_own {𝔄} (perm ptr : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[ptr ◁ ptr_ty; perm ◁ own_ptr 0 (points_to_ty ty)]
      (PPtr2Own [ptr; perm]) (λ v, +[v ◁ own_ptr (ty_size ty) ty])
      (λ post '-[l; (_, (l', x))], λ mask π,
        l = l' ∧ post -[(l, x)] mask π).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #PROPH #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [l [[? [l' x]] []]].
    iDestruct "TY" as "(Hptr & Hperm & _)".
    iDestruct "Hptr" as (pl d Heval) "[_ %Hphys]".
    iDestruct "Hperm" as (pl' d' Heval') "[Hown %Hphys']".
    simpl in Hphys, Hphys'. injection Hphys=> ?; subst pl.
    injection Hphys'=> ?; subst pl'.
    destruct d' as [|d'];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite own_ptr_gho /=. iDestruct "Hown" as "(_ & _ & Hown)".
    rewrite tracked_ty_gho.
    destruct d' as [|d'];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite own_ptr_gho /=. iDestruct "Hown" as "(Hl & Hfree & Hgho)".
    iApply twpw_fupdw_nonval; [done|].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [<- _]]; [solve_ndisj|].
    iModIntro. iFrame "W".
    wp_bind ptr. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_bind perm. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_rec. iModIntro.
    iExists -[(l, x)]. iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> ? Hpost. apply Hpost. }
    iSplit; [|done]. iExists (LitV (LitLoc l)), (S (S d')).
    iSplit; [done|].
    rewrite /ty_own own_ptr_gho /=. iFrame "Hl Hfree". iSplit; [|done].
    iDestruct (ty_gho_depth_mono with "Hgho") as "[$ _]"; [lia|lia].
  Qed.

  Definition PPtrFromOwn : val :=
    (λ: ["p"], let: "x" := new [ #1 ] in "x" <- "p";; "x")%V.

  Lemma typed_pptr_from_own {𝔄} (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ own_ptr (ty_size ty) ty] (PPtrFromOwn [p])
      (λ v, +[v ◁ own_ptr 1 (prod_ty ptr_ty (points_to_ty ty))])
      (λ post '-[(l, x)], λ mask π, ∀ lc, post -[(lc, (l, (l, x)))] mask π).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #PROPH #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [[l x] []]. iDestruct "TY" as "(TY & _)".
    iDestruct "TY" as (pl d Heval) "[Hown %Hphys]".
    simpl in Hphys. injection Hphys=> ?; subst pl.
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite own_ptr_gho /=. iDestruct "Hown" as "(Hl & Hfree & Hgho)".
    wp_bind p. iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    wp_rec. wp_bind (new [ #1 ])%E. iApply (twp_new 1); [lia|done|].
    iIntros (l') "[Hfree' Hl']". wp_let.
    rewrite Z2Nat.inj_pos. change (Pos.to_nat 1) with 1%nat.
    rewrite /= heap_mapsto_vec_singleton.
    wp_bind (_ <- _)%E.
    iApply (twp_write_na (W:=alerus_wsat) _ _ l' (LitV (LitLoc l))
      with "[Hl']"); [iFrame "Hl'"|]. iIntros "Hl'". wp_seq.
    iExists -[(l', (l, (l, x)))]. iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> ? Hpost. apply Hpost. }
    iSplit; [|done]. iExists #l', (S (S d)). iSplit; [done|].
    rewrite /ty_own own_ptr_gho /= prod_ty_gho /= tracked_ty_gho
      own_ptr_gho /= ptr_gho.
    iSplit; [|done]. iSplitL "Hl'".
    { iEval (rewrite -heap_mapsto_vec_singleton
        -(heap_mapsto_fancy_fmap_eq l')) in "Hl'". iExact "Hl'". }
    iSplitL "Hfree'".
    { rewrite freeable_sz_full. iDestruct "Hfree'" as "[A|%E0]";
        [by iLeft|iRight; iPureIntro; lia]. }
    iSplit; [done|]. iFrame "Hl Hfree".
    iDestruct (ty_gho_depth_mono with "Hgho") as "[$ _]"; [lia|lia].
  Qed.

  Lemma cloc_mapsto_empty_cells {𝔄} (ty: type 𝔄) l x tid :
    l ↦!∗ ty_phys ty x tid ⊣⊢
      (l, repeat (@nil cell_id) (ty_size ty)) #↦!∗ ty_phys ty x tid.
  Proof.
    rewrite -(ty_size_eq ty x tid).
    exact (heap_cloc_mapsto_fancy_empty l (ty_phys ty x tid)).
  Qed.

  Lemma mapsto_empty_cells {𝔄} (ty: type 𝔄) l x tid :
    l ↦!∗ ty_phys ty x tid ⊣⊢
      ((l, repeat (@nil cell_id) (ty_size ty)).1
        ↦[^ (l, repeat (@nil cell_id) (ty_size ty)).2]!∗
          ty_phys ty x tid).
  Proof.
    rewrite -(ty_size_eq ty x tid).
    exact (heap_mapsto_cells_fancy_empty l (ty_phys ty x tid)).
  Qed.

  Definition PPtrBorrow : val := (λ: ["ptr"; "perm_ref"], "ptr")%V.

  Lemma typed_pptr_borrow {𝔄} κ (ptr perm_ref : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[ptr ◁ ptr_ty; perm_ref ◁ shr_bor κ (points_to_ty ty)]
      (PPtrBorrow [ptr; perm_ref]) (λ v, +[v ◁ shr_bor κ ty])
      (λ post '-[l; (cl, (l', x))], λ mask π,
        l = l' ∧ post -[((l, repeat [] ty.(ty_size)), x)] mask π).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #PROPH #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [l [[c [l' x]] []]].
    iDestruct "TY" as "(Hptr & Hperm & _)".
    iDestruct "Hptr" as (pl d Heval) "[_ %Hphys]".
    simpl in Hphys. injection Hphys=> ?; subst pl.
    iDestruct "Hperm" as (pl' d' Heval') "[Hshr %Hphys']".
    simpl in Hphys'. injection Hphys'=> ?; subst pl'.
    destruct d' as [|[|d']].
    { by iDestruct (false_fml_sem_1 with "Hshr") as "[]". }
    { rewrite shr_bor_gho /=. iDestruct "Hshr" as "(_ & _ & #Hpers)".
      rewrite tracked_ty_gho_pers own_ptr_gho_pers /=.
      by iDestruct "Hpers" as "[]". }
    rewrite shr_bor_gho /=. iDestruct "Hshr" as "#(_ & Hshr & Hpers)".
    rewrite tracked_ty_gho_pers own_ptr_gho_pers /=.
    iDestruct (dguard_rhs_sep_l with "Hshr") as "#Hshrpt".
    iDestruct (dguard_rhs_sep_r with "Hshr") as "#Hshr3".
    iDestruct (dguard_rhs_sep_r with "Hshr3") as "#Hshrgho".
    iApply twpw_fupdw_nonval; [done|].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [<- _]]; [solve_ndisj|].
    iModIntro. iFrame "W".
    wp_bind ptr. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_bind perm_ref.
    iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->). wp_rec.
    iModIntro. iExists -[((l, repeat [] ty.(ty_size)), x)].
    iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> ? [_ Hpost]. apply Hpost. }
    iSplit; [|done]. iExists (LitV (LitLoc l)), (S (S (S d'))).
    iSplit; [done|].
    rewrite /ty_own shr_bor_gho /=. iSplit; [|done]. iSplit.
    { have Hpt : ∀ sem', alt_sem sem' →
        sem' (mapsto_fml l (ty_phys ty x tid)) ⊣⊢
        sem' (cells_fml (l, repeat (@nil cell_id) (ty_size ty)).1
               (l, repeat (@nil cell_id) (ty_size ty)).2 (ty_phys ty x tid)).
      { move=> sem' Hs. rewrite /mapsto_fml !(cells_sem_at Hs) ty_size_eq //. }
      iApply (dguard_rhs_iff Hpt with "Hshrpt"). }
    iSplit.
    { iApply (dguard_depth_mono ty with "Hshrgho"); lia. }
    iApply (ty_gho_pers_depth_mono with "Hpers"); lia.
  Qed.

  Definition PPtrMutBorrow : val := (λ: ["ptr"; "perm_ref"], "ptr")%V.

  (** The original's [⧗]/[⧖]/[£] and the halving of [llctx_interp L] are
    gone; the context is banked as an [Ltok] instead. *)
  Lemma typed_pptr_borrow_mut {𝔄} κ (ptr perm_ref : path) (ty : type 𝔄)
      E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[ptr ◁ ptr_ty; perm_ref ◁ &uniq{κ} (points_to_ty ty)]
      (PPtrMutBorrow [ptr; perm_ref]) (λ v, +[v ◁ &uniq{κ} ty])
      (λ post '-[l; m], λ mask π,
        let '(cl, (l', x), ξi, d, g, idx) := m in l = l' ∧ ∀ m',
          uniq_bor_current m' = (uniq_bor_current m).2 →
          uniq_bor_future m' π = (uniq_bor_future m π).2 →
          of_cloc (uniq_bor_loc m') = (uniq_bor_current m).1 →
          of_cloc (uniq_bor_loc m') = (uniq_bor_future m π).1 →
          post -[m'] mask π).
  Proof.
    move=> Alv tid post mask iκs vπl.
    iIntros "#LFT #PROPH #UNIQ #E L I TY #Obs"=>/=.
    iDestruct (Alv with "L E") as "#Alv".
    destruct vπl as [l [u []]].
    destruct u as [[[[[c [l' x]] ξi] d] g] ξidx].
    iDestruct "TY" as "(Hptr & Hperm & _)".
    iDestruct "Hptr" as (pl d' Heval) "[_ %Hphys]".
    simpl in Hphys. injection Hphys=> ?; subst pl.
    iDestruct "Hperm" as (pl' d'' Heval') "[Huniq %Hphys']".
    simpl in Hphys'. injection Hphys'=> ?; subst pl'.
    rewrite uniq_bor_gho.
    iDestruct "Huniq" as "(#Incl & %Hineq & UniqBody & #PtBase & #Pers)".
    iApply twpw_fupdw_nonval; [done|].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & [#key f])]".
    iDestruct (Ltok_guard_frac with "key") as "#Gfrac".
    iAssert (frac_tok γ 1 &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "Gfrac Alv"). }
    iDestruct "Pers" as "[Dead|#Pers]".
    { iDestruct "Dead" as (κ'') "[#Incl0 #Dead']".
      iDestruct (dincl_sem with "Incl0") as "#Incl'".
      iDestruct (guard_trans with "Gκ Incl'") as "#G3".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G3 f Wg") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    rewrite tracked_ty_gho_pers.
    destruct d as [|d];
      [rewrite own_ptr_gho_pers /=; by iDestruct "Pers" as "[]"|].
    rewrite own_ptr_gho_pers /=.
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [<- _]]; [solve_ndisj|].
    destruct c as [cl cs]. destruct cs as [|cs0 cs]; last first.
    { (* the permission's own cell list is empty, so this cannot happen *)
      iDestruct "UniqBody" as "(ξVo & ξTok & #ξBor)".
      iDestruct (idxbor_fml_to_full with "ξBor ξTok") as "Bor".
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
    have Hinj : Inj eq eq ((!ₛ) (pair_with_loc_trackedₛ (𝔄:=𝔄) l))
      by move=> ??[=].
    have Hmask : (↑Nllft ∪ ↑prophN ∪ ↑uniqN : coPset) ⊆ ⊤ by set_solver.
    iMod (uniq_body_transform (points_to_ty ty) ty (l, x) x (S d) g ξi ξidx κ
      tid (l, []) (l, repeat [] (ty_size ty)) ⊤ γ L 1
      (pair_with_loc_trackedₛ l) Hinj Hmask
      with "LFT PROPH UNIQ [] Gκ [$key $f] [$ξVo $ξTok] W")
      as "[W (%ζi & %ζidx & #Obs2 & UniqBody & tok)]".
    { iIntros "[gho pt]". rewrite tracked_ty_gho own_ptr_gho /=.
      iDestruct "gho" as "(phys & free & gho)".
      iDestruct (ty_gho_depth_mono ty d g (S d) g x tid with "gho")
        as "[gho _]"; [lia|lia|]. iModIntro.
      iEval (rewrite (cloc_mapsto_empty_cells ty l x tid)) in "phys".
      iFrame "gho phys". iIntros (y e h) "[gho2 pt2]". iModIntro.
      iExists (S e), h. rewrite tracked_ty_gho own_ptr_gho /=.
      iEval (rewrite -(cloc_mapsto_empty_cells ty l y tid)) in "pt2".
      iFrame "pt gho2 free pt2". }
    { iApply (idxbor_fml_iff_at alt_here with "[] ξBor").
      iIntros "!>" (sem' Hs). rewrite !(uniq_body_fml_sem_at Hs) /=.
      iSplit; iIntros "H"; iDestruct "H" as (x0 d0 g0) "(A & B & _)";
        iExists x0, d0, g0; iFrame "A B";
        by iApply (bi.equiv_entails_1_2 (heap_complete_mapsto_fancy_empty _)). }
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    wp_bind ptr. iApply twp_wand; [by iApply twp_eval_path|].
    iIntros (?->). wp_bind perm_ref.
    iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->). wp_rec.
    iModIntro.
    iExists -[((l, repeat [] (ty_size ty)), x, ζi, S d, g, ζidx)].
    iFrame "L I". iSplit; last first.
    { iCombine "Obs Obs2" as "#Obs3".
      iApply (proph_obs_impl with "Obs3")=> π [[_ Ha] Hb].
      apply Ha; [done| |done|]; rewrite /uniq_bor_future /= Hb //. }
    iSplit; [|done]. iExists (LitV (LitLoc l)), d''. iSplit; [done|].
    rewrite /ty_own uniq_bor_gho. iSplit; [|done].
    iSplitR; [iApply "Incl"|]. iSplitR; [iPureIntro; lia|].
    iFrame "UniqBody". iSplitR.
    { iApply dguard_cmapstoany_nil. }
    iRight. iApply (ty_gho_pers_depth_mono with "Pers"); lia.
  Qed.
End typing.

Global Hint Resolve ptr_resolve : lrust_typing.
