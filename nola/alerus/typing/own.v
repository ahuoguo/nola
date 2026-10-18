(** * Owning pointers

  Ported from VerusBelt ([typing/own.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer), itself from RustHornBelt.

  Two changes, both forced by later-freeness.

  - The original's [ty_gho] of [own_ptr n ty] is
    [l ↦!∗ … ∗ freeable_sz … ∗ ▷ (ty_gho ty) …], and its [ty_gho_pers] is
    [▷ (ty_gho_pers ty) …].  Those [▷]s are what make [own_ptr] *contractive*,
    and the reads below strip them with the [▷] that VerusBelt's [typed_read]
    puts in front of the borrowed contents.  Here [typed_read] hands the
    contents over without a [▷], so the type cannot hide one either: both go,
    and [own_ptr] is [TypeNonExpansive] rather than [TypeContractive].  (See
    [typing/shr_bor.v] for the same loss on the shared-borrow side.)

  - [read_own_copy] and [read_own_move] have to name their guard source as a
    *formula*; both are points-to assertions, so [GMapstoVec] serves.
    [write_own] uses [True], i.e. [empty_fml]. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.lang.lib Require Import memcpy new_delete.
From nola.alerus.typing Require Import uninit type_context programs
  freeable_util tracked.
From nola.alerus.typing Require Export type ctx.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Implicit Type 𝔄 𝔅: syn_type.

Section own.
  Context `{!typeG FML Σ}.

  Program Definition own_ptr {𝔄} (n: nat) (ty: type 𝔄) : type (at_locₛ 𝔄) := {|
    ty_size := 1;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);

    ty_ghox x d g tid := [Sx(d') := d]
      ((fst x) ↦!∗ ty.(ty_phys) (snd x) tid ∗
       freeable_fml n ty.(ty_size) (fst x) ∗
       ty.(ty_ghox) (snd x) d' g tid)%FML ;

    ty_gho_persx x d g tid := [Sx(d') := d]
      (ty.(ty_gho_persx) (snd x) d' g tid) ;

    ty_phys x tid := [FVal (LitV (fst x))];
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> 𝔄 n ty sem H [|d] g d' g' x tid ??.
    { rewrite /= (false_sem_at H). by iIntros "[]". }
    destruct d' as [|d']; first lia. rewrite /= !(sep_sem_at H).
    iIntros "(Hown & Hfree & Hgho)".
    iDestruct (ty_gho_depth_mono_at ty sem H with "Hgho") as "[$ Hwand]";
      [lia|lia|].
    iFrame. iIntros "($ & $ & Hgho)". by iApply "Hwand".
  Qed.
  Next Obligation.
    move=> 𝔄 n ty sem H [|d] g d' g' x tid ??.
    { rewrite /= (false_sem_at H). by iIntros "[]". }
    destruct d' as [|d']; first lia. simpl. iIntros "Hp".
    iApply (ty_gho_pers_depth_mono_at ty sem H with "Hp"); lia.
  Qed.
  Next Obligation.
    move=> 𝔄 n ty κ x d g tid ξ R Hin. iIntros "#LFT #Incl #Pers".
    destruct d as [|d'].
    { iIntros "_ _". by iDestruct (false_fml_sem_1 with "Pers") as "[]". }
    fml_simpl'. iIntros "#Rk #Rg".
    iApply (ty_guard_proph _ ty κ (snd x) d' g tid ξ R Hin
      with "LFT Incl Pers Rk").
    iApply (guard_trans with "Rg"). iApply (guard_trans with "[]").
    { iApply (guard_sep_r (P:=((fst x) ↦!∗ ty.(ty_phys) (snd x) tid)%I)). }
    iApply guard_sep_r.
  Qed.
  Next Obligation.
    move=> 𝔄 n ty sem H x d g tid. apply (by_succx_persistent_at H)=> d'.
    apply (ty_gho_pers_pers_at ty sem H).
  Qed.
  Next Obligation.
    move=> 𝔄 n ty x d g tid. destruct d as [|d'].
    { rewrite /= !false_fml_sem. by iIntros "[]". }
    fml_simpl'. iIntros "A". iDestruct "A" as "[_ [_ gho]]".
    by iApply ty_gho_pers_impl.
  Qed.

  Lemma own_ptr_gho {𝔄} n (ty: type 𝔄) x d g tid :
    ty_gho (own_ptr n ty) x d g tid ⊣⊢ [S(d') := d]
      ((fst x) ↦!∗ ty.(ty_phys) (snd x) tid ∗
       freeable_sz n ty.(ty_size) (fst x) ∗ ty_gho ty (snd x) d' g tid).
  Proof.
    rewrite /ty_gho. destruct d as [|d']; [apply false_fml_sem|].
    by rewrite /= !bor_sep_sem mapsto_fml_sem freeable_fml_sem.
  Qed.
  (** [own_ptr_gho] at an arbitrary candidate interpretation *)
  Lemma own_ptr_gho_at {sem} (H : alt_sem sem) {𝔄} n (ty: type 𝔄) x d g tid :
    sem ((own_ptr n ty).(ty_ghox) x d g tid) ⊣⊢ [S(d') := d]
      ((fst x) ↦!∗ ty.(ty_phys) (snd x) tid ∗
       freeable_sz n ty.(ty_size) (fst x) ∗
       sem (ty.(ty_ghox) (snd x) d' g tid)).
  Proof.
    destruct d as [|d']; [apply (false_sem_at H)|].
    rewrite /= !(sep_sem_at H) /mapsto_fml (cells_sem_at H)
      (freeable_sem_at H) //.
  Qed.

  Lemma own_ptr_gho_pers {𝔄} n (ty: type 𝔄) x d g tid :
    ty_gho_pers (own_ptr n ty) x d g tid ⊣⊢ [S(d') := d]
      (ty_gho_pers ty (snd x) d' g tid).
  Proof.
    rewrite /ty_gho_pers. destruct d as [|d']; [apply false_fml_sem|done].
  Qed.

  Global Instance into_sep_own_ptr_gho {𝔄} n (ty: type 𝔄) x d' g tid :
    IntoSep (ty_gho (own_ptr n ty) x (S d') g tid)
      ((fst x) ↦!∗ ty.(ty_phys) (snd x) tid)
      (freeable_sz n ty.(ty_size) (fst x) ∗ ty_gho ty (snd x) d' g tid).
  Proof. rewrite /IntoSep own_ptr_gho /=. by iIntros "$". Qed.
  Global Instance from_sep_own_ptr_gho {𝔄} n (ty: type 𝔄) x d' g tid :
    FromSep (ty_gho (own_ptr n ty) x (S d') g tid)
      ((fst x) ↦!∗ ty.(ty_phys) (snd x) tid)
      (freeable_sz n ty.(ty_size) (fst x) ∗ ty_gho ty (snd x) d' g tid).
  Proof. rewrite /FromSep own_ptr_gho /=. by iIntros "$". Qed.

  Global Instance own_ne {𝔄} n : NonExpansive (@own_ptr 𝔄 n).
  Proof. solve_ne_type. Qed.

  (** The original proves [TypeContractive]; see the header for why the two
    [▷]s that gave it are gone. *)
  Global Instance own_type_ne {𝔄} n : TypeNonExpansive (@own_ptr 𝔄 n).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| | |done].
    - move=>/= ? ty ty' -> ?? Eq Eq' Eqp x [|d] g tid=>//=.
      by rewrite Eqp (Eq x.2 d g tid).
    - move=>/= ? ty ty' ???? Eq' ? x [|d] g tid=>//=.
  Qed.

  Lemma own_stack_okay {𝔄} n (ty: type 𝔄) : StackOkay (own_ptr n ty).
  Proof. done. Qed.

  (** The original's [⧖ d0] and its [|={…}▷=>^d] disappear with the time
    receipts, and the arbitrary [G] guarding the lifetime tokens is a
    [Ktok]. *)
  Global Instance own_send {𝔄} n (ty: type 𝔄) : Send ty → Send (own_ptr n ty).
  Proof.
    move=> [Hphys Hgho]. split.
    - move=> ?? [??] [??] He. by inversion He.
    - move=> tid tid' x d g G κs. iIntros "LFT UNIQ lfts #gs K A".
      destruct d as [|d];
        [by iDestruct (false_fml_sem_1 with "A") as "[]"|].
      iDestruct "A" as "(Hown & Hfree & Hgho)".
      iIntros "W".
      iMod (Hgho with "LFT UNIQ lfts gs K Hgho W")
        as "(W & %x' & %off & gho & %Habs & lfts & K)".
      iModIntro. iFrame "W". iExists (x.1, x'), off. iFrame "lfts K".
      rewrite own_ptr_gho /=.
      rewrite -(Hphys tid tid' (x.2) x' (eq_sym Habs)).
      iFrame "Hown Hfree gho". iPureIntro. by rewrite Habs.
  Qed.

  Global Instance own_sync {𝔄} n (ty: type 𝔄) : Sync ty → Sync (own_ptr n ty).
  Proof.
    move=> HSync tid tid' x d g. split; [done|].
    destruct d as [|d]; [split=> sem Hsem; reflexivity|].
    destruct (HSync tid tid' (snd x) d g) as [Hp [Hg Hgp]].
    split=> sem Hsem.
    - rewrite /= !(sep_sem_at Hsem) /mapsto_fml Hp (Hg _ Hsem) //.
    - rewrite /= (Hgp _ Hsem) //.
  Qed.

  Global Instance own_just_loc {𝔄} n (ty: type 𝔄) : JustLoc (own_ptr n ty).
  Proof.
    iIntros (x [|d] g tid) "Hgho".
    { by iDestruct (false_fml_sem_1 with "Hgho") as "[]". }
    iDestruct "Hgho" as "(Hown & Hfree & Hgho)". by iExists _.
  Qed.

  Lemma own_resolve {𝔄} E L n (ty: type 𝔄) Φ :
    resolve E L ty Φ → resolve E L (own_ptr n ty) (λ '(l, v), Φ v).
  Proof.
    move=> Rslv γ q F x d g tid ?.
    iIntros "LFT PROPH UNIQ E tok A". destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "A") as "[]"|].
    iDestruct "A" as "(_ & _ & gho)". iIntros "W".
    iMod (Rslv with "LFT PROPH UNIQ E tok gho W") as "(W & Obs & tok)";
      [done|].
    iModIntro. iFrame "W tok". iApply (proph_obs_impl with "Obs")=> ?.
    by destruct x.
  Qed.

  Lemma own_type_incl {𝔄 𝔅} n (f: 𝔄 →ₛ 𝔅) ty1 ty2 :
    type_incl ty1 ty2 f -∗
      type_incl (own_ptr n ty1) (own_ptr n ty2) (at_loc_mapₛ f).
  Proof.
    iIntros "(%Eq & #Incl & #InOwn & #InOwnPers & %Phys)".
    do 2 (iSplit; [done|]).
    iSplit.
    { iIntros "!>" (sem Hsem [l x0] [|d] g tid) "Hown".
      { rewrite /= (false_sem_at Hsem). by iDestruct "Hown" as "[]". }
      rewrite /= !(sep_sem_at Hsem).
      iDestruct "Hown" as "(Hown & Hfree & Hgho)".
      iDestruct ("InOwn" $! sem Hsem with "Hgho") as "(Hgho & Hwand)".
      iSplitL "Hown Hfree Hgho".
      - rewrite Eq Phys. iFrame.
      - iIntros "(Hown & Hfree & Hgho)". rewrite Eq Phys. iFrame.
        by iApply "Hwand". }
    iSplit.
    { iIntros "!>" (sem Hsem [l x0] [|d] g tid) "Hown".
      { rewrite /= (false_sem_at Hsem). by iDestruct "Hown" as "[]". }
      rewrite /=. by iApply ("InOwnPers" $! sem Hsem). }
    { iPureIntro. by move=> [l x0] tid. }
  Qed.

  Lemma own_subtype {𝔄 𝔅} E L n (f: 𝔄 →ₛ 𝔅) ty ty' :
    subtype E L ty ty' f →
    subtype E L (own_ptr n ty) (own_ptr n ty') (at_loc_mapₛ f).
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iApply own_type_incl; by [|iApply "Incl"].
  Qed.

  Lemma own_eqtype {𝔄 𝔅} E L n (f: 𝔄 →ₛ 𝔅) g ty ty' :
    eqtype E L ty ty' f g →
    eqtype E L (own_ptr n ty) (own_ptr n ty') (at_loc_mapₛ f) (at_loc_mapₛ g).
  Proof. move=> [??]. split; by apply own_subtype. Qed.
End own.

Global Hint Rewrite @own_ptr_gho @own_ptr_gho_pers : fml_sem.

Section box.
  Context `{!typeG FML Σ}.

  Definition box {𝔄} (ty: type 𝔄) : type (at_locₛ 𝔄) := own_ptr ty.(ty_size) ty.

  Definition own_tracked {𝔄} (ty: type 𝔄) : type (at_locₛ (trackedₛ 𝔄)) :=
    own_ptr 0 (tracked_ty ty).

  Global Instance box_ne {𝔄} : NonExpansive (@box 𝔄).
  Proof. solve_ne_type. Qed.

  Lemma box_type_incl {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) ty ty':
    type_incl ty ty' f -∗ type_incl (box ty) (box ty') (at_loc_mapₛ f).
  Proof.
    iIntros "[%Eq ?]". rewrite /box Eq. iApply own_type_incl. by iSplit.
  Qed.

  Lemma box_subtype {𝔄 𝔅} E L (f: 𝔄 →ₛ 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (box ty) (box ty') (at_loc_mapₛ f).
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #?". iApply box_type_incl. by iApply "Incl".
  Qed.

  Lemma box_eqtype {𝔄 𝔅} E L (f: 𝔄 →ₛ 𝔅) g ty ty' :
    eqtype E L ty ty' f g →
    eqtype E L (box ty) (box ty') (at_loc_mapₛ f) (at_loc_mapₛ g).
  Proof. move=> [??]. split; by apply box_subtype. Qed.
End box.

Section typing.
  Context `{!typeG FML Σ}.

  (** Writing through an owning pointer.

    The guard source is [True], i.e. [empty_fml]: the location's cells are
    empty, so [l #↦∗_] is [True] too and [guard_true] gives the guard. *)
  Lemma write_own {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) n E L :
    ty.(ty_size) = ty'.(ty_size) →
    typed_write E L (own_ptr n ty) ty (own_ptr n ty') ty' (λ v, v.2)
      (λ u b' u', u' = (u.1, b')).
  Proof.
    move=> Sz. split; [done|].
    move=> [l x0] [|d] v tid γ q;
      iIntros "LFT UNIQ E tok [Hgho %Hphys]";
      [by iDestruct (false_fml_sem_1 with "Hgho") as "[]"|].
    iDestruct "Hgho" as "(Hown & Hfree & Hgho)".
    rewrite /own_ptr /= in Hphys. move: Hphys; case=> <-.
    iIntros "$ !>".
    iExists (l, repeat [] (length (ty_phys ty x0 tid))), d, empty_fml.
    iSplit; [done|]. iSplit; [done|].
    iSplitL "Hown Hgho".
    { iExists (ty_phys ty x0 tid). rewrite -heap_cloc_mapsto_fancy_empty.
      by iFrame. }
    iSplitR "tok Hfree". { iApply empty_fml_sem_2. }
    iSplitR "tok Hfree".
    { iApply (guard_lhs_iff empty_fml_sem).
      iApply (guard_rhs_iff (heap_cloc_mapsto_empty _ _)). iApply guard_true. }
    iIntros (y db') "Hown _ $ !>". rewrite /ty_own.
    iDestruct "Hown" as (vl) "[Pt [Gho %Phys]]".
    iExists (l, y). iFrame "tok". iSplit; [done|].
    iSplit; [|done]. rewrite own_ptr_gho /= -Sz -Phys. iFrame "Hfree".
    replace (length (ty_phys ty x0 tid)) with (length (ty_phys ty' y tid));
      last by do 2 rewrite ty_size_eq.
    rewrite -heap_cloc_mapsto_fancy_empty. iFrame "Pt".
    iDestruct (ty_gho_depth_mono with "Gho") as "[$ _]"; lia.
  Qed.

  (** Reading a [Copy] type out of an owning pointer.

    The original takes [£(d+1)] and spends it stripping the [▷] in front of
    the inner ghost state; here there is none.  The guard source is the
    points-to assertion itself, named as the formula [GMapstoVec]. *)
  Lemma read_own_copy {𝔄} (ty: type 𝔄) n E L :
    Copy ty → typed_read E L (own_ptr n ty) ty (own_ptr n ty) (λ v, snd v) (=).
  Proof.
    move=> Cpy [l x0] [|d] v tid γ q;
      iIntros "LFT E tok [Hgho %Hphys]";
      [by iDestruct (false_fml_sem_1 with "Hgho") as "[]"|].
    iDestruct "Hgho" as "(Hown & Hfree & #Hgho)".
    iDestruct (copy_concrete with "Hgho") as "%Conc".
    rewrite /own_ptr /= in Hphys. move: Hphys; case=> <-.
    iIntros "$ !>".
    iExists (l, repeat [] (length (ty_phys ty x0 tid))),
      (to_concrete (ty_phys ty x0 tid)), (ty_phys ty x0 tid),
      (gsrc_fml (GMapstoVec l (ty_phys ty x0 tid))).
    iSplit; [done|].
    iSplit; [iPureIntro; apply length_to_concrete|].
    iSplitL "Hown". { by iApply gsrc_fml_sem_2. }
    iSplit.
    { rewrite gsrc_fml_sem /= heap_mapsto_cells_fancy_empty
        -heap_mapsto_cells_fancy_fmap_eq (fmap_to_concrete _ Conc).
      iApply guard_refl. }
    iSplitR.
    { iIntros (l₁ c₁) "?". rewrite -heap_complete_mapsto_fancy_fmap_eq
        (fmap_to_concrete _ Conc). by iFrame. }
    iSplit. { iPureIntro=> _. by rewrite (fmap_to_concrete _ Conc). }
    rewrite /ty_own.
    iSplitR.
    { iSplit; [|done].
      iDestruct (ty_gho_depth_mono with "Hgho") as "[$ _]"; lia. }
    iIntros "Hown $ !>". iExists (l, x0). iSplit; [done|]. iFrame "tok".
    iSplit; [|done]. rewrite own_ptr_gho /=. iFrame "Hfree Hgho".
    by iApply (gsrc_fml_sem_1 (s := GMapstoVec l (ty_phys ty x0 tid))).
  Qed.

  Lemma read_own_move {𝔄} (ty: type 𝔄) n E L :
    typed_read E L (own_ptr n ty) ty (own_ptr n (↯ ty.(ty_size)))
      (λ v, v.2) (λ v z, v.1 = z.1).
  Proof.
    move=> [l x] [|d] v tid γ q;
      iIntros "LFT E tok [Hgho %Hphys]";
      [by iDestruct (false_fml_sem_1 with "Hgho") as "[]"|].
    iDestruct "Hgho" as "(Hown & Hfree & Hgho)".
    rewrite /own_ptr /= in Hphys. move: Hphys; case=> <-.
    iIntros "W".
    iMod (mapsto_vec_untether_emp _ _ ⊤ ∅ with "Hown")
      as (vl_concrete) "[Hconc [%Hleneq [Retether %ConcreteEq]]]".
    iModIntro. iFrame "W".
    iExists (l, repeat [] (length (ty_phys ty x tid))), vl_concrete,
      (ty_phys ty x tid), (gsrc_fml (GMapstoVec l (FVal <$> vl_concrete))).
    iSplit; [done|]. iSplit; [done|].
    iSplitL "Hconc".
    { iApply gsrc_fml_sem_2. by rewrite /= heap_mapsto_fancy_fmap_eq. }
    iSplit.
    { rewrite gsrc_fml_sem /= heap_mapsto_fancy_fmap_eq
        heap_mapsto_cells_empty Hleneq. iApply guard_refl. }
    iSplitL "Retether". { iIntros. by iApply "Retether". }
    iSplit. { iPureIntro=> ?. by rewrite ConcreteEq. }
    rewrite /ty_own.
    iSplitL "Hgho".
    { iSplit; [|done].
      iDestruct (ty_gho_depth_mono with "Hgho") as "[$ _]"; lia. }
    iIntros "Hown $ !>".
    replace (ty_size ty) with (length (ty_phys ty x tid));
      last by apply ty_size_eq.
    rewrite -Hleneq.
    iExists (l, list_to_vec vl_concrete). iSplit; [done|]. iFrame "tok".
    iSplit; [|done]. rewrite own_ptr_gho /=. iFrame "Hfree".
    iSplitL; [|by iApply empty_fml_sem_2]. rewrite vec_to_list_to_vec.
    by iApply (gsrc_fml_sem_1 (s := GMapstoVec l (FVal <$> vl_concrete))).
  Qed.

  (** Allocation.

    The original's [persistent_time_receipt_0] /
    [wp_persistent_time_receipt] pair exists only to mint the [⧖ 1] that
    [own_ptr]'s depth index demands; later-free the index is still there but
    needs no receipt. *)
  Lemma type_new_instr n E L I :
    0 ≤ n → let n' := Z.to_nat n in
    typed_instr_ty E L I +[] (new [ #n])%E (own_ptr n' (↯ n'))
        (λ post _ mask π, ∀ l junk, post (l, junk) mask π).
  Proof.
    iIntros (???????) "_ _ _ _ $$ _ Proph" => /=.
    iApply twp_new; [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, vrepeat #☠ (Z.to_nat n))]. iSplit.
    { rewrite /tctx_elt_interp. iSplit=>//=. rewrite /ty_own /=.
      iExists #l, 1%nat.
      rewrite own_ptr_gho /= freeable_sz_full Z2Nat.id; [|lia].
      iSplit=>//. iSplit=>//. rewrite vec_to_list_vrepeat. iFrame.
      rewrite heap_mapsto_fancy_fmap_eq. iFrame.
      iSplitL "†"; [|by iApply empty_fml_sem_2].
      iDestruct "†" as "[A|%E0]"; [by iLeft; iFrame|iRight; iPureIntro; lia]. }
    iApply proph_obs_impl; last by iFrame "Proph". done.
  Qed.

  Lemma type_new {𝔄l 𝔅} n x e tr E L (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) :
    Closed (x :b: []) e → 0 ≤ n → let n' := Z.to_nat n in
    (∀v: val, typed_body E L I C (v ◁ own_ptr n' (↯ n') +:: T)
      (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := new [ #n] in e)
      (λ post al mask π, forall l junk, tr post ((l, junk) -:: al) mask π).
  Proof.
    iIntros. iApply type_let.
    - by apply type_new_instr.
    - solve_typing.
    - instantiate (1 := tr). done.
    - done.
  Qed.

  Lemma type_new_subtype {𝔄 𝔅l ℭ} (ty: type 𝔄) n (T: tctx 𝔅l) f e tr x E L I
      (C: cctx ℭ) :
    Closed (x :b: []) e → 0 ≤ n → let n' := Z.to_nat n in
    subtype E L (↯ n') ty f →
    (∀v: val, typed_body E L I C (v ◁ own_ptr n' ty +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := new [ #n] in e)
      (λ post al mask π, forall l junk, tr post ((l, f ~~$ₛ junk) -:: al) mask π).
  Proof.
    iIntros (??? Sub) "?".
    iApply type_let; [by apply type_new_instr|solve_typing| |]; last first.
    { iIntros (?).
      iApply typed_body_tctx_incl;
        [eapply subtype_tctx_incl, own_subtype, Sub|done]. }
    done.
  Qed.

  Lemma type_delete_instr {𝔄} (ty: type 𝔄) (n: Z) p E L I :
    let n' := ty.(ty_size) in n = Z.of_nat n' →
    typed_instr E L I +[p ◁ own_ptr n' ty] (new_delete.delete [ #n; p])%E (λ _, +[])
      (λ post _, post -[]).
  Proof.
    iIntros (?->????[[l x][]]) "_ _ _ _ $$ [p _] #Obs".
    wp_bind p. iApply (twp_hasty with "p"). rewrite /ty_own /=.
    iIntros (?[|?] _) "[own %]";
      [by iDestruct (false_fml_sem_1 with "own") as "[]"|].
    iDestruct "own" as "(Hown & Hfree & Hgho)".
    move: H; case=> <-.
    have Sz := ty.(ty_size_eq).
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (mapsto_vec_untether_emp _ _ ⊤ ∅ with "Hown")
      as (vl_concrete) "[Hconc [%Hleneq _]]".
    iModIntro. iFrame "W".
    iApply (twp_delete vl_concrete n' with "[-]")=>//.
    { unfold n'. rewrite Hleneq. by rewrite Sz. }
    { iFrame "Hconc". rewrite Hleneq Sz. by iApply freeable_sz_full. }
    iIntros "_". iExists nil_tt. iSplit=>//; iFrame.
  Qed.

  Lemma type_delete {𝔄 𝔅l ℭl 𝔇} (ty: type 𝔄) n' (n: Z) p e
    E L I (C: cctx 𝔇) (T: tctx 𝔅l) (T': tctx ℭl) trx tr :
    Closed [] e → tctx_extract_ctx E L +[p ◁ own_ptr n' ty] T T' trx →
    n' = ty.(ty_size) → n = n' → typed_body E L I C T' e tr -∗
    typed_body E L I C T (new_delete.delete [ #n; p ];; e)
      (trx ∘ (λ post '(_ -:: al), tr post al)).
  Proof.
    iIntros (? Extr -> ?) "?".
    iApply type_seq; [by eapply type_delete_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case.
  Qed.

  (** [T] to [Tracked<T>] *)

  Lemma type_delete2_instr {𝔄} (ty: type 𝔄) (n: Z) p E L I :
    let n' := ty.(ty_size) in n = Z.of_nat n' →
    typed_instr E L I
      +[p ◁ own_ptr n' ty]
      (new_delete.delete [ #n; p])%E
      (λ _, +[p ◁ own_tracked ty])
      (λ post π, post π).
  Proof.
    iIntros (?->????[[l x][]]) "_ _ _ _ $$ [p _] #Obs".
    wp_bind p. iApply (twp_hasty with "p"). rewrite /ty_own /=.
    iIntros (?[|?] Hpath) "[own %Hv]";
      [by iDestruct (false_fml_sem_1 with "own") as "[]"|].
    iDestruct "own" as "(Hown & Hfree & Hgho)".
    inversion Hv. subst v.
    have Sz := ty.(ty_size_eq).
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (mapsto_vec_untether_emp _ _ ⊤ ∅ with "Hown")
      as (vl_concrete) "[Hconc [%Hleneq _]]".
    iModIntro. iFrame "W".
    iApply (twp_delete vl_concrete n' with "[Hconc Hfree]")=>//.
    { unfold n'. rewrite Hleneq. by rewrite Sz. }
    { iFrame "Hconc". rewrite Hleneq Sz. by iApply freeable_sz_full. }
    iIntros "_". iExists -[(l, x)]. iSplit=>//; iFrame.
    iSplit; last by done. rewrite /tctx_elt_interp.
    iExists (#l), (S n). iSplit. { iPureIntro. by symmetry. }
    iSplit.
    { rewrite own_ptr_gho /=. iFrame "Hgho".
      rewrite heap_mapsto_fancy_vec_nil. done. }
    iPureIntro. done.
  Qed.

  Lemma type_letalloc_1 {𝔄 𝔅l ℭl 𝔇} (ty: type 𝔄) (x: string) p e
    (T: tctx 𝔅l) (T': tctx ℭl) (tr : predl_trans' ((at_locₛ 𝔄) :: ℭl) 𝔇)
    (trx : predl_trans 𝔅l ([𝔄] ++ ℭl)) tr_res E L I (C: cctx 𝔇) :
    Closed [] p → Closed [x] e →
    tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    tr_res ≡ (λ pred_d, trx
      (λ '(a -:: cl) mask π, ∀ l, tr pred_d ((l, a) -:: cl) mask π)) →
    ty.(ty_size) = 1%nat →
    (∀v: val, typed_body E L I C (v ◁ box ty +:: T') (subst x v e) tr) -∗
    typed_body E L I C T (letalloc: x <- p in e) tr_res.
  Proof.
    iIntros (???? Sz) "?".
    iApply (typed_body_impl _ (_ ∘ _)).
    { move=> post xl mask π Htr_res. apply H2 in Htr_res. apply Htr_res. }
    iApply typed_body_tctx_incl; [done|].
    set (tr' := (λ post (al : plist ~~
        (at_locₛ (uninitₛ (Z.to_nat (Z.of_nat 1))):: 𝔄 :: ℭl)) mask π,
      let '((l, junk) -:: a -:: rest) := al in
      tr post ((l,a) -:: rest) mask π)).
    iApply (@typed_body_impl _ _ _ (𝔄 :: ℭl) _ _
      (λ post al mask π, ∀ l junk, tr' post ((l, junk) -:: al) mask π));
      last first.
    - iApply (@type_new (𝔄 :: ℭl) 𝔇 _ _ _ tr'); [|lia|].
      + rewrite /Closed /= !andb_True. split; [done|]. split; [|done].
        split; [apply bool_decide_spec|eapply is_closed_weaken=>//]; set_solver.
      + iIntros (xv) "/=".
        have ->: (subst x xv (x <- p;; e))%E = (xv <- p;; subst x xv e)%E.
        { rewrite /subst /=. repeat f_equal;
            [by rewrite bool_decide_true
            |eapply is_closed_subst=>//; set_solver]. }
        iApply typed_body_impl; last first.
        { iApply (type_assign (own_ptr (Z.to_nat 1%nat) (↯ (Z.to_nat 1%nat)))
            (↯ (Z.to_nat 1%nat))%T (own_ptr (Z.to_nat 1%nat) ty) ty snd
            _ _ _ _ _ _ _ _ _ T' id tr _).
          * apply subst_is_closed; [apply is_closed_of_val|done].
          * eapply tctx_extract_ctx_eq.
            eapply tctx_extract_ctx_elt.
            apply tctx_extract_elt_here_exact.
            eapply tctx_extract_ctx_elt.
            apply tctx_extract_elt_here_exact.
            apply tctx_extract_ctx_nil.
            rewrite /id /compose/trans_tail //=.
            fun_ext=> a. fun_ext=> b /=. by destruct b as [[? ?] [? ?]].
          * apply (write_own (↯ (Z.to_nat 1%nat)) ty 1%nat)=>/=; lia.
          * rewrite /resolve'. instantiate (1:= λ _ _ x, x).
            eapply resolve_impl=>//; first apply uninit_resolve.
          * by rewrite /box Sz. }
        move=>/= ?[[??][? ?]]????/=?; subst. done.
    - move=> ?[??]????? //=.
  Qed.
End typing.

Global Hint Resolve own_resolve own_subtype own_eqtype
  box_subtype box_eqtype write_own read_own_copy : lrust_typing.
(* By setting the priority high, we make sure copying is tried before
   moving. *)
Global Hint Resolve read_own_move | 100 : lrust_typing.
