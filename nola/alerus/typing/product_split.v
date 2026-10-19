(** * Splitting and merging pointers to products

  Ported from VerusBelt ([typing/product_split.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  The general split/merge machinery is purely logical and carries over
  unchanged.  [type_split_uniq_bor_instr] loses the original's [⧖]/[⧗]/[£]
  and the [▷]s they strip, and its two halves of [llctx_interp L] become the
  two halves of one [Ltok]. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.typing Require Export type.
From nola.alerus.typing Require Import type_context lft_contexts product own
  uniq_bor uniq_util freeable_util programs programs_util shr_bor mod_ty
  uninit.
From nola.alerus.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l ℭl: syn_typel).

Section product_split.
  Context `{!typeG FML Σ}.

  (** ** General split/merge for plain pointer types *)

  Fixpoint spec_ptr_offsets {𝔄l} (al: plist (~~) 𝔄l) (tyl: typel 𝔄l) (l: loc)
    : plist ~~ (map at_locₛ 𝔄l) :=
    match tyl in hlist _ 𝔄l, al return plist ~~ (map at_locₛ 𝔄l) with
    | +[], -[] => -[]
    | ty +:: tyl', a -:: al' =>
      (l, a) -:: spec_ptr_offsets al' tyl' (l +ₗ ty.(ty_size))
    end.

  Fixpoint hasty_ptr_offsets {𝔄l} (p: path)
      (ptr: ∀{𝔄}, type 𝔄 → type (at_locₛ 𝔄)) (tyl: typel 𝔄l) (off: nat)
      : tctx (map at_locₛ 𝔄l) :=
    match tyl with
    | +[] => +[]
    | ty +:: tyl' =>
      p +ₗ #off ◁ ptr ty +:: hasty_ptr_offsets p (@ptr) tyl' (off + ty.(ty_size))
    end.

  Lemma hasty_ptr_offsets_equiv {𝔄l} ptr p (tyl: typel 𝔄l) (off off': nat) :
    tctx_equiv (hasty_ptr_offsets (p +ₗ #off) ptr tyl off')
      (hasty_ptr_offsets p ptr tyl (off + off')).
  Proof.
    apply get_tctx_equiv=> ? vπl. move: p off off'.
    induction tyl, vπl; [done|]=>/= p ??.
    f_equiv; [|by rewrite IHtyl Nat.add_assoc].
    apply tctx_elt_interp_hasty_path=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc -Nat2Z.inj_add.
  Qed.

  Definition ptr_homo_sub (ptr: ∀{𝔄}, type 𝔄 → type (at_locₛ 𝔄)) : Prop :=
    ∀E L 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅) f,
      subtype E L ty ty' f → subtype E L (ptr ty) (ptr ty') (at_loc_mapₛ f).

  Lemma tctx_split_ptr_xprod {𝔄l} (ptr: ∀{𝔄}, type 𝔄 → type (at_locₛ 𝔄))
      (tyl: typel 𝔄l) E L :
    ptr_homo_sub (@ptr) →
    (∀p 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅),
        tctx_incl E L +[p ◁ ptr (ty * ty')]
          +[p +ₗ #0 ◁ ptr ty; p +ₗ #ty.(ty_size) ◁ ptr ty']
          (λ post '-[(l, (a, b))], post -[(l, a); (l +ₗ ty.(ty_size), b)])) →
    ∀p, tctx_incl E L +[p ◁ ptr (Π! tyl)] (hasty_ptr_offsets p (@ptr) tyl 0)
                       (λ post '-[(l, al)], post (spec_ptr_offsets al tyl l)).
  Proof.
    move=> HSub Split. elim: tyl.
    { move=> ?. eapply tctx_incl_ext; [apply tctx_incl_resolve_head|].
      by move=> ?[[?[]][]]. }
    move=>/= X Xl f tyl IH p. eapply tctx_incl_ext.
    { eapply tctx_incl_trans. { eapply subtype_tctx_incl, HSub, mod_ty_out. }
      eapply tctx_incl_trans. { apply Split. } apply tctx_incl_tail.
      eapply tctx_incl_trans. { apply IH. } rewrite -{2}[ty_size _]Nat.add_0_r.
      eapply proj1, hasty_ptr_offsets_equiv. }
    by move=>/= ?[[?[??]][]].
  Qed.

  Lemma tctx_merge_ptr_xprod {𝔄l} (ptr: ∀{𝔄}, type 𝔄 → type (at_locₛ 𝔄))
      (tyl: typel 𝔄l) E L `{∀𝔄 (ty: type 𝔄), JustLoc (ptr ty)} :
    ptr_homo_sub (@ptr) →
    (∀p 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅),
        tctx_incl E L +[p +ₗ #0 ◁ ptr ty; p +ₗ #ty.(ty_size) ◁ ptr ty']
          +[p ◁ ptr (ty * ty')] (λ post '-[(l, a); (l2, b)], λ mask π,
            l2 = l +ₗ ty.(ty_size) → post -[(l, (a, b))] mask π)) →
    𝔄l ≠ [] →
    ∀p, tctx_incl E L (hasty_ptr_offsets p (@ptr) tyl 0) +[p ◁ ptr (Π! tyl)]
          (λ post al mask π, ∀ l al',
            al = spec_ptr_offsets al' tyl l → post -[(l, al')] mask π).
  Proof.
    move=> HSub Merge. elim: tyl; [done|]=> ?? ty. case=>/=.
    { move=> _ _ ?. eapply tctx_incl_ext.
      { eapply tctx_incl_trans; [apply tctx_of_shift_loc_0|].
        eapply subtype_tctx_incl, HSub, subtype_trans, mod_ty_in.
        eapply subtype_trans; [apply prod_ty_right_id|].
        apply prod_subtype; solve_typing. }
      intros post [[l x][]] ?. simpl. split.
      - intros Ha. apply Ha. trivial.
      - intros Ha l0 al0. destruct al0 as [x0 []]. inversion 1. subst.
        trivial. }
    move=> ???? IH _ ?. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [|by eapply subtype_tctx_incl, HSub, mod_ty_in].
      eapply tctx_incl_trans; [|by apply Merge]. apply tctx_incl_tail.
      eapply tctx_incl_trans; [|by apply IH].
      apply (tctx_incl_app +[_] +[_]); [by apply tctx_to_shift_loc_0, _|].
      eapply proj2, hasty_ptr_offsets_equiv. }
    simpl. intros post [[l x] [[l1 x1] rest]] π. split.
    - intros Ha. simpl. unfold trans_app. simpl.
      intros l2 [a al] Hb Hadd. apply Ha. rewrite Hb. subst l2. trivial.
    - simpl. unfold trans_app. simpl. intros Ha l0 [x2 [x3 rest3]] Hb.
      inversion Hb. subst. apply (Ha (l0 +ₗ ty_size ty)); trivial.
  Qed.

  (** ** General split for plain pointer types, cloc version *)

  Fixpoint spec_ptr_cloc_offsets {𝔄l} (al: plist (~~) 𝔄l) (tyl: typel 𝔄l)
      (l: cloc) : plist ~~ (map at_clocₛ 𝔄l) :=
    match tyl in hlist _ 𝔄l, al return plist ~~ (map at_clocₛ 𝔄l) with
    | +[], -[] => -[]
    | ty +:: tyl', a -:: al' =>
      (cloc_take l ty.(ty_size), a) -::
        spec_ptr_cloc_offsets al' tyl' (cloc_skip l ty.(ty_size))
    end.

  Fixpoint hasty_ptr_cloc_offsets {𝔄l} (p: path)
      (ptr: ∀{𝔄}, type 𝔄 → type (at_clocₛ 𝔄)) (tyl: typel 𝔄l) (off: nat)
      : tctx (map at_clocₛ 𝔄l) :=
    match tyl with
    | +[] => +[]
    | ty +:: tyl' =>
      p +ₗ #off ◁ ptr ty +::
        hasty_ptr_cloc_offsets p (@ptr) tyl' (off + ty.(ty_size))
    end.

  Lemma hasty_ptr_cloc_offsets_equiv {𝔄l} ptr p (tyl: typel 𝔄l) (off off': nat) :
    tctx_equiv (hasty_ptr_cloc_offsets (p +ₗ #off) ptr tyl off')
      (hasty_ptr_cloc_offsets p ptr tyl (off + off')).
  Proof.
    apply get_tctx_equiv=> ? vπl. move: p off off'.
    induction tyl, vπl; [done|]=>/= p ??.
    f_equiv; [|by rewrite IHtyl Nat.add_assoc].
    apply tctx_elt_interp_hasty_path=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc -Nat2Z.inj_add.
  Qed.

  Definition ptr_cloc_homo_sub (ptr: ∀{𝔄}, type 𝔄 → type (at_clocₛ 𝔄)) : Prop :=
    ∀E L 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅) f,
      subtype E L ty ty' f → subtype E L (ptr ty) (ptr ty') (at_cloc_mapₛ f).

  Lemma tctx_split_ptr_cloc_xprod {𝔄l}
      (ptr: ∀{𝔄}, type 𝔄 → type (at_clocₛ 𝔄)) (tyl: typel 𝔄l) E L :
    ptr_cloc_homo_sub (@ptr) →
    (∀p 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅),
        tctx_incl E L +[p ◁ ptr (ty * ty')]
          +[p +ₗ #0 ◁ ptr ty; p +ₗ #ty.(ty_size) ◁ ptr ty']
          (λ post '-[(l, (a, b))],
            post -[(cloc_take l ty.(ty_size), a);
                   (cloc_skip l ty.(ty_size), b)])) →
    ∀p, tctx_incl E L +[p ◁ ptr (Π! tyl)]
          (hasty_ptr_cloc_offsets p (@ptr) tyl 0)
          (λ post '-[(l, al)], post (spec_ptr_cloc_offsets al tyl l)).
  Proof.
    move=> HSub Split. elim: tyl.
    { move=> ?. eapply tctx_incl_ext; [apply tctx_incl_resolve_head|].
      by move=> ?[[?[]][]]. }
    move=>/= X Xl f tyl IH p. eapply tctx_incl_ext.
    { eapply tctx_incl_trans. { eapply subtype_tctx_incl, HSub, mod_ty_out. }
      eapply tctx_incl_trans. { apply Split. } apply tctx_incl_tail.
      eapply tctx_incl_trans. { apply IH. } rewrite -{2}[ty_size _]Nat.add_0_r.
      eapply proj1, hasty_ptr_cloc_offsets_equiv. }
    by move=>/= ?[[?[??]][]].
  Qed.
End product_split.

Global Hint Unfold ptr_homo_sub : lrust_typing.
Global Hint Unfold ptr_cloc_homo_sub : lrust_typing.
Notation hasty_own_offsets p n :=
  (hasty_ptr_offsets p (λ 𝔄, own_ptr (𝔄:=𝔄) n)).
Notation hasty_shr_offsets p κ :=
  (hasty_ptr_cloc_offsets p (λ 𝔄, shr_bor (𝔄:=𝔄) κ)).

Section product_split.
  Context `{!typeG FML Σ}.

  (** ** Owning pointers *)

  Lemma tctx_split_own_prod {𝔄 𝔅} n (ty: type 𝔄) (ty': type 𝔅) p E L :
    tctx_incl E L +[p ◁ own_ptr n (ty * ty')]
      +[p +ₗ #0 ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty']
      (λ post '-[(l, (a, b))], post -[(l, a); (l +ₗ ty.(ty_size), b)]).
  Proof.
    split. { move=> ?? Eq [[?[??]][]] ??. by rewrite Eq. }
    move=> γ q tid [[l [x y]][]] mask post.
    iIntros "#LFT #PROPH #UNIQ #E tok [T _] #Obs W".
    iDestruct "T" as (v d) "[%path [gho %phys]]".
    destruct d as [|d'];
      [by iDestruct (false_fml_sem_1 with "gho") as "[]"|].
    rewrite own_ptr_gho /= prod_ty_gho /=.
    iDestruct "gho" as "(pt & free & gho1 & gho2)".
    rewrite heap_mapsto_fancy_vec_app -freeable_sz_split ty_size_eq.
    iDestruct "pt" as "[pt pt']". iDestruct "free" as "[free free']".
    inversion phys. subst v. iModIntro. iFrame "W tok".
    iExists -[(l, x); (l +ₗ ty.(ty_size), y)]. iSplit; last first.
    { iApply (proph_obs_eq with "Obs")=> ?. done. }
    iSplitL "pt free gho1".
    { iExists #l, (S d'). iSplit.
      { iPureIntro. by rewrite /= path shift_loc_0. }
      rewrite /ty_own own_ptr_gho /=. by iFrame "pt free gho1". }
    iSplit; [|done]. iExists #(l +ₗ ty_size ty), (S d'). iSplit.
    { iPureIntro. by rewrite /= path. }
    rewrite /ty_own own_ptr_gho /=. by iFrame "pt' free' gho2".
  Qed.

  Lemma tctx_merge_own_prod {𝔄 𝔅} n (ty: type 𝔄) (ty': type 𝔅) p E L :
    tctx_incl E L
      +[p +ₗ #0 ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty']
      +[p ◁ own_ptr n (ty * ty')] (λ post '-[(la, a); (lb, b)], λ mask π,
        lb = la +ₗ ty.(ty_size) → post -[(la, (a, b))] mask π).
  Proof.
    eapply tctx_incl_ext;
      [eapply tctx_incl_trans; [apply tctx_of_shift_loc_0|]
      |by move=> *; apply (iff_refl _)].
    split. { move=> ?? Eq [[??][[??][]]] ??. by setoid_rewrite Eq. }
    move=> γ q tid [[lx x][[ly y][]]] mask post.
    iIntros "#LFT #PROPH #UNIQ #E tok [T1 [T2 _]] #Obs W".
    iDestruct "T1" as (v1 d1) "[%path1 [gho1 %phys1]]".
    iDestruct "T2" as (v2 d2) "[%path2 [gho2 %phys2]]".
    destruct d1 as [|d1'];
      [by iDestruct (false_fml_sem_1 with "gho1") as "[]"|].
    destruct d2 as [|d2'];
      [by iDestruct (false_fml_sem_1 with "gho2") as "[]"|].
    rewrite own_ptr_gho /=. iDestruct "gho1" as "(pt & free & gho1)".
    rewrite own_ptr_gho /=. iDestruct "gho2" as "(pt' & free' & gho2)".
    inversion phys1. inversion phys2. subst.
    move: path2=>/=. rewrite path1=> [=<-].
    iModIntro. iFrame "W tok". iExists -[(lx, (x, y))]. iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> ? Ha. by apply Ha. }
    iSplit; [|done].
    iExists #lx, (S d1' `max` S d2'). iSplit; [done|].
    iDestruct (ty_gho_depth_mono ty d1' (S d1') (d1' `max` d2')
      (S d1' `max` S d2') x tid with "gho1") as "[gho1 _]"; [lia|lia|].
    iDestruct (ty_gho_depth_mono ty' d2' (S d2') (d1' `max` d2')
      (S d1' `max` S d2') y tid with "gho2") as "[gho2 _]"; [lia|lia|].
    rewrite /ty_own own_ptr_gho /= prod_ty_gho /=.
    iFrame "gho1 gho2".
    rewrite heap_mapsto_fancy_vec_app -freeable_sz_split ty_size_eq.
    by iFrame "pt pt' free free'".
  Qed.

  Lemma tctx_split_own_xprod {𝔄l} n (tyl: typel 𝔄l) p E L :
    tctx_incl E L +[p ◁ own_ptr n (Π! tyl)] (hasty_own_offsets p n tyl 0)
      (λ post '-[(l, al)], post (spec_ptr_offsets al tyl l)).
  Proof.
    apply (tctx_split_ptr_xprod (λ _, own_ptr n));
      [solve_typing|move=> *; apply tctx_split_own_prod].
  Qed.

  Lemma tctx_merge_own_xprod {𝔄 𝔄l} n (tyl: typel (𝔄 :: 𝔄l)) p E L :
    tctx_incl E L (hasty_own_offsets p n tyl 0) +[p ◁ own_ptr n (Π! tyl)]
      (λ post al mask π, ∀ l al',
        al = spec_ptr_offsets al' tyl l → post -[(l, al')] mask π).
  Proof.
    apply (tctx_merge_ptr_xprod (λ _, own_ptr n));
      [apply _|solve_typing|move=> *; apply tctx_merge_own_prod|done].
  Qed.

  (** ** Shared references *)

  Lemma tctx_split_shr_prod {𝔄 𝔅} κ (ty: type 𝔄) (ty': type 𝔅) p E L :
    tctx_incl E L +[p ◁ &shr{κ} (ty * ty')]
      +[p +ₗ #0 ◁ &shr{κ} ty; p +ₗ #ty.(ty_size) ◁ &shr{κ} ty']
      (λ post '-[(l, (a, b))],
        post -[(cloc_take l ty.(ty_size), a); (cloc_skip l ty.(ty_size), b)]).
  Proof.
    split. { move=> ?? Eq [[?[??]][]] ??. by setoid_rewrite Eq. }
    move=> γ q tid [[l [x y]][]] mask post.
    iIntros "#LFT #PROPH #UNIQ #E tok [T _] #Obs W".
    iDestruct "T" as (v d) "[%path [gho %phys]]".
    destruct d as [|d'];
      [by iDestruct (false_fml_sem_1 with "gho") as "[]"|].
    rewrite shr_bor_gho /=.
    iDestruct "gho" as "#(G↦ & Ggho & Pers)".
    rewrite prod_ty_gho_pers /=. iDestruct "Pers" as "#[Pers1 Pers2]".
    have Hsplit : ∀ sem', alt_sem sem' →
      sem' (cells_fml l.1 l.2 (ty_phys ty x tid ++ ty_phys ty' y tid)) ⊣⊢
      sem' (bor_sep
        (cells_fml (cloc_take l (ty_size ty)).1 (cloc_take l (ty_size ty)).2
          (ty_phys ty x tid))
        (cells_fml (cloc_skip l (ty_size ty)).1 (cloc_skip l (ty_size ty)).2
          (ty_phys ty' y tid))).
    { move=> sem' Hs. rewrite (cells_sem_at Hs) (sep_sem_at Hs)
        !(cells_sem_at Hs) heap_mapsto_cells_fancy_vec_app
        /cloc_take /cloc_skip /= ty_size_eq //. }
    iDestruct (dguard_rhs_iff Hsplit with "G↦") as "#G↦'".
    iDestruct (dguard_rhs_sep_l with "G↦'") as "#G↦1".
    iDestruct (dguard_rhs_sep_r with "G↦'") as "#G↦2".
    iDestruct (dguard_rhs_sep_l with "Ggho") as "#Ggho1".
    iDestruct (dguard_rhs_sep_r with "Ggho") as "#Ggho2".
    inversion phys. subst v. iModIntro. iFrame "W tok".
    iExists -[(cloc_take l ty.(ty_size), x); (cloc_skip l ty.(ty_size), y)].
    iSplit; last first.
    { iApply (proph_obs_eq with "Obs")=> ?. done. }
    iSplit.
    { iExists #l.1, (S d'). iSplit.
      { iPureIntro. by rewrite /= path shift_loc_0. }
      rewrite /ty_own shr_bor_gho /=. by iFrame "G↦1 Ggho1 Pers1". }
    iSplit; [|done]. iExists #(l.1 +ₗ ty_size ty), (S d'). iSplit.
    { iPureIntro. by rewrite /= path. }
    rewrite /ty_own shr_bor_gho /=. by iFrame "G↦2 Ggho2 Pers2".
  Qed.

  Lemma tctx_split_shr_xprod {𝔄l} κ (tyl: typel 𝔄l) p E L :
    tctx_incl E L +[p ◁ &shr{κ} (Π! tyl)] (hasty_shr_offsets p κ tyl 0)
      (λ post '-[(l, al)], post (spec_ptr_cloc_offsets al tyl l)).
  Proof.
    apply (tctx_split_ptr_cloc_xprod (λ _, &shr{κ}%T));
      [solve_typing|move=> *; apply tctx_split_shr_prod].
  Qed.

  (** ** Unique references *)

  (** Splitting a unique borrow of a product.

    The original's [⧖]/[⧗]/[£] and the [▷]s they strip are gone, and its two
    halves of [llctx_interp L] are the two halves of one [Ltok]. *)
  Lemma type_split_uniq_bor_instr {𝔄 𝔅} κ (ty: type 𝔄) (ty': type 𝔅) E L I p :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ &uniq{κ} (ty * ty')] SplitBor
      (const +[p +ₗ #0 ◁ &uniq{κ} ty; p +ₗ #ty.(ty_size) ◁ &uniq{κ} ty'])
      (λ post '-[m], λ mask π, ∀ m1 m2,
        uniq_bor_loc m1 = cloc_take (uniq_bor_loc m) ty.(ty_size) →
        uniq_bor_loc m2 = cloc_skip (uniq_bor_loc m) ty.(ty_size) →
        uniq_bor_current m1 = (uniq_bor_current m).1 →
        uniq_bor_future m1 π = (uniq_bor_future m π).1 →
        uniq_bor_current m2 = (uniq_bor_current m).2 →
        uniq_bor_future m2 π = (uniq_bor_future m π).2 →
        post -[m1; m2] mask π)%type.
  Proof.
    move=> Alv. apply typed_instr_of_skip.
    move=> [[[[[l [x0 y0]] ξi] d'] g'] idx] v d tid post mask iκs.
    iIntros "#LFT #PROPH #UNIQ #E L I %path [gho %Phys] #Obs W".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]".
    iDestruct (Ltok_split_1 with "tok") as "[[#key f1] [_ f2]]".
    iDestruct (Ltok_guard_frac with "key") as "#Gfrac".
    iAssert (frac_tok γ (1/2) &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "Gfrac Alv"). }
    rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Ineqs & UniqBody & #PtBase & #Pers)".
    iDestruct "Pers" as "[Dead|#Pers]".
    { (* [κ] is already dead, so the lifetime context is contradictory *)
      iDestruct "Dead" as (κ'') "[#Incl0 #Dead']".
      iDestruct (dincl_sem with "Incl0") as "#Incl'".
      iDestruct (guard_trans with "Gκ Incl'") as "#G3".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G3 f1 Wg") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    iDestruct "UniqBody" as "(ξVo & ξTok & #ξBor)".
    iDestruct (llftl_bor_idx_to_full with "ξBor ξTok") as "ξBorFull".
    iAssert (bor_sem (gsrc_fml (GFrac γ (1/2))) &&{Wguard}&&> @[κ])%I
      as "#Gκx".
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γ (1/2)))). iApply "Gκ". }
    iDestruct (llftl_bor_acc_guarded ⊤ (gsrc_fml (GFrac γ (1/2))) κ
      with "LFT ξBorFull Gκx [f1]") as "A";
      [by iApply (gsrc_fml_sem_2 (s := GFrac γ (1/2)))|].
    iDestruct (fupdw_incl (W:=alerus_wsat) with "A") as "A'".
    iMod ("A'" with "W") as "[W [P' ToBor]]".
    iEval (rewrite uniq_body_fml_sem) in "P'".
    iDestruct "P'" as (x'' d'' g'') "(ξPc & Gho1 & Pt1)".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
    subst d'' g''.
    have ?: Inhabited 𝔄 := populate (vπ x0 inhabitant).
    have ?: Inhabited 𝔅 := populate (vπ y0 inhabitant).
    iMod (uniq_intro x0 (vπ x0) (d', g') with "PROPH UNIQ")
      as (ζi) "[ζVo ζPc]"; [set_solver|].
    iMod (uniq_intro y0 (vπ y0) (d', g') with "PROPH UNIQ")
      as (ζ'i) "[ζ'Vo ζ'Pc]"; [set_solver|].
    set ξ := PrVar ((𝔄 * 𝔅)%ST ↾ prval_to_inh (@vπ (𝔄 * 𝔅)%ST (x0, y0))) ξi.
    set ζ := PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ζi.
    set ζ' := PrVar (𝔅 ↾ prval_to_inh (vπ y0)) ζ'i.
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ToζPc)".
    iDestruct (uniq_proph_tok with "ζ'Vo ζ'Pc") as "(ζ'Vo & ζ' & Toζ'Pc)".
    iMod (uniq_preresolve ξ [ζ; ζ'] (λ π, (π ζ, π ζ'))
      with "UNIQ PROPH ξVo ξPc [$ζ $ζ']")
      as "(#Obs' & (ζ & ζ' & _) & ToξPc)";
      [set_solver|apply (proph_dep_prod [_] [_]); apply proph_dep_one|done|].
    iDestruct ("ToζPc" with "ζ") as "ζPc".
    iDestruct ("Toζ'Pc" with "ζ'") as "ζ'Pc".
    iDestruct ("ToBor" $!
      (uniq_body_fml ty x0 ζi tid (cloc_take l ty.(ty_size)) ∗
       uniq_body_fml ty' y0 ζ'i tid (cloc_skip l ty.(ty_size)))%FML
      with "[ToξPc] [Gho1 Pt1 ζPc ζ'Pc]") as "B".
    { iIntros "Big". rewrite bor_sep_sem !uniq_body_fml_sem.
      iDestruct "Big" as "[(%x1 & %d1 & %g1 & ζPc & Gho1 & Pt1)
                           (%x2 & %d2 & %g2 & ζ'Pc & Gho2 & Pt2)]".
      iModIntro. iExists (x1, x2), (d1 `max` d2), (g1 `max` g2).
      iSplitL "ToξPc ζPc ζ'Pc".
      { iApply "ToξPc". iApply (proph_eqz_constr2 with "[ζPc] [ζ'Pc]");
          [iApply (proph_ctrl_eqz with "PROPH ζPc")
          |iApply (proph_ctrl_eqz with "PROPH ζ'Pc")]. }
      rewrite prod_ty_gho /= heap_cloc_mapsto_fancy_vec_app ty_size_eq.
      iFrame "Pt1 Pt2".
      iDestruct (ty_gho_depth_mono ty d1 g1 (d1 `max` d2) (g1 `max` g2) x1 tid
        with "Gho1") as "[$ _]"; [lia|lia|].
      iDestruct (ty_gho_depth_mono ty' d2 g2 (d1 `max` d2) (g1 `max` g2) x2 tid
        with "Gho2") as "[$ _]"; [lia|lia]. }
    { rewrite bor_sep_sem !uniq_body_fml_sem.
      iEval (rewrite prod_ty_gho /=) in "Gho1".
      iDestruct "Gho1" as "[Gho1 Gho2]".
      iEval (rewrite /= heap_cloc_mapsto_fancy_vec_app ty_size_eq) in "Pt1".
      iDestruct "Pt1" as "[Pt1 Pt2]".
      iSplitL "ζPc Gho1 Pt1".
      - iExists x0, d', g'. iFrame "ζPc Gho1 Pt1".
      - iExists y0, d', g'. iFrame "ζ'Pc Gho2 Pt2". }
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "B") as "B'";
      [set_solver|].
    iMod ("B'" with "W") as "[W [Bor f1]]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ (1/2)) with "f1") as "f1".
    iDestruct (llftl_sep_split ⊤ _ _ κ with "LFT Bor") as "C".
    iDestruct (fupdw_incl (W:=alerus_wsat) with "C") as "C'".
    iMod ("C'" with "W") as "[W [Bor1 Bor2]]".
    iDestruct (Ltok_split_2 with "[$key $f1] [$key $f2]") as "tok".
    iMod (Ltok_withdraw with "tok W") as "[W L]".
    rewrite (llftl_bor_idx κ
      (uniq_body_fml ty x0 ζi tid (cloc_take l ty.(ty_size)))).
    iDestruct "Bor1" as (ζidx) "[#ζBor ζTok]".
    rewrite (llftl_bor_idx κ
      (uniq_body_fml ty' y0 ζ'i tid (cloc_skip l ty.(ty_size)))).
    iDestruct "Bor2" as (ζ'idx) "[#ζ'Bor ζ'Tok]".
    have HsplitPt : ∀ sem', alt_sem sem' →
      sem' (cmapstoany_fml l) ⊣⊢
      sem' (bor_sep (cmapstoany_fml (cloc_take l (ty_size ty)))
                    (cmapstoany_fml (cloc_skip l (ty_size ty)))).
    { move=> sem' Hs. rewrite (cmapstoany_sem_at Hs) (sep_sem_at Hs)
        !(cmapstoany_sem_at Hs).
      apply (heap_cloc_mapsto_emp_vec_app l (ty_size ty)). }
    iDestruct (dguard_rhs_iff HsplitPt with "PtBase") as "#PtBase'".
    iDestruct (dguard_rhs_sep_l with "PtBase'") as "#PtBase1".
    iDestruct (dguard_rhs_sep_r with "PtBase'") as "#PtBase2".
    have Hl1 : ⊢ llft_incl (foldr meet static (ty_lfts ty ++ ty_lfts ty'))
                 (ty_lft ty).
    { rewrite lft_intersect_list_app. iApply llftl_intersect_incl_l. }
    have Hl2 : ⊢ llft_incl (foldr meet static (ty_lfts ty ++ ty_lfts ty'))
                 (ty_lft ty').
    { rewrite lft_intersect_list_app. iApply llftl_intersect_incl_r. }
    iAssert (dincl κ (ty_lft ty)) as "#Inκ1".
    { iApply (dincl_trans with "Incl"). by iApply (dincl_of Hl1). }
    iAssert (dincl κ (ty_lft ty')) as "#Inκ2".
    { iApply (dincl_trans with "Incl"). by iApply (dincl_of Hl2). }
    rewrite prod_ty_gho_pers /=. iDestruct "Pers" as "#[Pers1 Pers2]".
    inversion Phys as [Eqv]. subst v. iModIntro. iFrame "W L I".
    iExists -[(cloc_take l ty.(ty_size), x0, ζi, d', g', ζidx);
              (cloc_skip l ty.(ty_size), y0, ζ'i, d', g', ζ'idx)].
    iSplit; last first.
    { iCombine "Obs Obs'" as "#Obs2".
      iApply (proph_obs_impl with "Obs2")=> π [Ha Hb].
      apply Ha; [done|done|done| |done|];
        rewrite /uniq_bor_future /= Hb //. }
    iSplitL "ζVo ζTok".
    { iExists #l.1, d. iSplit; [by rewrite /= path shift_loc_0|].
      rewrite /ty_own uniq_bor_gho. iSplit; [|done].
      iSplitR; [iApply "Inκ1"|].
      iSplitR; [iPureIntro; lia|]. iFrame "ζVo ζTok ζBor".
      iFrame "PtBase1". by iRight. }
    iSplit; [|done].
    iExists #(l.1 +ₗ ty_size ty), d. iSplit; [by rewrite /= path|].
    rewrite /ty_own uniq_bor_gho. iSplit; [|done].
    iSplitR; [iApply "Inκ2"|].
    iSplitR; [iPureIntro; lia|]. iFrame "ζ'Vo ζ'Tok ζ'Bor".
    iFrame "PtBase2". by iRight.
  Qed.
End product_split.
