(** * Operations on sum types

  Ported from VerusBelt ([typing/type_sum.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  The [⧖]/[⧗]/[£] the original mints and the [▷]s they strip are gone, and
  with them the [leaf_goal laters to …] and [advance_credits] arithmetic;
  guarded reads need no credits here. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.lang.lib Require Import memcpy.
From nola.alerus.typing Require Import int uninit uniq_bor shr_bor own sum.
From nola.alerus.typing Require Import lft_contexts type_context programs
  product programs_util base_type freeable_util uniq_util.
From nola.alerus.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Open Scope nat.

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Notation sum_pad_size tyl ty := (max_ty_size tyl - ty.(ty_size))%nat.

Fixpoint padding_to_vec (n: nat) (p: list val) : vec val n :=
  match n, p with
  | 0, _ => [# ]
  | S n', [] => (#☠) ::: padding_to_vec n' []
  | S n', p' :: pad' => p' ::: padding_to_vec n' pad'
  end.

Lemma pad_eq_padding_to_vec b n :
  pad (fmap FVal b) n = fmap FVal (vec_to_list (padding_to_vec n b)).
Proof.
  generalize b. clear b. induction n.
  - intros. simpl. unfold pad. case_decide; [done|]. simpl. destruct b; [done|].
    simpl in H. lia.
  - intros. simpl. destruct b.
    + simpl. rewrite <- IHn. unfold pad. case_decide; [simpl in H; lia|].
      simpl. f_equal. f_equal. lia.
    + rewrite pad_cons. simpl. by rewrite <- IHn.
Qed.

Lemma pad_app (a : list fancy_val) (b: list val) (n: nat) :
  length a ≤ n →
  pad (a ++ fmap FVal b) n
    = a ++ fmap FVal (vec_to_list (padding_to_vec (n - length a) b)).
Proof.
  generalize n. clear n. induction a.
  - intros n Hineq. simpl. rewrite <- pad_eq_padding_to_vec. f_equal. lia.
  - intros n Hineq. simpl. simpl in Hineq. destruct n; [lia|].
    rewrite pad_cons IHa; [done|lia].
Qed.

Section type_sum.
  Context `{!typeG FML Σ}.

  Lemma split_freeable_xsum {𝔄l} i (tyl: typel 𝔄l) n l :
    freeable_sz n (ty_size (Σ! tyl)) l ⊣⊢
      freeable_sz n 1 l ∗
      freeable_sz n (ty_size (tyl +!! i)) (l +ₗ 1) ∗
      freeable_sz n (sum_pad_size tyl (tyl +!! i))
        (l +ₗ S (ty_size (tyl +!! i))).
  Proof.
    replace (S (ty_size (tyl +!! i))) with (1 + ty_size (tyl +!! i));
      last by lia.
    rewrite <- shift_loc_assoc_nat. rewrite freeable_sz_split.
    rewrite freeable_sz_split. f_equiv. simpl.
    have h := max_hlist_with_ge (λ X : syn_type, ty_size) tyl i.
    rewrite Nat.add_comm Nat.sub_add //.
  Qed.

  Lemma split_pt_xsum {𝔄l} i (tyl: typel 𝔄l) x0 pad tid l :
    l ↦!∗ ty_phys (Σ! tyl) (pinj i x0, pad) tid ⊣⊢
      (l ↦∗ [ #i ]) ∗
      ((l +ₗ 1) ↦!∗ ty_phys (tyl +!! i) x0 tid) ∗
      ((l +ₗ S (ty_size (tyl +!! i))) ↦!∗ fmap FVal
        (vec_to_list (padding_to_vec (sum_pad_size tyl (tyl +!! i)) pad))).
  Proof.
    replace (S (ty_size (tyl +!! i))) with (1 + ty_size (tyl +!! i));
      last by lia.
    rewrite <- shift_loc_assoc_nat.
    replace (l +ₗ 1%nat +ₗ ty_size (tyl +!! i))
      with (l +ₗ 1%nat +ₗ length (ty_phys (tyl +!! i) x0 tid)).
    2: { f_equal. by rewrite ty_size_eq. }
    rewrite <- heap_mapsto_fancy_vec_app. rewrite heap_mapsto_vec_singleton.
    replace (l ↦ #i)%I with (l ↦! FVal #i)%I; last by done.
    rewrite <- (heap_mapsto_fancy_vec_cons _ (FVal #i)).
    unfold ty_phys, xsum_ty. rewrite to_xsum_pinj pad_cons. f_equal. simpl.
    rewrite pad_app.
    - by rewrite ty_size_eq.
    - rewrite ty_size_eq. apply (max_hlist_with_ge (λ X : syn_type, ty_size) tyl i).
  Qed.

  Local Lemma drop_drop {A} n (cells: list A) :
    drop n (drop 1 cells) = drop (S n) cells.
  Proof. destruct n; destruct cells; trivial. Qed.

  Lemma split_pt_xsum_cells {𝔄l} i (tyl: typel 𝔄l) x0 pad tid l cells :
    l ↦[^ cells ]!∗ ty_phys (Σ! tyl) (pinj i x0, pad) tid ⊣⊢
      (l ↦[^ take 1 cells ]∗ [ #i ]) ∗
      ((l +ₗ 1) ↦[^ take (ty_size (tyl +!! i)) (drop 1 cells) ]!∗
        ty_phys (tyl +!! i) x0 tid) ∗
      ((l +ₗ S (ty_size (tyl +!! i)))
        ↦[^ drop (S (ty_size (tyl +!! i))) cells ]!∗ fmap FVal
        (vec_to_list (padding_to_vec (sum_pad_size tyl (tyl +!! i)) pad))).
  Proof.
    replace (S (ty_size (tyl +!! i))) with (1 + ty_size (tyl +!! i));
      last by lia.
    rewrite <- shift_loc_assoc_nat.
    replace (l +ₗ 1%nat +ₗ ty_size (tyl +!! i))
      with (l +ₗ 1%nat +ₗ length (ty_phys (tyl +!! i) x0 tid)).
    2: { f_equal. by rewrite ty_size_eq. }
    unfold xsum_ty, ty_phys. rewrite to_xsum_pinj.
    eassert ((FVal #i :: _ ++ _) = ([FVal #i] ++ _) ++ _) as ->.
    { by rewrite <- List.app_assoc. }
    rewrite pad_app. rewrite <- List.app_assoc.
    - do 2 rewrite heap_mapsto_cells_fancy_vec_app'. f_equiv; [|f_equiv].
      + by rewrite <- heap_mapsto_cells_fancy_fmap_eq.
      + by rewrite ty_size_eq.
      + rewrite List.length_app ty_size_eq /=. by rewrite drop_drop.
    - rewrite List.length_app ty_size_eq.
      have Ha := max_hlist_with_ge (λ X : syn_type, ty_size) tyl i.
      simpl. have Ht : ∀ x y, x ≤ y → S x ≤ S y by lia. apply Ht, Ha.
  Qed.

  Lemma split_pt_xsum_cells' {𝔄l} i (tyl: typel 𝔄l) l cells :
    (l, cells) #↦∗_ ⊣⊢
      ((l, take 1 cells) #↦∗_) ∗
      ((l +ₗ 1, take (ty_size (tyl +!! i)) (drop 1 cells)) #↦∗_) ∗
      ((l +ₗ S (ty_size (tyl +!! i)),
        drop (S (ty_size (tyl +!! i))) cells) #↦∗_).
  Proof.
    replace (S (ty_size (tyl +!! i))) with (1 + ty_size (tyl +!! i));
      last by lia.
    rewrite <- shift_loc_assoc_nat.
    rewrite (heap_cloc_mapsto_emp_vec_app _ (1 + ty_size (tyl +!! i))).
    rewrite bi.sep_assoc. f_equiv.
    - rewrite (heap_cloc_mapsto_emp_vec_app _ 1). f_equiv.
      + destruct cells; trivial.
      + destruct cells; trivial. destruct (ty_size (tyl +!! i)); trivial.
    - simpl. unfold cloc_skip. simpl. f_equiv. f_equal.
      by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma split_pt_xsum_cells'' {𝔄l} i (tyl: typel 𝔄l) x0 pad tid l :
    l #↦!∗ ty_phys (Σ! tyl) (pinj i x0, pad) tid ⊣⊢
      ((cloc_take l 1) #↦∗ [ #i ]) ∗
      (cloc_take (cloc_skip l 1) (ty_size (tyl +!! i)) #↦!∗
        ty_phys (tyl +!! i) x0 tid) ∗
      (cloc_skip (cloc_skip l 1) (ty_size (tyl +!! i)) #↦!∗ fmap FVal
        (vec_to_list (padding_to_vec (sum_pad_size tyl (tyl +!! i)) pad))).
  Proof.
    unfold ty_phys, xsum_ty. simpl. rewrite to_xsum_pinj.
    eassert ((FVal #i :: _ ++ _) = ([FVal #i] ++ _) ++ _) as ->.
    { by rewrite <- List.app_assoc. }
    rewrite pad_app. rewrite <- List.app_assoc.
    - do 2 rewrite heap_cloc_mapsto_fancy_vec_app. f_equiv; [|f_equiv].
      + by rewrite <- heap_complete_mapsto_fancy_fmap_eq.
      + by rewrite ty_size_eq.
      + rewrite List.length_app ty_size_eq /= /cloc_skip. by rewrite drop_drop.
    - rewrite List.length_app ty_size_eq.
      have Ha := max_hlist_with_ge (λ X : syn_type, ty_size) tyl i.
      simpl. have Ht : ∀ x y, x ≤ y → S x ≤ S y by lia. apply Ht, Ha.
  Qed.

  (** ** Owning pointers *)

  Lemma tctx_unwrap_own_xsum {𝔄l 𝔅l} i (tyl: typel 𝔄l) n p (T: tctx 𝔅l) E L :
    let tyi := tyl +!! i in
    tctx_incl E L (p ◁ own_ptr n (Σ! tyl) +:: T)
      (p +ₗ #0 ◁ own_ptr n int +:: p +ₗ #1 ◁ own_ptr n tyi +::
        p +ₗ #(S tyi.(ty_size)) ◁ own_ptr n (↯ (sum_pad_size tyl tyi)) +:: T)
      (λ post '((l, (s, pad)) -:: bl), λ mask π, ∃a: ~~(𝔄l !!ₗ i),
        s = pinj i a ∧ ∀ pad', post ((l, Z.of_nat i) -:: (l +ₗ 1, a) -::
          (l +ₗ S tyi.(ty_size), pad') -:: bl) mask π).
  Proof.
    split.
    { move=> p1 p2 Hyp [[l[s pad]] bl] mask π. split.
      - move=> [a[Heq Ha]]. exists a. split; [exact Heq|]=> pad'.
        apply (proj1 (Hyp _ mask π)), Ha.
      - move=> [a[Heq Ha]]. exists a. split; [exact Heq|]=> pad'.
        apply (proj2 (Hyp _ mask π)), Ha. }
    move=> γ q tid [[l [x pad]] xl] mask post.
    iIntros "#LFT #PROPH #UNIQ #E tok /=[T Tl] #Obs W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π X]; [solve_ndisj|].
    destruct X as [x0 [Heqx _]]. subst x.
    iDestruct "T" as (v d) "[%path [gho %phys]]". inversion phys. subst v.
    destruct d as [|d'];
      [by iDestruct (false_fml_sem_1 with "gho") as "[]"|].
    rewrite own_ptr_gho /=. iDestruct "gho" as "(pt & free & gho)".
    iDestruct (split_freeable_xsum i with "free") as "(free1 & free2 & free3)".
    iDestruct (split_pt_xsum i with "pt") as "(pt1 & pt2 & pt3)".
    rewrite xsum_ty_gho /= to_xsum_pinj.
    iModIntro. iFrame "W tok".
    set tyi := tyl +!! i.
    set pad' := padding_to_vec (sum_pad_size tyl tyi) pad.
    iExists ((l, Z.of_nat i) -:: (l +ₗ 1, x0) -::
      (l +ₗ S tyi.(ty_size), pad') -:: xl).
    iFrame "Tl". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π0 [x1 [Peq Ha]].
      apply pinj_Inj in Peq. subst x1. apply Ha. }
    iSplitL "pt1 free1".
    { iExists #l, (S d'). iSplit.
      { iPureIntro. by rewrite /= path shift_loc_0. }
      rewrite /ty_own own_ptr_gho /= int_gho -heap_mapsto_fancy_fmap_eq.
      by iFrame "pt1 free1". }
    iSplitL "pt2 free2 gho".
    { iExists #(l +ₗ 1), (S d'). iSplit; [by rewrite /= path|].
      rewrite /ty_own own_ptr_gho /=. by iFrame "pt2 free2 gho". }
    iExists #(l +ₗ S (ty_size tyi)), (S d'). iSplit; [by rewrite /= path|].
    rewrite /ty_own own_ptr_gho /= uninit_gho. by iFrame "pt3 free3".
  Qed.

  Lemma type_case_own_outer {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) n p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ own_ptr n (Σ! tyl)] T T' trx →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L I C (p ◁ own_ptr n (Σ! tyl) +:: T') e tr) -∗
    typed_body E L I C T (case: !p of el)
      (trx ∘ (λ post '((l, (s, pad)) -:: cl), let 'xinj i _ := to_xsum s in
        (trl -!! i) post ((l, (s, pad)) -:: cl)))%type.
  Proof.
    move=> ->. iIntros (?) "el". iApply typed_body_tctx_incl; [done|].
    iIntros (tid [s ?] mask post iκs) "#LFT #PROPH #UNIQ #E L I C /=[p T] #Obs".
    destruct s as [l [x pad]].
    replace x with (@of_xsum _ (~~) 𝔄l (to_xsum x));
      last by rewrite semi_iso'.
    refine (match to_xsum x with xinj i x0 => _ end).
    wp_bind p. iApply (twp_hasty with "p"). iIntros (v d) "%Hpath [gho %phys]".
    inversion phys. subst v.
    destruct d as [|d'];
      [by iDestruct (false_fml_sem_1 with "gho") as "[]"|].
    rewrite own_ptr_gho /=. iDestruct "gho" as "(pt & free & gho)".
    iDestruct (split_pt_xsum i with "pt") as "(pt1 & pt2 & pt3)".
    rewrite heap_mapsto_vec_singleton. wp_read.
    rewrite -heap_mapsto_vec_singleton. wp_case.
    { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepHL_2_lookup with "el") as "el".
    iApply ("el" $! _ (_ -:: _) with "LFT PROPH UNIQ E L I C [-] []");
      last first.
    { iApply (proph_obs_impl with "Obs")=> ?. by rewrite to_xsum_pinj. }
    iFrame "T". iExists #l, (S d'). iSplit; [done|].
    rewrite /ty_own own_ptr_gho /=. iFrame "free gho".
    rewrite split_pt_xsum. by iFrame "pt1 pt2 pt3".
  Qed.

  (** ** Shared references *)

  (** The sum's ghost assertion at an injected refinement is the injected
    type's, up to the [to_xsum]/[pinj] round trip. *)
  Lemma xsum_gho_pinj {𝔄l} i (tyl: typel 𝔄l) x0 pad d g tid :
    ty_gho (Σ! tyl) (pinj i x0, pad) d g tid ⊣⊢ ty_gho (tyl +!! i) x0 d g tid.
  Proof. rewrite xsum_ty_gho /= to_xsum_pinj //. Qed.
  Lemma xsum_gho_pers_pinj {𝔄l} i (tyl: typel 𝔄l) x0 pad d g tid :
    ty_gho_pers (Σ! tyl) (pinj i x0, pad) d g tid ⊣⊢
      ty_gho_pers (tyl +!! i) x0 d g tid.
  Proof. rewrite xsum_ty_gho_pers /= to_xsum_pinj //. Qed.

  Lemma tctx_unwrap_shr_xsum {𝔄l 𝔅l} i (tyl: typel 𝔄l) κ p (T: tctx 𝔅l) E L :
    tctx_incl E L (p ◁ &shr{κ} (Σ! tyl) +:: T)
      (p +ₗ #1 ◁ &shr{κ} (tyl +!! i) +:: T)
      (λ post '((l, (s, pad)) -:: bl), λ mask π, ∃a: ~~(𝔄l !!ₗ i),
        s = pinj i a ∧
        post ((cloc_take (cloc_skip l 1) (ty_size (tyl +!! i)), a) -:: bl)
          mask π).
  Proof.
    split.
    { move=> p1 p2 Hyp [[l[s pad]] bl] mask π. split.
      - move=> [a[Heq Ha]]. exists a. split; [exact Heq|].
        apply (proj1 (Hyp _ mask π)), Ha.
      - move=> [a[Heq Ha]]. exists a. split; [exact Heq|].
        apply (proj2 (Hyp _ mask π)), Ha. }
    move=> γ q tid [[cl [x pad]] xl] mask post.
    iIntros "#LFT #PROPH #UNIQ #E tok /=[p T] #Obs W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 X]; [solve_ndisj|].
    destruct X as [x0 [Heqx _]]. subst x.
    iDestruct "p" as (v d) "[%Ev [gho %phys]]". inversion phys. subst v.
    destruct d as [|d'];
      [by iDestruct (false_fml_sem_1 with "gho") as "[]"|].
    rewrite shr_bor_gho /=. iDestruct "gho" as "#(Gpt & Ggho & Pers)".
    iDestruct (guard_rhs_iff
      (split_pt_xsum_cells i tyl x0 pad tid cl.1 cl.2) with "Gpt") as "#Gpt2".
    iDestruct (guard_rhs_sep_r with "Gpt2") as "#Grest".
    iDestruct (guard_rhs_sep_l with "Grest") as "#Gmain".
    iDestruct (guard_rhs_iff (xsum_gho_pinj i tyl x0 pad d' (S d') tid)
      with "Ggho") as "#Ggho2".
    rewrite xsum_gho_pers_pinj.
    iModIntro. iFrame "W tok".
    iExists ((cloc_take (cloc_skip cl 1) (ty_size (tyl +!! i)), x0) -:: xl).
    iFrame "T". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π [xi [Heq Ha]].
      apply pinj_Inj in Heq. by subst xi. }
    destruct cl as [cl1 cells].
    iExists _, (S d'). iSplit; [by rewrite /= Ev|].
    rewrite /ty_own shr_bor_gho /=. iSplit; [|done].
    by iFrame "Gmain Ggho2 Pers".
  Qed.

  Lemma type_case_shr_outer {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (Σ! tyl)] T T' trx →
    lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L I C (p ◁ &shr{κ} (Σ! tyl) +:: T') e tr) -∗
    typed_body E L I C T (case: !p of el)
      (trx ∘ (λ post '((l, (s, pad)) -:: cl), let 'xinj i _ := to_xsum s in
        (trl -!! i) post ((l, (s, pad)) -:: cl)))%type.
  Proof.
    move=> ->. iIntros (? Alv) "el". iApply typed_body_tctx_incl; [done|].
    iIntros (tid [s ?] mask post iκs)
      "#LFT #PROPH #UNIQ #E L I C /=[p T] #Obs".
    destruct s as [l [x pad]].
    replace x with (@of_xsum _ (~~) 𝔄l (to_xsum x));
      last by rewrite semi_iso'.
    refine (match to_xsum x with xinj i x0 => _ end).
    wp_bind p. iApply (twp_hasty with "p"). iIntros (v d) "%Hpath [gho %phys]".
    inversion phys. subst v.
    destruct d as [|d'];
      [by iDestruct (false_fml_sem_1 with "gho") as "[]"|].
    rewrite shr_bor_gho /=. iDestruct "gho" as "#(Gpt & Ggho & Pers)".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (guard_trans with "Alv Gpt") as "#GptL".
    iDestruct (guard_rhs_iff
      (split_pt_xsum_cells i tyl x0 pad tid l.1 l.2) with "GptL") as "#Gpt2".
    iDestruct (guard_rhs_sep_l with "Gpt2") as "#Gdisc".
    wp_bind (!#l.1)%E.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & [#key f])]".
    iAssert (bor_sem (gsrc_fml (GFrac γ 1)) &&{Wguard}&&>
      (l.1 ↦[^ take 1 l.2 ]∗ [ #i ]))%I as "#Gdisc'".
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γ 1))).
      iApply (guard_trans with "[] Gdisc").
      iApply (Ltok_guard_frac with "key"). }
    iModIntro. iFrame "W".
    iApply (twp_read_na_guarded_cells_singleton _ _ _ _ _
      (gsrc_fml (GFrac γ 1)) with "[f]").
    { iFrame "Gdisc'". by iApply (gsrc_fml_sem_2 (s := GFrac γ 1)). }
    iIntros "f". iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ 1) with "f") as "f".
    iMod (Ltok_withdraw with "[$key $f] W") as "[W L]".
    iModIntro. iFrame "W".
    wp_case.
    { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepHL_2_lookup with "el") as "el".
    iApply ("el" $! _ (_ -:: _) with "LFT PROPH UNIQ E L I C [-] []");
      last first.
    { iApply (proph_obs_impl with "Obs")=> ?. by rewrite to_xsum_pinj. }
    iFrame "T". iExists #l.1, (S d'). iSplit; [done|].
    rewrite /ty_own shr_bor_gho /=. by iFrame "Gpt Ggho Pers".
  Qed.

  Lemma type_case_shr {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (Σ! tyl)] T T' trx →
    lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl, match tr with
      | inl otr => typed_body E L I C (p ◁ &shr{κ} (Σ! tyl) +:: T') e otr
      | inr itr => typed_body E L I C (p +ₗ #1 ◁ &shr{κ} ty +:: T') e itr
      end) -∗
    typed_body E L I C T (case: !p of el) (trx ∘
      (λ post '((l, (s, pad)) -:: cl), let 'xinj i a := to_xsum s in
        match trl -!! i with
        | inl otr => otr post ((l, (s, pad)) -:: cl)
        | inr itr =>
          itr post ((cloc_take (cloc_skip l 1) (ty_size (tyl +!! i)), a) -:: cl)
        end)).
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_shr_outer _ (pbyidx (λ i post
        '((l, (s, pad)) -:: cl), λ mask π, match trl -!! i with
          | inl otr => otr post ((l, (s, pad)) -:: cl) mask π
          | inr itr => _ end : Prop)));
        [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (i) "?". rewrite pbyidx_plookup.
      case (trl -!! i)=> ?.
      { via_tr_impl; first by done.
        move=> post xl mask π Ha. by destruct xl as [[l [s pad]] cl]. }
      via_tr_impl.
      { iApply typed_body_tctx_incl; [apply tctx_unwrap_shr_xsum|done]. }
      move=>/= ?[[?[??]]?]??. exact id. }
    move=> ?[[l [s pad]] ?]/= ??. case (to_xsum s) as [i ?] eqn: Eq.
    rewrite pbyidx_plookup. move: (trl -!! i). case; [done|]=>/= ??.
    eexists _. split; [|done].
    move: Eq=> /(f_equal of_xsum)=>/= <-. by rewrite semi_iso'.
  Qed.

  Lemma type_case_shr_inner {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (Σ! tyl)] T T' trx →
    lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L I C (p +ₗ #1 ◁ &shr{κ} ty +:: T') e tr) -∗
    typed_body E L I C T (case: !p of el) (trx ∘
      (λ post '((l, (s, pad)) -:: cl), let 'xinj i a := to_xsum s in
        (trl -!! i) post
          ((cloc_take (cloc_skip l 1) (ty_size (tyl +!! i)), a) -:: cl))).
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_shr _ (pbyidx (λ i, inr (trl -!! i))));
        [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (?) "?". by rewrite pbyidx_plookup. }
    move=> ?[[l [s pad]] ?]/=. case (to_xsum s)=>/= ??.
    by rewrite pbyidx_plookup.
  Qed.

  (** ** Unique references *)

  (** The original's [⧖]/[⧗]/[£] and the [▷]s they strip are gone; the
    arbitrary [Timeless G] guarding [@[κ]] is the fraction inside the
    [Ltok] the context now is. *)
  Lemma tctx_unwrap_uniq_xsum {𝔄l 𝔅l} i (tyl: typel 𝔄l) κ p (T: tctx 𝔅l) E L :
    lctx_lft_alive E L κ →
    tctx_incl E L (p ◁ &uniq{κ} (Σ! tyl) +:: T)
      (p +ₗ #1 ◁ &uniq{κ} (tyl +!! i) +:: T)
      (λ post '(m -:: bl), λ mask π, ∃a: ~~(𝔄l !!ₗ i),
        (uniq_bor_current m).1 = pinj i a ∧
        ∀a': 𝔄l !!ₗ i, (uniq_bor_future m π).1 = pinj i a' →
        ∀ m': ~~ (uniq_borₛ (𝔄l !!ₗ i)),
          uniq_bor_current m' = a → uniq_bor_future m' π = a' →
          post (m' -:: bl) mask π).
  Proof.
    move=> Alv. split.
    { move=> p1 p2 Eq [m bl] mask π. split.
      - move=> [a[Heq Ha]]. exists a. split; [exact Heq|]=> a' H1 m' H2 H3.
        apply (proj1 (Eq _ mask π)), (Ha a' H1 m' H2 H3).
      - move=> [a[Heq Ha]]. exists a. split; [exact Heq|]=> a' H1 m' H2 H3.
        apply (proj2 (Eq _ mask π)), (Ha a' H1 m' H2 H3). }
    move=> γ q tid [[[[[[l [x0 pad]] ξi] d'] g'] idx] xl] mask post.
    iIntros "#LFT #PROPH #UNIQ #E tok /=[p T] #Obs W".
    iDestruct (lctx_lft_alive_get_guards γ q E L κ Alv with "E tok W")
      as "(tok & W & #Alv)".
    iDestruct "tok" as "[#key f]".
    iAssert (frac_tok γ q &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "[] Alv"). iApply (Ltok_guard_frac with "key"). }
    iDestruct "p" as (v d) "[%Ev [gho %Phys]]".
    iMod (proph_obs_sat with "PROPH Obs") as %[πSat X]; [solve_ndisj|].
    destruct X as [x1 [PinjEq _]]. simpl in PinjEq. subst x0.
    rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Ineqs & UniqBody & #PtBase & #Pers)".
    iDestruct "Pers" as "[Dead|#Pers]".
    { (* [κ] is already dead, so the lifetime context is contradictory *)
      iDestruct "Dead" as (κ'') "[#Incl' #Dead']".
      iDestruct (guard_trans with "Gκ Incl'") as "#G3".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G3 f Wg") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    rewrite xsum_gho_pers_pinj.
    iDestruct "UniqBody" as "(ξVo & ξTok & #ξBor)".
    iDestruct (llftl_bor_idx_to_full with "ξBor ξTok") as "ξBorFull".
    iAssert (bor_sem (gsrc_fml (GFrac γ q)) &&{Wguard}&&> @[κ])%I as "#Gκx".
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γ q))). iApply "Gκ". }
    iDestruct (llftl_bor_acc_guarded ⊤ (gsrc_fml (GFrac γ q)) κ
      with "LFT ξBorFull Gκx [f]") as "A";
      [by iApply (gsrc_fml_sem_2 (s := GFrac γ q))|].
    iDestruct (fupdw_incl (W:=alerus_wsat) with "A") as "A'".
    iMod ("A'" with "W") as "[W [P' ToBor]]".
    iEval (rewrite uniq_body_fml_sem) in "P'".
    iDestruct "P'" as (x'' d'' g'') "(ξPc & Gho1 & Pt1)".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
    subst d'' g''.
    have ?: Inhabited (𝔄l !!ₗ i) := populate (vπ x1 inhabitant).
    iMod (uniq_intro x1 (vπ x1) (d', g') with "PROPH UNIQ")
      as (ζi) "[ζVo ζPc]"; [set_solver|].
    set ξ := PrVar ((Σ! 𝔄l)%ST ↾
      prval_to_inh (@vπ (Σ! 𝔄l)%ST (pinj i x1, pad))) ξi.
    set ζ := PrVar ((𝔄l !!ₗ i) ↾ prval_to_inh (vπ x1)) ζi.
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ToζPc)".
    iMod (uniq_preresolve ξ [ζ] (λ π, (of_xsum (xinj i (π ζ)), pad))
      with "UNIQ PROPH ξVo ξPc [$ζ]")
      as "(#Obs' & (ζ & _) & ToξPc)"; [set_solver| |done|].
    { move=> π π' Eqv. have Eqv2 := Eqv ζ. rewrite Eqv2; [done|].
      apply list_elem_of_here. }
    iDestruct ("ToζPc" with "ζ") as "ζPc".
    iEval (rewrite xsum_gho_pinj) in "Gho1".
    iEval (rewrite (split_pt_xsum_cells'' i)) in "Pt1".
    iDestruct "Pt1" as "(Pt1 & Pt2 & Pt3)".
    iDestruct ("ToBor" $! (uniq_body_fml (tyl +!! i) x1 ζi tid
      (cloc_take (cloc_skip l 1) (ty_size (tyl +!! i))))
      with "[ToξPc Pt1 Pt3] [ζPc Gho1 Pt2]") as "B".
    { iIntros "Body". iEval (rewrite uniq_body_fml_sem) in "Body".
      iDestruct "Body" as (y e h) "(ζPc & Gho & Pt)". iModIntro.
      rewrite uniq_body_fml_sem. iExists (pinj i y, pad), e, h.
      rewrite xsum_gho_pinj (split_pt_xsum_cells'' i).
      iFrame "Gho Pt1 Pt Pt3". iApply "ToξPc".
      iApply (proph_eqz_modify (λ π, (pinj i (π ζ), pad))).
      { iApply proph_obs_true=> ?. done. }
      iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
      iDestruct (proph_eqz_constr (λ t : 𝔄l !!ₗ i, (pinj i t, pad))
        (H:=ltac:(move=> u1 u2 ha; inversion ha as [hb];
          by apply pinj_Inj in hb)) with "Eqz") as "Eqz2".
      iApply (proph_eqz_eq with "Eqz2"); [done|].
      fun_ext=> ?. simpl. by rewrite psum_map1_pinj. }
    { rewrite uniq_body_fml_sem. iExists x1, d', g'. iFrame "ζPc Gho1 Pt2". }
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "B") as "B'";
      [set_solver|].
    iMod ("B'" with "W") as "[W [Bor f]]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ q) with "f") as "f".
    rewrite (llftl_bor_idx κ (uniq_body_fml (tyl +!! i) x1 ζi tid
      (cloc_take (cloc_skip l 1) (ty_size (tyl +!! i))))).
    iDestruct "Bor" as (ζidx) "[#ζBor ζTok]".
    iDestruct (guard_rhs_iff (split_pt_xsum_cells' i tyl l.1 l.2)
      with "PtBase") as "#PtBase'".
    iDestruct (guard_rhs_sep_r with "PtBase'") as "#PtBasex".
    iDestruct (guard_rhs_sep_l with "PtBasex") as "#PtBase2".
    inversion Phys as [Eqv]. subst v.
    iModIntro. iFrame "W key f".
    destruct l as [l1 cells].
    iExists ((cloc_take (cloc_skip (l1, cells) 1) (ty_size (tyl +!! i)),
      x1, ζi, d', g', ζidx) -:: xl).
    iFrame "T". iSplit; last first.
    { iCombine "Obs Obs'" as "#Obs2".
      iApply (proph_obs_impl with "Obs2")=>/= π [[x2 [Heq2 Ha]] Hb].
      apply pinj_Inj in Heq2. subst x2. apply (Ha (π ζ)); [|done|done].
      rewrite /uniq_bor_future /= Hb //. }
    iExists _, d. iSplit; [by rewrite /= Ev|].
    rewrite /ty_own uniq_bor_gho. iSplit; [|done].
    iSplitR.
    { iApply (guard_trans with "Incl []").
      iApply lft_intersect_tyl_lfts_lookup_incl. }
    iSplitR; [iPureIntro; lia|]. iFrame "ζVo ζTok ζBor".
    iFrame "PtBase2". by iRight.
  Qed.
End type_sum.
