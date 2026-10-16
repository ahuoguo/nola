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
Import GuardNotation ModwNotation WpwNotation.

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

  (** [type_case_uniq_outer]'s guard source.  The original's is
    [uniq_body … ∗ llctx_interp L]; here both halves have to be formulas. *)
  Definition case_uniq_src {𝔄} (ty: type 𝔄) (x: ~~𝔄) (ξi: positive)
      (d g: nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: cloc) (γ: gname)
      : FML $oi Σ :=
    (uniq_body_fmlx ty x ξi d g idx κ tid l ∗ gsrc_fml (GFrac γ 1))%FML.

  Lemma case_uniq_src_sem {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l γ :
    bor_sem (case_uniq_src ty x ξi d g idx κ tid l γ) ⊣⊢
      uniq_body ty x ξi d g idx κ tid l ∗ frac_tok γ 1.
  Proof.
    rewrite /case_uniq_src bor_sep_sem uniq_body_fmlx_sem
      (gsrc_fml_sem (GFrac γ 1)) //.
  Qed.
  Lemma case_uniq_src_sem_1 {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l γ :
    bor_sem (case_uniq_src ty x ξi d g idx κ tid l γ) ⊢
      uniq_body ty x ξi d g idx κ tid l ∗ frac_tok γ 1.
  Proof. by rewrite case_uniq_src_sem. Qed.
  Lemma case_uniq_src_sem_2 {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l γ :
    uniq_body ty x ξi d g idx κ tid l ∗ frac_tok γ 1 ⊢
      bor_sem (case_uniq_src ty x ξi d g idx κ tid l γ).
  Proof. by rewrite case_uniq_src_sem. Qed.

  Lemma type_case_uniq_outer {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (Σ! tyl)] T T' trx →
    lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L I C (p ◁ &uniq{κ} (Σ! tyl) +:: T') e tr) -∗
    typed_body E L I C T (case: !p of el)
      (trx ∘ (λ post '(m -:: cl),
        let 'xinj i _ := to_xsum (uniq_bor_current m).1 in
        (trl -!! i) post (m -:: cl)))%type.
  Proof.
    move=> ->. iIntros (? Alv) "el". iApply typed_body_tctx_incl; [done|].
    iIntros (tid [s ?] mask post iκs)
      "#LFT #PROPH #UNIQ #E L I C /=[p T] #Obs".
    destruct s as [[[[[l [x pad]] ξi] d'] g'] idx].
    replace x with (@of_xsum _ (~~) 𝔄l (to_xsum x));
      last by rewrite semi_iso'.
    refine (match to_xsum x with xinj i x0 => _ end).
    wp_bind p. iApply (twp_hasty with "p"). iIntros (v d) "%Hpath [gho %phys]".
    inversion phys. subst v.
    rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Hle & uniq & #pt & #pers)".
    iDestruct (Alv with "L E") as "#LguardsK".
    iDestruct (uniq_body_pers_component_impl with "uniq") as "#uniq_pers".
    wp_bind (!(LitV l.1))%E.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & [#key f])]".
    iAssert (bor_sem (case_uniq_src (Σ! tyl) (pinj i x0, pad) ξi d' g' idx κ
      tid l γ) &&{Wguard}&&> @[κ])%I as "#GκS".
    { iApply (guard_lhs_iff (case_uniq_src_sem (Σ! tyl) (pinj i x0, pad) ξi
        d' g' idx κ tid l γ)).
      iApply guard_lhs_sep_r. iApply (guard_trans with "[] LguardsK").
      iApply (Ltok_guard_frac with "key"). }
    iAssert (bor_sem (case_uniq_src (Σ! tyl) (pinj i x0, pad) ξi d' g' idx κ
      tid l γ) &&{Wguard}&&>
      uniq_body (Σ! tyl) (pinj i x0, pad) ξi d' g' idx κ tid l)%I as "#GuS".
    { iApply (guard_lhs_iff (case_uniq_src_sem (Σ! tyl) (pinj i x0, pad) ξi
        d' g' idx κ tid l γ)).
      iApply guard_sep_l. }
    iDestruct (guard_inner_from_guard_uniq_body _ _ _ _ _ _ _ _ _ _
      with "LFT uniq_pers GuS GκS") as "#Gu".
    iDestruct (guard_rhs_sep_r with "Gu") as "#Gu2".
    iDestruct (guard_cloc_combine_fancy with "[] Gu2") as "#Gpt".
    { iApply (guard_trans with "GκS pt"). }
    iDestruct (guard_rhs_iff
      (split_pt_xsum_cells i tyl x0 pad tid l.1 l.2) with "Gpt") as "#Gpt2".
    iDestruct (guard_rhs_sep_l with "Gpt2") as "#Gdisc".
    iModIntro. iFrame "W".
    iApply (twp_read_na_guarded_cells_singleton _ _ _ _ _
      (case_uniq_src (Σ! tyl) (pinj i x0, pad) ξi d' g' idx κ tid l γ)
      with "[uniq f]").
    { iFrame "Gdisc". iApply case_uniq_src_sem_2. iFrame "uniq f". }
    iIntros "S". iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iDestruct (case_uniq_src_sem_1 with "S") as "[uniq f]".
    iMod (Ltok_withdraw with "[$key $f] W") as "[W L]".
    iModIntro. iFrame "W".
    wp_case.
    { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepHL_2_lookup with "el") as "el".
    iApply ("el" $! _ (_ -:: _) with "LFT PROPH UNIQ E L I C [-] []");
      last first.
    { iApply (proph_obs_impl with "Obs")=> ?. by rewrite to_xsum_pinj. }
    iFrame "T". iExists _, d. iSplit; [done|].
    rewrite /ty_own uniq_bor_gho. iSplit; [|done].
    by iFrame "pers Incl uniq pt".
  Qed.

  Lemma type_case_uniq {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (Σ! tyl)] T T' trx →
    lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl, match tr with
      | inl otr => typed_body E L I C (p ◁ &uniq{κ} (Σ! tyl) +:: T') e otr
      | inr itr => typed_body E L I C (p +ₗ #1 ◁ &uniq{κ} ty +:: T') e itr
      end) -∗
    typed_body E L I C T (case: !p of el) (trx ∘ (λ post '(m -:: cl), λ mask π,
      let 'xinj i a := to_xsum (uniq_bor_current m).1 in
      match trl -!! i with
      | inl otr => otr post (m -:: cl) mask π
      | inr itr => ∀a': 𝔄l !!ₗ i, (uniq_bor_future m π).1 = pinj i a' →
        ∀ m': ~~ (uniq_borₛ (𝔄l !!ₗ i)),
          uniq_bor_current m' = a → uniq_bor_future m' π = a' →
          itr post (m' -:: cl) mask π
      end))%type.
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_uniq_outer _ (pbyidx (λ i post '(m -:: cl), λ mask π,
        match trl -!! i with
        | inl otr => otr post (m -:: cl) mask π
        | inr itr => _ end : Prop)));
        [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (i) "?". rewrite pbyidx_plookup.
      case (trl -!! i)=> ?; [by via_tr_impl; [done|]=> ?[[??]?]?|].
      via_tr_impl.
      { iApply typed_body_tctx_incl; [by apply tctx_unwrap_uniq_xsum|done]. }
      move=>/= ?[??]??. exact id. }
    move=> ?[m ?]/= ??. case (to_xsum (uniq_bor_current m).1) as [i ?] eqn: Eq.
    rewrite pbyidx_plookup. move: (trl -!! i). case; [done|]=>/= ??.
    eexists _. split; [|done].
    move: Eq=> /(f_equal of_xsum)=>/= <-. by rewrite semi_iso'.
  Qed.

  Lemma type_case_uniq_inner {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (Σ! tyl)] T T' trx →
    lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L I C (p +ₗ #1 ◁ &uniq{κ} ty +:: T') e tr) -∗
    typed_body E L I C T (case: !p of el) (trx ∘ (λ post '(m -:: cl), λ mask π,
      let 'xinj i a := to_xsum (uniq_bor_current m).1 in
      ∀a': 𝔄l !!ₗ i, (uniq_bor_future m π).1 = pinj i a' →
        ∀ m': ~~ (uniq_borₛ (𝔄l !!ₗ i)),
          uniq_bor_current m' = a → uniq_bor_future m' π = a' →
          (trl -!! i) post (m' -:: cl) mask π))%type.
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_uniq _ (pbyidx (λ i, inr (trl -!! i))));
        [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (?) "?". by rewrite pbyidx_plookup. }
    move=> ?[m ?]/=. case (to_xsum (uniq_bor_current m).1)=>/= ??.
    by rewrite pbyidx_plookup.
  Qed.

  (** ** Writing into a sum *)

  (** The original splits a four-way [£] budget here and feeds it to the two
    write guards, to [lc_step_fupdN_elim_later] for [resolve] and to the
    closing [typed_write] step.  Later-free, none of it is needed. *)
  Lemma type_sum_assign_instr {𝔄 𝔄' 𝔅 𝔅l} (tyl: typel 𝔅l) (i: fin _)
      (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄') p q gt st Φ E L I :
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    typed_instr E L I +[p ◁ ty; q ◁ tyl +!! i] (p <-{Σ i} q) (λ _, +[p ◁ ty'])
      (λ post '-[a; b], λ mask π, ∀ pad,
        Φ (gt a) π (∀ z, st a (pinj i b, pad) z → post -[z] mask π)).
  Proof.
    iIntros ([Eq Wrt] Rslv ???? (x & y &[]))
      "#LFT #PROPH #UNIQ #E L I (p & q & _) Obs".
    iDestruct (closed_hasty with "p") as %Cp.
    iDestruct (closed_hasty with "q") as %Cq.
    iApply twpw_fupdw_nonval; [done|].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]".
    iDestruct (Ltok_split_1 with "tok") as "[t1 t2]". iModIntro. iFrame "W".
    wp_bind p. iApply (twp_hasty with "p"). iIntros (v d Heq) "ty".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Wrt with "LFT UNIQ E t1 ty W") as
      "(W & %l & %d' & %Hx & %Heqv & -> & (%vl & ↦ & A) & H & #Hguards &
        Toty')".
    inversion Heqv. subst v.
    iDestruct "A" as "[tyb_ghos %tyb_phys]".
    assert (length vl = ty_size tyb) as Sz.
    { rewrite <- tyb_phys. apply ty_size_eq. }
    destruct vl as [|v vl]; [rewrite Eq in Sz; done|].
    destruct l as [l cells]. destruct cells as [|cells0 cells]; [done|].
    rewrite heap_mapsto_cloc_fancy_vec_cons. iDestruct "↦" as "[↦1 ↦2]".
    rewrite -heap_complete_mapsto_fancy_singleton.
    iMod (mapsto_vec_untether_singleton _ _ ⊤ ∅ with "↦1")
      as (v₀ l₀ c₀) "[%Hl [↦1 _]]". inversion Hl. subst l₀ c₀.
    iModIntro. iFrame "W". wp_bind (_ <- _)%E.
    iApply (twp_write_na_guarded _ _ _ _ _ _ _ Hx with "[H ↦1]").
    { iDestruct (guard_rhs_iff (heap_mapsto_cloc_emp_cons l cells0 cells)
        with "Hguards") as "#Hg0".
      iDestruct (guard_rhs_sep_l with "Hg0") as "#Hg". iFrame "Hg H ↦1". }
    iIntros "[↦1 H]". wp_seq.
    wp_bind p. iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    wp_op. wp_bind q. iApply (twp_hasty with "q"). iIntros (vb db ?) "tyb'".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Rslv _ _ ⊤ with "LFT PROPH UNIQ E t2 tyb_ghos W")
      as "(W & #Obs' & t2)"; [solve_ndisj|].
    iDestruct "tyb'" as "[tyb'_gho %tyb'_phys]".
    assert (ty_size (tyl +!! i) = 1) as Sz'.
    { rewrite <- (ty_size_eq _ y tid). by rewrite tyb'_phys. }
    destruct vl as [|v2 vl].
    { exfalso. have Hge := max_hlist_with_ge (λ X : syn_type, ty_size) tyl i.
      have X : ty_size tyb = S (max_hlist_with (λ X : syn_type, ty_size) tyl)
        by apply Eq.
      simpl in Sz. rewrite -Sz in X.
      have X0 : max_hlist_with (λ X : syn_type, ty_size) tyl = 0 by lia.
      rewrite X0 Sz' in Hge. lia. }
    destruct cells as [|cells2 cells]; [done|].
    rewrite heap_mapsto_cloc_fancy_vec_cons. iDestruct "↦2" as "[↦2 ↦3]".
    rewrite -heap_complete_mapsto_fancy_singleton.
    iMod (mapsto_vec_untether_singleton _ _ ⊤ ∅ with "↦2")
      as (v₁ l₁ c₁) "[%Hl₁ [↦2 _]]". inversion Hl₁. subst l₁ c₁.
    iMod (mapsto_vec_untether _ _ ⊤ ∅ with "↦3")
      as (vlc) "[↦3 [%Hlen3 _]]".
    iModIntro. iFrame "W".
    iApply (twp_write_na_guarded _ _ _ _ _ _ _ Hx with "[H ↦2]").
    { iDestruct (guard_rhs_iff
        (heap_mapsto_cloc_emp_cons l cells0 (cells2 :: cells))
        with "Hguards") as "#Hg0".
      iDestruct (guard_rhs_sep_r with "Hg0") as "#Hg1".
      iDestruct (guard_rhs_iff
        (heap_mapsto_cloc_emp_cons (l +ₗ 1) cells2 cells) with "Hg1")
        as "#Hg2".
      iDestruct (guard_rhs_sep_l with "Hg2") as "#Hg". iFrame "Hg H ↦2". }
    iIntros "[↦2 H] W".
    iMod ("Toty'" $! (pinj i y, vlc) db with "[↦1 ↦2 ↦3 tyb'_gho] H W")
      as "(W & %z & tok1 & %Hz & ty')".
    { iExists (FVal #i :: FVal vb :: fmap FVal vlc).
      rewrite !heap_mapsto_cloc_fancy_vec_cons /ty_own xsum_gho_pinj.
      iFrame "↦1 ↦2 ↦3". iSplitL.
      { iDestruct (ty_gho_depth_mono with "tyb'_gho") as "[$ _]"; [lia|lia]. }
      iPureIntro. rewrite /ty_phys /xsum_ty /= to_xsum_pinj tyb'_phys /=.
      apply pad_length'. rewrite /= length_fmap Hlen3.
      rewrite Eq in Sz. simpl in Sz. simpl. lia. }
    iDestruct (Ltok_split_2 with "tok1 t2") as "tok".
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    iExists -[z]. iFrame "L I". iSplitR "Obs".
    - rewrite right_id tctx_hasty_val'; [|done].
      iExists (S (d' `max` db)). iDestruct "ty'" as "[gho phys]". iFrame.
      iDestruct (ty_gho_depth_mono with "gho") as "[$ _]"; [lia|lia].
    - iCombine "Obs Obs'" as "Obs2".
      iApply (proph_obs_impl with "Obs2")=>/= ?[Ha Imp].
      generalize Hz. generalize z. apply Imp. apply Ha.
  Qed.

  Lemma type_sum_assign {𝔄 𝔄' 𝔅 𝔅l ℭl 𝔇l 𝔈} (tyl: typel 𝔅l) (i: fin _)
      (k: Z) (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄')
      (T: tctx ℭl) (T': tctx 𝔇l) p q gt st Φ tr trx E L I (C: cctx 𝔈) e :
    Closed [] e → k = i →
    tctx_extract_ctx E L +[p ◁ ty; q ◁ tyl +!! i] T T' trx →
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    typed_body E L I C (p ◁ ty' +:: T') e tr -∗
    typed_body E L I C T (p <-{Σ k} q;; e) (trx ∘
      (λ post '(a -:: b' -:: dl), λ mask π, ∀ pad,
        Φ (gt a) π (∀ z, st a (pinj i b', pad) z →
          tr post (z -:: dl) mask π)))%type.
  Proof.
    iIntros (?->???) "e". iApply typed_body_tctx_incl; [done|].
    iApply type_seq; [by eapply type_sum_assign_instr|apply tctx_incl_refl|
      |done].
    by move=> ?[?[??]]/=.
  Qed.

  Lemma type_sum_unit_instr {𝔄 𝔄' 𝔅 𝔅l} (tyl: typel 𝔅l) (i: fin _)
      (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄') f p gt st Φ E L I :
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    subtype E L () (tyl +!! i) f →
    typed_instr E L I +[p ◁ ty] (p <-{Σ i} ()) (λ _, +[p ◁ ty'])
      (λ post '-[a], λ mask π, ∀ pad,
        Φ (gt a) π (∀ z, st a (pinj i (f ~~$ₛ ()), pad) z →
          post -[z] mask π)).
  Proof.
    iIntros ([Eq Wrt] Rslv Subtype ???? (x & []))
      "#LFT #PROPH #UNIQ #E L I (p & _) Obs".
    iDestruct (closed_hasty with "p") as %Cp.
    iDestruct (Subtype with "L") as "#Sub".
    iDestruct ("Sub" with "E") as "(%Ssz & _ & Sgho & _ & %Sphys)".
    iApply twpw_fupdw_nonval; [done|].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]".
    iDestruct (Ltok_split_1 with "tok") as "[t1 t2]". iModIntro. iFrame "W".
    wp_bind p. iApply (twp_hasty with "p"). iIntros (v d Heq) "ty".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Wrt with "LFT UNIQ E t1 ty W") as
      "(W & %l & %d' & %Hx & %Heqv & -> & (%vl & ↦ & A) & H & #Hguards &
        Toty')".
    inversion Heqv. subst v.
    iDestruct "A" as "[tyb_ghos %tyb_phys]".
    assert (length vl = ty_size tyb) as Sz.
    { rewrite <- tyb_phys. apply ty_size_eq. }
    destruct vl as [|v vl]; [rewrite Eq in Sz; done|].
    destruct l as [l cells]. destruct cells as [|cells0 cells]; [done|].
    rewrite heap_mapsto_cloc_fancy_vec_cons. iDestruct "↦" as "[↦1 ↦2]".
    rewrite -heap_complete_mapsto_fancy_singleton.
    iMod (mapsto_vec_untether_singleton _ _ ⊤ ∅ with "↦1")
      as (v₀ l₀ c₀) "[%Hl [↦1 _]]". inversion Hl. subst l₀ c₀.
    iModIntro. iFrame "W". wp_bind (_ <- _)%E.
    iApply (twp_write_na_guarded _ _ _ _ _ _ _ Hx with "[H ↦1]").
    { iDestruct (guard_rhs_iff (heap_mapsto_cloc_emp_cons l cells0 cells)
        with "Hguards") as "#Hg0".
      iDestruct (guard_rhs_sep_l with "Hg0") as "#Hg". iFrame "Hg H ↦1". }
    iIntros "[↦1 H]". wp_seq. wp_seq. iIntros "W".
    iMod (Rslv _ _ ⊤ with "LFT PROPH UNIQ E t2 tyb_ghos W")
      as "(W & #Obs' & t2)"; [solve_ndisj|].
    iMod (mapsto_vec_untether _ _ ⊤ ∅ with "↦2")
      as (vlc) "[↦2 [%Hlen2 _]]".
    iMod ("Toty'" $! (pinj i (f ~~$ₛ ()), vlc) d'
      with "[↦1 ↦2] H W") as "(W & %z & tok1 & %Hz & ty')".
    { iExists (FVal #i :: fmap FVal vlc).
      rewrite heap_mapsto_cloc_fancy_vec_cons /ty_own xsum_gho_pinj.
      iFrame "↦1 ↦2". iSplitL.
      { iAssert (ty_own () () d' (S d') tid []) as "Hu";
          [by rewrite unit_ty_own|]. iDestruct "Hu" as "[Hu _]".
        iDestruct ("Sgho" $! () d' (S d') tid with "Hu") as "[$ _]". }
      iPureIntro. rewrite /ty_phys /xsum_ty /= to_xsum_pinj -Sphys /=.
      apply pad_length'. rewrite /= length_fmap Hlen2.
      rewrite Eq in Sz. simpl in Sz. simpl. lia. }
    iDestruct (Ltok_split_2 with "tok1 t2") as "tok".
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    iExists -[z]. iFrame "L I". iSplitR "Obs".
    - rewrite right_id tctx_hasty_val'; [|done].
      iExists (S d'). iDestruct "ty'" as "[gho phys]". iFrame.
      iDestruct (ty_gho_depth_mono with "gho") as "[$ _]"; [lia|lia].
    - iCombine "Obs Obs'" as "Obs2".
      iApply (proph_obs_impl with "Obs2")=>/= ?[Ha Imp].
      generalize Hz. generalize z. apply Imp. apply Ha.
  Qed.

  Lemma type_sum_unit {𝔄 𝔄' 𝔅 𝔅l ℭl 𝔇l 𝔈} (tyl: typel 𝔅l) (i: fin _) (k: Z)
      (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄') (T: tctx ℭl) (T': tctx 𝔇l)
      f trx tr p gt st e Φ E L I (C: cctx 𝔈) :
    Closed [] e → k = i → tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    subtype E L () (tyl +!! i) f →
    typed_body E L I C (p ◁ ty' +:: T') e tr -∗
    typed_body E L I C T (p <-{Σ k} ();; e) (trx ∘
      (λ post '(a -:: dl), λ mask π, ∀ pad,
        Φ (gt a) π (∀ z, st a (pinj i (f ~~$ₛ tt), pad) z →
          tr post (z -:: dl) mask π)))%type.
  Proof.
    iIntros (?->????) "e". iApply typed_body_tctx_incl; [done|].
    iApply type_seq; [by eapply type_sum_unit_instr|by apply tctx_incl_refl|
      |done].
    by move=> ?[??]/=.
  Qed.

  (** The original splits a seven-way [£] budget between the write guard,
    [resolve], [wp_memcpy_guarded] (which itself wants [£(6*d)]), the laters
    of the write guard it reopens and the closing [typed_write] step.
    Later-free, none of it is needed. *)
  Lemma type_sum_memcpy_instr {𝔄 𝔄' 𝔅 𝔅' ℭ ℭl} (tyl: typel ℭl) (i: fin _)
      (tyw: type 𝔄) (tyw': type 𝔄') (tyr: type 𝔅) (tyr': type 𝔅')
      (tyb: type ℭ) p q gtw stw gtr str Φ E L I :
    typed_write E L tyw tyb tyw' (Σ! tyl) gtw stw → resolve' E L tyb Φ →
    typed_read E L tyr (tyl +!! i) tyr' gtr str →
    typed_instr E L I +[p ◁ tyw; q ◁ tyr]
      (p <-{(tyl +!! i).(ty_size),Σ i} !q) (λ _, +[p ◁ tyw'; q ◁ tyr'])
      (λ post '-[a; b], λ mask π, ∀ pad,
        Φ (gtw a) π (∀ zw zr,
          stw a (pinj i (gtr b), pad) zw → str b zr →
          post -[zw; zr] mask π)).
  Proof.
    iIntros ([Eq Wrt] Rslv Rd ???? (x & y &[]))
      "/= #LFT #PROPH #UNIQ #E L I (p & q &_) Obs".
    iDestruct (closed_hasty with "p") as %Cp.
    iDestruct (closed_hasty with "q") as %Cq.
    iApply twpw_fupdw_nonval; [done|].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]".
    iDestruct (Ltok_split_1 with "tok") as "[t1 tok2]".
    iDestruct (Ltok_split_1 with "tok2") as "[t2 t3]". iModIntro. iFrame "W".
    wp_bind p. iApply (twp_hasty with "p"). iIntros (v d Heq) "tyw".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Wrt with "LFT UNIQ E t1 tyw W") as
      "(W & %l & %d' & %Hw & %Heqv & -> & (%vl & ↦ & Own) & Hw' & #Hwpt &
        Totyw)".
    inversion Heqv. subst v.
    iDestruct "Own" as "[tyb_gho %tyb_phys]".
    assert (length vl = ty_size tyb) as Sz.
    { rewrite <- tyb_phys. apply ty_size_eq. }
    destruct vl as [|v vl]; [rewrite Eq in Sz; done|].
    destruct l as [l cells]. destruct cells as [|cells0 cells]; [done|].
    rewrite heap_mapsto_cloc_fancy_vec_cons. iDestruct "↦" as "[↦1 ↦2]".
    rewrite -heap_complete_mapsto_fancy_singleton.
    iMod (mapsto_vec_untether_singleton _ _ ⊤ ∅ with "↦1")
      as (v₀ l₀ c₀) "[%Hl [↦1 _]]". inversion Hl. subst l₀ c₀.
    iDestruct (guard_rhs_iff (heap_mapsto_cloc_emp_cons l cells0 cells)
      with "Hwpt") as "#Hg0".
    iDestruct (guard_rhs_sep_l with "Hg0") as "#Hgdisc".
    iDestruct (guard_rhs_sep_r with "Hg0") as "#Hgrest".
    iModIntro. iFrame "W". wp_bind (_ <- _)%E.
    iApply (twp_write_na_guarded _ _ _ _ _ _ _ Hw with "[Hw' ↦1]").
    { iFrame "Hgdisc Hw' ↦1". }
    iIntros "[↦1 Hw']". wp_seq.
    wp_bind p. iApply twp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    wp_op. wp_bind q. iApply (twp_hasty with "q"). iIntros (vb db ?) "tyr".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Rd with "LFT E t2 tyr W") as
      "(W & %l0 & %vlbc & %vlb & %Hr & %Heqv2 & %Hleneq & Hr' & #Hrpt' &
        Retether & _ & Own' & Totyr')".
    inversion Heqv2. subst vb.
    iDestruct "Own'" as "[tyb'_gho %tyb'_phys]".
    assert (length vlb = ty_size (tyl +!! i)) as Sz'.
    { rewrite <- tyb'_phys. apply ty_size_eq. }
    assert (length vlb ≤ length vl) as HlenLe.
    { rewrite Eq in Sz. rewrite Sz'.
      have h := max_hlist_with_ge (λ X : syn_type, ty_size) tyl i.
      have Hlia : ∀ a b c, S a = S b → c ≤ b → c ≤ a by lia.
      apply (Hlia _ _ _ Sz h). }
    have Hmin : length vlb `min` length vl = length vlb by lia.
    iMod (Rslv _ _ ⊤ with "LFT PROPH UNIQ E t3 tyb_gho W")
      as "(W & #Obs' & t3)"; [solve_ndisj|].
    rewrite -{1}(take_drop (length vlb) vl) heap_cloc_mapsto_fancy_vec_app
      length_take Hmin.
    iDestruct "↦2" as "[↦2 ↦3]".
    iMod (mapsto_vec_untether _ _ ⊤ ∅ with "↦2")
      as (vl2c) "[↦2 [%Hvlen2 _]]".
    iMod (mapsto_vec_untether _ _ ⊤ ∅ with "↦3")
      as (vl3c) "[↦3 [%Hvlen3 _]]".
    iDestruct (guard_rhs_iff
      (heap_cloc_mapsto_emp_vec_app (l +ₗ 1, cells) (length vlb))
      with "Hgrest") as "#Hg1".
    iDestruct (guard_rhs_sep_l with "Hg1") as "#Hgmid".
    iModIntro. iFrame "W".
    iApply (twp_memcpy_guarded _ (cloc_take (l +ₗ 1, cells) (length vlb)) l0
      vl2c vlbc Hw Hr with "[↦2 Hw' Hr']").
    { rewrite Hvlen2 length_take /=. lia. }
    { congruence. }
    { iFrame "↦2 Hw' Hr'". iFrame "Hgmid Hrpt'". }
    iIntros "(↦2 & Hw' & Hr') W".
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "Hgmid Hw' Wg") as "[prefix back]".
    iMod (fupd_mask_mono ∅ ⊤ with "(Retether [$prefix $↦2])")
      as "[prefix ↦2]"; [set_solver|].
    iDestruct ("back" with "prefix") as "[Wg Hw']".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iMod ("Totyw" $! (pinj i (gtr y), vl3c) db
      with "[↦1 ↦2 ↦3 tyb'_gho] Hw' W") as "(W & %z & tok1 & %Hz & tyw')".
    { iExists (FVal #i :: vlb ++ fmap FVal vl3c).
      rewrite heap_mapsto_cloc_fancy_vec_cons
        heap_cloc_mapsto_fancy_vec_app /ty_own xsum_gho_pinj.
      rewrite -heap_complete_mapsto_fancy_fmap_eq.
      iFrame "↦1 ↦2 ↦3". iSplitL.
      { iDestruct (ty_gho_depth_mono with "tyb'_gho") as "[$ _]"; [lia|lia]. }
      iPureIntro. rewrite /ty_phys /xsum_ty /= to_xsum_pinj tyb'_phys.
      apply pad_length'. rewrite /= length_app length_fmap Hvlen3 length_drop.
      rewrite Eq in Sz. simpl in Sz. lia. }
    iMod ("Totyr'" with "Hr' W") as "(W & %zr & %Hzr & tok3 & tyr')".
    iDestruct (Ltok_split_2 with "tok3 t3") as "tok2".
    iDestruct (Ltok_split_2 with "tok1 tok2") as "tok".
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    iExists -[z; zr]. iFrame "L I". iSplit; [rewrite right_id|].
    - iSplitL "tyw'"; (rewrite tctx_hasty_val'; [|done]).
      + iExists (S d' `max` S db). iDestruct "tyw'" as "[gho phys]". iFrame.
        iDestruct (ty_gho_depth_mono with "gho") as "[$ _]"; [lia|lia].
      + iExists db. iFrame "tyr'".
    - iCombine "Obs Obs'" as "Obs2".
      iApply (proph_obs_impl with "Obs2")=>/= ?[Ha Imp].
      generalize Hzr. generalize Hz. generalize zr. generalize z. apply Imp.
      apply Ha.
  Qed.

  Lemma type_sum_memcpy {𝔄 𝔄' 𝔅 𝔅' ℭ ℭl 𝔇l 𝔈l 𝔉} (tyl: typel ℭl) (i: fin _)
      (tyw: type 𝔄) (tyr: type 𝔅) (tyw': type 𝔄') (tyr': type 𝔅')
      (tyb: type ℭ) (k n: Z) (T: tctx 𝔇l) (T': tctx 𝔈l) p q gtw stw gtr str
      trx tr e Φ E L I (C: cctx 𝔉) :
    Closed [] e → k = i → tctx_extract_ctx E L +[p ◁ tyw; q ◁ tyr] T T' trx →
    typed_write E L tyw tyb tyw' (Σ! tyl) gtw stw → resolve' E L tyb Φ →
    n = (tyl +!! i).(ty_size) → typed_read E L tyr (tyl +!! i) tyr' gtr str →
    typed_body E L I C (p ◁ tyw' +:: q ◁ tyr' +:: T') e tr -∗
    typed_body E L I C T (p <-{n,Σ k} !q;; e) (trx ∘
      (λ post '(a -:: b -:: el), λ mask π, ∀ pad,
        Φ (gtw a) π (∀ zw zr,
          stw a (pinj i (gtr b), pad) zw → str b zr →
          tr post (zw -:: zr -:: el) mask π)))%type.
  Proof.
    iIntros (?->???->?) "e". iApply typed_body_tctx_incl; [done|].
    iApply type_seq; [by eapply type_sum_memcpy_instr|by apply tctx_incl_refl|
      |done].
    by move=> ?[?[??]]/=.
  Qed.

  Lemma ty_outlives_E_elctx_sat_sum {𝔄l} E L (tyl: typel 𝔄l) κ :
    elctx_sat E L (tyl_outlives_E tyl κ) →
    elctx_sat E L (ty_outlives_E (Σ! tyl) κ).
  Proof.
    move=> Sat. eapply eq_ind; [done|]. clear Sat.
    rewrite /tyl_outlives_E /ty_outlives_E /=.
    induction tyl as [|???? IH]=>//=. by rewrite IH fmap_app.
  Qed.
End type_sum.

Global Hint Resolve ty_outlives_E_elctx_sat_sum : lrust_typing.
