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
End type_sum.
