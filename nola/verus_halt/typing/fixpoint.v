(** * Type-level fixpoints

  Ported from VerusBelt ([typing/fixpoint.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  The construction itself is generic in [TypeContractive T] and carries no
  laters of its own, so it ports unchanged.

  What changes is what can be *fed* to it.  VerusBelt's contractive type
  formers are contractive because of a later: [own_ptr] puts a [▷] in front of
  the inner ghost state, and [&shr{κ}] gets one from a guard at index ≥ 1
  ([guards_contractive_right_if_n_ge_1]).  Later-free, [typed_read] hands the
  borrowed contents over without a later, so neither type can hide one, and
  both are only [TypeNonExpansive] (see [typing/own.v], [typing/shr_bor.v]).
  So this file is kept, and is sound, but the development currently offers no
  non-trivial [TypeContractive] instance to apply it to.  Recovering recursive
  types would mean making the type interpretation itself syntactic - Nola's
  [cif] with a productivity index - which is the same change that
  [typing/uniq_bor.v] needs. *)

From iris.proofmode Require Import proofmode.
From nola.verus_halt.typing Require Export lft_contexts type bool.
From nola.verus_halt.typing Require Import base_type.
From nola.verus_halt.typing Require Export ctx.
From nola.bi Require Import guard modw.
Import uPred GuardNotation ModwNotation WpwNotation.
Implicit Type 𝔄 𝔅: syn_type.

Module fix_defs.

(** Type-level fixpoints are the one place that needs the formula language to
  be a COFE: the recursive type is built as the limit [compl] of a chain of
  ghost assertions.  Nola's [cif] is *not* a COFE - [nola/util/cit.v]'s
  [cit] is complete as a [prost], and recursion over it goes through [profix]
  with [Productive], as [nola/examples/rust_halt/rec.v] does - so this
  assumption is local to this file rather than a field of [TypeFml], and
  moving the construction to [profix] is what will discharge it. *)
Section S.
  Context `{!typeG FML Σ, !Cofe (FML $oi Σ)} {𝔄} (T: type 𝔄 → type 𝔄)
    {HT: TypeContractive T}.

  Definition Tn n := Nat.iter (S n) T base.

  Lemma Tn_ty_lft_const n n' : ⊢ ty_lft (Tn n) ≡ₗ ty_lft (Tn n').
  Proof using HT.
    have Eq: ∀n, ⊢ ty_lft (Tn n) ≡ₗ ty_lft (Tn 0); last first.
    { iApply lft_equiv_trans; [|iApply lft_equiv_sym]; iApply Eq. }
    clear n n'=> n. case type_contractive_type_lft_morphism=> [> Hα ?|> Hα ?]; last first.
    { iApply lft_equiv_trans; [iApply Hα|]. iApply lft_equiv_sym. iApply Hα. }
    elim: n=> [|n IH]; [apply lft_equiv_refl|]. rewrite /Tn /=.
    iApply lft_equiv_trans; [iApply type_lft_morphism_lft_equiv_proper; iApply IH|].
    iApply lft_equiv_trans; [iApply Hα|]. iApply lft_equiv_trans.
    { iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply Hα]. }
    iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
    rewrite assoc. iApply lft_intersect_equiv_proper; [|iApply lft_equiv_refl].
    iApply lft_intersect_equiv_idemp.
  Qed.

  Lemma Tn_ty_E_const n n' :
    elctx_interp (Tn (S n)).(ty_E) ≡ elctx_interp (Tn (S n')).(ty_E).
  Proof using HT.
    have Eq: ∀n, elctx_interp (Tn (S n)).(ty_E) ≡ elctx_interp (Tn 1).(ty_E);
    [|by rewrite !Eq]. clear n n'=> n.
    case type_contractive_type_lft_morphism=> [> Hα HE|> ? HE]; last by rewrite !HE.
    elim: n; [done|]=> n IH.
    rewrite (HE (Tn (S n))) IH !HE !assoc -!persistent_sep_dup -!assoc.
    iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
    iApply (big_sepL_impl with "H"). iIntros "!> * _". iIntros "#?".
    have Hc : ⊢ dincl (ty_lft (Tn 0)) (ty_lft (Tn (S n)))
      by iDestruct (Tn_ty_lft_const (S n) 0) as "[_ $]".
    iApply dincl_trans; [done|]. iApply Hc.
  Qed.
  
  Lemma Tn_cauchy n i : (n ≤ i)%nat →
    (∀x d g tid,
      ((Tn (2 + i)).(ty_ghox) x d g tid) ≡{n}≡ ((Tn (2 + n)).(ty_ghox) x d g tid)) ∧
    (∀x d g tid,
      (Tn (2 + i)).(ty_gho_persx) x d g tid ≡{n}≡ (Tn (2 + n)).(ty_gho_persx) x d g tid).
  Proof using HT.
    move: i. elim: n=> /=[|n IH]=> i ?.
    - split.
      + apply HT=>//.
        * apply type_contractive_ty_size.
        * apply (Tn_ty_lft_const (S i) 1).
        * apply (Tn_ty_E_const i 0).
        * intros; apply dist_later_0.
        * intros; apply dist_later_0.
        * intros. do 2 (rewrite <- ty_phys_eq2). trivial.
      + apply HT=>//.
        * apply type_contractive_ty_size.
        * apply (Tn_ty_lft_const (S i) 1).
        * apply (Tn_ty_E_const i 0).
        * intros; apply dist_later_0.
        * intros; apply dist_later_0.
        * intros. do 2 (rewrite <- ty_phys_eq2). trivial.
    - case i as [|]; [lia|]. case (IH i) as [??]; [lia|].
      split.
      + intros. apply HT.
        * apply type_contractive_ty_size.
        * apply (Tn_ty_lft_const (2 + i) (2 + n)).
        * apply (Tn_ty_E_const (S i) (S n)).
        * intros. rewrite <- dist_later_S. apply H.
        * intros. rewrite <- dist_later_S. apply H0.
        * intros. do 2 (rewrite <- ty_phys_eq2). trivial.
      + intros. apply HT.
        * apply type_contractive_ty_size.
        * apply (Tn_ty_lft_const (2 + i) (2 + n)).
        * apply (Tn_ty_E_const (S i) (S n)).
        * intros. rewrite <- dist_later_S. apply H.
        * intros. rewrite <- dist_later_S. apply H0.
        * intros. do 2 (rewrite <- ty_phys_eq2). trivial.
  Qed.
  
  (*Lemma Tn_cauchy n i : (n ≤ i)%nat →
    (∀x d g tid, dist_later n
      ((Tn (2 + i)).(ty_ghox) x d g tid) ((Tn (2 + n)).(ty_ghox) x d g tid)) ∧
    (∀x d g tid,
      (Tn (2 + i)).(ty_gho_persx) x d g tid ≡{n}≡ (Tn (2 + n)).(ty_gho_persx) x d g tid).
  Proof using HT.
    move: i. elim: n=> /=[|n IH]=> i ?.
    - split.
      + intros; apply dist_later_0.
      + apply HT=>//.
        * apply type_contractive_ty_size.
        * apply (Tn_ty_lft_const (S i) 1).
        * apply (Tn_ty_E_const i 0).
        * intros; apply dist_later_0.
        * intros; apply dist_later_0.
        * intros. do 2 (rewrite <- ty_phys_eq2). trivial.
    - case i as [|]; [lia|]. case (IH i) as [??]; [lia|].
      split.
      + intros. rewrite <- dist_later_S. apply HT.
        * apply type_contractive_ty_size.
        * apply (Tn_ty_lft_const (2 + i) (2 + n)).
        * apply (Tn_ty_E_const (S i) (S n)).
        * apply H.
        * intros. apply dist_dist_later. apply H0.
        * intros. do 2 (rewrite <- ty_phys_eq2). trivial.
      + intros. apply HT.
        * apply type_contractive_ty_size.
        * apply (Tn_ty_lft_const (2 + i) (2 + n)).
        * apply (Tn_ty_E_const (S i) (S n)).
        * intros. rewrite dist_later_S.
    
        apply (Tn_ty_lft_const (S i) 1)|apply (Tn_ty_E_const i 0)].
    - split; [done|]. apply HT=>//; [apply type_contractive_ty_size|
        apply (Tn_ty_lft_const (S i) 1)|apply (Tn_ty_E_const i 0)].
    - case i as [|]; [lia|]. case (IH i) as [??]; [lia|].
      split; (apply HT=>//; [apply type_contractive_ty_size|
        apply (Tn_ty_lft_const (2 + i) (2 + n))|apply (Tn_ty_E_const (S i) (S n))]).
  Qed.*)
  
  Program Definition gho_chain :=
    {| chain_car n := ((Tn (3 + n)).(ty_ghox), (Tn (3 + n)).(ty_gho_persx)) :
        prodO ((~~𝔄) -d> nat -d> nat -d> thread_id -d> FML $oi Σ)
          ((~~𝔄) -d> nat -d> nat -d> thread_id -d> FML $oi Σ) |}.
  Next Obligation.
    move=> n i Hni. simpl in Hni. split=>/=.
    - move=> >. apply (dist_le (S n)); last by lia. apply (Tn_cauchy (S _)). lia.
    - move=> >. apply dist_S, Tn_cauchy. lia.
  Qed.

  Program Definition Tn' n : type 𝔄 := {|
    ty_size := (Tn 0).(ty_size);  ty_lev := (Tn 0).(ty_lev);
    ty_lfts := (Tn 0).(ty_lfts);  ty_E := (Tn 1).(ty_E);
    ty_ghox := (Tn n).(ty_ghox);  ty_gho_persx := (Tn n).(ty_gho_persx);
    ty_phys := (Tn 0).(ty_phys);
  |}.
  Next Obligation.
    move=> *. rewrite ty_size_eq /Tn. (*iIntros "->!%/=". apply type_contractive_ty_size.*)
    trivial.
  Qed.
  Next Obligation. intros. apply ty_size_eq2. Qed.
  Next Obligation. intros. apply ty_phys_eq2. Qed.
  Next Obligation. move=> n sem H. apply (ty_gho_depth_mono_at (Tn n) sem H). Qed.
  Next Obligation.
    move=> n sem H. apply (ty_gho_pers_depth_mono_at (Tn n) sem H).
  Qed.
  Next Obligation.
    move=> n *. iIntros "#LFT #?". iApply (ty_guard_proph with "LFT").
    have Hc : ⊢ dincl (ty_lft (Tn 0)) (ty_lft (Tn n))
      by iDestruct (Tn_ty_lft_const n 0) as "[_ $]".
    have Hc' : ⊢ llft_incl (ty_lft (Tn 0)) (ty_lft (Tn n)).
    { iApply dincl_incl. iApply Hc. }
    iApply llftl_incl_trans; [done|]. iApply Hc'.
  Qed.
  Next Obligation. move=> n sem H. apply (ty_gho_pers_pers_at (Tn n) sem H). Qed.
  Next Obligation. move=> >. apply ty_gho_pers_impl. Qed.

  Program Definition fix_ty: type 𝔄 := {|
    ty_size := (Tn 0).(ty_size);  ty_lev := (Tn 0).(ty_lev);
    ty_lfts := (Tn 0).(ty_lfts);  ty_E := (Tn 1).(ty_E);
    ty_ghox := (compl gho_chain).1;  ty_gho_persx := (compl gho_chain).2;
    ty_phys := (Tn 0).(ty_phys);
  |}.
  Next Obligation. intros. apply ty_size_eq. Qed.
  Next Obligation. intros. apply ty_size_eq2. Qed.
  Next Obligation. intros. apply ty_phys_eq2. Qed.
  Next Obligation.
    move=> sem H *. have ? := alt_sem_ne H.
    apply @limit_preserving_compl;
      [|move=> ?; by apply (ty_gho_depth_mono_at (Tn' _) sem H)].
    apply limit_preserving_entails=> ??? Eq; [done|].
    repeat (apply Eq || f_equiv).
  Qed.
  Next Obligation.
    move=> sem H *. have ? := alt_sem_ne H.
    apply @limit_preserving_compl;
      [|move=> ?; by apply (ty_gho_pers_depth_mono_at (Tn' _) sem H)].
    apply limit_preserving_entails=> ??? Eq; [done|].
    repeat (apply Eq || f_equiv).
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving_compl; [|move=> ?; by apply (ty_guard_proph _ (Tn' _))].
    apply limit_preserving_entails; [done|]=> ??? Eq.
    repeat (apply Eq || f_equiv).
  Qed.
  Next Obligation.
    move=> sem H *. have ? := alt_sem_ne H.
    apply @limit_preserving_compl;
      [|move=> ?; by apply (ty_gho_pers_pers_at (Tn' _) sem H)].
    apply limit_preserving_Persistent=> ??? Eq.
    repeat (apply Eq || f_equiv).
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving_compl; [|move=> ?; by apply ty_gho_pers_impl].
    apply limit_preserving_entails; [done|]=> ??? Eq.
    repeat (apply Eq || f_equiv).
  Qed.

  Lemma fix_ty_Tn'_dist n : fix_ty ≡{n}≡ Tn' (3 + n).
  Proof. split=>// *; apply conv_compl. Qed.
End S.
End fix_defs.

Import fix_defs.
Global Notation fix_ty := fix_ty.

Section fix_ty.
  Context `{!typeG FML Σ, !Cofe (FML $oi Σ)}.

  Lemma fix_unfold_fold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    eqtype E L (fix_ty T) (T (fix_ty T)) idₛ idₛ.
  Proof.
    have EqOwn: ∀n vπ d tid vl, (T $ Tn T (3 + n)).(ty_ghox) vπ d tid vl ≡
      (T $ Tn' T (3 + n)).(ty_ghox) vπ d tid vl.
    { move=> n *. apply equiv_dist=> ?. apply HT=>//; [apply HT|
        apply (Tn_ty_lft_const T (3 + n) 0)|apply (Tn_ty_E_const T (2 + n) 0)|].
      intros. by do 2 (rewrite <- ty_phys_eq2).
    }
    have EqShr: ∀n vπ d tid l, (T $ Tn T (3 + n)).(ty_gho_persx) vπ d tid l ≡
      (T $ Tn' T (3 + n)).(ty_gho_persx) vπ d tid l.
    { move=> n *. apply equiv_dist=> n'. apply HT=>//; [apply HT|
        apply (Tn_ty_lft_const T (3 + n) 0)|apply (Tn_ty_E_const T (2 + n) 0)|].
      intros. by do 2 (rewrite <- ty_phys_eq2).
    }
    have EqOwn': ∀vπ d tid vl, (fix_ty T).(ty_ghox) vπ d tid vl ≡
      (T (fix_ty T)).(ty_ghox) vπ d tid vl.
    { move=> *. apply equiv_dist=> n. etrans; [apply dist_S, conv_compl|].
      rewrite/= (EqOwn n). symmetry. apply HT=>// *; [apply lft_equiv_refl| |].
      - move: n=> [|n]; [apply dist_later_0|].
        case (fix_ty_Tn'_dist T (S n))=> [_ _ _ _ Eq _]. intros. apply dist_dist_later, Eq.
      - case (fix_ty_Tn'_dist T n)=> [_ _ _ _ _ Eq]. intros. apply dist_dist_later, Eq. }
    have EqShr': ∀vπ d tid l, (fix_ty T).(ty_gho_persx) vπ d tid l ≡
      (T (fix_ty T)).(ty_gho_persx) vπ d tid l.
    { move=> *. apply equiv_dist=> n. etrans; [apply dist_S, conv_compl|].
      rewrite/= (EqShr n). symmetry. apply HT=>// *; [apply lft_equiv_refl| |].
      - move: n=> [|n]; [apply dist_later_0|].
        case (fix_ty_Tn'_dist T (S n))=> [_ _ _ _ Eq _]. intros. apply dist_dist_later, Eq.
      - case (fix_ty_Tn'_dist T n)=> [_ _ _ _ _ Eq]. intros. apply dist_dist_later, Eq. }
    apply eqtype_id_unfold. iIntros "*_!>_". iSplit; [iPureIntro; by apply HT|].
    iSplit.
    { case type_contractive_type_lft_morphism=> [α βs E' Hα HE'|α E' Hα HE'].
      + iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
        iApply lft_equiv_trans; [iApply Hα|].
        iApply lft_equiv_trans; [|iApply lft_intersect_equiv_proper;
          [iApply lft_equiv_refl|iApply lft_equiv_sym; iApply Hα]].
        rewrite assoc. iApply lft_intersect_equiv_proper; [|iApply lft_equiv_refl].
        iApply lft_equiv_sym. iApply lft_intersect_equiv_idemp.
      + iApply lft_equiv_trans; [iApply Hα|iApply lft_equiv_sym; iApply Hα].
    }
    iSplit.
    { iIntros "!>" (sem Hsem x d g tid).
      have ? := alt_sem_ne Hsem.
      have ? : Proper ((≡) ==> (≡)) sem := ne_proper _.
      rewrite (EqOwn' x d g tid). by iApply bi.equiv_iff. }
    iSplit.
    { iIntros "!>" (sem Hsem x d g tid).
      have ? := alt_sem_ne Hsem.
      have ? : Proper ((≡) ==> (≡)) sem := ne_proper _.
      rewrite (EqShr' x d g tid). by iApply bi.equiv_iff. }
    { iPureIntro. intros. do 2 (rewrite <- ty_phys_eq2). trivial. }
  Qed.
  Lemma fix_fold_unfold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    eqtype E L (T (fix_ty T)) (fix_ty T) idₛ idₛ.
  Proof. apply eqtype_symm, fix_unfold_fold. Qed.
  Lemma fix_unfold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    subtype E L (fix_ty T) (T (fix_ty T)) idₛ.
  Proof. eapply proj1, fix_unfold_fold. Qed.
  Lemma fix_fold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    subtype E L (T (fix_ty T)) (fix_ty T) idₛ.
  Proof. eapply proj2, fix_unfold_fold. Qed.

  Lemma fix_ty_ne {𝔄} (T T': type 𝔄 → type 𝔄)
      `{!TypeContractive T, !NonExpansive T, !TypeContractive T'} n :
    (∀ty, T ty ≡{n}≡ T' ty) → fix_ty T ≡{n}≡ fix_ty T'.
  Proof.
    move=> Eq.
    have Eq': compl (gho_chain T) ≡{n}≡ compl (gho_chain T').
    { have Eq'': Tn T (3 + n) ≡{n}≡ Tn T' (3 + n).
      { rewrite /Tn. elim (S (3 + n)); [done|]=> ? IH. by rewrite !Nat.iter_succ IH Eq. }
      etrans; [apply conv_compl|]. etrans; [|symmetry; apply conv_compl].
      split; repeat move=> ? /=; apply Eq''. }
    split=>/=; try apply Eq; try apply Eq'. by rewrite /Tn /= (Eq base) Eq.
  Qed.

  Lemma fix_type_ne {𝔄 𝔅} (T : type 𝔄 → type 𝔅 → type 𝔅)
      `{!(∀ty, TypeContractive (T ty))} :
    (∀`{!TypeNonExpansive U}, TypeNonExpansive (λ ty, T ty (U ty))) →
      TypeNonExpansive (λ ty, fix_ty (T ty)).
  Proof.
    move=> HT. have Hne: ∀n, TypeNonExpansive (λ ty, Tn (T ty) n).
    { elim=> [|? IH]; [apply HT, _|apply HT, IH]. }
    split=>/=.
    - case (type_ne_type_lft_morphism (T := λ ty, Tn (T ty) 1))=>
      [α βs E Hα HE|α E Hα HE].
      + eapply (type_lft_morphism_add _ α βs E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
      + eapply (type_lft_morphism_const _ α E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
    - apply HT, _.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
    - intros. do 2 (rewrite <- ty_phys_eq2). trivial.
  Qed.

  Lemma fix_type_contractive {𝔄 𝔅} (T : type 𝔄 → type 𝔅 → type 𝔅)
      `{!(∀ty, TypeContractive (T ty))} :
    (∀`{!TypeContractive U}, TypeContractive (λ ty, T ty (U ty))) →
      TypeContractive (λ ty, fix_ty (T ty)).
  Proof.
    move=> HT. have Hne: ∀n, TypeContractive (λ ty, Tn (T ty) n).
    { elim=> [|? IH]; [apply HT, _|apply HT, IH]. }
    split=>/=.
    - case (type_ne_type_lft_morphism (T := λ ty, Tn (T ty) 1))=>
      [α βs E Hα HE|α E Hα HE].
      + eapply (type_lft_morphism_add _ α βs E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
      + eapply (type_lft_morphism_const _ α E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
    - apply HT, _.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
    - intros. do 2 (rewrite <- ty_phys_eq2). trivial.
  Qed.
End fix_ty.

Section fix_ty.
  Context `{!typeG FML Σ, !Cofe (FML $oi Σ)} {𝔄} (T: type 𝔄 → type 𝔄)
    {HT: TypeContractive T}.

  Global Instance fix_copy :
    (∀`(!Copy ty), Copy (T ty)) → Copy (fix_ty T).
  Proof.
    move=> ?. have ?: ∀n, Copy (Tn T n) by elim; apply _.
    split; rewrite /ty_gho /fix_ty /=.
    - move=> >. eapply @limit_preserving_compl; [|apply _].
      apply limit_preserving_Persistent=> ??? Eq.
    repeat (apply Eq || f_equiv).
    - move=> >. 
      eapply @limit_preserving_compl.
      + apply limit_preserving_entails=> ??? Eq.
        * f_equiv. apply Eq.
        * done.
      + intros. iIntros "G". iDestruct (copy_concrete with "G") as "%Hconc".
        iPureIntro. rewrite <- ty_phys_eq2 in Hconc. rewrite <- ty_phys_eq2. done.
  Qed.

  Global Instance fix_send :
    (∀`(!Send ty), Send (T ty)) → Send (fix_ty T).
  Proof.
    move=> ?. have ?: ∀n, Send (Tn T n) by elim; apply _. split; rewrite /fix_ty=> > /=.
    { do 2 (rewrite <- ty_phys_eq2). apply syn_abstract_phys_eq. }
    rewrite /ty_gho /=. eapply @limit_preserving_compl.
    + apply limit_preserving_entails=> ??? Eq; [done|].
      repeat (apply Eq || f_equiv).
    + intros. apply send_change_tid; trivial.
  Qed.

  Global Instance fix_sync :
    (∀`(!Sync ty), Sync (T ty)) → Sync (fix_ty T).
  Proof.
    move=> ?. have ?: ∀n, Sync (Tn T n) by elim; apply _.
    rewrite /fix_ty=> tid tid' x d g.
    cbn [ty_phys ty_ghox ty_gho_persx].
    unshelve eapply (@limit_preserving_compl _ _ _
      (λ p : prodO (~~𝔄 -d> nat -d> nat -d> thread_id -d> FML $oi Σ)
                   (~~𝔄 -d> nat -d> nat -d> thread_id -d> FML $oi Σ),
        ty_phys (Tn T 0) x tid = ty_phys (Tn T 0) x tid' ∧
        p.1 x d g tid ≡ p.1 x d g tid' ∧
        p.2 x d g tid ≡ p.2 x d g tid')
      _ (gho_chain T)).
      + apply limit_preserving_and; [|apply limit_preserving_and].
        * do 2 (rewrite <- ty_phys_eq2). apply limit_preserving_const.
        * apply (limit_preserving_equiv
            (A:=prodO (~~𝔄 -d> nat -d> nat -d> thread_id -d> FML $oi Σ)
                      (~~𝔄 -d> nat -d> nat -d> thread_id -d> FML $oi Σ))
            (λ p, p.1 x d g tid) (λ p, p.1 x d g tid'))
            => ??? [Eq _]; apply Eq.
        * apply (limit_preserving_equiv
            (A:=prodO (~~𝔄 -d> nat -d> nat -d> thread_id -d> FML $oi Σ)
                      (~~𝔄 -d> nat -d> nat -d> thread_id -d> FML $oi Σ))
            (λ p, p.2 x d g tid) (λ p, p.2 x d g tid'))
            => ??? [_ Eq]; apply Eq.
      + intros. split.
        * do 2 (rewrite <- ty_phys_eq2). done.
        * apply sync_change_tid.
  Qed.

  Lemma fix_resolve E L Φ :
    (∀ty, resolve E L ty Φ → resolve E L (T ty) Φ) → resolve E L (fix_ty T) Φ.
  Proof.
    move=> Loop. have Rslv: ∀n, resolve E L (Tn T n) Φ.
    { elim=> [|? H]; apply Loop; [apply base_resolve|apply H]. }
    move=> > ?. unfold ty_gho, fix_ty, ty_ghox.
    eapply @limit_preserving_compl; [|move=> ?; by apply Rslv].
    apply limit_preserving_entails; [done|]=> ??? Eq.
    repeat (apply Eq || f_equiv).
  Qed.
End fix_ty.

Section fix_subtyping.
  Context `{!typeG FML Σ, !Cofe (FML $oi Σ)}.

  Local Lemma wand_forall P (Φ: nat → iProp Σ) : (∀n, P -∗ Φ n) ⊢ (P -∗ ∀n, Φ n).
  Proof. iIntros "To P %". iApply ("To" with "P"). Qed.
  Local Lemma entails_dist_True (P Q: iProp Σ) : (P ⊢ Q) ↔ ∀n, (P → Q)%I ≡{n}≡ True%I.
  Proof. by rewrite entails_eq_True equiv_dist. Qed.

  Lemma fix_subtype {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅)
    (T : type 𝔄 → type 𝔄) `{!TypeContractive T}
    (T' : type 𝔅 → type 𝔅) `{!TypeContractive T'} E L :
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    (size_of 𝔄 = size_of 𝔅) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) f x)) →
    (∀ty ty', subtype E L ty ty' f → subtype E L (T ty) (T' ty') f) →
    subtype E L (fix_ty T) (fix_ty T') f.
  Proof.
    move=> Heq1 Heq2 Heq3 Loop.
    have Incl: llctx_interp L ⊢ □ (elctx_interp E -∗
      ∀n, type_incl (Tn T n) (Tn T' n) f).
    { apply wand_entails.
      rewrite intuitionistically_into_persistently -wand_forall persistently_forall.
      rewrite -wand_forall.
      apply forall_intro=> n. rewrite -intuitionistically_into_persistently.
      apply Loop. elim n=> [|??]; [apply base_subtype; done|by apply Loop].
    }
    unfold subtype.
    rewrite Incl /type_incl /ty_gho /ty_gho_pers -!persistent_and_sep /=.
    apply entails_wand. do 2 f_equiv.
    (* FIXME : change the definition of limit_preserving so that it
       applies even if the limti is not computed with compl. *)
    apply and_intro; [|apply and_intro; [|apply and_intro; [|apply and_intro]]].
    - iIntros "H". iDestruct ("H" $! 0%nat) as "($&_)".
    - iIntros "H". iDestruct ("H" $! 0%nat) as "(_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&_&$&_)".
    - iIntros. iPureIntro. intros. do 2 (rewrite <- ty_phys_eq2). done.
  Qed.

  Lemma fix_eqtype_subtype {𝔄 𝔅} f g
    (T : type 𝔄 → type 𝔄) `{!TypeContractive T}
    (T' : type 𝔅 → type 𝔅) `{!TypeContractive T'} E L :
    (∀ty ty', eqtype E L ty ty' f g → eqtype E L (T ty) (T' ty') f g) →
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    (∀ x, ξl x = ξl ((~~!ₛ) g x)) →
    (size_of 𝔄 = size_of 𝔅) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) f x)) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) g x)) →
    subtype E L (fix_ty T) (fix_ty T') f.
  Proof.
    move=> Loop Eq1 Eq2 Eq3 Eq4 Eq5.
    have Incl: llctx_interp L ⊢ □ (elctx_interp E -∗
      ∀n, type_incl (Tn T n) (Tn T' n) f).
    { apply wand_entails.
      rewrite intuitionistically_into_persistently -wand_forall persistently_forall.
      rewrite -wand_forall.
      apply forall_intro=> n. rewrite -intuitionistically_into_persistently.
      apply Loop. elim n=> [|??]; [apply base_eqtype|by apply Loop]; done. }
    unfold subtype.
    rewrite Incl /type_incl /ty_gho /ty_gho_pers -!persistent_and_sep /=.
    apply entails_wand. do 2 f_equiv.
    apply and_intro; [|apply and_intro; [|apply and_intro; [|apply and_intro]]].
    - iIntros "H". iDestruct ("H" $! 0%nat) as "($&_)".
    - iIntros "H". iDestruct ("H" $! 0%nat) as "(_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&_&$&_)".
    - iIntros. iPureIntro. intros. do 2 (rewrite <- ty_phys_eq2). done.
  Qed.

  Lemma fix_eqtype {𝔄 𝔅} f g
    (T: type 𝔄 → type 𝔄) `{!TypeContractive T}
    (T': type 𝔅 → type 𝔅) `{!TypeContractive T'} E L :
    (∀ty ty', eqtype E L ty ty' f g → eqtype E L (T ty) (T' ty') f g) →
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    (∀ x, ξl x = ξl ((~~!ₛ) g x)) →
    (size_of 𝔄 = size_of 𝔅) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) f x)) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) g x)) →
    eqtype E L (fix_ty T) (fix_ty T') f g.
  Proof.
    move=> Loop.
    have ?: ∀ty' ty, eqtype E L ty' ty g f → eqtype E L (T' ty') (T ty) g f.
    { move=> ??[??]. split; apply Loop; by split. }
    split; by eapply fix_eqtype_subtype.
  Qed.

  Lemma fix_subtype_l {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) ty T `{!TypeContractive T} E L :
    subtype E L ty (T (fix_ty T)) f → subtype E L ty (fix_ty T) f.
  Proof.
    move=> ?. eapply (subtype_trans _ _ _ _ idₛ); [done|]. apply fix_fold.
  Qed.
  Lemma fix_subtype_r {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) ty T `{!TypeContractive T} E L :
    subtype E L (T (fix_ty T)) ty f → subtype E L (fix_ty T) ty f.
  Proof.
    move=> ?. eapply (subtype_trans _ _ _ idₛ); [|done]. apply fix_unfold.
  Qed.
  Lemma fix_eqtype_l {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) g ty T `{!TypeContractive T} E L :
    eqtype E L ty (T (fix_ty T)) f g → eqtype E L ty (fix_ty T) f g.
  Proof.
    move=> ?. eapply (eqtype_trans _ _ _ _ _ idₛ idₛ); [done|]. apply fix_fold_unfold.
  Qed.
  Lemma fix_eqtype_r {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) g ty T `{!TypeContractive T} E L :
    eqtype E L (T (fix_ty T)) ty f g → eqtype E L (fix_ty T) ty f g.
  Proof.
    move=> ?. eapply (eqtype_trans _ _ _ idₛ idₛ); [|done]. apply fix_unfold_fold.
  Qed.
End fix_subtyping.

Global Hint Resolve fix_subtype_l fix_subtype_r fix_eqtype_l fix_eqtype_r | 100
  : lrust_typing.
