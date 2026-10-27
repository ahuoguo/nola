(** * The stored owning pointer, as a type

  [typing/rec.v]'s [sown_tyd] is the owning pointer that can be the guarded
  former of a recursion: its pointee sits behind [ctx.v]'s [eown_fml] rather
  than in hand, which is what makes it [Productive], and [sown_tyd_take] is
  what makes that free - the pointee still moves out.

  This file packages it as a [type] and gives it the three rules
  [typing/own.v] gives [own_ptr], so a recursive type is read and written by
  [typed_read] and [typed_write] rather than by hand.  The proofs are
  [own.v]'s with one step in front: [sown_ptr_take] spends the two-state
  token and brings the pointee into hand, after which everything is the
  same.  Closing is [sown_ptr_alloc], which allocates a *fresh* token - the
  refinement type carries its name, so the new pointer's refinement differs
  from the old one's in that component and in no other.

  Why the refinement carries the name at all is [rec.v]'s business: the
  prophecy law is handed a guard at a universally quantified [R] and can
  only ever compose, and composing past an [∃ γ] is what a guard cannot
  do. *)

From iris.proofmode Require Import proofmode.
From nola.verus_halt.typing Require Import uninit type_context programs.
From nola.verus_halt.typing Require Export rec own.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Implicit Type 𝔄 𝔅: syn_type.

Section sown.
  Context `{!typeG FML Σ}.

  (** [rec.v] declares these inside its own sections, so they do not
    escape; same four projections, same spelling. *)
  Notation tyd_size T := (T.1) (only parsing).
  Notation tyd_ghox T := (T.2.1) (only parsing).
  Notation tyd_persx T := (T.2.2.1) (only parsing).
  Notation tyd_phys T := (T.2.2.2) (only parsing).

  (** The stored owning pointer.  Its data *is* [sown_tyd n (ty_d ty)], so
    every law comes from [rec.v] and nothing is proved twice. *)
  Program Definition sown_ptr {𝔄} (n: nat) (ty: type 𝔄)
    : type (at_loctokₛ 𝔄) := {|
    ty_size := 1;
    ty_lev := ty.(ty_lev);
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_ghox := tyd_ghox (sown_tyd n (ty_d ty));
    ty_gho_persx := tyd_persx (sown_tyd n (ty_d ty));
    ty_phys := tyd_phys (sown_tyd n (ty_d ty));
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> 𝔄 n ty sem Hs *.
    by apply (tyd_gho_mono_at (T := sown_tyd n (ty_d ty)) sem Hs).
  Qed.
  Next Obligation.
    move=> 𝔄 n ty sem Hs *.
    by apply (tyd_pers_mono_at (T := sown_tyd n (ty_d ty)) sem Hs).
  Qed.
  Next Obligation.
    move=> 𝔄 n ty κ x d g tid R.
    exact (sown_tyd_TyProphAt n ty.(ty_lfts) (ty_d ty) d
      (λ d' _, ty_d_TyProphAt ty d') κ x g tid R).
  Qed.
  Next Obligation.
    move=> 𝔄 n ty sem Hs *.
    exact: (tyd_pers_pers_at (T := sown_tyd n (ty_d ty)) sem Hs).
  Qed.
  Next Obligation.
    move=> 𝔄 n ty *. exact: (tyd_pers_impl (T := sown_tyd n (ty_d ty))).
  Qed.

  (** *** The two moves [own_ptr] does not need

    [own_ptr] holds its pointee in hand, so its reads just take it.  Here
    the pointee is in the store and the token buys it, which is an update -
    the one extra step every rule below begins with. *)
  Lemma sown_ptr_take {𝔄} n (ty: type 𝔄) x d g tid :
    ty_gho (sown_ptr n ty) x d g tid =[verus_halt_WGuard]=∗
      (fst x) ↦!∗ ty.(ty_phys) (snd (snd x)) tid ∗
      freeable_sz n ty.(ty_size) (fst x) ∗
      ∃ d' gg, ⌜(d' < d)%nat⌝ ∗ ⌜(gg ≤ g)%nat⌝ ∗
        ty_gho ty (snd (snd x)) d' gg tid.
  Proof.
    rewrite /ty_gho -(ty_size_eq2 _ ty) -(ty_phys_eq2 _ ty).
    exact: (sown_tyd_take n (ty_d ty) x d g tid).
  Qed.

  Lemma sown_ptr_alloc {𝔄} n (ty: type 𝔄) l d' g x tid :
    l ↦!∗ ty.(ty_phys) x tid -∗ freeable_sz n ty.(ty_size) l -∗
    ty_gho ty x d' g tid -∗ ty_gho_pers ty x d' g tid =[verus_halt_WGuard]=∗
      ∃ γ, ty_gho (sown_ptr n ty) (l, (γ, x)) (S d') g tid.
  Proof.
    rewrite /ty_gho /ty_gho_pers -(ty_size_eq2 _ ty) -(ty_phys_eq2 _ ty).
    exact: (sown_tyd_alloc n (ty_d ty) l d' g x tid).
  Qed.

  (** The refinement's physical part is the pointer, as [own_ptr]'s is *)
  Lemma sown_ptr_phys {𝔄} n (ty: type 𝔄) x tid :
    (sown_ptr n ty).(ty_phys) x tid = [FVal (LitV (fst x))].
  Proof. done. Qed.

  (** *** The bridge to the recursion

    [sown_ptr]'s data *is* [sown_tyd], and [type_of_tyd] gives back the
    data it was handed, so the slot a guarded recursion puts its hole in -
    [sown_tyd n Self] in [rec.v]'s [own_list_gen] - is exactly
    [sown_ptr n <the type the fixpoint denotes>].  That is what makes the
    three rules below apply to a recursive type rather than only to a
    standalone pointer. *)
  Lemma sown_ptr_d {𝔄} n (ty: type 𝔄) :
    ty_d (sown_ptr n ty) = sown_tyd n (ty_d ty).
  Proof. done. Qed.
  Lemma ty_d_type_of_tyd {𝔄} lfts E (T: tydata 𝔄) HT HP :
    ty_d (type_of_tyd lfts E T HT HP) = T.
  Proof. by move: T HT HP=> [?[?[??]]]. Qed.
  Corollary sown_ptr_of_tyd {𝔄} n lfts E (T: tydata 𝔄) HT HP :
    ty_d (sown_ptr n (type_of_tyd lfts E T HT HP)) = sown_tyd n T.
  Proof. by rewrite sown_ptr_d ty_d_type_of_tyd. Qed.

  (** [verus_halt_WGuard] is a conjunct of [verus_halt_wsat], so the two moves
    above run inside [typed_read]'s and [typed_write]'s update. *)
  Lemma sown_ptr_take_wsat {𝔄} n (ty: type 𝔄) x d g tid :
    ty_gho (sown_ptr n ty) x d g tid =[verus_halt_wsat]{⊤}=∗
      (fst x) ↦!∗ ty.(ty_phys) (snd (snd x)) tid ∗
      freeable_sz n ty.(ty_size) (fst x) ∗
      ∃ d' gg, ⌜(d' < d)%nat⌝ ∗ ⌜(gg ≤ g)%nat⌝ ∗
        ty_gho ty (snd (snd x)) d' gg tid.
  Proof.
    iIntros "Gho W". rewrite (wsat_incl verus_halt_wsat verus_halt_WGuard _).
    iDestruct "W" as "[Wg Wr]".
    iMod (sown_ptr_take with "Gho Wg") as "[Wg $]". iModIntro. by iFrame.
  Qed.

  Lemma sown_ptr_alloc_wsat {𝔄} n (ty: type 𝔄) l d' g x tid :
    l ↦!∗ ty.(ty_phys) x tid -∗ freeable_sz n ty.(ty_size) l -∗
    ty_gho ty x d' g tid -∗ ty_gho_pers ty x d' g tid =[verus_halt_wsat]{⊤}=∗
      ∃ γ, ty_gho (sown_ptr n ty) (l, (γ, x)) (S d') g tid.
  Proof.
    iIntros "↦ free Gho Pers W".
    rewrite (wsat_incl verus_halt_wsat verus_halt_WGuard _).
    iDestruct "W" as "[Wg Wr]".
    iMod (sown_ptr_alloc with "↦ free Gho Pers Wg") as "[Wg $]".
    iModIntro. by iFrame.
  Qed.
End sown.

(** ** The three rules [typing/own.v] gives [own_ptr]

  Each is [own.v]'s proof with [sown_ptr_take_wsat] in front.  Two things
  differ from [own_ptr]'s, and both come from the token.

  The pointee's depth is only *bounded* by the pointer's, not one below it
  exactly, so the depth is lifted with [ty_gho_depth_mono] rather than read
  off a [by_succ].  That is the same step [own.v] already takes to meet
  [typed_read]'s "same depth on both sides"; here it starts one further
  down.

  And closing allocates a **fresh** token, so the residual refinement's
  ghost name is not the one it started with.  That is why [typed_read]'s
  [st] and [typed_write]'s are *relations*: they pin the location and the
  value and say nothing about the name. *)
Section typing.
  Context `{!typeG FML Σ}.

  (** Reading a [Copy] type out of a stored owning pointer.  The pointee
    is put back, under a fresh token. *)
  Lemma read_sown_copy {𝔄} (ty: type 𝔄) n E L :
    Copy ty →
    typed_read E L (sown_ptr n ty) ty (sown_ptr n ty) (λ v, v.2.2)
      (λ v z, z.1 = v.1 ∧ z.2.2 = v.2.2).
  Proof.
    move=> Cpy [l [γ0 x0]] d v tid γ q.
    iIntros "LFT E tok [Hgho %Hphys] W".
    iMod (sown_ptr_take_wsat with "Hgho W")
      as "[W (Hown & Hfree & %d0 & %gg & %Hd0 & %Hgg & #Gho0)]".
    iAssert (ty_gho ty x0 d d tid) as "#Hg".
    { iApply (ty_gho_depth_mono with "Gho0"); lia. }
    iDestruct (copy_concrete with "Hg") as "%Conc".
    rewrite /sown_ptr /= in Hphys. move: Hphys; case=> <-.
    iModIntro. iFrame "W".
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
    rewrite /ty_own. iSplitR; [by iSplit|].
    iIntros "Hown W".
    iDestruct (gsrc_fml_sem_1 (s := GMapstoVec l (ty_phys ty x0 tid))
      with "Hown") as "Hown".
    iDestruct (ty_gho_pers_impl with "Gho0") as "#Hpers".
    iMod (sown_ptr_alloc_wsat n ty l d0 gg x0 tid
      with "Hown Hfree Gho0 Hpers W") as "[$ (%γ' & Gho)]".
    iModIntro. iExists (l, (γ', x0)). iSplit; [done|].
    iFrame "tok". iSplit; [|done].
    iApply (ty_gho_depth_mono with "Gho"); lia.
  Qed.

  (** Moving the pointee out.  What is left is an *ordinary* owning
    pointer: the token is spent, and there is nothing in the store any
    more that would need one. *)
  Lemma read_sown_move {𝔄} (ty: type 𝔄) n E L :
    typed_read E L (sown_ptr n ty) ty (own_ptr n (↯ ty.(ty_size)))
      (λ v, v.2.2) (λ v z, v.1 = z.1).
  Proof.
    move=> [l [γ0 x0]] d v tid γ q. iIntros "LFT E tok [Hgho %Hphys] W".
    iMod (sown_ptr_take_wsat with "Hgho W")
      as "[W (Hown & Hfree & %d0 & %gg & %Hd0 & %Hgg & Gho0)]".
    (* the residue is an ordinary [own_ptr], whose depth index is matched
       exactly, so [d] has to be exposed as a successor - which it is,
       [d0] being strictly below it *)
    destruct d as [|dd]; [lia|].
    iAssert (ty_gho ty x0 (S dd) (S dd) tid) with "[Gho0]" as "Hg".
    { iApply (ty_gho_depth_mono with "Gho0"); lia. }
    rewrite /sown_ptr /= in Hphys. move: Hphys; case=> <-.
    iMod (mapsto_vec_untether_emp _ _ ⊤ ∅ with "Hown")
      as (vl_concrete) "[Hconc [%Hleneq [Retether %ConcreteEq]]]".
    iModIntro. iFrame "W".
    iExists (l, repeat [] (length (ty_phys ty x0 tid))), vl_concrete,
      (ty_phys ty x0 tid), (gsrc_fml (GMapstoVec l (FVal <$> vl_concrete))).
    iSplit; [done|]. iSplit; [done|].
    iSplitL "Hconc".
    { iApply gsrc_fml_sem_2. by rewrite /= heap_mapsto_fancy_fmap_eq. }
    iSplit.
    { rewrite gsrc_fml_sem /= heap_mapsto_fancy_fmap_eq
        heap_mapsto_cells_empty Hleneq. iApply guard_refl. }
    iSplitL "Retether". { iIntros. by iApply "Retether". }
    iSplit. { iPureIntro=> ?. by rewrite ConcreteEq. }
    rewrite /ty_own. iSplitL "Hg"; [by iSplit|].
    iIntros "Hown $ !>".
    have Hsz : ty_size ty = length vl_concrete.
    { rewrite -(ty_size_eq ty x0 tid).
      by first [exact Hleneq|exact (eq_sym Hleneq)]. }
    rewrite Hsz.
    iExists (l, list_to_vec vl_concrete). iSplit; [done|]. iFrame "tok".
    iSplit; [|done]. rewrite own_ptr_gho /=. iFrame "Hfree".
    iSplitL; [|by iApply empty_fml_sem_2]. rewrite vec_to_list_to_vec.
    by iApply (gsrc_fml_sem_1 (s := GMapstoVec l (FVal <$> vl_concrete))).
  Qed.

  (** Writing through a stored owning pointer.  The new pointee goes back
    into the store, under a fresh token. *)
  Lemma write_sown {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) n E L :
    ty.(ty_size) = ty'.(ty_size) →
    typed_write E L (sown_ptr n ty) ty (sown_ptr n ty') ty' (λ v, v.2.2)
      (λ u b' u', u'.1 = u.1 ∧ u'.2.2 = b').
  Proof.
    move=> Sz. split; [done|].
    move=> [l [γ0 x0]] d v tid γ q.
    iIntros "LFT UNIQ E tok [Hgho %Hphys] W".
    iMod (sown_ptr_take_wsat with "Hgho W")
      as "[W (Hown & Hfree & %d0 & %gg & %Hd0 & %Hgg & Gho0)]".
    rewrite /sown_ptr /= in Hphys. move: Hphys; case=> <-.
    destruct d as [|d']; [lia|]. iModIntro. iFrame "W".
    iAssert (ty_gho ty x0 d' (S d') tid) with "[Gho0]" as "Hg".
    { iApply (ty_gho_depth_mono with "Gho0"); lia. }
    iExists (l, repeat [] (length (ty_phys ty x0 tid))), d', empty_fml.
    iSplit; [done|]. iSplit; [done|].
    iSplitL "Hown Hg".
    { iExists (ty_phys ty x0 tid).
      rewrite -heap_cloc_mapsto_fancy_empty. by iFrame "Hown Hg". }
    iSplitR "tok Hfree". { iApply empty_fml_sem_2. }
    iSplitR "tok Hfree".
    { iApply (guard_lhs_iff empty_fml_sem).
      iApply (guard_rhs_iff (heap_cloc_mapsto_empty _ _)). iApply guard_true. }
    iIntros (y db') "Hown _ W". rewrite /ty_own.
    iDestruct "Hown" as (vl) "[Pt [Gho %Phys]]".
    iAssert (ty_gho ty' y db' (S d' `max` S db') tid) with "[Gho]" as "Gho2".
    { iApply (ty_gho_depth_mono with "Gho"); lia. }
    iDestruct (ty_gho_pers_impl with "Gho2") as "#Pers".
    rewrite -Phys.
    replace (length (ty_phys ty x0 tid)) with (length (ty_phys ty' y tid));
      last by do 2 rewrite ty_size_eq.
    rewrite -heap_cloc_mapsto_fancy_empty.
    iMod (sown_ptr_alloc_wsat n ty' l db' (S d' `max` S db') y tid
      with "Pt [Hfree] Gho2 Pers W") as "[$ (%γ' & Gho')]".
    { by rewrite -Sz. }
    iModIntro. iExists (l, (γ', y)). iFrame "tok". iSplit; [done|].
    by iFrame "Gho'".
  Qed.
End typing.
