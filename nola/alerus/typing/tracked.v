(** * Tracked types

  Ported from VerusBelt ([typing/tracked.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  [Tracked<T>] is [T] with the physical contents cleared out.  Everything is
  inherited from [ty], so nothing here changes in the later-free setting. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.typing Require Import programs.
From nola.alerus.typing Require Export type ctx.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Section tracked.
  Context `{!typeG FML Σ}.

  Program Definition tracked_ty {𝔄} (ty: type 𝔄) : type (trackedₛ 𝔄) := {|
    ty_size := 0;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_gho x d g tid := (ty.(ty_gho) x d g tid) ;
    ty_gho_pers x d g tid := (ty.(ty_gho_pers) x d g tid) ;
    ty_phys x tid := [];
  |}%I.
  Next Obligation. intros; done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. intros. apply (ty_gho_depth_mono ty); trivial. Qed.
  Next Obligation. intros. apply (ty_gho_pers_depth_mono ty); trivial. Qed.
  Next Obligation.
    move=> ? ty κ x d g tid ξ R Hin. iIntros "LFT Incl Pers Rk Rg".
    iApply (ty_guard_proph _ ty κ x d g tid ξ R Hin with "LFT Incl Pers Rk Rg").
  Qed.
  Next Obligation. intros. apply (ty_gho_pers_impl); trivial. Qed.

  Global Instance tracked_ne {𝔄} : NonExpansive (@tracked_ty 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance tracked_send {𝔄} (ty : type 𝔄) : Send ty → Send (tracked_ty ty).
  Proof. intros [Hphys Hgho]. split; trivial. Qed.

  Global Instance tracked_sync {𝔄} (ty : type 𝔄) : Sync ty → Sync (tracked_ty ty).
  Proof.
    intros Hsync tid tid' x d g.
    destruct (Hsync tid tid' x d g) as [A [B C]].
    split; [done|]. split; [exact B|exact C].
  Qed.

  Global Instance tracked_copy {𝔄} (ty : type 𝔄) : Copy ty → Copy (tracked_ty ty).
  Proof.
    intros Hcopy. destruct Hcopy. split; trivial. intros. iIntros "_".
    iPureIntro. done.
  Qed.

  Lemma tracked_resolve {𝔄} (ty: type 𝔄) E L f :
    resolve E L ty f → resolve E L (tracked_ty ty) f.
  Proof. intros Hresolve. apply Hresolve. Qed.

  (** Subtyping *)

  Lemma tracked_type_incl {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) f :
    type_incl ty ty' f ⊢ type_incl (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f).
  Proof. iIntros "(A & B & C & D & E)". iFrame. iSplit; done. Qed.

  Lemma tracked_subtype {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅) f :
    subtype E L ty ty' f →
    subtype E L (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f).
  Proof.
    intros Hsub. iIntros "A". iDestruct (Hsub with "A") as "#B". iModIntro.
    iIntros "E". iApply tracked_type_incl. iApply "B". iFrame.
  Qed.

  Lemma tracked_eqtype {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅) f g :
    eqtype E L ty ty' f g →
    eqtype E L (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f) (tracked_mapₛ g).
  Proof. intros [Ha Hb]. split; apply tracked_subtype; trivial. Qed.

End tracked.

Global Hint Resolve tracked_resolve : lrust_typing.
