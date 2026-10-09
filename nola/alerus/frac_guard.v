(** * Fractional guards, later-free

  Replaces Leaf's [guarding/lib/fractional.v] (MIT, Hance), which VerusBelt's
  [typing/] uses through [llctx_interp_make_guarded] to hand several
  sub-derivations simultaneous shared access to one resource.

  Leaf builds this on the *storage protocol* machinery: a protocol over
  [option Qp] whose interpretation is [sep_pow n P], together with
  [sp_deposit]/[sp_withdraw]/[sp_guard].  The guard it obtains is
  [own_frac γ q &&{↑N}&&> ▷ P] - note the [▷], which is why the typing layer
  then needs [guards_remove_later_rhs] and a [Timeless] side condition on [P].

  With a world satisfaction in place of an invariant mask the protocol is not
  needed at all.  Store, next to the content, a *death token*: the world
  satisfaction holds [sm Px ∨ frac_dead γ], and a fraction of [γ] is
  incompatible with [frac_dead γ] *under conjunction*, so
  [nola.bi.guard.guard_cancel_or] cancels the right disjunct outright.  The
  result is a later-free guard from *any* fraction, with no [Timeless] side
  condition and no storage protocol.

  Fractionality also makes Leaf's [frac_split_guard_in_half] - which allocates
  a *second* protocol chained onto the first - unnecessary: splitting a share
  in half is just [frac_tok_add], and both pieces guard the content because
  every fraction does. *)

From nola.bi Require Export guard modw.
From nola.iris Require Export sinv guard point.
From nola.alerus Require Import own_and.
From iris.algebra Require Import frac csum excl.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
Import iPropAppNotation GuardNotation ModwNotation.

(** The resource algebra of shares.

  [Cinl q] is a share of size [q]; [Cinr (Excl ())] is the death token handed
  to the world satisfaction once the content has been withdrawn.  The [option]
  wrapper makes the algebra total, which [nola.alerus.own_and] needs in order
  to reason about [own γ a ∧ own γ b]. *)
Definition frac_shareR : cmra := optionR (csumR fracR (exclR unitO)).

Class fracGuardGS FML Σ : Type := FracGuardGS {
  #[global] frac_guard_sinvGpreS :: sinvGpreS FML Σ;
  #[global] frac_guard_inG :: inG Σ frac_shareR;
  frac_guard_name : gname;
}.
Class fracGuardGpreS FML Σ : Type := FracGuardGpreS {
  #[global] fracGuardGpreS_sinv :: sinvGpreS FML Σ;
  #[global] fracGuardGpreS_inG :: inG Σ frac_shareR;
}.
Definition fracGuardΣ FML `{!oFunctorContractive FML} : gFunctors :=
  #[sinvΣ FML; GFunctor frac_shareR].
#[export] Instance subG_fracGuardGpreS
  `{!oFunctorContractive FML, !subG (fracGuardΣ FML) Σ} : fracGuardGpreS FML Σ.
Proof. solve_inG. Qed.

Section frac_guard.
  Context `{!fracGuardGS FML Σ}.
  Implicit Type (Px Qx : FML $oi Σ) (sm : FML $oi Σ → iProp Σ) (γ : gname)
    (q : Qp).

  (** The simple-invariant family the shares live in.

    Deliberately a plain definition rather than a [Context] of class type: a
    [Context (x : C)] on a class [C] registers [x] as an instance, which would
    silently capture every other [sinvGS FML Σ] in scope. *)
  Definition frac_sinvGS : sinvGS FML Σ :=
    SinvGS FML Σ frac_guard_sinvGpreS frac_guard_name.
  Local Notation sinv_tok' := (sinv_tok (sinvGS0:=frac_sinvGS)).
  Local Notation sinv_wsat' := (sinv_wsat (sinvGS0:=frac_sinvGS)).

  (** A share of [γ], and the death token of [γ] *)
  Definition frac_tok γ q : iProp Σ := own γ (Some (Cinl q) : frac_shareR).
  Definition frac_dead γ : iProp Σ :=
    own γ (Some (Cinr (Excl ())) : frac_shareR).
  (** The half share, as in Leaf *)
  Definition half γ : iProp Σ := frac_tok γ (1/2)%Qp.

  #[export] Instance frac_tok_timeless {γ q} : Timeless (frac_tok γ q).
  Proof. exact _. Qed.
  #[export] Instance frac_dead_timeless {γ} : Timeless (frac_dead γ).
  Proof. exact _. Qed.

  (** What the world satisfaction holds for each share: either the content, or
    the death token saying the content has been withdrawn *)
  Definition frac_body sm γ Px : iProp Σ := frac_dead γ ∨ sm Px.
  (** World satisfaction for fractional guards *)
  Definition frac_wsat sm : iProp Σ := sinv_wsat' (frac_body sm).

  (** The token for a share, naming the content *)
  Definition frac_sinv γ Px : iProp Σ := sinv_tok' γ Px.
  #[export] Instance frac_sinv_persistent {γ Px} : Persistent (frac_sinv γ Px).
  Proof. exact _. Qed.
  #[export] Instance frac_sinv_ne {γ} : NonExpansive (frac_sinv γ).
  Proof. rewrite /frac_sinv. exact: sinv_tok_ne. Qed.

  (** ** Arithmetic of shares *)

  Lemma frac_tok_add {γ p q} :
    frac_tok γ (p + q) ⊣⊢ frac_tok γ p ∗ frac_tok γ q.
  Proof. by rewrite /frac_tok -own_op. Qed.
  Lemma frac_tok_half {γ q} :
    frac_tok γ q ⊣⊢ frac_tok γ (q/2) ∗ frac_tok γ (q/2).
  Proof. by rewrite -frac_tok_add Qp.div_2. Qed.
  Lemma half_add {γ} : frac_tok γ 1 ⊣⊢ half γ ∗ half γ.
  Proof. by rewrite /half -frac_tok_add Qp.half_half. Qed.

  (** A share and the death token cannot coexist, even under conjunction.

    This is what replaces Leaf's storage protocol: under [∗] the statement is
    routine, but the guard rules need it under [∧], and that is exactly what
    [nola.alerus.own_and] provides for a discrete total algebra. *)
  Lemma frac_tok_dead_and {γ q} : frac_tok γ q ∧ frac_dead γ ⊢ False.
  Proof.
    apply and_own_discrete_ucmra_contradiction=> c' val in1 in2.
    destruct c' as [b|]; last first.
    { by apply option_included in in1 as [[=]|(?&?&?&[=]&?)]. }
    move: val. rewrite Some_valid=> val. destruct b as [p|u|].
    - (* the death token cannot be included in a share *)
      apply option_included in in2 as [[=]|(?&?&[= <-]&[= <-]&[eq|inc])].
      + by inversion eq.
      + by apply csum_included in inc as [[=]|[(?&?&[=]&?)|(?&?&?&[=]&?)]].
    - (* a share cannot be included in the death token *)
      apply option_included in in1 as [[=]|(?&?&[= <-]&[= <-]&[eq|inc])].
      + by inversion eq.
      + by apply csum_included in inc as [[=]|[(?&?&?&[=]&?)|(?&?&[=]&?)]].
    - by destruct val.
  Qed.

  (** ** Allocating, guarding and withdrawing *)

  (** Deposit the content and get two halves *)
  Lemma frac_split_in_half {sm} Px :
    sm Px -∗ frac_wsat sm ==∗ ∃ γ,
      frac_sinv γ Px ∗ half γ ∗ half γ ∗ frac_wsat sm.
  Proof.
    rewrite /frac_wsat. iIntros "Px W".
    iDestruct (sinv_tok_alloc_suspend (sinvGS0:=frac_sinvGS) Px with "W")
      as (I) "→".
    iMod (own_alloc_cofinite
      (Some (Cinl (1/2)%Qp) ⋅ Some (Cinl (1/2)%Qp) : frac_shareR) I)
      as (γ) "[%nin [tok tok']]".
    { by rewrite -Some_op -Cinl_op frac_op Qp.half_half. }
    iMod ("→" $! γ with "[//]") as "[#sinv →W]". iModIntro. iExists γ.
    iFrame "sinv tok tok'". iApply "→W". rewrite /frac_body. by iRight.
  Qed.

  (** *Any* share guards the content.

    Leaf's [frac_guard] gives [own_frac γ q &&{↑N}&&> ▷ R]; here there is no
    later, so no [Timeless] side condition is needed downstream. *)
  Lemma frac_guard {sm γ Px q} :
    frac_sinv γ Px ⊢ frac_tok γ q &&{frac_wsat sm}&&> sm Px.
  Proof.
    iIntros "#sinv".
    iDestruct (sinv_tok_guard_any (sinvGS0:=frac_sinvGS)
      (sm:=frac_body sm) (P:=frac_tok γ q) with "sinv") as "g".
    iApply (guard_cancel_or frac_tok_dead_and with "[] g"). iApply guard_refl.
  Qed.

  (** Withdraw the content with the full share.

    Unlike Leaf's [frac_withdraw] the result carries no [▷]. *)
  Lemma frac_withdraw {sm γ Px} :
    frac_sinv γ Px -∗ frac_tok γ 1 -∗ frac_wsat sm ==∗ sm Px ∗ frac_wsat sm.
  Proof.
    rewrite /frac_wsat. iIntros "#sinv tok W".
    iDestruct (sinv_tok_acc (sinvGS0:=frac_sinvGS) with "sinv W")
      as "[body →W]". rewrite {1}/frac_body.
    iDestruct "body" as "[dead|$]".
    { iDestruct (own_valid_2 with "tok dead") as %[]. }
    iMod (own_update _ _ (Some (Cinr (Excl ())) : frac_shareR) with "tok")
      as "dead".
    { apply option_update, cmra_update_exclusive. done. }
    iModIntro. iApply "→W". rewrite /frac_body. by iLeft.
  Qed.

  (** Leaf's [frac_split_in_half], as a single package *)
  Lemma frac_split_in_half_full {sm} Px :
    sm Px -∗ frac_wsat sm ==∗ ∃ γ,
      half γ ∗ half γ ∗ (half γ &&{frac_wsat sm}&&> sm Px) ∗
      □ (half γ -∗ half γ -∗ frac_wsat sm ==∗ sm Px ∗ frac_wsat sm) ∗
      frac_wsat sm.
  Proof.
    iIntros "Px W".
    iMod (frac_split_in_half with "Px W") as (γ) "(#sinv & h & h' & W)".
    iModIntro. iExists γ. iFrame "h h' W". iSplitR; [by iApply frac_guard|].
    iIntros "!> h h' W". iApply (frac_withdraw with "sinv [h h'] W").
    rewrite half_add. iFrame.
  Qed.

  (** Leaf's [frac_split_guard_in_half].

    Leaf allocates a second storage protocol chained onto the first.  Here a
    share simply splits, and both pieces guard the content because every
    fraction does. *)
  Lemma frac_split_guard_in_half {sm γ Px q} :
    frac_sinv γ Px -∗ frac_tok γ q -∗
      frac_tok γ (q/2) ∗ frac_tok γ (q/2) ∗
      (frac_tok γ (q/2) &&{frac_wsat sm}&&> sm Px) ∗
      □ (frac_tok γ (q/2) -∗ frac_tok γ (q/2) -∗ frac_tok γ q).
  Proof.
    iIntros "#sinv tok". iEval (rewrite (frac_tok_half (q:=q))) in "tok".
    iDestruct "tok" as "[$$]". iSplitR; [by iApply frac_guard|].
    iIntros "!> h h'". iEval (rewrite (frac_tok_half (q:=q))). iFrame.
  Qed.

  (** Non-expansiveness of the body, for allocating the world satisfaction *)
  Lemma frac_body_ne {sm} :
    internal_ne (PROP:=iProp Σ) sm -∗ ∀ γ, internal_ne (frac_body sm γ).
  Proof.
    iIntros "#Ne" (γ). rewrite /internal_ne /frac_body. iIntros (Px Qx) "eq".
    iDestruct ("Ne" $! Px Qx with "eq") as "eq'". by iRewrite "eq'".
  Qed.

  (** A guard over a larger world satisfaction *)
  Lemma frac_guard_wsat `{!WsatIncl W (frac_wsat sm) Wr} {γ Px q} :
    frac_sinv γ Px ⊢ frac_tok γ q &&{W}&&> sm Px.
  Proof. rewrite frac_guard. iApply guard_wsat_incl. Qed.
End frac_guard.

(** Allocate the world satisfaction for fractional guards *)
Lemma frac_wsat_alloc `{!fracGuardGpreS FML Σ} :
  ⊢ |==> ∃ _ : fracGuardGS FML Σ,
    ∀ sm, internal_ne (PROP:=iProp Σ) sm -∗ frac_wsat sm.
Proof.
  iMod (sinv_wsat_alloc (FML:=FML)) as ([pre γ]) "W". iModIntro.
  iExists (FracGuardGS FML Σ pre _ γ). iIntros (sm) "Ne".
  rewrite /frac_wsat /frac_sinvGS. iApply "W". by iApply frac_body_ne.
Qed.
