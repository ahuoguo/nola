(** * Later-free guarding over Iris resources

  The part of the guarding logic that needs the Iris resource model: Leaf's
  conjunction rule, and the connection between guards and Nola's simple
  invariants.

  The conjunction rule is what distinguishes guards from plain accessors: two
  guards out of the same [P] can be *merged* with the non-separating conjunction
  [∧].  This is unsound for arbitrary right-hand sides, so Leaf restricts it to
  *point propositions* (see [nola.iris.point]).  Unlike Leaf's version, ours is
  free of [▷] and [◇], because Nola's world satisfactions hand out their
  contents without a later. *)

From nola.bi Require Export guard.
From nola.iris Require Export point sinv.
From iris.proofmode Require Import proofmode.
Import GuardNotation iPropAppNotation.

Implicit Type (Σ : gFunctors) (FML : oFunctor).

Section guard_and.
  Context {Σ}.
  Implicit Type W P Q R : iProp Σ.

  (** Merge two guards out of the same [P] with [∧]

    This is Leaf's [guards_and], without the later and except-0 modalities. *)
  Lemma guard_and {W P Q R S} `{!point_prop S} : (Q ∧ R ⊢ S) →
    (P &&{W}&&> Q) -∗ (P &&{W}&&> R) -∗ P &&{W}&&> S.
  Proof.
    move=> QRtoS. rewrite /guard. iIntros "#gQ #gR !>" (T) "PT".
    (* The two guards view the *same* resource as [Q] and as [R], so the
      non-separating conjunction holds of it *)
    iAssert ((P ∗ (P -∗ W ∗ T)) -∗ S)%I as "toS".
    { iIntros "PT". iApply QRtoS. iSplit.
      - iDestruct ("gQ" with "PT") as "[$ _]".
      - iDestruct ("gR" with "PT") as "[$ _]". }
    (* [S] is a point proposition, so it factors out of the resource *)
    iDestruct (point_factor with "[$toS $PT]") as "[$ toPT]".
    iIntros "S". iDestruct ("toPT" with "S") as "[P toWT]". by iApply "toWT".
  Qed.

  (** Specialization: the right-hand sides are themselves kept *)
  Lemma guard_and' {W P Q R} `{!point_prop (Q ∧ R)} :
    (P &&{W}&&> Q) -∗ (P &&{W}&&> R) -∗ P &&{W}&&> (Q ∧ R).
  Proof. by apply guard_and. Qed.
End guard_and.

(** ** Guards from simple invariants *)

Section guard_sinv.
  Context `{!sinvGS FML Σ}.
  Implicit Type (Px : FML $oi Σ) (sm : positive → FML $oi Σ → iProp Σ).

  (** A simple invariant token guards its contents, with no later

    This is the later-free counterpart of Leaf's [guards_from_ownI], where the
    right-hand side could only be obtained under a [▷]. *)
  Lemma sinv_tok_guard {i sm Px} :
    sinv_tok i Px ⊢ True &&{sinv_wsat sm}&&> sm i Px.
  Proof.
    rewrite /guard. iIntros "#i !>" (T) "[_ toWT]".
    iDestruct ("toWT" with "[//]") as "[W T]".
    iDestruct (sinv_tok_acc with "i W") as "[$ toW]". iIntros "Px".
    iFrame "T". by iApply "toW".
  Qed.

  (** Hence any [P] guards the contents of a simple invariant *)
  Lemma sinv_tok_guard_any {i sm Px P} :
    sinv_tok i Px ⊢ P &&{sinv_wsat sm}&&> sm i Px.
  Proof.
    rewrite sinv_tok_guard. iIntros "g".
    iApply (guard_trans with "[] g"). iApply guard_true.
  Qed.
End guard_sinv.
