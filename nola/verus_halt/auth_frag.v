(** * Inclusion in an [auth] camera

  If a single element of [auth C] is above both an authoritative [● x] and a
  fragment [◯ y], then [y ≼ x].  This is what lets us compare the two halves of
  an [excl_auth] under the *non-separating* conjunction, which is in turn what
  the conjunction rule for guards needs ([box_own_auth_agree_and]).

  Ported from the Leaf library ([guarding/internal/auth_frag_util.v], MIT,
  Hance et al.).  Purely algebraic: no laters, no invariants. *)

From nola Require Export prelude.
From iris.algebra Require Export auth.
From iris.prelude Require Import options.

Section auth_frag.
  Context {SI : sidx} {C : ucmra}.
  Implicit Type (x y p : C) (z : auth C).

  (** Anything composable with an authoritative element is a fragment *)
  Lemma auth_op_rhs_is_frag p z : ✓ (● p ⋅ z) → ∃ q, z = ◯ q.
  Proof.
    move=> val. destruct z as [z_auth z_frag]. destruct z_auth as [[dq a]|].
    { exfalso. rewrite cmra_valid_validN in val. specialize (val 0ᵢ).
      pose proof val as val'. apply cmra_validN_op_r in val'.
      pose proof val as val''. apply cmra_validN_op_l in val''.
      rewrite view_auth_dfrac_validN in val''. destruct val'' as [Hdq1 _].
      destruct val' as [Hdq2 [a0 [Hag _]]].
      have Heq : View (Some (dq, a)) z_frag ≡{0ᵢ}≡ (●V{dq} a0 ⋅ ◯V z_frag : auth C).
      { unfold "●V", "◯V". constructor; simpl;
          [by rewrite right_id Hag|by rewrite left_id]. }
      rewrite Heq assoc in val. apply cmra_validN_op_l in val.
      apply auth_auth_dfrac_op_validN in val. destruct val as [Hq _].
      by apply dfrac_valid_own_l, Qp.lt_strict in Hq. }
    by exists z_frag.
  Qed.

  Local Lemma view_op_rw (x w : option (dfrac * agree C)) (y z : C) :
    (View (rel:=@auth_view_rel_raw _ C) x y) ⋅ (View w z) = View (x ⋅ w) (y ⋅ z).
  Proof. done. Qed.

  (** An element equal to [● x ⋅ _] and to [◯ y ⋅ q2] has [● x] inside [q2] *)
  Lemma rhs_has_auth x y (q1 q2 : auth C) :
    ✓ (● x ⋅ q1) → ● x ⋅ q1 ≡ ◯ y ⋅ q2 → ∃ r, q2 ≡ ● x ⋅ r.
  Proof.
    move=> v eq. have [q eq1] := auth_op_rhs_is_frag x q1 v. subst q1.
    destruct q2 as [a f]. exists (◯ f). unfold "●", "●V", "◯", "◯V".
    rewrite view_op_rw. f_equiv.
    - unfold "◯", "◯V", "●", "●V" in eq. rewrite !view_op_rw in eq.
      inversion eq as [Q R]. unfold view.view_auth_proj in Q.
      setoid_rewrite Q. by destruct a.
    - by rewrite left_id.
  Qed.

  (** The key lemma *)
  Lemma auth_frag_incl `{!CmraDiscrete C} x y z :
    ● x ≼ z → ◯ y ≼ z → ✓ z → y ≼ x.
  Proof.
    move=> [t1 l1][t2 l2] val. setoid_rewrite l1 in l2.
    have D : ✓ (● x ⋅ t1) by setoid_rewrite <-l1.
    have [r jj] := rhs_has_auth _ _ _ _ D l2.
    setoid_rewrite jj in l2. setoid_rewrite l2 in l1.
    setoid_rewrite l1 in val.
    have asso : ◯ y ⋅ (● x ⋅ r) ≡ ◯ y ⋅ ● x ⋅ r := cmra_assoc _ _ _.
    setoid_rewrite asso in val.
    have com : ◯ y ⋅ ● x ≡ ● x ⋅ ◯ y := cmra_comm _ _.
    setoid_rewrite com in val.
    have ll := cmra_valid_op_l _ _ val. move: ll.
    rewrite auth_both_valid_discrete. by move=> [??].
  Qed.
End auth_frag.
