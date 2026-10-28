(** * Point propositions and factoring

  A *point proposition* is one of the form [uPred_ownM x ∗ □ Q], i.e., one whose
  resource content is a single, minimal element.  The key property is that such
  a proposition can be *factored out* of any resource that entails it
  ([point_factor]): if [P] entails [Q] and [Q] is a point proposition, then [P]
  can be split into [Q] and a remainder [Q -∗ P].

  This is the later-free core of the Leaf library's factoring machinery
  (Hance et al., [guarding/factoring_props.v] and
  [guarding/internal/factoring_upred.v], MIT-licensed); we keep only the
  later- and except-0-free fragment, which is all that a total program logic
  needs.  It is what makes the conjunction rule for guards ([guard_and] in
  [nola.iris.guard]) go through. *)

From nola Require Export prelude.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import proofmode.

Implicit Type Σ : gFunctors.

(** ** Factoring out an [uPred_ownM] *)

Section ownM_factor.
  Context {Σ}.

  (** A resource that entails [uPred_ownM x] contains [x] as a separate piece *)
  Lemma ownM_factor {x} {P : iProp Σ} :
    (P -∗ uPred_ownM x) ∗ P ⊢ uPred_ownM x ∗ (uPred_ownM x -∗ P).
  Proof.
    uPred.unseal. split=> n r vr. rewrite /uPred_holds /=.
    move=> [r1[r2[eqr[tox Pr2]]]].
    have v12 : ✓{n} (r1 ⋅ r2) by rewrite -eqr.
    unfold uPred_holds, upred.uPred_wand_def in tox. simpl in tox.
    have [z eqz] : x ≼{n} (r1 ⋅ r2) by apply tox.
    (* [r] itself satisfies [P], since [r2] does and [r2 ≼{n} r] *)
    have Pr : uPred_holds P n r.
    { eapply uPred_mono; [exact Pr2| |done]. exists r1. by rewrite eqr comm. }
    (* [r ≡{n}≡ x ⋅ z], so we hand out [x] and keep [z] *)
    have eqxz : r ≡{n}≡ x ⋅ z by rewrite eqr eqz.
    exists x, z. split; [done|]. split.
    { exists ε. by rewrite right_id. }
    move=> n' r' len v' [w eqw]. eapply uPred_mono; [exact Pr| |done].
    exists w. rewrite eqw assoc [z ⋅ x]comm. f_equiv. by apply: dist_le.
  Qed.
End ownM_factor.

(** ** Point propositions *)

(** [point_prop P] : [P] is a point proposition, i.e., owning a single
  resource plus persistent knowledge *)
Definition point_prop {Σ} (P : iProp Σ) : Prop :=
  ∃ x Q, P ≡ (uPred_ownM x ∗ □ Q)%I.
(** Let type class search solve [point_prop] goals *)
Existing Class point_prop.

Section point_prop.
  Context {Σ}.
  Implicit Type P Q : iProp Σ.

  #[export] Instance point_prop_proper : Proper ((≡) ==> (↔)) (@point_prop Σ).
  Proof. solve_proper. Qed.

  (** [emp] and [True] are point propositions *)
  Lemma point_prop_true : point_prop (True : iProp Σ).
  Proof.
    exists ε, True%I. rewrite uPred.ownM_unit'. iSplit; iIntros "_"; [|done].
    by iSplit.
  Qed.
  Lemma point_prop_emp : point_prop (emp : iProp Σ).
  Proof.
    exists ε, True%I. rewrite uPred.ownM_unit'. iSplit; iIntros "_"; [|done].
    by iSplit.
  Qed.

  (** A persistent, affine proposition is a point proposition *)
  Lemma point_prop_persistent `{!Persistent P, !Affine P} : point_prop P.
  Proof.
    exists ε, P. rewrite uPred.ownM_unit'. iSplit.
    - iIntros "#?". iSplit; [done|]. by iModIntro.
    - by iIntros "[_ #$]".
  Qed.

  (** Point propositions are closed under [∗] *)
  Lemma point_prop_sep `{pP : !point_prop P, pQ : !point_prop Q} :
    point_prop (P ∗ Q).
  Proof.
    move: pP pQ=> [x[R eqP]][y[S eqQ]].
    exists (x ⋅ y), (R ∗ S)%I. rewrite eqP eqQ uPred.ownM_op. iSplit.
    - iIntros "[[$ #R][$ #S]]". iModIntro. iSplitL; [iApply "R"|iApply "S"].
    - iIntros "[[$$] #[R S]]". iSplitL; iModIntro; [iApply "R"|iApply "S"].
  Qed.

  (** [own] is a point proposition *)
  Lemma point_prop_own `{!inG Σ A} {γ} {a : A} : point_prop (own γ a).
  Proof.
    rewrite own.own_eq /own.own_def. exists (own.iRes_singleton γ a), True%I.
    iSplit.
    - iIntros "$". by iModIntro.
    - by iIntros "[$ _]".
  Qed.

  (** Point propositions are closed under [big_sepS] *)
  Lemma point_prop_big_sepS `{!EqDecision A, !Countable A}
    {X : gset A} {Φ : A → iProp Σ} :
    (∀ a, a ∈ X → point_prop (Φ a)) → point_prop ([∗ set] a ∈ X, Φ a).
  Proof.
    induction X as [|a X ? IH] using set_ind_L; intros pt.
    { rewrite big_sepS_empty. exact point_prop_emp. }
    rewrite big_sepS_union; [|set_solver]. rewrite big_sepS_singleton.
    have ? : point_prop (Φ a) by apply pt; set_solver.
    have ? : point_prop ([∗ set] b ∈ X, Φ b)
      by apply IH=> ??; apply pt; set_solver.
    exact point_prop_sep.
  Qed.

  (** ** The key lemma: a point proposition factors out *)
  Lemma point_factor `{pQ : !point_prop Q} {P} : (P -∗ Q) ∗ P ⊢ Q ∗ (Q -∗ P).
  Proof.
    move: pQ=> [x[R eqQ]]. rewrite eqQ. iIntros "[toQ P]".
    iAssert (□ R)%I as "#R". { by iDestruct ("toQ" with "P") as "[_ $]". }
    iAssert (P -∗ uPred_ownM x)%I with "[toQ]" as "tox".
    { iIntros "P". by iDestruct ("toQ" with "P") as "[$ _]". }
    iDestruct (ownM_factor with "[$tox $P]") as "[$ toP]". iFrame "R".
    iIntros "[x _]". by iApply "toP".
  Qed.
End point_prop.

(** Instances for type class search *)
#[export] Existing Instances point_prop_sep point_prop_own.
#[export] Hint Extern 0 (point_prop emp) => apply point_prop_emp
  : typeclass_instances.
#[export] Hint Extern 0 (point_prop True) => apply point_prop_true
  : typeclass_instances.
