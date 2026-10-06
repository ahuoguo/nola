(** * Later-free guarding

  A reconstruction of the Leaf library's guarding logic (Hance et al.,
  MIT-licensed) over Nola's explicit world satisfactions instead of Iris's
  invariants.  Leaf's guard [P &&{E ; n}&&> Q] is indexed by an invariant mask
  [E] and a *later count* [n]: opening a guard costs [n] laters, because the
  underlying Iris invariant hands back [▷ P].  That cost is fatal for a total
  program logic, where no step is available to strip a later.

  Here the invariant storage is replaced by a world satisfaction [W], threaded
  explicitly in the style of [nola.bi.modw].  Since Nola's world satisfactions
  are later-free, so is the guard:

    P &&{ W }&&> Q  :=  □ ∀ T, P ∗ (P -∗ W ∗ T) -∗ Q ∗ (Q -∗ W ∗ T)

  Leaf's mask bookkeeping ([∃ m ⊆ E, …] plus the knowledge that the invariants
  in [m] exist) is subsumed by [WsatIncl]: a guard over a smaller world
  satisfaction weakens into one over a larger world satisfaction
  ([guard_wsat_incl]).

  The conjunction rule, which is what makes guards more than plain accessors,
  lives in [nola.iris.guard] because it needs the point-proposition machinery
  of [nola.iris.point]. *)

From nola.bi Require Export modw.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : bi.

(** ** [guard]: [P] gives shared access to [Q] under the world satisfaction [W]

  Read [P &&{ W }&&> Q] as "[P] guards [Q] over [W]".  The frame [T] is
  universally quantified, which is what makes the guard compose. *)
Definition guard {PROP} (W P Q : PROP) : PROP :=
  □ ∀ T, P ∗ (P -∗ W ∗ T) -∗ Q ∗ (Q -∗ W ∗ T).
Arguments guard : simpl never.

Module GuardNotation.
  Notation "P &&{ W }&&> Q" := (guard W P Q)
    (at level 99, W at level 50, Q at level 200,
      format "P  &&{ W }&&>  Q") : bi_scope.
End GuardNotation.
Import GuardNotation.

Section guard.
  Context {PROP}.
  Implicit Type W P Q R T : PROP.

  (** [guard] is non-expansive and proper *)
  #[export] Instance guard_ne {n} :
    Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) (guard (PROP:=PROP)).
  Proof. rewrite /guard. solve_proper. Qed.
  #[export] Instance guard_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (guard (PROP:=PROP)).
  Proof. rewrite /guard. solve_proper. Qed.

  (** [guard] is persistent *)
  #[export] Instance guard_persistent {W P Q} : Persistent (P &&{W}&&> Q).
  Proof. rewrite /guard. exact _. Qed.

  (** Introduce a guard from a persistent accessor *)
  Lemma guard_intro {W P Q} : □ (P -∗ Q ∗ (Q -∗ P)) ⊢ P &&{W}&&> Q.
  Proof.
    rewrite /guard. iIntros "#toQ !>" (T) "[P toWT]".
    iDestruct ("toQ" with "P") as "[$ toP]". iIntros "Q".
    iApply "toWT". by iApply "toP".
  Qed.

  (** [guard] is reflexive and transitive *)
  Lemma guard_refl {W P} : ⊢ P &&{W}&&> P.
  Proof. rewrite /guard. by iIntros "!>" (?) "$". Qed.
  Lemma guard_trans {W P Q R} :
    (P &&{W}&&> Q) -∗ (Q &&{W}&&> R) -∗ P &&{W}&&> R.
  Proof.
    rewrite /guard. iIntros "#gPQ #gQR !>" (T) "PT".
    iDestruct ("gPQ" with "PT") as "QT". by iApply "gQR".
  Qed.

  (** A guard can be weakened to a larger world satisfaction *)
  Lemma guard_wsat_sep {W W' P Q} : (P &&{W}&&> Q) ⊢ P &&{W ∗ W'}&&> Q.
  Proof.
    rewrite /guard. iIntros "#g !>" (T) "[P toWT]".
    iDestruct ("g" $! (W' ∗ T)%I with "[$P toWT]") as "[$ toWT]".
    { iIntros "P". iDestruct ("toWT" with "P") as "[[$$]$]". }
    iIntros "Q". iDestruct ("toWT" with "Q") as "[$[$$]]".
  Qed.
  Lemma guard_wsat_incl `{!WsatIncl W W' Wr} {P Q} :
    (P &&{W'}&&> Q) ⊢ P &&{W}&&> Q.
  Proof. rewrite (wsat_incl W W' Wr). exact guard_wsat_sep. Qed.

  (** A separating conjunct is guarded by the whole *)
  Lemma guard_sep_l {W P Q} : ⊢ (P ∗ Q) &&{W}&&> P.
  Proof.
    rewrite /guard. iIntros "!>" (T) "[[$ Q] toWT]". iIntros "P".
    iApply "toWT". iFrame.
  Qed.
  Lemma guard_sep_r {W P Q} : ⊢ (P ∗ Q) &&{W}&&> Q.
  Proof.
    rewrite /guard. iIntros "!>" (T) "[[P $] toWT]". iIntros "Q".
    iApply "toWT". iFrame.
  Qed.

  (** Weaken the right-hand side of a guard *)
  Lemma guard_rhs_sep_l {W P Q R} :
    (P &&{W}&&> (Q ∗ R)) ⊢ P &&{W}&&> Q.
  Proof. iIntros "g". iApply (guard_trans with "g"). iApply guard_sep_l. Qed.
  Lemma guard_rhs_sep_r {W P Q R} :
    (P &&{W}&&> (Q ∗ R)) ⊢ P &&{W}&&> R.
  Proof. iIntros "g". iApply (guard_trans with "g"). iApply guard_sep_r. Qed.

  (** Attach persistent knowledge to the right-hand side *)
  Lemma guard_pers_rhs `{!Persistent R, !Affine R} {W P Q} :
    R -∗ (P &&{W}&&> Q) -∗ P &&{W}&&> (Q ∗ R).
  Proof.
    rewrite /guard. iIntros "#R #g !>" (T) "PT".
    iDestruct ("g" with "PT") as "[$ toWT]". iFrame "R".
    iIntros "[Q _]". by iApply "toWT".
  Qed.

  (** Anything guards [True], in an affine logic *)
  Lemma guard_true `{!BiAffine PROP} {W P} : ⊢ P &&{W}&&> True.
  Proof.
    rewrite /guard. iIntros "!>" (T) "[P toWT]". iSplitR; [done|].
    iIntros "_". by iApply "toWT".
  Qed.

  (** ** Using a guard

    This is the later-free counterpart of Leaf's [guards_open].  The frame is
    instantiated with [P] itself, so that closing the guard returns both the
    world satisfaction and [P]. *)
  Lemma guard_acc {W P Q} : (P &&{W}&&> Q) -∗ P -∗ W -∗ Q ∗ (Q -∗ W ∗ P).
  Proof.
    rewrite /guard. iIntros "#g P W".
    iApply ("g" $! P with "[$P W]"). iIntros "$". iFrame "W".
  Qed.
  (** Variant for a world satisfaction that includes the guard's one *)
  Lemma guard_accw `{!WsatIncl W W' Wr} {P Q} :
    (P &&{W'}&&> Q) -∗ P -∗ W -∗ Q ∗ (Q -∗ W ∗ P).
  Proof.
    iIntros "g". iDestruct (guard_wsat_incl (W:=W) with "g") as "g".
    iApply (guard_acc with "g").
  Qed.
End guard.
