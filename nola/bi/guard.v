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

  (** A guard over a world satisfaction that is itself guarded

    The later-free counterpart of opening a nested invariant.  If [W'] can be
    had out of [W] and handed back - which is what [guard_wsat_out] gives for
    a conjunct of [W], and what an invariant token gives for its contents -
    then a guard taken over [W'] is a guard over [W].

    Unlike [guard_wsat_incl] this asks for no [WsatIncl]: [W'] may be
    *produced* by [W] rather than be a syntactic conjunct of it, which is
    exactly the case of a storage protocol's world satisfaction held in an
    invariant ([nola/verus_halt/typing/protocol.v]). *)
  Lemma guard_wsat_trans {W W' P Q} :
    (P &&{W}&&> W') -∗ (P &&{W'}&&> Q) -∗ P &&{W}&&> Q.
  Proof.
    rewrite /guard. iIntros "#gW #g !>" (T) "[P toWT]".
    iAssert (P -∗ W' ∗ (W' -∗ W ∗ T))%I with "[toWT]" as "toW'".
    { iIntros "P". iApply ("gW" $! T). iFrame "P". iExact "toWT". }
    iDestruct ("g" $! (W' -∗ W ∗ T)%I with "[$P $toW']") as "[$ toW'T]".
    iIntros "Q". iDestruct ("toW'T" with "Q") as "[W' back]".
    by iApply "back".
  Qed.

  (** A conjunct of the world satisfaction is guarded by anything

    This is the later-free, world-satisfaction counterpart of Leaf's
    [guards_from_inv]: whatever sits inside the world satisfaction can be
    observed by any guard without consuming it. *)
  Lemma guard_wsat_out `{!WsatIncl W W' Wr} {P} : ⊢ P &&{W}&&> W'.
  Proof.
    rewrite /guard. iIntros "!>" (T) "[P toWT]".
    iDestruct ("toWT" with "P") as "[W $]". rewrite (wsat_incl W W' Wr).
    iDestruct "W" as "[$ Wr]". iIntros "W'". iFrame.
  Qed.

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

  (** Weaken the left-hand side of a guard *)
  Lemma guard_lhs_sep_l {W P Q R} : (P &&{W}&&> Q) ⊢ (P ∗ R) &&{W}&&> Q.
  Proof. iIntros "g". iApply (guard_trans with "[] g"). iApply guard_sep_l. Qed.
  Lemma guard_lhs_sep_r {W P Q R} : (P &&{W}&&> Q) ⊢ (R ∗ P) &&{W}&&> Q.
  Proof. iIntros "g". iApply (guard_trans with "[] g"). iApply guard_sep_r. Qed.

  (** A persistent resource held outside joins a guard's right-hand side.

    What this is for: a shared borrow's contents may mix a persistent part
    with an exclusive one, and a *rebuilt* guard has to produce both.  The
    persistent part is read once outside and framed back in here, rather
    than carried through the guard - which [guard_rhs_sep_l] would lose. *)
  Lemma guard_rhs_pers {W P Q} {R : PROP} `{!Persistent R, !Affine R} :
    R -∗ (P &&{W}&&> Q) -∗ P &&{W}&&> (R ∗ Q).
  Proof.
    rewrite /guard. iIntros "#R #g !>" (T) "PT".
    iDestruct ("g" $! T with "PT") as "[Q toWT]".
    iSplitL "Q"; [by iFrame "R Q"|]. iIntros "[_ Q]". by iApply "toWT".
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

  (** Strengthen the body of a guarded existential with persistent knowledge

    Leaf's [guards_strengthen_exists].  This is what lets a guarded existential
    be refined once the rest of the guarded resources pin down the witness; it
    is the rule behind [box_guard]. *)
  Lemma guard_exist_strengthen `{!BiAffine PROP} {A W P Q} {R S : A → PROP} :
    (∀ a, Q ∧ R a ⊢ S a) → (∀ a, Persistent (S a)) →
    (P &&{W}&&> Q) -∗ (P &&{W}&&> ∃ a, R a) -∗ P &&{W}&&> ∃ a, R a ∗ S a.
  Proof.
    move=> QRtoS ?. rewrite /guard. iIntros "#gQ #gR !>" (T) "PT".
    iAssert (Q ∧ ((∃ a, R a) ∗ ((∃ a, R a) -∗ W ∗ T)))%I with "[PT]" as "X".
    { iSplit; [iDestruct ("gQ" with "PT") as "[$ _]"|by iApply "gR"]. }
    rewrite bi.sep_exist_r bi.and_exist_l. iDestruct "X" as (a) "X".
    iAssert (S a ∧ (R a ∗ ((∃ a, R a) -∗ W ∗ T)))%I with "[X]" as "X".
    { iSplit; [|by iDestruct "X" as "[_ $]"]. iApply QRtoS. iSplit.
      - by iDestruct "X" as "[$ _]".
      - by iDestruct "X" as "[_[$ _]]". }
    iDestruct "X" as "[#S[R toWT]]". iSplitL "R"; [by iFrame "R S"|].
    iIntros "[%a'[R _]]". iApply "toWT". by iExists a'.
  Qed.
  Lemma guard_exist_strengthen_lhs `{!BiAffine PROP} {A W P} {R S : A → PROP} :
    (∀ a, P ∧ R a ⊢ S a) → (∀ a, Persistent (S a)) →
    (P &&{W}&&> ∃ a, R a) ⊢ P &&{W}&&> ∃ a, R a ∗ S a.
  Proof.
    move=> ??. iIntros "g". iApply (guard_exist_strengthen with "[] g")=>//.
    iApply guard_refl.
  Qed.

  (** Cancel a disjunct that guards a contradiction

    Leaf's [guards_cancel_or_by_chaining]. *)
  Lemma guard_or_false {W P Q R} :
    (P &&{W}&&> (Q ∨ R)) -∗ (Q &&{W}&&> False) -∗ P &&{W}&&> R.
  Proof.
    rewrite /guard. iIntros "#g #gF !>" (T) "PT".
    iDestruct ("g" with "PT") as "[[Q|$] toWT]"; last first.
    { iIntros "R". iApply "toWT". by iRight. }
    iDestruct ("gF" $! T with "[Q toWT]") as "[[] _]".
    iFrame "Q". iIntros "Q". iApply "toWT". by iLeft.
  Qed.
  (** Cancel a disjunct that is incompatible with another guarded resource

    Leaf's [guards_cancel_or]. *)
  Lemma guard_cancel_or `{!BiAffine PROP} {W P Q R S} : (Q ∧ R ⊢ False) →
    (P &&{W}&&> Q) -∗ (P &&{W}&&> (R ∨ S)) -∗ P &&{W}&&> S.
  Proof.
    move=> QR. iIntros "gQ gRS".
    iAssert (P &&{W}&&> ∃ b : bool, if b then R else S)%I with "[gRS]" as "gRS".
    { iApply (guard_trans with "gRS"). iApply guard_intro. iIntros "!> [R|S]".
      - iSplitL; [by iExists true|]. iIntros "[%b ?]". destruct b; [by iLeft|].
        by iRight.
      - iSplitL; [by iExists false|]. iIntros "[%b ?]". destruct b; [by iLeft|].
        by iRight. }
    iDestruct (guard_exist_strengthen (S:=λ b : bool, ⌜b = false⌝)%I
      with "gQ gRS") as "g".
    { move=> b. destruct b; [|by iIntros "_"]. iIntros "QR". iExFalso.
      by iApply QR. }
    iAssert ((∃ b : bool, (if b then R else S) ∗ ⌜b = false⌝) &&{W}&&> S)%I
      as "g2".
    { iApply guard_intro. iIntros "!> [%b[? ->]]". iFrame. iIntros "S".
      by iExists false; iFrame. }
    iApply (guard_trans with "g g2").
  Qed.

  (** Combine two guards over disjoint world satisfactions

    Leaf's [guards_true_sep_mask_disjoint]: disjointness of namespaces becomes
    separation of world satisfactions. *)
  Lemma guard_sep_wsat `{!BiAffine PROP} {W W' Q R} :
    (True &&{W}&&> Q) -∗ (True &&{W'}&&> R) -∗ True &&{W ∗ W'}&&> (Q ∗ R).
  Proof.
    rewrite /guard. iIntros "#g #g' !>" (T) "[_ toWT]".
    iDestruct ("toWT" with "[//]") as "[[W W'] T]".
    iDestruct ("g" $! emp%I with "[W]") as "[Q toW]".
    { iSplitR; [done|]. iIntros "_". iFrame "W". }
    iDestruct ("g'" $! emp%I with "[W']") as "[R toW']".
    { iSplitR; [done|]. iIntros "_". iFrame "W'". }
    iFrame "Q R". iIntros "[Q R]".
    iDestruct ("toW" with "Q") as "[$ _]". iDestruct ("toW'" with "R") as "[$ _]".
    iFrame "T".
  Qed.

  (** A guard on [False] guards anything *)
  Lemma guard_false {W P Q} : (P &&{W}&&> False) ⊢ P &&{W}&&> Q.
  Proof.
    iIntros "g". iApply (guard_trans with "g"). iApply guard_intro.
    by iIntros "!> []".
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
  (** Using a guard against a frame the caller chooses.  This is the
    definition itself, named so that a proof can apply a guard it holds
    without unfolding it. *)
  Lemma guard_apply {W P Q T} :
    (P &&{W}&&> Q) -∗ P ∗ (P -∗ W ∗ T) -∗ Q ∗ (Q -∗ W ∗ T).
  Proof. rewrite /guard. iIntros "#g". iApply "g". Qed.

  (** A guard on an existential whose body carries its own guard

    Guards do not commute with [∃] - opening one gives no witness to
    narrow by - and this is the exception that matters: when the witness
    comes with a *persistent* [Ψ a] that already guards [Q] from
    [Φ a ∗ Ψ a], the witness can be read off the resource in hand and the
    guard that justifies it survives being looked at.

    [typing/rec.v]'s owning pointer is exactly this shape: its ghost
    component is [∃ γ, ts_full γ ∗ eown_fml γ Px], and its prophecy law
    is handed a guard on the whole of it. *)
  Lemma guard_exist_pers `{!BiAffine PROP} {W A} (Φ Ψ : A → PROP) {Q} :
    (∀ a, Persistent (Ψ a)) →
    (∀ a, Ψ a ⊢ (Φ a ∗ Ψ a) &&{W}&&> Q) →
    ⊢ (∃ a, Φ a ∗ Ψ a) &&{W}&&> Q.
  Proof.
    move=> ? H. rewrite /guard. iIntros "!>" (T) "[(%a & Φ & #Ψ) clo]".
    iDestruct (H a with "Ψ") as "#g".
    iApply (guard_apply with "g [Φ clo]"). iFrame "Φ Ψ".
    iIntros "[Φ _]". iApply "clo". iExists a. iFrame "Φ Ψ".
  Qed.

  Lemma guard_acc {W P Q} : (P &&{W}&&> Q) -∗ P -∗ W -∗ Q ∗ (Q -∗ W ∗ P).
  Proof.
    rewrite /guard. iIntros "#g P W".
    iApply ("g" $! P with "[$P W]"). iIntros "$". iFrame "W".
  Qed.
  (** Open two guards out of the same [P] at once

    Leaf's [guards_open_two_simultaneously].  The intermediate [U] is what the
    two guards are opened against, so that neither closes the other out. *)
  Lemma guard_open_two {W P Q R} :
    (P &&{W}&&> Q) -∗ (P &&{W}&&> R) -∗ P -∗ W -∗ ∃ U, U ∗
      □ (U -∗ Q ∗ (Q -∗ U)) ∗ □ (U -∗ R ∗ (R -∗ U)) ∗ (U -∗ W ∗ P).
  Proof.
    rewrite /guard. iIntros "#gQ #gR P W".
    iExists (P ∗ (P -∗ W ∗ P))%I. iSplitL.
    { iFrame "P". iIntros "$". iFrame "W". }
    iSplit; [|iSplit].
    - iIntros "!> U". iDestruct ("gQ" $! P with "U") as "[$ toU]".
      iIntros "Q". iDestruct ("toU" with "Q") as "[W $]". iIntros "$". iFrame "W".
    - iIntros "!> U". iDestruct ("gR" $! P with "U") as "[$ toU]".
      iIntros "R". iDestruct ("toU" with "R") as "[W $]". iIntros "$". iFrame "W".
    - iIntros "[P toWP]". by iApply "toWP".
  Qed.

  (** Observe persistent knowledge from two guards at once

    Leaf's [guards_and_pers]: the two guards see the *same* resource, so the
    non-separating conjunction of their right-hand sides holds of it. *)
  Lemma guard_and_pers `{!BiAffine PROP} {W P Q R S} `{!Persistent S} :
    □ (Q ∧ R -∗ S) -∗ (P &&{W}&&> Q) -∗ (P &&{W}&&> R) -∗ P -∗ W -∗
      W ∗ P ∗ S.
  Proof.
    iIntros "#toS gQ gR P W".
    iDestruct (guard_open_two with "gQ gR P W") as (U) "(U & #accQ & #accR & toWP)".
    iAssert (S ∧ U)%I with "[U]" as "SU".
    { iSplit; [|iFrame "U"]. iApply "toS". iSplit.
      - iDestruct ("accQ" with "U") as "[$ _]".
      - iDestruct ("accR" with "U") as "[$ _]". }
    iDestruct "SU" as "[#S U]".
    iDestruct ("toWP" with "U") as "[$$]". iFrame "S".
  Qed.
  (** The same, with an extra exclusive resource available to the observation *)
  Lemma guard_and_pers_with_excl `{!BiAffine PROP} {W P Q R S T}
    `{!Persistent S} :
    □ ((Q ∧ R) ∗ T -∗ S) -∗ (P &&{W}&&> Q) -∗ (P &&{W}&&> R) -∗ P -∗ T -∗ W -∗
      W ∗ P ∗ T ∗ S.
  Proof.
    iIntros "#toS gQ gR P T W".
    iDestruct (guard_open_two with "gQ gR P W") as (U) "(U & #accQ & #accR & toWP)".
    iAssert (S ∧ (U ∗ T))%I with "[U T]" as "SUT".
    { iSplit; [|iFrame "U T"]. iApply "toS". iFrame "T". iSplit.
      - iDestruct ("accQ" with "U") as "[$ _]".
      - iDestruct ("accR" with "U") as "[$ _]". }
    iDestruct "SUT" as "[#S [U $]]".
    iDestruct ("toWP" with "U") as "[$$]". iFrame "S".
  Qed.

  (** Variant for a world satisfaction that includes the guard's one *)
  Lemma guard_accw `{!WsatIncl W W' Wr} {P Q} :
    (P &&{W'}&&> Q) -∗ P -∗ W -∗ Q ∗ (Q -∗ W ∗ P).
  Proof.
    iIntros "g". iDestruct (guard_wsat_incl (W:=W) with "g") as "g".
    iApply (guard_acc with "g").
  Qed.
End guard.
