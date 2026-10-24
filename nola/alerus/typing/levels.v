(** * Execution levels, as ghost names

  The thesis's Chapter 5 stratifies its type system by a level [i ∈ N] and
  interprets the function type as a total Hoare triple whose world
  satisfaction mentions *only lower levels*:

  >  J T →ⱼ U K ᵢ δ v  ≜  ∀u. [J T K ᵢ δ u] v(u) [J U K ᵢ δ] { ∗_{k<j} Winv_k J K ᵢ δ* }   (5.4)

  which is well-formed because [k < j ≤ i], so the recursion on the level
  is well-founded.  That is the device [typing/ctx.v]'s [FnFml] is missing,
  and PLAN.md records it as the remaining large item.

  This file settles the part of its cost that was overestimated.  The
  thesis says (§ 5.2 fn. 3):

  >  Unfortunately, in the current Coq mechanization of Iris, only a finite
  >  number of component RAs are allowed for the global camera.  So we
  >  parameterized our proof with the maximum level L ∈ N to be used.

  With Nola's present [sinv] interface that is no longer so.
  [sinv_wsat_alloc_name] mints a *fresh ghost name* against the [inG] an
  existing instance already carries, so a level is a [gname] rather than a
  component of the global camera - the development allocates as many as a
  proof needs, with no global maximum and no new [inG].  This port already
  relies on the same trick once, for the store world satisfaction that
  [typing/ctx.v] puts inside [alerus_WGuard] beside [boxes.v]'s.

  Nothing here depends on the typing layer; it is the level machinery on
  its own, so that the stratification can be built on top of a piece that
  is already checked. *)

From iris.proofmode Require Import proofmode.
From nola.iris Require Import sinv.
From nola.bi Require Import internal modw wpw.
Import iPropAppNotation WpwNotation.

Section levels.
  Context `{!sinvGS FML Σ}.
  Implicit Type (γ : gname) (γs : list gname) (j k L : nat).

  (** One instance of the simple-invariant mechanism, at a fresh name *)
  Definition lv_wsat γ (sm : _) : iProp Σ :=
    sinv_wsat (sinvGS0 := SinvGS FML Σ sinvGS_pre γ) sm.

  (** The family.  [smf k] is level [k]'s interpretation, and the levels'
    interpretations may differ - which is what (5.2) needs, each level
    interpreting its own [nProp_k]. *)
  Definition lvs_wsat γs (smf : nat → _) : iProp Σ :=
    [∗ list] k ↦ γ ∈ γs, lv_wsat γ (smf k).

  (** Allocating the family: as many levels as asked for, from the one
    [inG].  No component of the global camera is added, hence no global
    maximum level. *)
  Lemma lvs_wsat_alloc L :
    ∀ smf : nat → _, (∀ k i, internal_ne (smf k i)) ⊢
      |==> ∃ γs, ⌜length γs = L⌝ ∗ lvs_wsat γs smf.
  Proof.
    induction L as [|L IH]=> smf.
    { iIntros "_ !>". iExists []. iSplitR; [done|]. by rewrite /lvs_wsat. }
    iIntros "#Ne".
    iMod (IH (λ k, smf (S k)) with "[]") as (γs Hlen) "W".
    { iIntros (??). iApply "Ne". }
    iMod (sinv_wsat_alloc_name (FML:=FML)) as (γ) "W0".
    iDestruct ("W0" $! (smf 0) with "[]") as "W0". { iIntros (?). iApply "Ne". }
    iModIntro. iExists (γ :: γs). rewrite /lvs_wsat /=. iFrame.
    iPureIntro. by rewrite Hlen.
  Qed.

  (** [lvs_below γs smf j]: the thesis's [∗_{k<j} Winv_k], the world
    satisfaction a function of execution level [j] runs under *)
  Definition lvs_below γs (smf : nat → _) j : iProp Σ :=
    lvs_wsat (take j γs) smf.

  (** A prefix splits off *)
  Lemma lvs_wsat_split {γs smf} j :
    lvs_wsat γs smf ⊣⊢
      lvs_wsat (take j γs) smf ∗
      ([∗ list] k ↦ γ ∈ drop j γs, lv_wsat γ (smf (length (take j γs) + k))).
  Proof. by rewrite /lvs_wsat -{1}(take_drop j γs) big_sepL_app. Qed.

  (** ...so a lower execution level's world satisfaction sits inside a
    higher one's, which is exactly what the thesis's [ty-lev] - raising a
    typing judgment's execution level - needs, and what makes [k < j ≤ i]
    usable rather than merely true. *)
  Lemma lvs_below_le {γs smf j j'} : (j ≤ j')%nat →
    lvs_below γs smf j' ⊣⊢
      lvs_below γs smf j ∗
      ([∗ list] k ↦ γ ∈ drop j (take j' γs),
         lv_wsat γ (smf (length (take j γs) + k))).
  Proof.
    move=> Hle. rewrite /lvs_below (lvs_wsat_split (γs:=take j' γs) j).
    by rewrite take_take Nat.min_l.
  Qed.

  #[export] Instance wsat_incl_lvs_below {γs smf j j'} (Hle : (j ≤ j')%nat) :
    WsatIncl (lvs_below γs smf j') (lvs_below γs smf j)
      ([∗ list] k ↦ γ ∈ drop j (take j' γs),
         lv_wsat γ (smf (length (take j γs) + k))) :=
    lvs_below_le Hle.
End levels.

(** ** A reference at a level, and the two rules that make a level useful

  A level is only worth having if (a) a reference at level [k] can be
  dereferenced by a function whose execution level [j] exceeds [k], and
  (b) a judgment's execution level can be raised.  Those are the thesis's
  two structural rules, and both come out of [lvs_below] directly. *)
Section lv_tok.
  Context `{!sinvGS FML Σ}.
  Implicit Type (γ : gname) (γs : list gname) (j k : nat) (i : positive).

  (** A reference *at a level*: the thesis's [ref°ₖ], stripped of
    everything but the level. *)
  Definition lv_tok γ i (Px : FML $oi Σ) : iProp Σ :=
    sinv_tok (sinvGS0 := SinvGS FML Σ sinvGS_pre γ) i Px.

  #[export] Instance lv_tok_persistent {γ i Px} : Persistent (lv_tok γ i Px).
  Proof. rewrite /lv_tok. exact _. Qed.

  Lemma lv_tok_acc {γ sm i Px} :
    lv_tok γ i Px -∗ lv_wsat γ sm -∗ sm i Px ∗ (sm i Px -∗ lv_wsat γ sm).
  Proof. exact sinv_tok_acc. Qed.

  (** **** Dereferencing, and why the level is what cuts the circularity

    A function of execution level [j] runs under [lvs_below γs smf j], and
    a reference at level [k < j] is reachable inside it.  The content comes
    back at [smf k], *level [k]'s* interpretation - never level [j]'s - so
    the definition of level [j] may mention it, which is (5.4)'s
    well-formedness.  The accessor is reversible, as [sinv]'s is. *)
  Lemma lvs_below_acc {γs smf j k γ i Px} :
    (k < j)%nat → γs !! k = Some γ →
    lv_tok γ i Px -∗ lvs_below γs smf j -∗
      smf k i Px ∗ (smf k i Px -∗ lvs_below γs smf j).
  Proof.
    move=> Hk Hγ. iIntros "tok W". rewrite /lvs_below /lvs_wsat.
    iDestruct (big_sepL_lookup_acc _ _ k γ with "W") as "[Wk →W]".
    { by rewrite lookup_take_lt. }
    iDestruct (lv_tok_acc with "tok Wk") as "[$ back]".
    iIntros "P". iApply "→W". by iApply "back".
  Qed.
End lv_tok.

(** ** [ty-lev]: raising a judgment's execution level

  (5.2) states the typing judgment as a total Hoare triple at
  [∗_{k<i} Winv_k], and the thesis's [ty-lev] raises [i].  Here that is
  [twpw_incl] along [wsat_incl_lvs_below] and nothing else - a one-liner,
  and it is a one-liner *because a level is a ghost name*: no camera is
  indexed by the level, so there is nothing to re-prove per level and no
  global maximum to respect.

  This is as far as the stratification can be taken without the typing
  layer.  What remains is on the other side of the interface: PLAN.md's
  item 2 - the interpretation has to become a family [⟦⟧ᶜ_i(δ)] by strong
  recursion on [i], with [fn_fml]'s selector carrying its execution level,
  and a level on every type former and on [typed_body]. *)
Section lv_wp.
  Context `{!sinvGS FML Σ, !iris'GS_gen hlc Λ Σ}.
  Implicit Type (γs : list gname) (j : nat).

  (** The world satisfaction of a higher execution level opens into the
    world satisfaction of a lower one and back - [lvs_below_le] in the
    shape the weakest precondition wants. *)
  Lemma lvs_below_acsr {γs smf j j'} (Hle : (j ≤ j')%nat) {E} :
    ⊢ □ (lvs_below (FML:=FML) γs smf j' ={E}=∗
         lvs_below γs smf j ∗ (lvs_below γs smf j ={E}=∗ lvs_below γs smf j')).
  Proof.
    iIntros "!>". rewrite (lvs_below_le (FML:=FML) (γs:=γs) (smf:=smf) Hle).
    iIntros "[W Wr]". iModIntro. iFrame "W". iIntros "W !>". iFrame.
  Qed.

  Lemma twpw_lvs_le {γs smf j j'} (Hle : (j ≤ j')%nat) {s E e Φ} :
    WP[lvs_below (FML:=FML) γs smf j] e @ s; E [{ Φ }] ⊢
    WP[lvs_below (FML:=FML) γs smf j'] e @ s; E [{ Φ }].
  Proof.
    iIntros "twp". iApply (twpw_incl_fupd (E:=E) with "[] twp"); [done|].
    iApply (lvs_below_acsr Hle).
  Qed.

  Lemma wpw_lvs_le {γs smf j j'} (Hle : (j ≤ j')%nat) {s E e Φ} :
    WP[lvs_below (FML:=FML) γs smf j] e @ s; E {{ Φ }} ⊢
    WP[lvs_below (FML:=FML) γs smf j'] e @ s; E {{ Φ }}.
  Proof.
    iIntros "wp". iApply (wpw_incl_fupd (E:=E) with "[] wp"); [done|].
    iApply (lvs_below_acsr Hle).
  Qed.

  (** The same for the triple (5.4) is stated about, so that a function
    type at execution level [j] is a subtype of one at [j' ≥ j]. *)
  Lemma thoarew_lvs_le {γs smf j j'} (Hle : (j ≤ j')%nat) {s E P e Ψ} :
    [[{ P }]][lvs_below (FML:=FML) γs smf j] e @ s; E [[{ v, RET v; Ψ v }]] -∗
    [[{ P }]][lvs_below (FML:=FML) γs smf j'] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    iIntros "#H !>" (Φ) "P →Φ". iApply (twpw_lvs_le Hle).
    iApply ("H" with "P →Φ").
  Qed.
End lv_wp.

(** Axiom-free, as the rest of the level machinery is. *)
Print Assumptions lvs_wsat_alloc.
Print Assumptions lvs_below_acc.
Print Assumptions twpw_lvs_le.
