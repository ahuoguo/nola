(** * Levelled borrows: a closure stored in a borrow, and termination

  This file settles the design question that [strat.v] leaves open, that
  PLAN.md's item 2 is blocked on, and that **neither of the port's two
  sources answers**:

  - the thesis's Chapter 5 stratifies a *functional* language.  Its only
    sharing mechanism is Nola's invariant, and it has no lifetimes and no
    borrows.
  - [nola/examples/rust_halt/] has lifetimes and borrows and proves total
    correctness with them - and has **no function type at all**.  There is
    no [ty_fn] in that directory.

  So "a function type whose execution level bounds what it may reach,
  stored in a *borrow*" is built in neither place, and the port's
  [typing/function.v] needs exactly that.  Before rebuilding
  [lifetime/ra.v] around it, the design is checked here, small and whole.

  ** The question

  Levelling the port means giving each execution level its own borrowing
  machinery, so that a function at level [j] runs under [∗_{k<j} Wbor_k]
  and can only reach borrows strictly below it.  Two things had to be true
  for that to be possible at all, and both are facts about Nola's existing
  code rather than guesses:

  - **the lifetime tokens and the borrow bookkeeping are separate ghost
    state.**  [lftG Σ] is [inG Σ lftR] with *no ghost name* - an atomic
    lifetime is its own name - while [borrowGS] carries [borrow_name].  So
    [L] borrowing machineries over *one* shared lifetime algebra is just
    [L] names, and needs no new camera.  (In the port this is false:
    [lifetime/ra.v]'s [LtRa] is one record holding the alive multiset, the
    dead set *and* the borrow-state map, under one [llft_name].  That is
    the refactor this file is the justification for.)

  - **ending a lifetime needs no world satisfaction.**  [lft_end] is
    [1.[α] ==∗ [†α]], a bare basic update.  Borrows of a dead lifetime are
    settled *lazily*, by the lender, with whichever [Wbor_k] it is holding.
    Had killing a lifetime needed every level's world satisfaction at once,
    levelling the borrows would have been impossible, because a body at
    level [j] never holds the levels above it.

  What those two leave open is whether the *recursion* still closes with
  borrows in it, and that is what is mechanized below.

  ** The answer

  It does, and the reason is the same one that makes (5.5) work for
  references: [⟦&{α}ₖ T⟧ v] is a borrow *token*, naming the syntax [T],
  and it never interprets [T].  So level [k]'s world satisfaction holds
  [⟦T⟧ₖ] for stored [T], whose function types are at levels [≤ k], which
  mention only [Wbor_h] for [h < k].  Strictly decreasing, hence the
  recursion on the level goes through exactly as in [strat.v].

  And Landin's knot is blocked, now through a borrow rather than a
  reference.  To put [f : T →ⱼ U] in a borrow one needs a slot at level
  [k ≥ j] ([bwf]), and opening that slot needs execution level [> k].  So
  [f]'s own body, which runs under [∗_{h<j} Wbor_h] and [j ≤ k], cannot
  open the borrow that holds it.  [typed_call_borrowed] below does the
  legal half of that, and terminates. *)

From iris.proofmode Require Import proofmode.
From nola.bi Require Import internal modw wpw.
From nola.iris Require Import borrow lft.
From iris.program_logic Require Import total_ectx_lifting.
From nola.lrust Require Import notation proofmode lifting adequacy.
Import ModwNotation WpwNotation iPropAppNotation LftNotation.

(** ** Levelled types, with a borrow former

  [strat.v]'s grammar with [ref°ₖ] replaced by a full borrow [&{α}ₖ].  The
  lifetime is part of the type, as it is in λRust. *)
Inductive btyp : Type :=
| (** [unit] *) bunit
| (** [nat] *) bnat
| (** [T →ⱼ U]: a function whose *execution* level is [j ≤ i] *)
  bfn (j : nat) (T U : btyp)
| (** [&{α}ₖ T]: a full borrow, at lifetime [α], held in the borrowing
    machinery of level [k], of a location holding a [T].

    As with the thesis's [ref°ₖ Tₖ], the level [k] of the slot bounds the
    stored type and is unconstrained by the surrounding level: the
    interpretation is a token and never interprets [T]. *)
  bbor (α : lft) (k : nat) (T : btyp).

(** [bwf i T]: [T ∈ Typᵢ] *)
Fixpoint bwf (i : nat) (T : btyp) : Prop :=
  match T with
  | bunit | bnat => True
  | bfn j T U => (j ≤ i)%nat ∧ bwf i T ∧ bwf i U
  | bbor _ k T => bwf k T
  end.

Lemma bwf_mono T : ∀ i i', (i ≤ i')%nat → bwf i T → bwf i' T.
Proof.
  induction T as [| |j T IHT U IHU|α k T IH]; simpl; intros i i' Hle;
    [done|done| |done].
  intros (?&?&?). split; [lia|]. split; [by apply (IHT i)|by apply (IHU i)].
Qed.

(** The formulas a borrow slot holds: [ℓ ↦ T], exactly (5.2). *)
Notation bfmlO := (leibnizO (loc * btyp)).
Notation bFML := (constOF bfmlO).

Section strat_bor.
  Context `{!lrustGS_gen HasNoLc Σ, !borrowGpreS bFML Σ}.
  (** One ghost name per level: one borrowing machinery per level. *)
  Context (γs : list gname).
  Notation SEM := (btyp -d> val -d> iProp Σ).

  Implicit Type (T U : btyp) (i j k : nat) (v u w : val) (α : lft)
    (q : Qp) (sm : bfmlO -d> iProp Σ).

  (** *** The borrowing machinery of one level *)

  (** Level [k]'s world satisfaction.  The modality is [bupd]: this case
    study has no invariants for a lender to need. *)
  Definition bwsat (γ : gname) sm : iProp Σ :=
    borrow_wsat (borrowGS0 := borrowGS_of γ) bupd sm.
  (** A borrow token in level [k]'s machinery *)
  Definition bwtok (γ : gname) α (Px : bfmlO) : iProp Σ :=
    bor_tok (borrowGS0 := borrowGS_of γ) α Px.
  Definition bwlend (γ : gname) α (Px : bfmlO) : iProp Σ :=
    lend_tok (borrowGS0 := borrowGS_of γ) α Px.

  (** [∗_{k<j} Wbor_k]: the world satisfaction of execution level [j] *)
  Definition bors_below (smf : nat → bfmlO -d> iProp Σ) j : iProp Σ :=
    ([∗ list] k ↦ γ ∈ take j γs, bwsat γ (smf k))%I.

  (** Only the levels below [j] are looked at *)
  Lemma bors_below_ext {smf smf' j} :
    (∀ k, (k < j)%nat → smf k = smf' k) →
    bors_below smf j ⊣⊢ bors_below smf' j.
  Proof.
    move=> eq. rewrite /bors_below. apply big_sepL_proper=> k γ Hk.
    have Hkj : (k < j)%nat.
    { apply lookup_lt_Some in Hk. rewrite length_take in Hk. lia. }
    by rewrite (eq k Hkj).
  Qed.

  (** A lower level's world satisfaction splits off *)
  Lemma bors_below_le {smf j j'} : (j ≤ j')%nat →
    bors_below smf j' ⊣⊢
      bors_below smf j ∗
      ([∗ list] k ↦ γ ∈ drop j (take j' γs),
         bwsat γ (smf (length (take j γs) + k)%nat)).
  Proof.
    move=> Hle. rewrite /bors_below -{1}(take_drop j (take j' γs)).
    rewrite big_sepL_app take_take Nat.min_l //.
  Qed.

  (** Reaching level [k]'s machinery from execution level [j > k].  This
    is the whole point of the level: the content comes back at [smf k],
    *level [k]'s* interpretation, never level [j]'s. *)
  Lemma bors_below_acc {smf j k γ} : (k < j)%nat → γs !! k = Some γ →
    bors_below smf j ⊢ bwsat γ (smf k) ∗ (bwsat γ (smf k) -∗ bors_below smf j).
  Proof.
    move=> Hk Hγ. iIntros "W". rewrite /bors_below.
    iDestruct (big_sepL_lookup_acc _ _ k γ with "W") as "[$ $]".
    by rewrite lookup_take_lt.
  Qed.

  (** *** The interpretation, level by level

    Exactly [strat.v]'s construction, with the borrow former in place of
    the reference former. *)

  Definition nthsem (l : list SEM) k : SEM := nth k l (λ _ _, False%I).

  (** (5.2): level [k] interprets [ℓ ↦ T] by [⟦T⟧ₖ] *)
  Definition smf_of (l : list SEM) : nat → bfmlO -d> iProp Σ :=
    λ k lT, (∃ w, lT.1 ↦ w ∗ nthsem l k lT.2 w)%I.

  (** [⟦&{α}ₖ T⟧ v]: a borrow token in level [k]'s machinery, naming the
    *syntax* [T].  It never interprets [T], which is (5.5)'s property and
    the reason the recursion on the level below is well-founded even
    though a borrow may hold a function. *)
  Definition borsem k α T v : iProp Σ :=
    (∃ (lo : loc) (γ : gname), ⌜v = #lo⌝ ∗ ⌜γs !! k = Some γ⌝ ∗
      bwtok γ α (lo, T))%I.

  Lemma borsem_loc {k α T v} : borsem k α T v ⊢ ⌜∃ lo : loc, v = #lo⌝.
  Proof. iIntros "(%lo & % & -> & _)". iPureIntro. by eexists. Qed.

  Definition bsem_gen (l : list SEM) : SEM :=
    fix go T v : iProp Σ := match T with
    | bunit => ⌜v = #☠⌝%I
    | bnat => (∃ n : Z, ⌜v = #n⌝)%I
    | bfn j T U => (⌜(j ≤ length l)%nat⌝ ∗ □ ∀ u, go T u -∗
        WP[bors_below (smf_of l) j] App (of_val v) [of_val u]
          [{ w, go U w }])%I
    | bbor α k T => borsem k α T v
    end.

  Fixpoint bsems (i : nat) : list SEM :=
    match i with
    | O => @nil SEM
    | S i' => (bsems i' ++ cons (bsem_gen (bsems i')) nil)%list
    end.
  (** [⟦⟧ᵢ] *)
  Definition bsem (i : nat) : SEM := bsem_gen (bsems i).

  Lemma bsems_length i : length (bsems i) = i.
  Proof. induction i as [|i IH]=>//=. rewrite length_app IH /=. lia. Qed.
  Lemma bsems_nth {i k} : (k < i)%nat → nthsem (bsems i) k = bsem k.
  Proof.
    move: k. induction i as [|i IH]=> k Hk; [lia|]=>/=.
    rewrite /nthsem /=. case (decide (k < i)%nat)=> Hki.
    - rewrite app_nth1; [|rewrite bsems_length; lia]. by apply (IH k).
    - have -> : k = i by lia.
      rewrite app_nth2; [|rewrite bsems_length; lia].
      by rewrite bsems_length Nat.sub_diag.
  Qed.

  (** The global family, and the world satisfaction of execution level [j] *)
  Definition bsmf : nat → bfmlO -d> iProp Σ :=
    λ k lT, (∃ w, lT.1 ↦ w ∗ bsem k lT.2 w)%I.
  Definition Wlv j : iProp Σ := bors_below bsmf j.

  Lemma smf_of_bsems {i k} : (k < i)%nat → smf_of (bsems i) k = bsmf k.
  Proof. move=> Hk. rewrite /smf_of /bsmf (bsems_nth Hk) //. Qed.
  Lemma Wlv_bsems {i j} : (j ≤ i)%nat →
    bors_below (smf_of (bsems i)) j ⊣⊢ Wlv j.
  Proof. move=> ?. apply bors_below_ext=> k ?. apply smf_of_bsems. lia. Qed.

  Lemma twpw_wsat_eq {W W' : iProp Σ} (eq : W ⊣⊢ W') {s E e Φ} :
    WP[W] e @ s; E [{ Φ }] ⊢ WP[W'] e @ s; E [{ Φ }].
  Proof.
    iIntros "twp". iApply (twpw_incl_fupd (E:=E) with "[] twp"); [done|].
    iIntros "!> W'". iModIntro.
    iDestruct (bi.equiv_entails_1_2 _ _ eq with "W'") as "W". iFrame "W".
    iIntros "W !>". by iApply (bi.equiv_entails_1_1 _ _ eq with "W").
  Qed.

  (** (5.4), with the world satisfaction in its global form *)
  Lemma bsem_fn {i j T U v} : (j ≤ i)%nat →
    bsem i (bfn j T U) v ⊣⊢
      □ ∀ u, bsem i T u -∗ WP[Wlv j] App (of_val v) [of_val u]
        [{ w, bsem i U w }].
  Proof.
    move=> Hji. rewrite /bsem /=. rewrite bsems_length.
    iSplit.
    - iIntros "[_ #f] !>" (u) "Tu". iApply (twpw_wsat_eq (Wlv_bsems Hji)).
      by iApply "f".
    - iIntros "#f". iSplit; [done|]. iIntros "!>" (u) "Tu".
      iApply (twpw_wsat_eq (symmetry (Wlv_bsems Hji))). by iApply "f".
  Qed.
  Lemma bsem_bor {i α k T v} : bsem i (bbor α k T) v = borsem k α T v.
  Proof. done. Qed.

  (** A function type's interpretation is persistent, as in Lemma 5.1.  A
    *borrow*'s is not - a borrow token is exclusive - which is the one
    place this file departs from [strat.v], and is why the rules below
    hand the token back. *)
  #[export] Instance bsem_fn_persistent {i j T U v} :
    Persistent (bsem i (bfn j T U) v).
  Proof. rewrite /bsem /=. exact _. Qed.

  (** The level does not change a well-formed type's interpretation *)
  Lemma bsem_lev T : ∀ i i' v, (i ≤ i')%nat → bwf i T →
    bsem i T v ⊣⊢ bsem i' T v.
  Proof.
    induction T as [| |j T IHT U IHU|α k T IH]=> i i' v Hle Hwf;
      [done|done| |done].
    move: Hwf=> [Hji[HT HU]].
    rewrite (bsem_fn Hji) (bsem_fn (Nat.le_trans _ _ _ Hji Hle)).
    iSplit.
    - iIntros "#f !>" (u) "Tu".
      iDestruct (bi.equiv_entails_1_2 _ _ (IHT i i' u Hle HT) with "Tu")
        as "Tu'".
      iDestruct ("f" with "Tu'") as "twp". iApply (twp_wand with "twp").
      iIntros (w) "H".
      by iApply (bi.equiv_entails_1_1 _ _ (IHU i i' w Hle HU)).
    - iIntros "#f !>" (u) "Tu".
      iDestruct (bi.equiv_entails_1_1 _ _ (IHT i i' u Hle HT) with "Tu")
        as "Tu'".
      iDestruct ("f" with "Tu'") as "twp". iApply (twp_wand with "twp").
      iIntros (w) "H".
      by iApply (bi.equiv_entails_1_2 _ _ (IHU i i' w Hle HU)).
  Qed.

  (** [ty-lev] for the world satisfaction *)
  Lemma bors_below_acsr {smf j j'} (Hle : (j ≤ j')%nat) {E} :
    ⊢ □ (bors_below smf j' ={E}=∗
         bors_below smf j ∗ (bors_below smf j ={E}=∗ bors_below smf j')).
  Proof.
    iIntros "!>". rewrite (bors_below_le (smf:=smf) Hle).
    iIntros "[W Wr]". iModIntro. iFrame "W". iIntros "W !>". iFrame.
  Qed.
  Lemma twpw_bors_le {smf j j'} (Hle : (j ≤ j')%nat) {s E e Φ} :
    WP[bors_below smf j] e @ s; E [{ Φ }] ⊢
    WP[bors_below smf j'] e @ s; E [{ Φ }].
  Proof.
    iIntros "twp". iApply (twpw_incl_fupd (E:=E) with "[] twp"); [done|].
    iApply (bors_below_acsr Hle).
  Qed.

  (** *** Borrowing at a level

    Each rule is [bors_below_acc] followed by the corresponding rule of
    [nola/iris/borrow.v], and each asks [k < j]: level [k]'s borrowing
    machinery is reachable only from strictly above it.  That single
    side condition is the whole stratification. *)

  Lemma bor_new_lv {j k γ α} (Px : bfmlO) : (k < j)%nat → γs !! k = Some γ →
    bsmf k Px =[Wlv j]=∗ bwtok γ α Px ∗ bwlend γ α Px.
  Proof.
    move=> Hk Hγ. iIntros "P W".
    iDestruct (bors_below_acc Hk Hγ with "W") as "[Wk →W]".
    iMod (bor_lend_tok_new (FML:=bFML) (borrowGS0 := borrowGS_of γ) (M:=bupd) α Px
      with "P Wk") as "[Wk $]".
    iModIntro. by iApply "→W".
  Qed.

  Lemma bor_open_lv {j k γ α q} {Px : bfmlO} :
    (k < j)%nat → γs !! k = Some γ →
    q.[α] -∗ bwtok γ α Px =[Wlv j]=∗
      obor_tok (borrowGS0 := borrowGS_of γ) α q Px ∗ bsmf k Px.
  Proof.
    move=> Hk Hγ. iIntros "α b W".
    iDestruct (bors_below_acc Hk Hγ with "W") as "[Wk →W]".
    iMod (bor_tok_open (FML:=bFML) (borrowGS0 := borrowGS_of γ) (M:=bupd)
      with "α b Wk") as "[Wk $]".
    iModIntro. by iApply "→W".
  Qed.

  Lemma bor_close_lv {j k γ α q} {Px : bfmlO} :
    (k < j)%nat → γs !! k = Some γ →
    obor_tok (borrowGS0 := borrowGS_of γ) α q Px -∗ bsmf k Px =[Wlv j]=∗
      q.[α] ∗ bwtok γ α Px.
  Proof.
    move=> Hk Hγ. iIntros "o P W".
    iDestruct (bors_below_acc Hk Hγ with "W") as "[Wk →W]".
    iMod (obor_tok_close (FML:=bFML) (borrowGS0 := borrowGS_of γ) (M:=bupd)
      with "o P Wk") as "[Wk $]".
    iModIntro. by iApply "→W".
  Qed.

  (** The lender gets the content back once the lifetime is over - at
    *its* level, whichever level that is.  This is the rule that would be
    impossible if ending a lifetime needed every level at once. *)
  Lemma lend_retrieve_lv {j k γ α} {Px : bfmlO} :
    (k < j)%nat → γs !! k = Some γ →
    [†α] -∗ bwlend γ α Px =[Wlv j]=∗ bsmf k Px.
  Proof.
    move=> Hk Hγ. iIntros "† l W".
    iDestruct (bors_below_acc Hk Hγ with "W") as "[Wk →W]".
    iMod (lend_tok_retrieve (FML:=bFML) (borrowGS0 := borrowGS_of γ) (M:=bupd)
      with "† l Wk") as "[Wk $]".
    iModIntro. by iApply "→W".
  Qed.

  (** *** The typing judgment

    (5.2)'s [𝛤 ⊢ e :ᵢ T] for a closed expression: a *total* weakest
    precondition over [∗_{k<i} Wbor_k].  Totality is termination. *)
  Definition typed i (e : expr) T : iProp Σ :=
    WP[Wlv i] e [{ v, bsem i T v }].

  (** [ty-lev] *)
  Lemma typed_lev {i i' e T} : (i ≤ i')%nat → bwf i T →
    typed i e T ⊢ typed i' e T.
  Proof.
    move=> Hle Hwf. rewrite /typed. iIntros "twp".
    iApply (twpw_bors_le Hle). iApply (twp_wand with "twp").
    iIntros (v) "H". by iApply (bi.equiv_entails_1_1 _ _ (bsem_lev T i i' v Hle Hwf)).
  Qed.

  Lemma typed_val {i v T} : bsem i T v ⊢ typed i (of_val v) T.
  Proof. rewrite /typed. iIntros "T". by iApply twp_value. Qed.
  Lemma typed_nat {i} (n : Z) : ⊢ typed i (of_val (LitV (LitInt n))) bnat.
  Proof. iApply typed_val. by iExists n. Qed.
  Lemma typed_unit {i} : ⊢ typed i (of_val (LitV LitPoison)) bunit.
  Proof. by iApply typed_val. Qed.

  Lemma typed_bind {i e K T U} :
    typed i e T -∗ (∀ v, bsem i T v -∗ typed i (fill K (of_val v)) U) -∗
    typed i (fill K e) U.
  Proof.
    rewrite /typed. iIntros "twp →". iApply twp_bind.
    iApply (twp_wand with "twp"). iIntros (v) "T". by iApply "→".
  Qed.

  (** [ty-fun] *)
  Lemma typed_fun {i i' x e T U} `{!Closed (<> :b: [x]%binder +b+ []) e} :
    (i ≤ i')%nat → bwf i T → bwf i U →
    □ (∀ u : val, bsem i T u -∗ typed i (subst' x u e) U) ⊢
      typed i' (of_val (λ: [x], e)%V) (bfn i T U).
  Proof.
    move=> Hle HT HU. iIntros "#f". iApply typed_val.
    rewrite (bsem_fn Hle). iIntros "!>" (u) "Tu".
    iDestruct (bi.equiv_entails_1_2 _ _ (bsem_lev T i i' u Hle HT)
      with "Tu") as "Tu'".
    iDestruct ("f" with "Tu'") as "twp". rewrite /typed.
    wp_rec. iApply (twp_wand with "twp"). iIntros (w) "H".
    by iApply (bi.equiv_entails_1_1 _ _ (bsem_lev U i i' w Hle HU)).
  Qed.

  (** [ty-call] *)
  Lemma typed_call {i e1 e2 T U} :
    typed i e1 (bfn i T U) -∗ typed i e2 T -∗ typed i (App e1 [e2]) U.
  Proof.
    iIntros "f a".
    iApply (typed_bind (K:=[AppLCtx [e2]]) with "f"). iIntros (v1) "F /=".
    iDestruct (bi.equiv_entails_1_1 _ _ (bsem_fn (le_n i)) with "F") as "#F'".
    iApply (typed_bind (K:=[AppRCtx v1 [] []]) with "a"). iIntros (v2) "A /=".
    rewrite /typed. by iApply "F'".
  Qed.

  (** *** What the file exists to show

    A closure of type [A →ⱼ B] stored in a borrow at slot level [k], with
    [j ≤ k < i], retrieved at execution level [i] and called - and the
    whole thing terminating.

    The two side conditions are forced, and together they are the
    argument.  Storing [A →ⱼ B] in a level-[k] slot asks
    [bwf k (bfn j A B)], hence [j ≤ k]; opening a level-[k] slot asks
    [k < i].  So the callee runs under [∗_{h<j} Wbor_h] while the borrow
    that holds it lives at level [k ≥ j] - which the callee therefore does
    *not* hold, and cannot open.  Landin's knot is precisely the attempt
    to break that, and it is not typable: no [j] satisfies [j ≤ k] and
    [k < j] at once. *)

  (** [ty-borrow] *)
  Lemma typed_borrow {i k α T} (lo : loc) (w : val) :
    (k < i)%nat → (k < length γs)%nat →
    lo ↦ w -∗ bsem k T w =[Wlv i]=∗ bsem i (bbor α k T) #lo.
  Proof.
    move=> Hk Hlen.
    have [γ Hγ] : is_Some (γs !! k) by apply lookup_lt_is_Some.
    iIntros "↦ T W".
    iMod (bor_new_lv (j:=i) (γ:=γ) (α:=α) (lo, T) Hk Hγ with "[↦ T] W")
      as "[W [b _]]".
    { rewrite /bsmf /=. iExists w. iFrame. }
    iModIntro. iFrame "W". rewrite bsem_bor /borsem. iExists lo, γ. by iFrame.
  Qed.

  (** [ty-call] through a borrow *)
  Lemma typed_call_borrowed {i j k α A B q e1 e2} :
    (j ≤ k)%nat → (k < i)%nat → bwf k A → bwf k B →
    q.[α] -∗ typed i e1 (bbor α k (bfn j A B)) -∗ typed i e2 A -∗
      WP[Wlv i] App (!ˢᶜ e1) [e2] [{ u, bsem i B u ∗ q.[α] }].
  Proof.
    move=> Hjk Hki HA HB.
    have Hji : (j ≤ i)%nat by lia. have Hki' : (k ≤ i)%nat by lia.
    iIntros "α e1 e2".
    (* evaluate the borrow expression *)
    iApply (twp_bind (fill [ReadCtx ScOrd; AppLCtx [e2]])).
    iApply (twp_wand with "e1"). iIntros (v1) "R /=".
    iDestruct "R" as (lo γ) "(-> & %Hγ & b)".
    (* open the borrow of level [k] from execution level [i > k] *)
    iApply (fupdw_twpw_nonval (W:=Wlv i)); [done|].
    iMod (bor_open_lv Hki Hγ with "α b") as "[o P]".
    rewrite /bsmf /=. iDestruct "P" as (w) "[↦ #F]". iModIntro.
    (* read the closure out *)
    iApply (twp_bind (fill [AppLCtx [e2]])). wp_read.
    (* and put the borrow back: the closure's interpretation is persistent *)
    iApply (fupdw_twpw_nonval (W:=Wlv i)); [done|].
    iMod (bor_close_lv Hki Hγ with "o [↦]") as "[α _]".
    { rewrite /bsmf /=. iExists w. by iFrame "↦ F". }
    iModIntro.
    (* evaluate the argument *)
    iApply (twp_bind (fill [AppRCtx w [] []])).
    iApply (twp_wand with "e2"). iIntros (v2) "Av /=".
    (* the closure was stored at level [k]; read it at level [i] *)
    iDestruct (bi.equiv_entails_1_1 _ _
      (bsem_lev (bfn j A B) k i w Hki' (conj Hjk (conj HA HB))) with "F")
      as "#F'".
    iDestruct (bi.equiv_entails_1_1 _ _ (bsem_fn (i:=i) Hji) with "F'")
      as "#F''".
    (* call it: its execution level [j ≤ i], so [Wlv j] is part of [Wlv i] *)
    iDestruct ("F''" with "Av") as "twp".
    iApply (twpw_bors_le (smf:=bsmf) Hji). iApply (twp_wand with "twp").
    iIntros (u) "$". done.
  Qed.

  (** The interpretations are internally non-expansive, which
    [borrow_wsat] asks for.  Trivially: the formulas are discrete. *)
  Lemma bsmf_internal_ne {k} :
    ⊢@{iProp Σ} internal_ne (A:=bfmlO) (B:=iPropO Σ) (bsmf k).
  Proof. iIntros (a a') "eq". by iDestruct (discrete_eq_1 with "eq") as %->. Qed.
End strat_bor.


(** ** Allocating the levels

  [L] borrowing machineries over *one* lifetime algebra: [L] ghost names
  and no new camera.  This is the step that [lifetime/ra.v]'s [LtRa]
  blocks in the port, because there the alive multiset, the dead set and
  the borrow-state map share one record and therefore one [llft_name]. *)
Lemma bors_names_alloc `{!borrowGpreS bFML Σ} L :
  ⊢ |==> ∃ γs : list gname, ⌜length γs = L⌝ ∗
    ∀ smf : nat → bfmlO -d> iProp Σ, (∀ k, internal_ne (smf k)) -∗
      [∗ list] k ↦ γ ∈ γs, bwsat γ (smf k).
Proof.
  induction L as [|L IH].
  { iIntros "!>". iExists []. iSplitR; [done|]. by iIntros (?) "_". }
  iMod IH as (γs Hlen) "→W".
  iMod (borrow_wsat_alloc_name (FML:=bFML)) as (γ) "→W0".
  iModIntro. iExists (γs ++ [γ]).
  iSplitR; [iPureIntro; rewrite length_app Hlen /=; lia|].
  iIntros (smf) "#Ne". rewrite big_sepL_app /=.
  iDestruct ("→W" $! smf with "Ne") as "$".
  rewrite Hlen Nat.add_0_r. iSplitL; [|done].
  rewrite /bwsat. iApply "→W0". iApply "Ne".
Qed.

(** ** Termination adequacy

  Corollary 5.3, with borrows: a program typed at level [i] terminates. *)
Class strat_borGpreS Σ : Type := StratBorGpreS {
  strat_borGpreS_lrust :: lrustGpreS Σ;
  strat_borGpreS_borrow :: borrowGpreS bFML Σ;
}.
Definition strat_borΣ : gFunctors := #[lrustΣ; borrowΣ bFML].
#[export] Instance subG_strat_borGpreS `{!subG strat_borΣ Σ} :
  strat_borGpreS Σ.
Proof.
  split; [solve_inG|].
  apply subG_inv in subG0 as [_ H]. apply subG_inv in H as [H _].
  by apply subG_borrow.
Qed.

Theorem strat_bor_total `{!strat_borGpreS Σ} {i e T σ} :
  (∀ `(!lrustGS_gen HasNoLc Σ) (γs : list gname),
    length γs = i → ⊢ typed γs i e T) →
  sn erased_step ([e], σ).
Proof.
  move=> typ. apply (lrust_total (Σ:=Σ) (s:=NotStuck)). iIntros (?) "_".
  iMod (bors_names_alloc i) as (γs Hlen) "→W".
  iDestruct ("→W" $! (bsmf γs) with "[]") as "W".
  { iIntros (?). iApply bsmf_internal_ne. }
  iModIntro.
  iExists (Wlv γs i), (λ v, bsem γs i T v)%I.
  iSplitL "W". { rewrite /Wlv /bors_below take_ge; [|lia]. iExact "W". }
  iApply (typ _ γs Hlen).
Qed.

(** ** Why the knot is not typable

  The whole argument, as a one-line fact about the grammar: a borrow slot
  of level [k] admits a function only of execution level [j ≤ k], while
  opening that slot ([bor_open_lv]) asks for execution level [> k].  A
  closure that reaches the borrow holding it would need [k < j] as well,
  and no [j] satisfies both. *)
Lemma knot_not_typable {α k j A B i} :
  bwf i (bbor α k (bfn j A B)) → (j ≤ k)%nat.
Proof. by move=> [? _]. Qed.

(** ** A worked program

  A closure stored in a borrow, read back out through the borrow and
  called - the shape [typing/function.v] needs, and the one neither the
  thesis's Chapter 5 (no borrows) nor [rust_halt] (no function type) has.
  It terminates. *)
Section example.
  Context `{!lrustGS_gen HasNoLc Σ, !borrowGpreS bFML Σ} (γs : list gname).

  (** The identity on numbers, at execution level 0.  Level 0 runs under
    *no* borrowing machinery at all - [Wlv γs 0] is the empty big
    separating conjunction - which is the base of the stratification. *)
  Definition idfn : val := λ: ["x"], "x".

  Lemma Wlv_0 : Wlv γs 0 ⊣⊢ emp.
  Proof. by rewrite /Wlv /bors_below take_0. Qed.

  Lemma bsem_idfn {i} : ⊢ bsem γs i (bfn 0 bnat bnat) idfn.
  Proof.
    rewrite (bsem_fn γs (i:=i) (j:=0) (Nat.le_0_l i)).
    iIntros "!>" (u) "N". rewrite /idfn. wp_rec. iExact "N".
  Qed.

  Definition ex_borfn : expr :=
    let: "c" := Alloc #1 in "c" <-ˢᶜ idfn ;;
      App (!ˢᶜ "c") (cons (Lit (LitInt 7)) nil).

  Lemma typed_ex_borfn : (0 < length γs)%nat → ⊢ typed γs 1 ex_borfn bnat.
  Proof.
    move=> Hlen. rewrite /typed /ex_borfn.
    have H1 : (0 < 1)%nat by lia.
    iApply (fupdw_twpw_nonval (W:=Wlv γs 1)); [done|].
    iMod lft_alloc as (α) "[_ α]". iModIntro.
    wp_apply twp_alloc; [lia|done|].
    iIntros (lo sz) "[%Hsz [† ↦]]". have -> : sz = 1%nat by lia.
    rewrite heap_pointsto_vec_singleton. wp_let. wp_write.
    (* borrow the cell at level 0, from execution level 1 *)
    iApply (fupdw_twpw_nonval (W:=Wlv γs 1)); [done|].
    iMod (typed_borrow γs (i:=1) (k:=0) (α:=α) (T:=bfn 0 bnat bnat) lo idfn
      H1 Hlen with "↦ []") as "b"; [iApply bsem_idfn|].
    iModIntro.
    (* and call through it *)
    iApply (twp_wand with "[α b]").
    - iApply (typed_call_borrowed γs (i:=1) (j:=0) (k:=0) (A:=bnat) (B:=bnat)
        with "α [b] []"); [lia|lia|done|done| |].
      + by iApply (typed_val γs (v := LitV (LitLoc lo))).
      + iApply (typed_nat γs 7).
    - iIntros (u) "[$ _]".
  Qed.

  (** The same program, reclaimed through the *lender* instead.

    This is the death path, and it is the one that differs between the
    two lifetime logics.  Here ending the lifetime is [lft_end], a bare
    [==∗] needing no world satisfaction, and the lender reclaims the cell
    at *its own* level with [lend_retrieve_lv].  So death touches one
    level at a time, and never needs a level the running body does not
    hold.

    The port's lifetime logic is not like this: [expire_lt.v]'s
    [inner_kill_lt] runs under [|=[box_wsat bor_sem]{…}=>], so killing a
    lifetime there needs the interpretation-carrying world satisfaction
    of every level at which that lifetime still has borrows.  That, and
    not the shape of [LtRa], is what the port has to arrange. *)
  Lemma typed_ex_endlft : (0 < length γs)%nat → ⊢ typed γs 1 ex_borfn bnat.
  Proof.
    move=> Hlen.
    have [γ Hγ] : is_Some (γs !! 0%nat) by apply lookup_lt_is_Some.
    have H1 : (0 < 1)%nat by lia.
    rewrite /typed /ex_borfn.
    iApply (fupdw_twpw_nonval (W:=Wlv γs 1)); [done|].
    iMod lft_alloc as (α) "[%Hne α]". iModIntro.
    wp_apply twp_alloc; [lia|done|].
    iIntros (lo sz) "[%Hsz [† ↦]]". have -> : sz = 1%nat by lia.
    rewrite heap_pointsto_vec_singleton. wp_let. wp_write.
    iApply (fupdw_twpw_nonval (W:=Wlv γs 1)); [done|].
    (* borrow at level 0, keeping the lender *)
    iMod (bor_new_lv γs (j:=1) (k:=0) (γ:=γ) (α:=α) (lo, bfn 0 bnat bnat)
      H1 Hγ with "[↦]") as "[_ l]".
    { rewrite /bsmf. iExists idfn.
      iSplitL "↦"; [iExact "↦"|iApply bsem_idfn]. }
    (* end the lifetime: no world satisfaction needed *)
    iMod (lft_end Hne with "α") as "#dead".
    (* and reclaim at the lender's level *)
    iMod (lend_retrieve_lv γs (j:=1) (k:=0) (γ:=γ) H1 Hγ with "dead l") as "P".
    rewrite /bsmf /=. iDestruct "P" as (w) "[↦ #F]". iModIntro.
    iApply (twp_bind (fill [AppLCtx (cons (Lit (LitInt 7)) nil)])). wp_read.
    iDestruct (bi.equiv_entails_1_1 _ _
      (bsem_lev γs (bfn 0 bnat bnat) 0 1 w (Nat.le_0_l 1)
        (conj (Nat.le_refl 0) (conj I I))) with "F") as "#F'".
    iDestruct (bi.equiv_entails_1_1 _ _
      (bsem_fn γs (i:=1) (j:=0) (Nat.le_0_l 1)) with "F'") as "#F''".
    iApply (twpw_bors_le γs (smf:=bsmf γs) (Nat.le_0_l 1)).
    iApply ("F''" $! (LitV (LitInt 7))). by iExists 7.
  Qed.
End example.

Theorem ex_borfn_total `{!strat_borGpreS Σ} {σ} :
  sn erased_step ([ex_borfn], σ).
Proof.
  apply (strat_bor_total (i:=1) (T:=bnat))=> ? γs Hlen.
  iApply typed_ex_borfn. lia.
Qed.

Print Assumptions strat_bor_total.
Print Assumptions typed_call_borrowed.
Print Assumptions ex_borfn_total.
Print Assumptions typed_ex_endlft.
