(** * Strong normalization of a stratified type system

  The thesis's Chapter 5, mechanized: a type system whose types carry an
  execution level, with higher-order shared mutable references, a function
  type and an infinite list type, proved **strongly normalizing**.

  Two devices of the thesis meet here, and the file exists to show that
  they compose.

  - The **level** (§ 5.2) gives the function type a model.  The
    interpretation is a family [J K ᵢ], defined by recursion on the level,
    and

    >  J T →ⱼ U K ᵢᵟ v ≜ ∀u. [J T K ᵢᵟ u] v(u) [J U K ᵢᵟ] { ∗_{k<j} Winv_k }  (5.4)

    is well-formed because the world satisfaction mentions only the levels
    [k < j ≤ i], which are already defined.  No derivability is involved:
    the level *replaces* it for this connective.

  - **Magic derivability** (§ 5.3, Chapter 4) gives the reference type its
    subtyping rule.  A reference stores a type, an invariant token names
    the formula it holds, and nothing turns [inv(ℓ ↦ T)] into
    [inv(ℓ ↦ U)].  So (5.5) stores a *different* type, tied to the
    declared one by two derivability assertions:

    >  J ref°ₖ T K ᵢᵟ v ≜ ∃U, k' ≤ k. □ δ(T ≤̇ U) ∗ □ δ(U ≤̇ T) ∗
    >                      inv_{k'}((ℓ+o) ↦ U)                            (5.5)

    and [≤-ref] is then the transitivity of derivability.  Notably (5.5)
    does not mention [J K ₖᵟ] at all, which is both what makes the level
    of the body free and what makes a recursive type's occurrence under
    [ref] *guarded*.

  ** What this says about [typing/function.v]'s [fn_fml_sem_2]

  That field has no model, and the reason is now exactly locatable.  A
  function type's ghost assertion has to be a *formula*, because it can be
  borrowed; a formula's semantics is [⟦⟧ᶜ(der)]; [der] is built from
  [Jsem]; and [Jsem] would have to mention [typed_body], which mentions
  [⟦⟧ᶜ(der)].  [Deriv_factor'] does not cut that loop, because introducing
  the judgment then asks for [typed_body] at *every* candidate, and a
  candidate is not sound - a body cannot open the stored guards its own
  argument types carry.

  The level cuts it, and the cut has a price this file makes visible:
  level [j]'s interpretation is used *only* inside the world satisfaction
  of level [j]'s own weakest precondition, so the levels must be separate
  *families of invariants* - separate ghost names - and a caller at level
  [i] hands a callee at level [j ≤ i] strictly fewer of them.  That is
  [lvs_below], and it is why the port's [verus_halt_wsat] would have to become
  a chain: a single family cannot be read at two interpretations at once.

  ** The language

  [nola.lrust], not [nola.verus_halt.lang].  The thesis keeps the heap in the
  *state interpretation* and only the invariants in [Winv], and this file
  does the same; the port's own language keeps guards over [verus_halt_WGuard]
  in the heap's read and write banks, which would level the heap too.
  Separating them is the point, so the demonstration uses the language in
  which they are already separate.

  ** What is here and what is not

  Types are [unit], [nat], [ref°ₖ T], [T →ⱼ U] and [listₖ T]: enough for
  Landin's knot, which is what the stratification exists to rule out, and
  enough for (5.1)'s infinite singly linked list, which is what the
  guardedness condition exists to allow.

  [listₖ T] is a *constructor* rather than a general [rec Xⱼ. Tⱼ], and the
  reason is worth stating, because it is the same reason the thesis's
  guardedness condition works.  A general [rec] is interpreted by
  substituting, [⟦rec Xⱼ.Tⱼ⟧ᵢ ≜ ⟦Tⱼ[rec/X]⟧ⱼ], and mechanizing that needs
  a measure on types that descends through substitution - which it does
  *because* every recursive occurrence is guarded by [ref], whose
  interpretation (5.5) never looks at the body.  Taking the guarded
  unfolding as primitive makes [⟦listₖ T⟧] outright non-recursive: two
  reference clauses holding *syntax*.  Everything the condition is for is
  then visible, and the substitution machinery is not needed.

  Subtyping is here: [≤-refl], [≤-trans], the level conversion, [≤-→] and
  [≤-ref] - and [≤-ref] *used coinductively*, which is § 5.1 fn. 1 and
  § 5.3 fn. 4, and which is what the induction-hypothesis parameter of
  [subty] is for.

  The thesis's closing example is here too, in semantic form
  ([twp_iter_list]): an arbitrary terminating function iterated a bounded
  number of times over a list that may be *cyclic*.

  Products, intersections, universals and existentials are not here.

  ** Reading this beside [typing/rec.v]

  The two files reach the same conclusion from opposite directions, and
  reading them together is the point of having both.

  [rec.v] proves subtyping of the port's recursive types by *induction on
  the depth*, and records that it needed neither coinduction nor [Deriv],
  because the port's guarded formers carry an index to descend on and
  [type_incl] is already quantified over every candidate.  Here there is
  no index - the thesis's [rec] is plain substitution - so the loop is cut
  coinductively, by [Deriv_ind], exactly as § 5.1 fn. 1 says.

  And [rec.v]'s owning pointer had no subtyping rule at all until its
  pointee moved from a bare invariant token to a *stored guard*, because a
  token names the formula it holds.  (5.5) is the same move: the reference
  stores a different type and ties it to the declared one with two
  derivability assertions.  [subty_ref] here is three lines of
  transitivity because of it. *)

From iris.proofmode Require Import proofmode.
From nola.bi Require Import internal modw wpw deriv.
From nola.iris Require Import sinv.
From nola.verus_halt.typing Require Import levels.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From nola.lrust Require Import notation proofmode lifting adequacy.
From nola.lrust Require Import tactics.
Import ModwNotation WpwNotation iPropAppNotation DsemNotation.

(** ** Leveled types

  The thesis's [Typᵢ], with the level carried by a well-formedness
  predicate rather than by the type's own index, so that one inductive
  serves every level. *)
Inductive styp : Type :=
| (** [unit] *) tunit
| (** [nat] *) tnat
| (** [ref°ₖ T]: a shared mutable reference at offset [o] whose body type
    is at level [k].  (5.5): the body level is unconstrained by the
    surrounding level, because the reference's interpretation never
    interprets the body. *) tref (o : Z) (k : nat) (T : styp)
| (** [T →ⱼ U]: a function whose *execution* level is [j ≤ i] *)
  tfn (j : nat) (T U : styp)
| (** [listₖ T ≜ rec Xₖ. ref⁰ₖ T ∧ ref¹ₖ Xₖ] (5.1), the thesis's infinite
    singly linked list.

    A constructor rather than a general [rec]: the recursive occurrence of
    [Xₖ] sits under [ref¹], so by (5.5) it is never semantically
    interpreted, and the interpretation below is not recursive at all. *)
  tlist (k : nat) (T : styp).

(** [twf i T]: [T ∈ Typᵢ] *)
Fixpoint twf (i : nat) (T : styp) : Prop :=
  match T with
  | tunit | tnat => True
  | tref _ k T => twf k T
  | tfn j T U => (j ≤ i)%nat ∧ twf i T ∧ twf i U
  | tlist k T => twf k T
  end.

(** "We can always convert a type [Tᵢ] into a type [Tⱼ] of a higher level
  [j ≥ i]" *)
Lemma twf_mono T : ∀ i i', (i ≤ i')%nat → twf i T → twf i' T.
Proof.
  induction T as [| |o k T IH|j T IHT U IHU|k T IH]; simpl; intros i i' Hle;
    [done|done|done| |done].
  intros (?&?&?). split; [lia|]. split; [by apply (IHT i)|by apply (IHU i)].
Qed.

(** The formulas the level invariants hold.

  The thesis's [nPropᵢ] for this type system is exactly [ℓ ↦ T] (5.2), so
  the formula language is a pair of a location and a *syntactic* type -
  no domain equation, and no [cif].  That is the whole reason the thesis's
  function type poses no realizability problem and the port's does: there,
  a type is syntax. *)
Notation tfmlO := (leibnizO (loc * styp)).
Notation tFML := (constOF tfmlO).

(** ** The judgment

  The thesis's [Judg ∋ Tᵢ ≤̇ Uⱼ] (§ 5.3): a *syntactic* subtyping judgment
  between two types at two levels.  There is exactly one judgment, so no
  [inJ] plumbing is needed. *)
Definition sJUDG : ofe := leibnizO (nat * styp * nat * styp)%type.
Definition subJ (i : nat) (T : styp) (j : nat) (U : styp) : sJUDG :=
  (i, T, j, U).

Section strat.
  Context `{!lrustGS_gen HasNoLc Σ, !sinvGS tFML Σ}.
  Local Hint Constructors base_step un_op_eval bin_op_eval lit_neq lit_eq
    : core.
  (** One ghost name per level.  [levels.v]'s [lvs_names_alloc] produces
    them, and the interpretation below mentions them, which is why the
    names have to come first. *)
  Context (γs : list gname).
  Notation SEM := (styp -d> val -d> iProp Σ).

  Implicit Type (T U : styp) (i j k : nat) (v u w : val)
    (δ : sJUDG -n> iProp Σ).

  (** *** The interpretation, level by level *)

  Definition nthsem (l : list SEM) (k : nat) : SEM :=
    nth k l (λ _ _, False%I).

  (** (5.2): [⟦ℓ ↦ T⟧*ₖ ≜ ∃w. ℓ ↦ w ∗ ⟦T⟧ₖ w] *)
  Definition smf_of (l : list SEM) : nat → positive → (loc * styp) → iProp Σ :=
    λ k _ lT, (∃ w, lT.1 ↦ w ∗ nthsem l k lT.2 w)%I.

  (** (5.5): the reference type.

    The stored type [U] is not the declared type [T]; the two are tied by
    derivability assertions, which is what lets [≤-ref] retarget a
    reference that an invariant token could not.  Note what is *absent*:
    no [⟦ ⟧ₖ] anywhere.  This clause is a leaf of the recursion, which is
    why [listₖ] below can mention itself inside it. *)
  Definition refsem δ (o : Z) k T v : iProp Σ :=
    (∃ (lo : loc) (n : positive) (k' : nat) (γ : gname) (U : styp),
      ⌜v = #lo⌝ ∗ ⌜(k' ≤ k)%nat⌝ ∗ ⌜γs !! k' = Some γ⌝ ∗
      □ δ (subJ k T k' U) ∗ □ δ (subJ k' U k T) ∗
      lv_tok γ n (lo +ₗ o, U))%I.

  #[export] Instance refsem_persistent {δ o k T v} :
    Persistent (refsem δ o k T v) := _.
  Lemma refsem_loc {δ o k T v} : refsem δ o k T v ⊢ ⌜∃ lo : loc, v = #lo⌝.
  Proof.
    iIntros "(%lo & %n & %k' & %γ & %U & -> & _)". iPureIntro. by exists lo.
  Qed.

  (** The value interpretation at a level whose *lower* levels are given by
    [l].  Only the function type looks at [l], and only through the world
    satisfaction of its body - which is (5.4)'s well-formedness. *)
  Definition tsem_gen δ (l : list SEM) : SEM :=
    fix go T v : iProp Σ :=
      match T with
      | tunit => ⌜v = #☠⌝%I
      | tnat => (∃ n : Z, ⌜v = #n⌝)%I
      | tref o k T => refsem δ o k T v
      | tfn j T U => (⌜(j ≤ length l)%nat⌝ ∗
          □ ∀ u, go T u -∗
            WP[lvs_below γs (smf_of l) j] App (of_val v) [of_val u]
              [{ w, go U w }])%I
      | tlist k T => (refsem δ 0 k T v ∗ refsem δ 1 k (tlist k T) v)%I
      end.

  (** [tsems δ i = [⟦⟧₀ᵟ; …; ⟦⟧_{i-1}ᵟ]], by structural recursion; the
    level recursion of (5.4) in the form Coq accepts. *)
  Fixpoint tsems δ (i : nat) : list SEM :=
    match i with
    | O => @nil SEM
    | S i' => (tsems δ i' ++ cons (tsem_gen δ (tsems δ i')) nil)%list
    end.
  (** [⟦⟧ᵢᵟ] *)
  Definition tsem δ (i : nat) : SEM := tsem_gen δ (tsems δ i).

  Lemma tsems_length δ (i : nat) : length (tsems δ i) = i.
  Proof. induction i as [|i IH]=>//=. rewrite length_app IH /=. lia. Qed.
  Lemma tsems_nth {δ i k} : (k < i)%nat → nthsem (tsems δ i) k = tsem δ k.
  Proof.
    move: k. induction i as [|i IH]=> k Hk; [lia|]=>/=.
    rewrite /nthsem /=. case (decide (k < i)%nat)=> Hki.
    - rewrite app_nth1; [|rewrite tsems_length; lia]. by apply (IH k).
    - have -> : k = i by lia.
      rewrite app_nth2; [|rewrite tsems_length; lia].
      by rewrite tsems_length Nat.sub_diag.
  Qed.

  (** The global family: level [k] interprets [ℓ ↦ T] by [⟦T⟧ₖᵟ]. *)
  Definition tsmf δ : nat → positive → (loc * styp) → iProp Σ :=
    λ k _ lT, (∃ w, lT.1 ↦ w ∗ tsem δ k lT.2 w)%I.
  (** [∗_{k<j} Winv_k]: the world satisfaction of execution level [j] *)
  Definition Wlv δ j : iProp Σ := lvs_below (FML:=tFML) γs (tsmf δ) j.

  Lemma smf_of_tsems {δ i k} : (k < i)%nat → smf_of (tsems δ i) k = tsmf δ k.
  Proof. move=> Hk. rewrite /smf_of /tsmf (tsems_nth Hk) //. Qed.
  Lemma Wlv_tsems {δ i j} : (j ≤ i)%nat →
    lvs_below (FML:=tFML) γs (smf_of (tsems δ i)) j ⊣⊢ Wlv δ j.
  Proof.
    move=> ?. apply lvs_below_ext=> k ?. apply smf_of_tsems. lia.
  Qed.

  (** Transporting a weakest precondition along an equivalence of world
    satisfactions.  [twpw_proper] is stated for the eta-expanded
    [(λ W, twpw W)] and will not apply here, so this goes through
    [twpw_incl_fupd], as [twpw_lvs_le] does. *)
  Lemma twpw_wsat_eq {W W' : iProp Σ} (eq : W ⊣⊢ W') {s E e Φ} :
    WP[W] e @ s; E [{ Φ }] ⊢ WP[W'] e @ s; E [{ Φ }].
  Proof.
    iIntros "twp". iApply (twpw_incl_fupd (E:=E) with "[] twp"); [done|].
    iIntros "!> W'". iModIntro.
    iDestruct (bi.equiv_entails_1_2 _ _ eq with "W'") as "W". iFrame "W".
    iIntros "W !>". by iApply (bi.equiv_entails_1_1 _ _ eq with "W").
  Qed.

  (** (5.4), with the world satisfaction in its global form *)
  Lemma tsem_fn {δ i j T U v} : (j ≤ i)%nat →
    tsem δ i (tfn j T U) v ⊣⊢
      □ ∀ u, tsem δ i T u -∗ WP[Wlv δ j] App (of_val v) [of_val u]
        [{ w, tsem δ i U w }].
  Proof.
    move=> Hji. rewrite /tsem /=. rewrite tsems_length.
    iSplit.
    - iIntros "[_ #f] !>" (u) "Tu". iApply (twpw_wsat_eq (Wlv_tsems Hji)).
      by iApply "f".
    - iIntros "#f". iSplit; [done|]. iIntros "!>" (u) "Tu".
      iApply (twpw_wsat_eq (symmetry (Wlv_tsems Hji))). by iApply "f".
  Qed.
  (** The two reference-shaped clauses, unfolded *)
  Lemma tsem_ref {δ i o k T v} : tsem δ i (tref o k T) v = refsem δ o k T v.
  Proof. done. Qed.
  Lemma tsem_list {δ i k T v} :
    tsem δ i (tlist k T) v =
      (refsem δ 0 k T v ∗ refsem δ 1 k (tlist k T) v)%I.
  Proof. done. Qed.

  (** Lemma 5.1: the semantics of a type is persistent, at every [δ] *)
  #[export] Instance tsem_persistent {δ i T v} : Persistent (tsem δ i T v).
  Proof. rewrite /tsem. case: T=> [| |? ? ?|? ? ?|? ?] /=; exact _. Qed.

  (** A type's interpretation does not change with the level, as long as
    the level is one the type belongs to.  The thesis's silent conversion
    [Typᵢ ⊆ Typⱼ]; in the model it is an equality, because the only thing
    the level does to the interpretation is bound the function type's
    execution level. *)
  Lemma tsem_lev T : ∀ δ i i' v, (i ≤ i')%nat → twf i T →
    tsem δ i T v ⊣⊢ tsem δ i' T v.
  Proof.
    induction T as [| |o k T IH|j T IHT U IHU|k T IH]=> δ i i' v Hle Hwf;
      [done|done|done| |done].
    move: Hwf=> [Hji[HT HU]].
    rewrite (tsem_fn Hji) (tsem_fn (Nat.le_trans _ _ _ Hji Hle)).
    iSplit.
    - iIntros "#f !>" (u) "Tu".
      iDestruct (bi.equiv_entails_1_2 _ _ (IHT δ i i' u Hle HT) with "Tu")
        as "Tu'".
      iDestruct ("f" with "Tu'") as "twp". iApply (twp_wand with "twp").
      iIntros (w) "H".
      by iApply (bi.equiv_entails_1_1 _ _ (IHU δ i i' w Hle HU)).
    - iIntros "#f !>" (u) "Tu".
      iDestruct (bi.equiv_entails_1_1 _ _ (IHT δ i i' u Hle HT) with "Tu")
        as "Tu'".
      iDestruct ("f" with "Tu'") as "twp". iApply (twp_wand with "twp").
      iIntros (w) "H".
      by iApply (bi.equiv_entails_1_2 _ _ (IHU δ i i' w Hle HU)).
  Qed.

  (** *** The judgment's semantics, and hence [der]

    § 5.3: [⟦Tᵢ ≤̇ Uⱼ⟧ᵟ ≜ ∀v. ⟦Tᵢ⟧ᵢᵟ v -∗ ⟦Uⱼ⟧ⱼᵟ v].  It *applies* [δ] and
    never quantifies over it, which is Nola's construction order
    ([Csem] → [Jsem] → [Deriv], [der]) and the reason there is no cycle. *)
  #[local] Program Instance sJsem : Jsem sJUDG (iProp Σ) :=
    @DSEM sJUDG sJUDG (iProp Σ)
      (λ δ J, let '(i, T, j, U) := J in
        ∀ v, tsem δ i T v -∗ tsem δ j U v)%I _.

  Lemma subJ_sem {δ i T j U} :
    ⟦ subJ i T j U ⟧(δ) ⊣⊢ ∀ v, tsem δ i T v -∗ tsem δ j U v.
  Proof. done. Qed.

  (** (5.6) and (5.7): reflexivity and transitivity of derivability *)
  Lemma subJ_refl {ih δ} `{!Deriv ih δ} {i T} : ⊢ δ (subJ i T i T).
  Proof.
    iApply Deriv_factor'. iIntros (δ' _ _ _). rewrite subJ_sem.
    by iIntros (v) "$".
  Qed.
  Lemma subJ_trans {ih δ} `{!Deriv ih δ} {i T j U k V} :
    δ (subJ i T j U) -∗ δ (subJ j U k V) -∗ δ (subJ i T k V).
  Proof.
    iIntros "J J'". iApply (Deriv_map2 with "[] J J'"). iIntros (δ' _ _ _).
    rewrite !subJ_sem. iIntros "f g" (v) "T". iApply "g". by iApply "f".
  Qed.

  (** *** Subtyping

    [⟦T ≤ U⟧ ≜ ∀δ ∈ Deriv_φ, v. □ (⟦T⟧ᵟ v -∗ ⟦U⟧ᵟ v)], quantified over the
    good derivability predicates - which is what (5.8) needs, and which is
    parameterized by an induction hypothesis [φ] so that [≤-ref] can be
    used coinductively (§ 5.1 fn. 1, § 5.3 fn. 4). *)
  Definition subty (ih : (sJUDG -n> iProp Σ) → Prop) i T j U : iProp Σ :=
    (□ ∀ δ, ⌜Deriv ih δ⌝ → ∀ v, tsem δ i T v -∗ tsem δ j U v)%I.

  #[export] Instance subty_persistent {ih i T j U} :
    Persistent (subty ih i T j U) := _.

  (** The trivial induction hypothesis, i.e. no coinduction *)
  Definition ihTrue : (sJUDG -n> iProp Σ) → Prop := λ _, True.

  (** (5.8): a subtyping fact becomes a derivability assertion *)
  Lemma subty_derJ {ih δ} `{!Deriv ih δ} {i T j U} :
    subty ih i T j U ⊢ □ δ (subJ i T j U).
  Proof.
    iIntros "#s !>". iApply Deriv_factor'. iIntros (δ' ? _ _).
    rewrite subJ_sem. by iApply "s".
  Qed.
  (** (5.9): [der] is sound *)
  Lemma subJ_der {i T j U v} :
    der (subJ i T j U) -∗ tsem der i T v -∗ tsem der j U v.
  Proof. iIntros "J". iDestruct (der_sound with "J") as "f". iApply "f". Qed.

  Lemma subty_refl {ih i T} : ⊢ subty ih i T i T.
  Proof. by iIntros "!>" (δ ? v) "$". Qed.
  Lemma subty_trans {ih i T j U k V} :
    subty ih i T j U -∗ subty ih j U k V -∗ subty ih i T k V.
  Proof.
    iIntros "#s #s' !>" (δ ? v) "T". iApply ("s'" with "[//]").
    by iApply "s".
  Qed.
  (** The level conversion, as a subtyping fact *)
  Lemma subty_lev {ih i i' T} : (i ≤ i')%nat → twf i T →
    ⊢ subty ih i T i' T.
  Proof.
    move=> Hle Hwf. iIntros "!>" (δ ? v) "T".
    by iApply (bi.equiv_entails_1_1 _ _ (tsem_lev T δ i i' v Hle Hwf)).
  Qed.
  (** ...and back down, which the level conversion being an [⊣⊢] allows *)
  Lemma subty_lev' {ih i i' T} : (i ≤ i')%nat → twf i T →
    ⊢ subty ih i' T i T.
  Proof.
    move=> Hle Hwf. iIntros "!>" (δ ? v) "T".
    by iApply (bi.equiv_entails_1_2 _ _ (tsem_lev T δ i i' v Hle Hwf)).
  Qed.

  (** § 5.1's [≤-→]: the argument contravariant, the result covariant, and
    the execution level relaxable.  The level part is [twpw_lvs_le] and
    nothing else. *)
  Lemma subty_fn {ih i j j' T T' U U'} :
    (j ≤ j')%nat → (j' ≤ i)%nat →
    subty ih i T' i T -∗ subty ih i U i U' -∗
    subty ih i (tfn j T U) i (tfn j' T' U').
  Proof.
    move=> Hjj' Hj'i. iIntros "#sT #sU !>" (δ Hδ v).
    rewrite (tsem_fn (Nat.le_trans _ _ _ Hjj' Hj'i)) (tsem_fn Hj'i).
    iIntros "#f !>" (u) "T'u".
    iDestruct ("sT" with "[//] T'u") as "Tu".
    iApply (twpw_lvs_le (FML:=tFML) Hjj').
    iDestruct ("f" with "Tu") as "twp". iApply (twp_wand with "twp").
    iIntros (w) "Uw". by iApply ("sU" with "[//]").
  Qed.

  (** § 5.1's [≤-ref], the rule (5.5) exists for.

    The stored type is retargeted by *composing derivability assertions*,
    never by changing an invariant token.  [typing/rec.v] records the same
    fact from the other side: the port's owning pointer had no subtyping
    rule until its pointee moved behind a stored guard, because a token
    names the formula it holds. *)
  Lemma subty_ref {ih o i i' k k' T U} :
    (k ≤ k')%nat → twf k U →
    subty ih k T k U -∗ subty ih k U k T -∗
    subty ih i (tref o k T) i' (tref o k' U).
  Proof.
    move=> Hkk' HU. iIntros "#sTU #sUT !>" (δ Hδ v).
    have ? : Deriv ih δ := Hδ.
    iDestruct (subty_derJ (δ:=δ) with "sTU") as "#jTU".
    iDestruct (subty_derJ (δ:=δ) with "sUT") as "#jUT".
    iAssert (subty ih k U k' U) as "#sUU'"; [iApply (subty_lev Hkk' HU)|].
    iAssert (subty ih k' U k U) as "#sU'U"; [iApply (subty_lev' Hkk' HU)|].
    iDestruct (subty_derJ (δ:=δ) with "sUU'") as "#jUU'".
    iDestruct (subty_derJ (δ:=δ) with "sU'U") as "#jU'U".
    rewrite !tsem_ref /refsem.
    iIntros "(%lo & %n & %k0 & %γ & %V & -> & %Hk0 & %Hγ & #j1 & #j2 & #tok)".
    iExists lo, n, k0, γ, V. iSplit; [done|]. iSplit; [iPureIntro; lia|].
    iSplit; [done|]. iFrame "tok". iSplit; iModIntro.
    - iApply (subJ_trans with "jU'U"). iApply (subJ_trans with "jUT j1").
    - iApply (subJ_trans with "j2"). iApply (subJ_trans with "jTU jUU'").
  Qed.

  (** *** [≤-ref] used coinductively: two list types related

    § 5.1 fn. 1 allows [≤-ref] to be used *coinductively*, and the example
    it gives is [listᵢ T ≤ listⱼ U] from [T ≤ U] and [U ≤ T].  § 5.3 fn. 4
    says what that costs the model: the subtyping judgment quantifies over
    [Deriv_φ] rather than [Deriv], with [φ] the coinductive hypotheses.
    [subty] above already carries that parameter; here is the use.

    One deviation from the footnote, and it is forced rather than a gap in
    the mechanization.  The footnote also relaxes the level, [i ≤ j].  But
    [≤-ref] needs the body types related in *both* directions, so the tail
    reference of [listᵢ T] needs both [listᵢ T ≤ listⱼ U] and
    [listⱼ U ≤ listᵢ T]; the second is itself a [≤-ref] at the tail and so
    asks for [j ≤ i].  The two together force [i = j], which is what is
    proved here.  Raising the level of a list is a different fact, and not
    one [≤-ref] gives. *)
  Local Lemma tlist_sub_body {ih δ} `{!Deriv ih δ} {i i' k T U} :
    □ δ (subJ k T k U) -∗ □ δ (subJ k U k T) -∗
    □ δ (subJ k (tlist k T) k (tlist k U)) -∗
    □ δ (subJ k (tlist k U) k (tlist k T)) -∗
    ∀ v, tsem δ i (tlist k T) v -∗ tsem δ i' (tlist k U) v.
  Proof.
    iIntros "#hTU #hUT #lTU #lUT" (v). rewrite !tsem_list.
    iIntros "[#Hd #Tl]". iSplit.
    - iDestruct "Hd" as
        "(%lo & %n & %k0 & %γ & %V & -> & %Hk0 & %Hγ & #j1 & #j2 & #tok)".
      iExists lo, n, k0, γ, V. do 3 (iSplit; [done|]). iFrame "tok".
      iSplit; iModIntro.
      + iApply (subJ_trans with "hUT j1").
      + iApply (subJ_trans with "j2 hTU").
    - iDestruct "Tl" as
        "(%lo & %n & %k0 & %γ & %V & -> & %Hk0 & %Hγ & #j1 & #j2 & #tok)".
      iExists lo, n, k0, γ, V. do 3 (iSplit; [done|]). iFrame "tok".
      iSplit; iModIntro.
      + iApply (subJ_trans with "lUT j1").
      + iApply (subJ_trans with "j2 lTU").
  Qed.

  (** The coinductive hypothesis: both list judgments hold at [δ]. *)
  Local Definition lih k T U : (sJUDG -n> iProp Σ) → Prop := λ δ,
    (⊢ δ (subJ k (tlist k T) k (tlist k U))) ∧
    (⊢ δ (subJ k (tlist k U) k (tlist k T))).

  (** The coinduction itself.  [Deriv_ind] is what turns "assume the goal"
    into a legitimate induction on the derivability candidate: the
    hypothesis is available at every candidate the factored judgment
    quantifies over, which is exactly where the tail reference needs
    it. *)
  Local Lemma lih_holds {k T U} :
    (∀ ih', ⊢ subty ih' k T k U) → (∀ ih', ⊢ subty ih' k U k T) →
    ∀ ih δ, Deriv ih δ → lih k T U δ.
  Proof.
    move=> sTU sUT ih δ Hδ. have ? : Deriv ih δ := Hδ.
    apply (Deriv_ind (lih k T U))=> δ' Hδ'.
    have ? : Deriv (λ δ'', lih k T U δ'' ∧ ih δ'') δ' := Hδ'.
    split; iApply Deriv_factor'; iIntros (δ'' Hδ'' [[Hl1 Hl2] _] _);
      have ? : Deriv (λ δ3, lih k T U δ3 ∧ ih δ3) δ'' := Hδ'';
      rewrite subJ_sem;
      iDestruct (subty_derJ (δ:=δ'') with "[]") as "#hTU"; [iApply sTU| |
        iApply sTU|];
      iDestruct (subty_derJ (δ:=δ'') with "[]") as "#hUT"; [iApply sUT| |
        iApply sUT|].
    - iApply (tlist_sub_body with "hTU hUT [] []");
        [iModIntro; iApply Hl1|iModIntro; iApply Hl2].
    - iApply (tlist_sub_body with "hUT hTU [] []");
        [iModIntro; iApply Hl2|iModIntro; iApply Hl1].
  Qed.

  (** [listₖ T ≤ listₖ U], coinductively *)
  Lemma subty_list {i i' k T U} :
    (∀ ih', ⊢ subty ih' k T k U) → (∀ ih', ⊢ subty ih' k U k T) →
    ⊢ subty ihTrue i (tlist k T) i' (tlist k U).
  Proof.
    move=> sTU sUT. iIntros "!>" (δ Hδ). have ? : Deriv ihTrue δ := Hδ.
    move: (lih_holds sTU sUT ihTrue δ Hδ)=> [Hl1 Hl2].
    iDestruct (subty_derJ (δ:=δ) with "[]") as "#hTU"; [iApply sTU|].
    iDestruct (subty_derJ (δ:=δ) with "[]") as "#hUT"; [iApply sUT|].
    iApply (tlist_sub_body with "hTU hUT [] []");
      [iModIntro; iApply Hl1|iModIntro; iApply Hl2].
  Qed.

  (** An instance.  The grammar here has no intersections, so it has no
    two *distinct* types that are subtypes of each other and the instance
    comes out reflexive - but the derivation does not: it goes through
    [lih_holds], and the tail reference is discharged by the coinductive
    hypothesis, not by reflexivity. *)
  Lemma subty_list_nat {i i' k} :
    ⊢ subty ihTrue i (tlist k tnat) i' (tlist k tnat).
  Proof. apply subty_list; move=> ?; iApply subty_refl. Qed.

  (** *** The typing judgment

    (5.2)'s [𝛤 ⊢ e :ᵢ T], for a closed expression: a *total* weakest
    precondition over [∗_{k<i} Winv_k], at the best derivability predicate
    [der].  Totality is strong normalization. *)
  Definition typed i (e : expr) T : iProp Σ :=
    WP[Wlv der i] e [{ v, tsem der i T v }].

  (** [ty-≤] *)
  Lemma typed_sub {i T U e} :
    subty ihTrue i T i U -∗ typed i e T -∗ typed i e U.
  Proof.
    iIntros "#s twp". rewrite /typed. iApply (twp_wand with "twp").
    iIntros (v) "T". iApply ("s" with "[] T"). iPureIntro. exact _.
  Qed.

  (** [ty-lev]: the execution level can be raised.  Two halves - the world
    satisfaction grows ([twpw_lvs_le]) and the type's interpretation does
    not change ([tsem_lev]). *)
  Lemma typed_lev {i i' e T} : (i ≤ i')%nat → twf i T →
    typed i e T ⊢ typed i' e T.
  Proof.
    move=> Hle Hwf. rewrite /typed. iIntros "twp".
    iApply (twpw_lvs_le (FML:=tFML) Hle). iApply (twp_wand with "twp").
    iIntros (v) "H".
    by iApply (bi.equiv_entails_1_1 _ _ (tsem_lev T der i i' v Hle Hwf)).
  Qed.

  (** A value of the type is typed *)
  Lemma typed_val {i v T} : tsem der i T v ⊢ typed i (of_val v) T.
  Proof. rewrite /typed. iIntros "T". by iApply twp_value. Qed.

  Lemma typed_nat {i} (n : Z) : ⊢ typed i (of_val (LitV (LitInt n))) tnat.
  Proof. iApply typed_val. by iExists n. Qed.
  Lemma typed_unit {i} : ⊢ typed i (of_val (LitV LitPoison)) tunit.
  Proof. by iApply typed_val. Qed.

  (** Sequencing: every other rule is this one plus a step *)
  Lemma typed_bind {i e K T U} :
    typed i e T -∗ (∀ v, tsem der i T v -∗ typed i (fill K (of_val v)) U) -∗
    typed i (fill K e) U.
  Proof.
    rewrite /typed. iIntros "twp →". iApply twp_bind.
    iApply (twp_wand with "twp"). iIntros (v) "T". by iApply "→".
  Qed.

  (** [ty-fun]: a function value, typed at *any* level, whose body is typed
    at the execution level the arrow carries *)
  Lemma typed_fun {i i' x e T U} `{!Closed (<> :b: [x]%binder +b+ []) e} :
    (i ≤ i')%nat → twf i T → twf i U →
    □ (∀ u : val, tsem der i T u -∗ typed i (subst' x u e) U) ⊢
      typed i' (of_val (λ: [x], e)%V) (tfn i T U).
  Proof.
    move=> Hle HT HU. iIntros "#f". iApply typed_val.
    rewrite (tsem_fn Hle). iIntros "!>" (u) "Tu".
    iDestruct (bi.equiv_entails_1_2 _ _ (tsem_lev T der i i' u Hle HT)
      with "Tu") as "Tu'".
    iDestruct ("f" with "Tu'") as "twp". rewrite /typed.
    wp_rec. iApply (twp_wand with "twp"). iIntros (w) "H".
    by iApply (bi.equiv_entails_1_1 _ _ (tsem_lev U der i i' w Hle HU)).
  Qed.

  (** [ty-call] *)
  Lemma typed_call {i e1 e2 T U} :
    typed i e1 (tfn i T U) -∗ typed i e2 T -∗ typed i (App e1 [e2]) U.
  Proof.
    iIntros "f a".
    iApply (typed_bind (K:=[AppLCtx [e2]]) with "f"). iIntros (v1) "F /=".
    iDestruct (bi.equiv_entails_1_1 _ _ (tsem_fn (le_n i)) with "F") as "#F'".
    iApply (typed_bind (K:=[AppRCtx v1 [] []]) with "a"). iIntros (v2) "A /=".
    rewrite /typed. by iApply "F'".
  Qed.

  (** *** References

    Reading and writing, as lifting rules: the invariant is opened inside
    the step, because [sinv] has no masks, and the content comes back at
    level [k']'s interpretation, never level [j]'s.  That *is* the cut.
    The stored type is converted to the declared one by [der]'s soundness
    (5.9) - which is the one place (5.5)'s indirection has to be paid
    for. *)
  Lemma twp_read_lv {j o k T s E} {lo : loc} : (k < j)%nat →
    [[{ refsem der o k T #lo }]][Wlv der j]
      Read ScOrd (Lit $ LitLoc (lo +ₗ o)) @ s; E
    [[{ w, RET w; tsem der k T w }]].
  Proof.
    move=> Hk. iIntros (Φ)
      "(%lo0 & %n & %k0 & %γ & %U & %Heq & %Hk0 & %Hγ & #j1 & #j2 & #tok) →Φ".
    move: Heq=> [=<-]. have Hk0j : (k0 < j)%nat by lia.
    iApply twp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ1 ???) "[W Hσ]".
    iDestruct (lvs_below_acc (FML:=tFML) Hk0j Hγ with "tok W") as "[Hc →W]".
    rewrite /tsmf /=. iDestruct "Hc" as (w) "[↦ #Uw]".
    iDestruct (heap_read with "Hσ ↦") as %[m Hm].
    iModIntro. iSplit.
    { iPureIntro. do 3 eexists. by apply (ReadScS (lo +ₗ o) m w σ1). }
    iIntros (?????) "!>". inv_base_step.
    iSplit; [done|]. iSplit; [done|]. rewrite to_of_val /=.
    iSplitR "→Φ"; last first.
    { iApply "→Φ". iApply (subJ_der with "j2 Uw"). }
    iSplitL "→W ↦"; [|iFrame "Hσ"]. iApply "→W". iExists w.
    by iFrame "↦ Uw".
  Qed.

  Lemma twp_write_lv {j o k T s E} {lo : loc} (w : val) : (k < j)%nat →
    [[{ refsem der o k T #lo ∗ tsem der k T w }]][Wlv der j]
      Write ScOrd (Lit $ LitLoc (lo +ₗ o)) (of_val w) @ s; E
    [[{ RET #☠; True }]].
  Proof.
    move=> Hk. iIntros (Φ)
      "[(%lo0 & %n & %k0 & %γ & %U & %Heq & %Hk0 & %Hγ & #j1 & #j2 & #tok)
        #Tw] →Φ".
    move: Heq=> [=<-]. have Hk0j : (k0 < j)%nat by lia.
    iApply twp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ1 ???) "[W Hσ]".
    iDestruct (lvs_below_acc (FML:=tFML) Hk0j Hγ with "tok W") as "[Hc →W]".
    rewrite /tsmf /=. iDestruct "Hc" as (w0) "[↦ _]".
    iDestruct (heap_read_1 with "Hσ ↦") as %Hm.
    iMod (heap_write _ _ _ w with "Hσ ↦") as "[Hσ ↦]".
    iModIntro. iSplit.
    { iPureIntro. do 3 eexists.
      apply (WriteScS (lo +ₗ o) (of_val w) w w0 σ1); [exact: to_of_val|done]. }
    iIntros (?????) "!>". inv_base_step.
    iSplit; [done|]. iSplit; [done|]=>/=.
    iSplitR "→Φ"; last first. { by iApply "→Φ". }
    iSplitL "→W ↦"; [|iFrame "Hσ"]. iApply "→W". iExists w. iFrame "↦".
    iApply (subJ_der with "j1 Tw").
  Qed.

  (** [ty-ref], [ty-load], [ty-store].  Each asks [k < j]: the execution
    level must exceed the reference's body level.  That is the syntactic
    side of the same cut. *)
  Definition new_ref : val :=
    λ: ["v"], let: "r" := Alloc #1 in "r" <-ˢᶜ "v";; "r".

  Lemma typed_ref {k j e T} : twf k T → (k < j)%nat → (k < length γs)%nat →
    typed j e T -∗ typed j (new_ref [e]) (tref 0 k T).
  Proof.
    move=> HT Hkj Hlen.
    have [γ Hγ] : is_Some (γs !! k) by apply lookup_lt_is_Some.
    iIntros "e". iApply (typed_bind (K:=[AppRCtx new_ref [] []]) with "e").
    iIntros (v) "Tv /=". rewrite /typed.
    rewrite -(tsem_lev T der k j v (Nat.lt_le_incl _ _ Hkj) HT).
    wp_rec. wp_apply twp_alloc; [lia|done|].
    iIntros (lo sz) "[%Hsz [† ↦]]". have -> : sz = 1%nat by lia.
    rewrite heap_pointsto_vec_singleton. wp_let.
    iApply twpw_fupdw_nonval; [done|]. wp_write. iIntros "W".
    iDestruct (lvs_below_alloc (FML:=tFML) (lo +ₗ 0, T) Hkj Hγ with "W")
      as (I) "cl".
    iMod ("cl" $! (fresh I) with "[%]") as "[#tok →W]"; [exact: is_fresh|].
    iDestruct ("→W" with "[↦ Tv]") as "W".
    { rewrite /tsmf /= shift_loc_0. iExists v. by iFrame "↦ Tv". }
    iModIntro. iFrame "W". rewrite /tsem /= /refsem.
    iExists lo, (fresh I), k, γ, T. iFrame "tok".
    do 3 (iSplit; [done|]). iSplit; iModIntro; iApply subJ_refl.
  Qed.

  Lemma typed_load {o k j e T} : twf k T → (k < j)%nat →
    typed j e (tref o k T) -∗ typed j (!ˢᶜ (e +ₗ #o)) T.
  Proof.
    move=> HT Hkj. iIntros "e".
    iApply (typed_bind (K:=[BinOpLCtx OffsetOp #o; ReadCtx ScOrd]) with "e").
    iIntros (v) "#R /=". rewrite /typed.
    iDestruct (refsem_loc with "R") as %[lo ->]. wp_op.
    wp_apply (twp_read_lv Hkj with "R"). iIntros (w) "Tw".
    by rewrite (tsem_lev T der k j w (Nat.lt_le_incl _ _ Hkj) HT).
  Qed.

  Lemma typed_store {o k j e1 e2 T} : twf k T → (k < j)%nat →
    typed j e1 (tref o k T) -∗ typed j e2 T -∗
    typed j ((e1 +ₗ #o) <-ˢᶜ e2) tunit.
  Proof.
    move=> HT Hkj. iIntros "e1 e2".
    iApply (typed_bind
      (K:=[BinOpLCtx OffsetOp #o; WriteLCtx ScOrd e2]) with "e1").
    iIntros (v1) "#R /=". iDestruct (refsem_loc with "R") as %[lo ->].
    rewrite /typed. wp_op.
    iApply (twp_bind (fill [WriteRCtx ScOrd #(lo +ₗ o)])).
    iApply (twp_wand with "e2"). iIntros (v2) "Tv /=".
    rewrite -(tsem_lev T der k j v2 (Nat.lt_le_incl _ _ Hkj) HT).
    wp_apply (twp_write_lv v2 Hkj with "[$R $Tv]"). iIntros "_". done.
  Qed.

  (** *** The list type (5.1)

    Note what is *absent*: no rule interprets the body of the tail
    reference, and no definition above recurses through it.  § 5.1's
    guardedness condition and (5.5)'s "this interpretation does not depend
    on [⟦T⟧ₖᵟ]" are the same fact, and this is where it is visible. *)
  Lemma typed_list_head {k j e T} : twf k T → (k < j)%nat →
    typed j e (tlist k T) -∗ typed j (!ˢᶜ (e +ₗ #0)) T.
  Proof.
    move=> HT Hkj. iIntros "e".
    iApply (typed_bind (K:=[BinOpLCtx OffsetOp #0; ReadCtx ScOrd]) with "e").
    iIntros (v) "#L /=". iDestruct "L" as "[#R _]".
    rewrite /typed. iDestruct (refsem_loc with "R") as %[lo ->]. wp_op.
    wp_apply (twp_read_lv Hkj with "R"). iIntros (w) "Tw".
    by rewrite (tsem_lev T der k j w (Nat.lt_le_incl _ _ Hkj) HT).
  Qed.

  Lemma typed_list_tail {k j e T} : (k < j)%nat →
    typed j e (tlist k T) -∗ typed j (!ˢᶜ (e +ₗ #1)) (tlist k T).
  Proof.
    move=> Hkj. iIntros "e".
    iApply (typed_bind (K:=[BinOpLCtx OffsetOp #1; ReadCtx ScOrd]) with "e").
    iIntros (v) "#L /=". iDestruct "L" as "[_ #R]".
    rewrite /typed. iDestruct (refsem_loc with "R") as %[lo ->]. wp_op.
    wp_apply (twp_read_lv Hkj with "R"). iIntros (w) "Tw". iExact "Tw".
  Qed.

  (** Building one, and the only way to build an *infinite* list in a
    finite heap: tie it to itself.  Both invariants are allocated before
    either is filled, because the tail's content mentions both tokens -
    the same move [nola/examples/ilist.v]'s [twp_new_ilist_cyclic]
    makes. *)
  Definition new_clist : val :=
    λ: ["v"], let: "l" := Alloc #2 in
      "l" <-ˢᶜ "v";; ("l" +ₗ #1) <-ˢᶜ "l";; "l".

  Lemma typed_clist {k j e T} : twf k T → (k < j)%nat → (k < length γs)%nat →
    typed j e T -∗ typed j (new_clist [e]) (tlist k T).
  Proof.
    move=> HT Hkj Hlen.
    have [γ Hγ] : is_Some (γs !! k) by apply lookup_lt_is_Some.
    iIntros "e". iApply (typed_bind (K:=[AppRCtx new_clist [] []]) with "e").
    iIntros (v) "Tv /=". rewrite /typed.
    rewrite -(tsem_lev T der k j v (Nat.lt_le_incl _ _ Hkj) HT).
    wp_rec. wp_apply twp_alloc; [lia|done|].
    iIntros (lo sz) "[%Hsz [† ↦]]". have -> : sz = 2%nat by lia.
    rewrite /= heap_pointsto_vec_cons heap_pointsto_vec_singleton.
    iDestruct "↦" as "[↦0 ↦1]". wp_let.
    iApply twpw_fupdw_nonval; [done|]. wp_write. wp_op. wp_write.
    iIntros "W".
    iDestruct (lvs_below_alloc (FML:=tFML) (lo +ₗ 0, T) Hkj Hγ with "W")
      as (I) "cl".
    iMod ("cl" $! (fresh I) with "[%]") as "[#tok →W]"; [exact: is_fresh|].
    iDestruct ("→W" with "[↦0 Tv]") as "W".
    { rewrite /tsmf /= shift_loc_0. iExists v. by iFrame "↦0 Tv". }
    iDestruct (lvs_below_alloc (FML:=tFML) (lo +ₗ 1, tlist k T) Hkj Hγ
      with "W") as (I') "cl'".
    iMod ("cl'" $! (fresh I') with "[%]") as "[#tok' →W]"; [exact: is_fresh|].
    iAssert (tsem der k (tlist k T) #lo) as "#L".
    { rewrite tsem_list /refsem. iSplitL.
      - iExists lo, (fresh I), k, γ, T. rewrite shift_loc_0. iFrame "tok".
        do 3 (iSplit; [done|]). iSplit; iModIntro; iApply subJ_refl.
      - iExists lo, (fresh I'), k, γ, (tlist k T). iFrame "tok'".
        do 3 (iSplit; [done|]). iSplit; iModIntro; iApply subJ_refl. }
    iDestruct ("→W" with "[↦1]") as "W".
    { rewrite /tsmf /=. iExists #lo. by iFrame "↦1 L". }
    iModIntro. by iFrame "W L".
  Qed.

  (** *** Bounded iteration over an infinite list

    § 5.1's closing example, in semantic form:

    >  f : ref⁰ᵢ T →ⱼ unit ⊢ fiter (fun (ℓ) { f(ℓ); !(ℓ+1) })
    >                          : nat × listᵢ T →ⱼ listᵢ T

    "Notably, the function f can mutate the list elements.  Recall that
    our function type and typing judgment ensure termination.  [This]
    verifies that the iteration always terminates for any function f that
    always terminates."

    The list may be *cyclic*, so the iteration is bounded by a counter
    rather than by the data; what is not bounded is [f], which is an
    arbitrary value of the function type.  That the whole thing
    terminates is the content of the total weakest precondition.

    Stated semantically rather than as a [ty-fiter] rule because the type
    language here has no products to pair the counter with the list, and
    currying a closure over a closed expression language is bookkeeping
    with nothing to show. *)
  Definition iter_list : val :=
    rec: "self" ["f"; "n"; "l"] :=
      if: "n" ≤ #0 then #☠
      else "f" ["l"];; "self" ["f"; "n" - #1; !ˢᶜ ("l" +ₗ #1)].

  Lemma twp_iter_list {j k T} {f : val} : (k < j)%nat →
    tsem der j (tfn j (tlist k T) tunit) f -∗
    ∀ (n : nat) (v : val), tsem der k (tlist k T) v -∗
      WP[Wlv der j] App (of_val iter_list)
        [of_val f; of_val (LitV (LitInt (Z.of_nat n))); of_val v]
        [{ w, tsem der j tunit w }].
  Proof.
    move=> Hkj. rewrite (tsem_fn (le_n j)). iIntros "#F" (n).
    iInduction n as [|m] "IH"; iIntros (v) "#L".
    - wp_rec. wp_op. wp_if. done.
    - wp_rec. wp_op. wp_if.
      iDestruct ("F" $! v with "L") as "callf".
      wp_apply (twp_wand with "callf"). iIntros (?) "_". wp_seq.
      wp_op. have -> : (Z.of_nat (S m) - 1)%Z = Z.of_nat m by lia.
      iDestruct "L" as "[_ #R]".
      iDestruct (refsem_loc with "R") as %[lo ->]. wp_op.
      wp_apply (twp_read_lv Hkj with "R"). iIntros (w) "#Lw".
      by iApply ("IH" with "Lw").
  Qed.

  (** The iteration, run on a cyclic list with a function that does
    nothing.  Everything about it is finite except the list. *)
  Definition unitfn : val := λ: ["x"], #☠.
  Lemma tsem_unitfn {j k T} : ⊢ tsem der j (tfn j (tlist k T) tunit) unitfn.
  Proof.
    rewrite (tsem_fn (le_n j)). iIntros "!>" (u) "_". wp_rec. done.
  Qed.

  Lemma typed_iter_clist {j k} (n : nat) :
    (k < j)%nat → (k < length γs)%nat →
    ⊢ typed j (App (of_val iter_list)
        [of_val unitfn; of_val (LitV (LitInt (Z.of_nat n)));
         new_clist [of_val (LitV (LitInt 7))]]) tunit.
  Proof.
    move=> Hkj Hlen. rewrite /typed.
    iApply (twp_bind (fill
      [AppRCtx iter_list [unitfn; LitV (LitInt (Z.of_nat n))] []])).
    iApply (twp_wand with "[]").
    { iApply (typed_clist (k:=k) (T:=tnat)); [done|done|done|].
      iApply typed_nat. }
    iIntros (v) "#L /=". iApply (twp_iter_list Hkj with "[] L").
    iApply tsem_unitfn.
  Qed.

  (** *** A function read out of a shared mutable reference, and called

    This is the shape of Landin's knot, and it is the shape the levels are
    there to control.  Both premises are forced: [ty-load] asks [k < j],
    and [ty-call] asks the arrow's execution level to be the judgment's,
    which [subty_fn] relaxes only *upwards*.  To tie the knot the function
    would have to call itself - a level-[k] body reaching a level-[k]
    reference - and [k < k] is false. *)
  Lemma typed_call_stored {k j e1 e2 T U} :
    twf k T → twf k U → (k < j)%nat →
    typed j e1 (tref 0 k (tfn k T U)) -∗ typed j e2 T -∗
    typed j (App (!ˢᶜ (e1 +ₗ #0)) [e2]) U.
  Proof.
    move=> HT HU Hkj. iIntros "e1 e2".
    iDestruct (typed_load (T:=tfn k T U) with "e1") as "f";
      [by split; [lia|]|done|].
    iDestruct (typed_sub with "[] f") as "f'"; last first.
    { iApply (typed_call with "f' e2"). }
    iApply (subty_fn (j:=k) (j':=j)); [lia|lia| |]; iApply subty_refl.
  Qed.
  (** The best derivability predicate of *this* model, named so that the
    adequacy theorem below can mention it outside the section. *)
  Definition sder : sJUDG -n> iProp Σ := der.

  (** The level interpretations are non-expansive internally, which
    [sinv_wsat] asks for.  Trivially so: the formulas are discrete. *)
  Lemma tsmf_internal_ne {δ k n} :
    ⊢@{iProp Σ} internal_ne (A:=leibnizO (loc * styp)) (B:=iPropO Σ)
      (tsmf δ k n).
  Proof. iIntros (a a') "eq". by iDestruct (discrete_eq_1 with "eq") as %->. Qed.
End strat.

(** ** Termination adequacy

  Corollary 5.3: a program typed at level [i] terminates.  The proof
  allocates the [i] invariant families - [lvs_names_alloc], which hands out
  the ghost *names* first, because level [k]'s interpretation mentions them
  - hands in the interpretation, and applies the total weakest
  precondition's adequacy. *)
Class stratGpreS Σ : Type := StratGpreS {
  stratGpreS_lrust :: lrustGpreS Σ;
  stratGpreS_sinv :: sinvGpreS tFML Σ;
}.
Definition stratΣ : gFunctors := #[lrustΣ; sinvΣ tFML].
#[export] Instance subG_stratGpreS `{!subG stratΣ Σ} : stratGpreS Σ.
Proof. split; solve_inG. Qed.

Theorem strat_total `{!stratGpreS Σ} {i e T σ} :
  (∀ `(!lrustGS_gen HasNoLc Σ) `(!sinvGS tFML Σ) (γs : list gname),
    length γs = i → ⊢ typed γs i e T) →
  sn erased_step ([e], σ).
Proof.
  move=> typ. apply (lrust_total (Σ:=Σ) (s:=NotStuck)). iIntros (?) "_".
  iMod (sinv_wsat_alloc (FML:=tFML)) as (SI) "_".
  iMod (lvs_names_alloc (FML:=tFML) i) as (γs Hlen) "→W".
  iDestruct ("→W" $! (tsmf γs (sder γs)) with "[]") as "W".
  { iIntros (??). iApply tsmf_internal_ne. }
  iModIntro.
  iExists (Wlv γs (sder γs) i), (λ v, tsem γs (sder γs) i T v)%I.
  iSplitL "W". { rewrite /Wlv /lvs_below take_ge; [|lia]. iExact "W". }
  iApply (typ _ SI γs Hlen).
Qed.

(** ** Worked programs

  The rules are not vacuous.  Each of these is typed by the rules above
  and therefore terminates. *)
Section examples.
  Context `{!lrustGS_gen HasNoLc Σ, !sinvGS tFML Σ} (γs : list gname).

  (** A reference at level 0, allocated and read back at level 1 *)
  Lemma typed_ex_ref : (0 < length γs)%nat →
    ⊢ typed γs 1 (!ˢᶜ (new_ref [of_val (LitV (LitInt 42))] +ₗ #0)) tnat.
  Proof.
    move=> ?. iApply (typed_load γs (k:=0)); [done|lia|].
    iApply (typed_ref γs (k:=0)); [done|lia|lia|]. iApply typed_nat.
  Qed.

  (** The identity on [nat], at execution level 0 *)
  Definition idfn : val := λ: ["x"], "x".
  Lemma typed_idfn {i} : ⊢ typed γs i (of_val idfn) (tfn 0 tnat tnat).
  Proof.
    iApply (typed_fun γs (i:=0)); [lia|done|done|].
    iIntros "!>" (u) "Tu"=>/=. by iApply typed_val.
  Qed.

  (** ...stored in a level-0 reference, read back and called at level 1.

    This is Landin's knot's shape.  What stops the knot is that
    [typed_call_stored] forces the reference's body level below the
    execution level: a function whose *own* body ran at the level of the
    reference holding it would need [0 < 0]. *)
  Lemma typed_ex_horef : (0 < length γs)%nat →
    ⊢ typed γs 1
      (App (!ˢᶜ (new_ref [of_val idfn] +ₗ #0)) [of_val (LitV (LitInt 42))])
      tnat.
  Proof.
    move=> ?.
    iApply (typed_call_stored γs (k:=0) (T:=tnat) (U:=tnat));
      [done|done|lia| |].
    - iApply (typed_ref γs (k:=0) (T:=tfn 0 tnat tnat));
        [by split; [lia|done]|lia|lia|].
      iApply typed_idfn.
    - iApply typed_nat.
  Qed.

  (** An infinite list, in a two-cell heap: the head of its own tail.

    [list₀ nat] is a genuinely recursive type, and the program below walks
    one step of it.  That it terminates is not obvious from the heap - the
    list is cyclic - and it is what the level buys. *)
  Lemma typed_ex_clist : (0 < length γs)%nat →
    ⊢ typed γs 1
      (!ˢᶜ (!ˢᶜ (new_clist [of_val (LitV (LitInt 7))] +ₗ #1) +ₗ #0)) tnat.
  Proof.
    move=> ?. iApply (typed_list_head γs (k:=0)); [done|lia|].
    iApply (typed_list_tail γs (k:=0)); [lia|].
    iApply (typed_clist γs (k:=0)); [done|lia|lia|]. iApply typed_nat.
  Qed.
End examples.

Theorem ex_ref_total `{!stratGpreS Σ} σ :
  sn erased_step
    ([!ˢᶜ (new_ref [of_val (LitV (LitInt 42))] +ₗ #0)]%E, σ).
Proof.
  apply (strat_total (Σ:=Σ) (i:=1) (T:=tnat))=> ?? γs Hlen.
  iApply typed_ex_ref. lia.
Qed.
Theorem ex_horef_total `{!stratGpreS Σ} σ :
  sn erased_step
    ([App (!ˢᶜ (new_ref [of_val idfn] +ₗ #0))
        [of_val (LitV (LitInt 42))]]%E, σ).
Proof.
  apply (strat_total (Σ:=Σ) (i:=1) (T:=tnat))=> ?? γs Hlen.
  iApply typed_ex_horef. lia.
Qed.
(** The thesis's closing example: an iteration over a *cyclic* list,
  with an arbitrary terminating function applied at each step, and a
  counter that bounds nothing but the number of steps. *)
Theorem ex_iter_total `{!stratGpreS Σ} σ (n : nat) :
  sn erased_step
    ([App (of_val iter_list)
        [of_val unitfn; of_val (LitV (LitInt (Z.of_nat n)));
         new_clist [of_val (LitV (LitInt 7))]]]%E, σ).
Proof.
  apply (strat_total (Σ:=Σ) (i:=1) (T:=tunit))=> ?? γs Hlen.
  iApply (typed_iter_clist γs (k:=0) n); lia.
Qed.

Theorem ex_clist_total `{!stratGpreS Σ} σ :
  sn erased_step
    ([!ˢᶜ (!ˢᶜ (new_clist [of_val (LitV (LitInt 7))] +ₗ #1) +ₗ #0)]%E, σ).
Proof.
  apply (strat_total (Σ:=Σ) (i:=1) (T:=tnat))=> ?? γs Hlen.
  iApply typed_ex_clist. lia.
Qed.

(** Axiom-free. *)
Print Assumptions strat_total.
Print Assumptions subty_ref.
Print Assumptions subty_list.
Print Assumptions ex_horef_total.
Print Assumptions ex_clist_total.
Print Assumptions ex_iter_total.
