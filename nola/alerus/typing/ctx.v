(** * The global ghost state and world satisfaction of the typing layer

  This file has no counterpart in VerusBelt: there, the pieces it fixes are
  *namespaces*, and a namespace needs no definition.  Later-free they are
  world satisfactions, and a world satisfaction has to be built, once, in a
  way that does not refer to itself.

  The key identification is [naN = NllftG].  VerusBelt defines

    Definition naN : namespace := nroot .@ "leaf_lifetime_logic" .@ "guarding".

  which is literally [NllftG], so the Points-To Cell Logic's guards and the
  lifetime logic's inclusion guards live at the *same* mask.  Here, therefore,
  [NaSem]'s world satisfaction is [llft_wsatG], and every guard in the
  development is taken over it.

  Nothing is circular:

  - [llft_wsatG] holds the lifetime logic's own invariants and the user's
    [WG]; the *outlives* guards that mention it are kept in [llft_inv_other],
    outside (see [nola.alerus.lifetime.lifetime_full]).
  - The read and write banks that store guards over [llft_wsatG] live in
    [heap_ctx], the state *interpretation*, not in the world satisfaction.
  - [cna_wsat] takes its guards over [llft_wsatG] and so must sit beside it,
    never inside it. *)

From nola.bi Require Export guard modw.
From nola.iris Require Export sinv dinv.
From nola.alerus Require Export eternal frac_guard na_inv_fork boxes.
From nola.alerus.util Require Export non_atomic_cell_map atomic_lock_counter
  cancellable_na_invariants.
From nola.alerus.lifetime Require Export inv lifetime_full.
From nola.alerus.lang Require Export heap lifting.
From nola.alerus.prophecy Require Export prophecy.
From nola.alerus.typing Require Export base uniq_cmra.
From iris.algebra Require Import auth gset.
From iris.proofmode Require Import proofmode.
Import GuardNotation ModwNotation iPropAppNotation.
Export iPropAppNotation.

(** [nola.alerus.lifetime.lifetime_full] keeps these [Local], but the typing
  layer needs them to state [BorStateFml] and to speak about [box_wsat]. *)
#[export] Existing Instances llft_logic_inG llft_boxG.

(** Splitting and rejoining a world satisfaction.

  These exist because [rewrite (wsat_incl …)] inside the Iris proof context
  trips over the [Proper] search for [envs]; going through a lemma and
  [iDestruct] is robust. *)
Section wsat_split.
  Context {PROP : bi}.
  Lemma wsat_split {W W' Wr : PROP} `{!WsatIncl W W' Wr} : W ⊢ W' ∗ Wr.
  Proof. by rewrite (wsat_incl W W' Wr). Qed.
  Lemma wsat_join {W W' Wr : PROP} `{!WsatIncl W W' Wr} : W' -∗ Wr -∗ W.
  Proof. rewrite (wsat_incl W W' Wr). by iIntros "$$". Qed.
End wsat_split.

(** [bor_sem] respects [≡].  It is [NonExpansive] by [BorSem]; the [Proper]
  form is what [setoid_rewrite] needs. *)
#[export] Instance bor_sem_proper `{!BorSem FML Σ} :
  Proper ((≡) ==> (≡)) (bor_sem (FML:=FML) (Σ:=Σ)).
Proof. apply ne_proper, _. Qed.

(** Rewriting a guard along an equivalence.

  VerusBelt does this with [leaf_goal lhs/rhs to …].  [guard_proper] would do
  it too, but [rewrite] of an [⊣⊢] inside the Iris proof context trips over
  the [Proper] search for [envs], so these are stated as directed lemmas. *)
Section guard_iff.
  Context {PROP : bi}.
  Lemma guard_rhs_iff {W P Q Q' : PROP} :
    (Q ⊣⊢ Q') → (P &&{W}&&> Q) ⊢ P &&{W}&&> Q'.
  Proof. move=> eq. by rewrite eq. Qed.
  Lemma guard_lhs_iff {W P P' Q : PROP} :
    (P ⊣⊢ P') → (P' &&{W}&&> Q) ⊢ P &&{W}&&> Q.
  Proof. move=> eq. by rewrite eq. Qed.
  Lemma iff_1 {P Q : PROP} : (P ⊣⊢ Q) → P -∗ Q.
  Proof. move=> eq. rewrite eq. by iIntros "$". Qed.
End guard_iff.

(** Weaken both the world satisfaction and the mask of a [fupdw].  The
  lifetime logic's updates are over [llft_wsat] at [↑NllftUsr ∪ ↑NllftUsr2];
  the typing layer works over the whole world satisfaction at [⊤]. *)
Lemma fupdw_incl_mask {PROP : bi} `{!BiFUpd PROP}
  {W W' Wr : PROP} `{!WsatIncl W W' Wr} {E E' P} :
  E ⊆ E' → (|=[W']{E}=> P) ⊢ |=[W]{E'}=> P.
Proof.
  move=> ?. rewrite /modw (wsat_incl W W' Wr). iIntros "big [W' Wr]".
  iApply fupd_mask_mono; [done|]. iMod ("big" with "W'") as "[$$]". by iFrame.
Qed.

(** ** Lifetime contexts

  These live here, rather than in [typing/lifetime.v] and
  [typing/lft_contexts.v] where VerusBelt puts them, because the global world
  satisfaction has to hold fractional shares of [llctx_interp] (see
  [llctx_interp_make_guarded]) and so must mention it. *)

Definition elctx_elt : Type := lft * lft.
Notation elctx := (list elctx_elt).

Declare Scope lrust_elctx_scope.
Delimit Scope lrust_elctx_scope with EL.
(* We need to define [elctx] and [llctx] as notations to make eauto work.  But
   then, Coq is not able to bind them to their notations, so we have to use
   [Arguments] everywhere. *)
Bind Scope lrust_elctx_scope with elctx_elt.

Notation "κ1 ⊑ₑ κ2" := (@pair lft lft κ1 κ2) (at level 55).

Definition llctx_elt : Type := lft * list lft.
Notation llctx := (list llctx_elt).

Notation "κ ⊑ₗ κl" := (@pair lft (list lft) κ κl) (at level 55).

Definition static := llft_empty.
Notation lft_intersect_list l := (foldr (⊓) static l).

Canonical lftO := leibnizO lft.

(** The formula language must have a formula standing for [True].

  The Points-To Cell Logic stores it while a write is in progress on a plain
  location; the original could just write [True%I], since slices stored
  propositions. *)
Class EmptySem (FML : oFunctor) Σ `{!BorSem FML Σ} := {
  empty_fml : FML $oi Σ;
  empty_fml_sem : bor_sem empty_fml ⊣⊢ True;
}.

(** Directed forms, for [iApply]: see [guard_iff] above *)
Lemma empty_fml_sem_2 `{!BorSem FML Σ, !EmptySem FML Σ} : ⊢ bor_sem empty_fml.
Proof. by rewrite empty_fml_sem. Qed.

(** ** Guard sources for the Points-To Cell Logic

  VerusBelt's [typed_read] and [typed_write] hand the client an arbitrary
  [Timeless] proposition [H] as the source of the read (resp. write) guard.
  The Points-To Cell Logic parks that source in its read and write banks
  while the access is in flight (see
  [nola.alerus.util.non_atomic_cell_map]), and the banks remember *which*
  proposition they hold with an [agreeR (FML $oi Σ)].  Agreeing on an
  arbitrary [iProp Σ] instead would be [saved_prop], and reading one back
  costs a later - exactly what this development is built to avoid.  So a
  guard source has to be a formula.

  Rather than demand a constructor of [FML] for each source the typing layer
  happens to use, we collect their shapes in one [Σ]-free datatype and ask
  for a single constructor interpreting it.  New shapes are added here as
  new types need them. *)
Inductive gsrc : Type :=
| (** [True] *) GTrue
| (** Separating conjunction *) GSep (s s' : gsrc)
| (** A fractional share [frac_tok γ q], as held by [Ltok] and [Ktok] *)
  GFrac (γ : gname) (q : Qp)
| (** A points-to assertion [l ↦!∗ fv] over a vector of fancy values *)
  GMapstoVec (l : loc) (fv : list fancy_val).

(** All the ghost state of the typing layer.

  [HeapSem] is deliberately *not* a field: it is stated against [NaSem], and
  the [NaSem] instance is built below out of these fields.  Typing files
  therefore take [Context `{!alerusGS FML Σ, !AlerusSem FML Σ, !HeapSem FML Σ}]. *)
Class alerusGS (FML : oFunctor) Σ : Type := AlerusGS {
  #[global] alerus_invGS :: invGS_gen HasNoLc Σ;
  #[global] alerus_llftGS :: llft_logicGS Σ;
  #[global] alerus_sinvGS :: sinvGS FML Σ;
  #[global] alerus_heapGS :: heapGS FML Σ;
  #[global] alerus_naInvGS :: naInvGS FML Σ;
  #[global] alerus_alcG :: alc_logicG Σ;
  #[global] alerus_prophG :: prophG Σ;
  #[global] alerus_uniqG :: uniqG Σ;
  #[global] alerus_cnaGS :: cnaGS FML Σ;
  #[global] alerus_fracGS :: fracGuardGS FML Σ;
  #[global] alerus_eternalG :: inG Σ (authUR (gsetUR lft));
  #[global] alerus_llctxFracGS :: fracKeyGS llctx Σ;
  #[global] alerus_lftsFracGS :: fracKeyGS (gmultiset lft) Σ;
  (** The shared-borrow simple-invariant family, as a bare ghost name *)
  alerus_shr_name : gname;
  (** The eternalized-lifetime family *)
  alerus_eternal_name : gname;
  (** The *store* family.

    A type's persistent ghost part has to be reachable from inside a
    guarded former without being one of that former's visible children -
    see [typing/shr_bor.v] - so it is parked in a direct invariant, exactly
    as [nola/examples/rust_halt/shrref.v] parks [ty_shr T] in
    [cif_store].  [nola/alerus/boxes.v] already owns the [sinvGS] family
    that [alerus_sinvGS] names, so the store gets a second one: [dinvGS] is
    definitionally [sinvGS], so this is just another [sinv_name]. *)
  alerus_store_name : gname;
}.

(** The store's [dinvGS], kept out of the instance database so that it never
  competes with [alerus_sinvGS] when something asks for an [sinvGS]. *)
Definition alerus_dinvGS `{!alerusGS FML Σ} : dinvGS FML Σ :=
  SinvGS _ _ (@sinvGS_pre FML Σ alerus_sinvGS) alerus_store_name.

(** ** The interpretation of formulas

  [alerusGS] above is *ghost state only*: it fixes the resource algebras and
  the ghost names, and says nothing about what a formula means.  What a
  formula means is this second class.

  The split matters.  The guarding world satisfaction [alerus_WGuard] is
  built out of [bor_sem] - [frac_wsat bor_sem], [box_wsat bor_sem],
  [shr_wsat] - so a *model* has to be able to write it down at an
  interpretation other than the ambient one, exactly as Nola writes
  [inv_wsat ⟦⟧(δ)] and [borrow_wsat borrowM ⟦⟧(δ)]
  ([nola/iris/inv_deriv.v], [nola/examples/rust_halt/base.v:146-148]).  That
  is impossible while the interpretation is a field of the ghost-state
  record, because then "the same ghost state at another interpretation" is
  not expressible.  With the split it is: keep [alerusGS], vary
  [AlerusSem]. *)
Class AlerusSem (FML : oFunctor) Σ `{!alerusGS FML Σ} : Type := AlerusSemI {
  #[global] alerus_borSem :: BorSem FML Σ;
  #[global] alerus_borStateFml :: BorStateFml llft_name;
  #[global] alerus_shrBorSem :: ShrBorSem FML Σ;
  #[global] alerus_emptySem :: EmptySem FML Σ;
}.

(** ** Candidate interpretations

  A *candidate* carries a whole [AlerusSem], not just a function on formulas:
  the guarding world satisfaction a guard lives at contains [llft_inv_main],
  which the lifetime logic builds from the [BorSem] record, so it is not a
  function of [bor_sem] alone.

  It is *wrapped*, though.  [AlerusSem] is a class, so a candidate bound by a
  [∀] would be an instance in its own scope and would shadow the ambient one
  for every [bor_sem], [empty_fml], [bor_state_fml] … in the statement under
  it.  [Cand] is a record with no instances, and the coercion below lets one
  still write [sem Px]. *)
Record Cand (FML : oFunctor) Σ `{!alerusGS FML Σ} : Type :=
  MkCand { cand_asem : AlerusSem FML Σ }.
Arguments MkCand {_ _ _} _. Arguments cand_asem {_ _ _} _.

Definition cand_fun `{!alerusGS FML Σ} (S : Cand FML Σ)
  : FML $oi Σ → iProp Σ :=
  @bor_sem FML Σ (@alerus_borSem FML Σ _ (cand_asem S)).
Coercion cand_fun : Cand >-> Funclass.

#[export] Instance cand_ne `{!alerusGS FML Σ} {S : Cand FML Σ} :
  NonExpansive S.
Proof. rewrite /cand_fun. exact bor_sem_ne. Qed.

(** The ambient candidate *)
Definition alt_amb `{!alerusGS FML Σ, AS : !AlerusSem FML Σ} : Cand FML Σ :=
  MkCand AS.

Section alerus.
  Context `{!alerusGS FML Σ, !AlerusSem FML Σ}.

  (** Local lifetime context *)
  Definition llctx_elt_interp (x : llctx_elt) : iProp Σ :=
    let κ' := lft_intersect_list (x.2) in
    (∃ κ0, ⌜x.1 = κ' ⊓ κ0⌝ ∗ @[κ0] ∗ ⌜κ0 ≠ ∅⌝)%I.
  Definition llctx_interp (L : llctx) : iProp Σ :=
    ([∗ list] x ∈ L, llctx_elt_interp x)%I.

  (** The user's guarding world satisfaction: Leaf's [↑NllftG] minus the
    lifetime logic's own invariants.

    Everything guarded at [↑NllftG] that is not a borrow lives here:
    eternalized lifetime tokens ([lft_eternalize]), fractional shares of
    formulas, and fractional shares of a local lifetime context
    ([llctx_interp_make_guarded]).  None of these stores a guard, so none of
    them may refer to [alerus_WGuard] - and none does.  [cna_wsat], which
    *does* store guards over [alerus_WGuard], is therefore kept outside. *)
  (** A multiset of lifetime tokens, the thing [Send] shares *)
  Definition lfts_interp (κs : gmultiset lft) : iProp Σ :=
    [∗ mset] κ ∈ κs, llft_alive κ.

  (** [send_wsat] is deliberately *not* here.  [Send] moves a type's ghost
    assertion to another thread pool, and for the null pool that means
    destroying an invariant held there, which needs [cna_lifetimes
    atomic_pool_name ∅] - i.e. [send_wsat] - as a *resource*.  The original
    keeps it in an Iris invariant at its own namespace and opens it while
    [cna_destroy] opens its guards at [↑NllftG]; a guard here is opened by
    consuming the world satisfaction, so the two would collide.  Keeping
    [send_wsat] outside the guarding world satisfaction - and outside the one
    [Send] runs under, [alerus_wsat_core] - separates them. *)
  (** Where a type's persistent ghost part is parked, so that a guarded
    former can reach it without exposing the borrowed type as one of its
    visible children.  [rust_halt_wsat] has the same conjunct,
    [dinv_wsat ⟦⟧ᶜ].

    It sits *inside* [alerus_WGuard] rather than beside it, and that is the
    whole point: a guard's definition hands its body the world satisfaction
    ([guard_acc]), so a former building a guard can open the store on the
    way - which is what [&shr{κ}]'s prophecy obligation needs, and what
    keeps [ty_guard_proph] free of any modality.  This is the same position
    [box_wsat bor_sem] already occupies. *)
  Definition alerus_store_wsat : iProp Σ :=
    @dinv_wsat FML Σ alerus_dinvGS bor_sem.

  Definition alerus_WG : iProp Σ :=
    eternal_wsat alerus_eternal_name llft_alive ∗
    frac_wsat bor_sem ∗
    frac_key_wsat llctx_interp ∗
    frac_key_wsat lfts_interp ∗
    alerus_store_wsat.

  (** Fix the lifetime logic's two parameters *)
  #[export] Instance alerus_LlftWG : LlftWG Σ :=
    {| llft_shr_name := alerus_shr_name; llft_WG := alerus_WG |}.

  (** [↑NllftG] itself: the world satisfaction every guard is taken over *)
  Definition alerus_WGuard : iProp Σ := llft_wsatG.

  (** The same as a function of the *interpretation*.

    [alerus_WGuard] is phrased through the [AlerusSem] record, so it is a
    function of that record.  [AltSem]'s [alt_WGuard] has to map a candidate
    interpretation - which is just a function - to the world satisfaction
    its guards live at, so the model needs this form.  The body is
    [llft_wsatG]'s with [bor_sem] replaced by the argument; they agree at
    the ambient interpretation by [alerus_WGuard_of_here]. *)
  Definition alerus_WGuard_of (sem : FML $oi Σ → iProp Σ) : iProp Σ :=
    (eternal_wsat alerus_eternal_name llft_alive ∗ frac_wsat sem ∗
     frac_key_wsat llctx_interp ∗ frac_key_wsat lfts_interp ∗
     @dinv_wsat FML Σ alerus_dinvGS sem) ∗
    sinv_wsat (sinvGS0 := SinvGS FML Σ sinvGS_pre alerus_shr_name)
      (λ _ Px, sem Px) ∗
    box_wsat sem ∗ llft_inv_main.

  Lemma alerus_WGuard_of_here : alerus_WGuard_of bor_sem = alerus_WGuard.
  Proof. done. Qed.

  (** The Points-To Cell Logic guards at [naN = NllftG] *)
  #[export] Instance alerus_NaSem : NaSem FML Σ := {|
    na_sem := bor_sem;
    na_sem_ne := bor_sem_ne;
    na_wsat := alerus_WGuard;
    na_emptyx := empty_fml;
    na_emptyx_sem := empty_fml_sem;
  |}.

  (** What a guard-source descriptor stands for *)
  Fixpoint gsrc_interp (s : gsrc) : iProp Σ :=
    match s with
    | GTrue => True
    | GSep s s' => gsrc_interp s ∗ gsrc_interp s'
    | GFrac γ q => frac_tok γ q
    | GMapstoVec l fv => l ↦!∗ fv
    end%I.

  (** ** Fractional deallocation permission

    VerusBelt puts this in [typing/freeable_util.v]; here it has to be
    available to the formula language below, which must be able to express
    the ghost assertion of [own_ptr]. *)
  Definition freeable_sz (n sz : nat) (l : loc) : iProp Σ :=
    match sz, n with 0%nat, _ => True | _, 0%nat => False |
      sz, n => †{pos_to_Qp (Pos.of_nat sz) / pos_to_Qp (Pos.of_nat n)}l…sz end.
  Arguments freeable_sz : simpl never.

  #[export] Instance freeable_sz_timeless n sz l : Timeless (freeable_sz n sz l).
  Proof. case sz, n; apply _. Qed.

  Context `{!HeapSem FML Σ}.

  (** The program logic *)
  #[export] Instance alerus_lrustGS : lrustGS_gen HasNoLc FML Σ := {|
    lrustGS_invGS := alerus_invGS;
    lrustGS_na_invGS := na_inv_invG;
    lrustGS_alcGS := alerus_alcG;
    lrustGS_heapGS := alerus_heapGS;
    lrustGS_naSem := alerus_NaSem;
    lrustGS_heapSem := _;
  |}.

  (** The global world satisfaction.

    [na_inv_wsat] is where the *atomic* invariants of [typing/atomic_inv.v]
    live: the original holds them in Iris invariants, so opening one yields a
    [▷]; here they are simple invariants over formulas whose world
    satisfaction has to be threaded explicitly. *)
  Definition alerus_wsat_core : iProp Σ :=
    llft_wsat ∗ cna_wsat alerus_WGuard bor_sem ∗
    na_inv_wsat atomic_threadpool bor_sem.
  Definition alerus_wsat : iProp Σ := alerus_wsat_core ∗ send_wsat.

  (** ** Shared access to a local lifetime context

    VerusBelt's typing judgments take an arbitrary [Timeless G] together with
    a guard [G &&{↑NllftG}&&> llctx_interp L], and halve it by storing [G]
    itself in a fresh storage protocol ([frac_split_guard_in_half]).  A
    later-free world satisfaction holds syntax, not arbitrary propositions, so
    that is not available - and it is not needed: the only things a judgment
    does with [G] are open the guard and halve it, and a *fraction* of a share
    does both.  So the pair [G ∗ (G &&{↑NllftG}&&> llctx_interp L)] becomes a
    single [Ltok γ L q]. *)
  Definition Ltok (γ : gname) (L : llctx) (q : Qp) : iProp Σ :=
    frac_key_tok γ L ∗ frac_tok γ q.

  #[export] Instance Ltok_timeless {γ L q} : Timeless (Ltok γ L q).
  Proof. exact _. Qed.

  Lemma Ltok_split {γ L q} : Ltok γ L q ⊣⊢ Ltok γ L (q/2) ∗ Ltok γ L (q/2).
  Proof.
    rewrite /Ltok {1}frac_tok_half. iSplit.
    - by iIntros "[#$ [$$]]".
    - by iIntros "[[#$ $][_ $]]".
  Qed.

  (** Directed forms, for [iDestruct]: rewriting an [⊣⊢] inside the Iris
    context trips over the [Proper] search for [envs]. *)
  Lemma Ltok_split_1 {γ L q} : Ltok γ L q -∗ Ltok γ L (q/2) ∗ Ltok γ L (q/2).
  Proof. rewrite Ltok_split. by iIntros "$". Qed.
  Lemma Ltok_split_2 {γ L q} :
    Ltok γ L (q/2) -∗ Ltok γ L (q/2) -∗ Ltok γ L q.
  Proof. iIntros "t t'". rewrite (Ltok_split (q:=q)). iFrame. Qed.

  (** The guard needs only the persistent half of the share *)
  Lemma Ltok_guard {γ L q} :
    frac_key_tok γ L ⊢ Ltok γ L q &&{alerus_WGuard}&&> llctx_interp L.
  Proof.
    iIntros "#tok". iApply guard_lhs_sep_r.
    iApply (frac_key_guard_wsat llctx_interp with "tok").
  Qed.
  Lemma Ltok_guard' {γ L q} :
    Ltok γ L q -∗
      (Ltok γ L q &&{alerus_WGuard}&&> llctx_interp L) ∗ Ltok γ L q.
  Proof. iIntros "[#tok $]". iFrame "tok". by iApply Ltok_guard. Qed.

  (** The share alone, without the persistent key, is a guard source: this is
    the form [typed_read] and [typed_write] hand out, since only a formula
    can go into the Points-To Cell Logic's banks. *)
  Lemma Ltok_guard_frac {γ L q} :
    frac_key_tok γ L ⊢ frac_tok γ q &&{alerus_WGuard}&&> llctx_interp L.
  Proof. iApply (frac_key_guard_wsat llctx_interp). Qed.

  (** Open a share against the world satisfaction *)
  Lemma Ltok_acc `{!WsatIncl W alerus_WGuard Wr} {γ L q} :
    Ltok γ L q -∗ W -∗ llctx_interp L ∗ (llctx_interp L -∗ W ∗ Ltok γ L q).
  Proof.
    iIntros "tok W". iDestruct (Ltok_guard' with "tok") as "[#g tok]".
    iApply (guard_acc with "[g] tok W").
    by iApply (guard_wsat_incl (W':=alerus_WGuard)).
  Qed.

  (** Create and destroy a share *)
  Lemma Ltok_alloc {L} : llctx_interp L =[alerus_wsat]=∗ ∃ γ, Ltok γ L 1.
  Proof.
    iIntros "L W".
    iDestruct (wsat_split (W':=frac_key_wsat llctx_interp) with "W")
      as "[Wf Wr]".
    iMod (frac_key_alloc with "L Wf") as (γ) "(#tok & h & h' & Wf)".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wf Wr") as "$". iModIntro.
    iExists γ. rewrite /Ltok frac_half_add. iFrame "tok h h'".
  Qed.
  Lemma Ltok_withdraw {γ L} :
    Ltok γ L 1 =[alerus_wsat]=∗ llctx_interp L.
  Proof.
    iIntros "[#tok f] W".
    iDestruct (wsat_split (W':=frac_key_wsat llctx_interp) with "W")
      as "[Wf Wr]".
    iMod (frac_key_withdraw with "tok f Wf") as "[$ Wf]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wf Wr") as "$". by iModIntro.
  Qed.

  (** The inclusions the rest of the development needs.  They are given
    explicitly rather than left to the structural instances, which would have
    to unfold [llft_wsat], [llft_wsatG] and the [LlftWG] projections. *)
  #[export] Instance wsat_incl_alerus_core :
    WsatIncl alerus_wsat alerus_wsat_core send_wsat.
  Proof. done. Qed.
  #[export] Instance wsat_incl_alerus_send :
    WsatIncl alerus_wsat send_wsat alerus_wsat_core.
  Proof.
    rewrite /WsatIncl /alerus_wsat. iSplit.
    - iIntros "[A B]". iFrame.
    - iIntros "[A B]". iFrame.
  Qed.
  #[export] Instance wsat_incl_alerus_core_llft :
    WsatIncl alerus_wsat_core llft_wsat
      (cna_wsat alerus_WGuard bor_sem ∗ na_inv_wsat atomic_threadpool bor_sem).
  Proof. done. Qed.
  #[export] Instance wsat_incl_alerus_llft :
    WsatIncl alerus_wsat llft_wsat
      ((cna_wsat alerus_WGuard bor_sem ∗
        na_inv_wsat atomic_threadpool bor_sem) ∗ send_wsat).
  Proof.
    rewrite /WsatIncl /alerus_wsat /alerus_wsat_core. iSplit.
    - iIntros "((A & B & C) & D)". iFrame.
    - iIntros "(A & (B & C) & D)". iFrame.
  Qed.
  #[export] Instance wsat_incl_alerus_core_guard :
    WsatIncl alerus_wsat_core alerus_WGuard
      (llft_inv_other ∗ cna_wsat alerus_WGuard bor_sem ∗
        na_inv_wsat atomic_threadpool bor_sem).
  Proof.
    rewrite /WsatIncl /alerus_wsat_core /alerus_WGuard /llft_wsat. iSplit.
    - iIntros "([A B] & C & D)". iFrame.
    - iIntros "(A & B & C & D)". iFrame.
  Qed.
  #[export] Instance wsat_incl_alerus_guard :
    WsatIncl alerus_wsat alerus_WGuard
      ((llft_inv_other ∗ cna_wsat alerus_WGuard bor_sem ∗
        na_inv_wsat atomic_threadpool bor_sem) ∗ send_wsat).
  Proof.
    rewrite /WsatIncl /alerus_wsat /alerus_wsat_core /alerus_WGuard
      /llft_wsat. iSplit.
    - iIntros "(([A B] & C & D) & E)". iFrame.
    - iIntros "(A & (B & C & D) & E)". iFrame.
  Qed.
  #[export] Instance wsat_incl_alerus_core_cna :
    WsatIncl alerus_wsat_core (cna_wsat alerus_WGuard bor_sem ∗ alerus_WGuard)
      (llft_inv_other ∗ na_inv_wsat atomic_threadpool bor_sem).
  Proof.
    rewrite /WsatIncl /alerus_wsat_core /alerus_WGuard /llft_wsat. iSplit.
    - iIntros "([A B] & C & D)". iFrame.
    - iIntros "((A & B) & C & D)". iFrame.
  Qed.
  #[export] Instance wsat_incl_alerus_cna :
    WsatIncl alerus_wsat (cna_wsat alerus_WGuard bor_sem ∗ alerus_WGuard)
      ((llft_inv_other ∗ na_inv_wsat atomic_threadpool bor_sem) ∗ send_wsat).
  Proof.
    rewrite /WsatIncl /alerus_wsat /alerus_wsat_core /alerus_WGuard
      /llft_wsat. iSplit.
    - iIntros "(([A B] & C & D) & E)". iFrame.
    - iIntros "((A & B) & (C & D) & E)". iFrame.
  Qed.
  #[export] Instance wsat_incl_alerus_core_nainv :
    WsatIncl alerus_wsat_core (na_inv_wsat atomic_threadpool bor_sem)
      (llft_wsat ∗ cna_wsat alerus_WGuard bor_sem).
  Proof.
    rewrite /WsatIncl /alerus_wsat_core. iSplit.
    - iIntros "(A & B & C)". iFrame.
    - iIntros "(A & B & C)". iFrame.
  Qed.
  #[export] Instance wsat_incl_alerus_nainv :
    WsatIncl alerus_wsat (na_inv_wsat atomic_threadpool bor_sem)
      ((llft_wsat ∗ cna_wsat alerus_WGuard bor_sem) ∗ send_wsat).
  Proof.
    rewrite /WsatIncl /alerus_wsat /alerus_wsat_core. iSplit.
    - iIntros "((A & B & C) & D)". iFrame.
    - iIntros "(A & (B & C) & D)". iFrame.
  Qed.

  (** [alerus_WG] and its parts sit inside [alerus_WGuard] *)
  #[export] Instance wsat_incl_alerus_WG :
    WsatIncl alerus_WGuard alerus_WG
      (shr_wsat ∗ box_wsat bor_sem ∗ llft_inv_main).
  Proof. done. Qed.
  #[export] Instance wsat_incl_alerus_eternal :
    WsatIncl alerus_WG (eternal_wsat alerus_eternal_name llft_alive)
      (frac_wsat bor_sem ∗ frac_key_wsat llctx_interp ∗
        frac_key_wsat lfts_interp ∗ alerus_store_wsat).
  Proof. done. Qed.

  (** The store sits inside the guarding world satisfaction *)
  #[export] Instance wsat_incl_alerus_WGuard_store :
    WsatIncl alerus_WGuard alerus_store_wsat
      ((eternal_wsat alerus_eternal_name llft_alive ∗ frac_wsat bor_sem ∗
        frac_key_wsat llctx_interp ∗ frac_key_wsat lfts_interp) ∗
       shr_wsat ∗ box_wsat bor_sem ∗ llft_inv_main).
  Proof.
    rewrite /WsatIncl /alerus_WGuard /alerus_WG. iSplit.
    - iIntros "((A & B & C & D & E) & F)". iFrame.
    - iIntros "(E & (A & B & C & D) & F)". iFrame.
  Qed.
  #[export] Instance wsat_incl_alerus_WG_store :
    WsatIncl alerus_WG alerus_store_wsat
      (eternal_wsat alerus_eternal_name llft_alive ∗ frac_wsat bor_sem ∗
        frac_key_wsat llctx_interp ∗ frac_key_wsat lfts_interp).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - iIntros "(A & B & C & D & E)". iFrame.
    - iIntros "(E & A & B & C & D)". iFrame.
  Qed.
  #[export] Instance wsat_incl_alerus_fracfml :
    WsatIncl alerus_WG (frac_wsat bor_sem)
      (eternal_wsat alerus_eternal_name llft_alive ∗
        frac_key_wsat llctx_interp ∗ frac_key_wsat lfts_interp ∗
        alerus_store_wsat).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - by iIntros "($ & $ & $ & $ & $)".
    - by iIntros "($ & $ & $ & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_llctx :
    WsatIncl alerus_WG (frac_key_wsat llctx_interp)
      (eternal_wsat alerus_eternal_name llft_alive ∗ frac_wsat bor_sem ∗
        frac_key_wsat lfts_interp ∗ alerus_store_wsat).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - by iIntros "($ & $ & $ & $ & $)".
    - by iIntros "($ & $ & $ & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_lfts :
    WsatIncl alerus_WG (frac_key_wsat lfts_interp)
      (eternal_wsat alerus_eternal_name llft_alive ∗ frac_wsat bor_sem ∗
        frac_key_wsat llctx_interp ∗ alerus_store_wsat).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - by iIntros "($ & $ & $ & $ & $)".
    - by iIntros "($ & $ & $ & $ & $)".
  Qed.

  (** ** Shares of a multiset of lifetime tokens

    [Send] passes an arbitrary [G] with [∀ κ ∈ κs, G &&{↑NllftG}&&> @[κ]] and
    halves it with [frac_split_in_half]; the same reasoning as for [Ltok]
    applies, with the key now the multiset itself. *)
  Definition Ktok (γ : gname) (κs : gmultiset lft) (q : Qp) : iProp Σ :=
    frac_key_tok γ κs ∗ frac_tok γ q.

  #[export] Instance Ktok_timeless {γ κs q} : Timeless (Ktok γ κs q).
  Proof. exact _. Qed.

  Lemma Ktok_split {γ κs q} : Ktok γ κs q ⊣⊢ Ktok γ κs (q/2) ∗ Ktok γ κs (q/2).
  Proof.
    rewrite /Ktok {1}frac_tok_half. iSplit.
    - by iIntros "[#$ [$$]]".
    - by iIntros "[[#$ $][_ $]]".
  Qed.
  Lemma Ktok_split_1 {γ κs q} :
    Ktok γ κs q -∗ Ktok γ κs (q/2) ∗ Ktok γ κs (q/2).
  Proof. rewrite Ktok_split. by iIntros "$". Qed.
  Lemma Ktok_split_2 {γ κs q} :
    Ktok γ κs (q/2) -∗ Ktok γ κs (q/2) -∗ Ktok γ κs q.
  Proof. iIntros "t t'". rewrite (Ktok_split (q:=q)). iFrame. Qed.

  Lemma Ktok_guard {γ κs q κ} : κ ∈ κs →
    frac_key_tok γ κs ⊢ Ktok γ κs q &&{alerus_WGuard}&&> llft_alive κ.
  Proof.
    move=> in'. iIntros "#tok". iApply guard_lhs_sep_r.
    iApply (guard_trans with "[] []").
    { iApply (frac_key_guard_wsat lfts_interp with "tok"). }
    iApply guard_intro. iIntros "!> big". rewrite /lfts_interp.
    by iApply (big_sepMS_elem_of_acc with "big").
  Qed.

  Lemma Ktok_alloc {κs} : lfts_interp κs =[alerus_wsat]=∗ ∃ γ, Ktok γ κs 1.
  Proof.
    iIntros "K W".
    iDestruct (wsat_split (W':=frac_key_wsat lfts_interp) with "W")
      as "[Wf Wr]".
    iMod (frac_key_alloc with "K Wf") as (γ) "(#tok & h & h' & Wf)".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wf Wr") as "$". iModIntro.
    iExists γ. rewrite /Ktok frac_half_add. iFrame "tok h h'".
  Qed.
  Lemma Ktok_withdraw {γ κs} :
    Ktok γ κs 1 =[alerus_wsat]=∗ lfts_interp κs.
  Proof.
    iIntros "[#tok f] W".
    iDestruct (wsat_split (W':=frac_key_wsat lfts_interp) with "W")
      as "[Wf Wr]".
    iMod (frac_key_withdraw with "tok f Wf") as "[$ Wf]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wf Wr") as "$". by iModIntro.
  Qed.
End alerus.

(** The guarding world satisfaction at a candidate.  It is a function of the
  whole [AlerusSem] the candidate carries - that is why a candidate is not a
  bare function on formulas. *)
Definition cand_WGuard `{!alerusGS FML Σ} (S : Cand FML Σ) : iProp Σ :=
  @alerus_WGuard FML Σ _ (cand_asem S).
Notation alt_WGuard := cand_WGuard.
Lemma alt_WGuard_here `{!alerusGS FML Σ, !AlerusSem FML Σ} :
  alt_WGuard alt_amb = alerus_WGuard.
Proof. done. Qed.

(** The formula language must express every guard source.

  Like [HeapSem] this is *not* a field of [alerusGS]: [gsrc_interp] is stated
  against the [NaSem] instance that [alerusGS] builds.  Typing files get it
  through [typeG]. *)
Class GsrcSem (FML : oFunctor) Σ `{!alerusGS FML Σ, !AlerusSem FML Σ} := {
  gsrc_fml : gsrc → FML $oi Σ;
  gsrc_fml_sem s : bor_sem (gsrc_fml s) ⊣⊢ gsrc_interp s;
}.

Section gsrc.
  Context `{!alerusGS FML Σ, !AlerusSem FML Σ, !GsrcSem FML Σ}.

  (** Directed forms of [gsrc_fml_sem], for [iApply] and [iDestruct] *)
  Lemma gsrc_fml_sem_1 {s} : bor_sem (gsrc_fml s) ⊢ gsrc_interp s.
  Proof. by rewrite gsrc_fml_sem. Qed.
  Lemma gsrc_fml_sem_2 {s} : gsrc_interp s ⊢ bor_sem (gsrc_fml s).
  Proof. by rewrite gsrc_fml_sem. Qed.
End gsrc.

(** ** The formula language of the typing layer

  This follows Nola's [rust_halt] ([nola/examples/rust_halt/type.v]), where a
  type's interpretation *is* a formula: [ty_own]/[ty_shr] land in
  [cif CON Σ], and every property of a type is stated about [⟦ · ⟧ᶜ] of it.
  The reason is the same here.  A unique borrow [&uniq{κ} ty] keeps the
  borrowed contents in [&{κ,idx}(…)], and the Points-To Cell Logic keeps a
  type's ghost assertion in a [cna_inv]; in a later-free development both of
  those store a *formula* ([idx_bor κ idx (Px : FML $oi Σ)],
  [cna_inv γ p N Px]), because agreeing on an arbitrary [iProp Σ] is
  [saved_prop] and reading one back costs a later.  So a type's ghost
  assertion has to be a formula too.

  Nola gets the shapes it needs from [cif]'s built-in BI connectives plus a
  [rust_haltC] class listing the custom constructors.  Here [FML] is left
  abstract - every layer below ([BorSem] with its [bor_sep], [BorStateFml],
  [ShrBorSem], [EmptySem], [HeapSem], [GsrcSem]) is already written that way -
  so this class plays the role of *both*: it lists the connectives and the
  custom constructors the type formers need, each with the equation pinning
  down its semantics.  A concrete [FML] (a [cif] instance) has to satisfy it;
  see the note on [typing/soundness.v]. *)
Class TypeFml (FML : oFunctor) Σ `{!alerusGS FML Σ, !AlerusSem FML Σ} := {
  (** [False], for the empty type used in fixpoints *)
  false_fml : FML $oi Σ;
  false_fml_sem : bor_sem false_fml ⊣⊢ False;
  (** A pure proposition *)
  pure_fml : Prop → FML $oi Σ;
  pure_fml_sem φ : bor_sem (pure_fml φ) ⊣⊢ ⌜φ⌝;
  (** Existential quantification, for the body of a unique borrow *)
  ex_fml {A : Type} : (A → FML $oi Σ) → FML $oi Σ;
  ex_fml_sem {A} (Φ : A → FML $oi Σ) :
    bor_sem (ex_fml Φ) ⊣⊢ ∃ a : A, bor_sem (Φ a);
  ex_fml_ne {A} n (Φ Ψ : A → FML $oi Σ) :
    (∀ a, Φ a ≡{n}≡ Ψ a) → ex_fml Φ ≡{n}≡ ex_fml Ψ;
  (** An existential over a *syntactic* type's values.

    Separate from [ex_fml] because [~~𝔄] lives in a universe strictly above
    the one [cif]'s own existential can quantify over, so the model has to
    give it its own constructor; see [model.v]'s [exCT]. *)
  exs_fml {𝔄 : syn_type} : ((~~𝔄) → FML $oi Σ) → FML $oi Σ;
  exs_fml_sem {𝔄} (Φ : (~~𝔄) → FML $oi Σ) :
    bor_sem (exs_fml Φ) ⊣⊢ ∃ a : ~~𝔄, bor_sem (Φ a);
  exs_fml_ne {𝔄} n (Φ Ψ : (~~𝔄) → FML $oi Σ) :
    (∀ a, Φ a ≡{n}≡ Ψ a) → exs_fml Φ ≡{n}≡ exs_fml Ψ;
  (** A *persistently stored* formula.

    [&shr{κ} ty] holds the borrowed type's persistent ghost part behind this
    rather than as a visible child, because a visible child would stop
    [λ T, &shr{κ} T] from being [Productive] - see [typing/model.v]'s
    [pstoreJT].  Like [guard_fml] it has no [⊣⊢] semantics: its elimination
    is [store_fml_acc] and its introduction [store_fml_alloc], both in
    [AltSem]. *)
  store_fml : FML $oi Σ → FML $oi Σ;
  store_fml_ne :: NonExpansive store_fml;
  (** A formula held in a *simple invariant*.

    [store_fml] is one-way and sound only for persistent content.  This one
    holds *owned* content and its accessor gives it back, which is what a
    Leaf guard needs - and it is why an owning pointer can hold its pointee
    behind it and still be [Productive].  Unlike [store_fml] it does have a
    [⊣⊢] semantics, [dinv_fml_sem_at_any], because [dinv_tok] mentions no
    interpretation. *)
  dinv_fml : FML $oi Σ → FML $oi Σ;
  dinv_fml_ne :: NonExpansive dinv_fml;
  (** [□], so that a former can be *structurally* persistent.

    [&shr{κ}] needs its ghost assertion to be persistent without appealing to
    the borrowed type's own persistence law - otherwise [&shr{κ}] could not
    guard a recursive type.  [nola/examples/rust_halt/shrref.v] does exactly
    this, writing [□ cif_store (ty_shr T …)]. *)
  pers_fml : FML $oi Σ → FML $oi Σ;
  pers_fml_ne :: NonExpansive pers_fml;
  pers_fml_sem Px : bor_sem (pers_fml Px) ⊣⊢ □ bor_sem Px;
  (** A guard over the guarding world satisfaction, for [&shr{κ}] *)
  guard_fml : FML $oi Σ → FML $oi Σ → FML $oi Σ;
  guard_fml_ne :: NonExpansive2 guard_fml;
  (** [guard_fml] has *no* [⊣⊢] semantics: see the note on [AltSem] below.
    Its elimination is [guard_fml_sem_into], its introduction
    [guard_fml_sem_2], and both live in [AltSem]. *)
  (** A lifetime token, for [&shr{κ}] *)
  (** A *storable* lifetime inclusion.  Unlike a guard between arbitrary
    formulas, an inclusion's endpoints are lifetime tokens, which mean the
    same at every interpretation - so the whole family
    [□ ∀ δ good, @[κ] &&{W δ}&&> @[κ']] has a [⊣⊢] semantics at every
    candidate and can live in a formula.  That is what a type's ghost
    assertion stores and what shortens a borrow. *)
  incl_fml : lft → lft → FML $oi Σ;
  alive_fml : lft → FML $oi Σ;
  alive_fml_sem κ : bor_sem (alive_fml κ) ⊣⊢ @[κ];
  (** A points-to assertion over a vector of fancy values, with cells *)
  cells_fml : loc → list (list cell_id) → list fancy_val → FML $oi Σ;
  cells_fml_sem l cs fv : bor_sem (cells_fml l cs fv) ⊣⊢ l ↦[^ cs ]!∗ fv;
  (** A *complete* points-to assertion, for the body of a unique borrow *)
  ccells_fml : cloc → list fancy_val → FML $oi Σ;
  ccells_fml_sem l fv : bor_sem (ccells_fml l fv) ⊣⊢ l #↦!∗ fv;
  (** The deallocation permission, for [own_ptr] *)
  freeable_fml : nat → nat → loc → FML $oi Σ;
  freeable_fml_sem n sz l :
    bor_sem (freeable_fml n sz l) ⊣⊢ freeable_sz n sz l;
  (** The prophecy controller, for the body of a unique borrow *)
  pc_fml (ξ : proph_var) : ~~ (`ξ.(pv_ty)) → proph ξ.(pv_ty) → nat * nat →
    FML $oi Σ;
  pc_fml_sem ξ x vπ d : bor_sem (pc_fml ξ x vπ d) ⊣⊢ .PC[ξ] x vπ d;
  (** Disjunction, for [&uniq{κ}]'s "the lifetime is already dead" case *)
  or_fml : FML $oi Σ → FML $oi Σ → FML $oi Σ;
  or_fml_sem Px Qx :
    bor_sem (or_fml Px Qx) ⊣⊢ bor_sem Px ∨ bor_sem Qx;
  or_fml_ne :: NonExpansive2 or_fml;
  (** The value observer of a unique reference *)
  vo_fml (ξ : proph_var) : ~~ (`ξ.(pv_ty)) → nat * nat → FML $oi Σ;
  vo_fml_sem ξ x d : bor_sem (vo_fml ξ x d) ⊣⊢ .VO[ξ] x d;
  (** An indexed borrow, for the body of a unique reference *)
  idxbor_fml : lft → Idx → FML $oi Σ → FML $oi Σ;
  (** [idxbor_fml] has *no* [⊣⊢] semantics either: [idx_bor κ i Px] carries
    [□ (bor_sem Px' ↔ bor_sem Px)] at an existentially quantified [Px'],
    which is not a subformula.  Its elimination is [idxbor_fml_sem_1] and
    its introduction [idxbor_fml_of_bor], both in [AltSem]. *)
  idxbor_fml_ne κ idx :: NonExpansive (idxbor_fml κ idx);
  (** A dead lifetime *)
  dead_fml : lft → FML $oi Σ;
  dead_fml_sem κ : bor_sem (dead_fml κ) ⊣⊢ [†κ];
  (** "This location is allocated", as [&uniq{κ}] guards it *)
  cmapstoany_fml : cloc → FML $oi Σ;
  cmapstoany_fml_sem l : bor_sem (cmapstoany_fml l) ⊣⊢ l #↦∗_;
  (** Separating conjunction comes from [BorSem]; non-expansiveness of it is
    needed here and nowhere below, so it is asked for here. *)
  sep_fml_ne :: NonExpansive2 (bor_sep (FML:=FML) (Σ:=Σ));
}.

Section type_fml.
  Context `{!alerusGS FML Σ, !AlerusSem FML Σ, !TypeFml FML Σ}.

  (** A points-to assertion over a plain location, as [own_ptr] uses it *)
  Definition mapsto_fml (l : loc) (fv : list fancy_val) : FML $oi Σ :=
    cells_fml l (repeat [] (length fv)) fv.
  Lemma mapsto_fml_sem {l fv} : bor_sem (mapsto_fml l fv) ⊣⊢ l ↦!∗ fv.
  Proof. by rewrite /mapsto_fml cells_fml_sem. Qed.

  (** [exs_fml] is proper *)
  #[export] Instance exs_fml_ne' {𝔄} n :
    Proper (pointwise_relation (~~𝔄) (dist n) ==> dist n)
      (@exs_fml _ _ _ _ _ 𝔄).
  Proof. move=> ???. by apply exs_fml_ne. Qed.

  (** [ex_fml] is proper *)
  #[export] Instance ex_fml_ne' {A} n :
    Proper (pointwise_relation A (dist n) ==> dist n) (@ex_fml _ _ _ _ _ A).
  Proof. move=> ?? eq. by apply ex_fml_ne. Qed.
  #[export] Instance ex_fml_proper' {A} :
    Proper (pointwise_relation A (≡) ==> (≡)) (@ex_fml _ _ _ _ _ A).
  Proof.
    move=> ?? eq. apply equiv_dist=> n. apply ex_fml_ne=> a.
    by apply equiv_dist.
  Qed.

  (** [≡]-properness of every formula constructor, so that [Sync] - which is
    an equation of formulas (see [typing/type.v]) - can be proved by plain
    [rewrite]. *)
  #[export] Instance sep_fml_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (bor_sep (FML:=FML) (Σ:=Σ)) :=
    ne_proper_2 _.
  #[export] Instance or_fml_proper : Proper ((≡) ==> (≡) ==> (≡)) or_fml :=
    ne_proper_2 _.
  #[export] Instance guard_fml_proper :
    Proper ((≡) ==> (≡) ==> (≡)) guard_fml := ne_proper_2 _.
  #[export] Instance idxbor_fml_proper {κ idx} :
    Proper ((≡) ==> (≡)) (idxbor_fml κ idx) := ne_proper _.
  #[export] Instance exs_fml_proper' {𝔄} :
    Proper (pointwise_relation (~~𝔄) (≡) ==> (≡)) (@exs_fml _ _ _ _ _ 𝔄).
  Proof.
    move=> ?? eq. apply equiv_dist=> n. apply exs_fml_ne=> a.
    by apply equiv_dist.
  Qed.

  (** Persistence, so that the [Persistent] obligations of the type formers
    are discharged by type class search as they were before. *)
  #[export] Instance false_fml_persistent : Persistent (bor_sem false_fml).
  Proof. rewrite false_fml_sem. exact _. Qed.
  #[export] Instance empty_fml_persistent : Persistent (bor_sem empty_fml).
  Proof. rewrite empty_fml_sem. exact _. Qed.
  #[export] Instance pure_fml_persistent {φ} :
    Persistent (bor_sem (pure_fml φ)).
  Proof. rewrite pure_fml_sem. exact _. Qed.
  #[export] Instance dead_fml_persistent {κ} :
    Persistent (bor_sem (dead_fml κ)).
  Proof. rewrite dead_fml_sem. exact _. Qed.
  #[export] Instance or_fml_persistent {Px Qx} :
    Persistent (bor_sem Px) → Persistent (bor_sem Qx) →
    Persistent (bor_sem (or_fml Px Qx)).
  Proof. move=> ??. rewrite or_fml_sem. exact _. Qed.
  #[export] Instance sep_fml_persistent {Px Qx} :
    Persistent (bor_sem Px) → Persistent (bor_sem Qx) →
    Persistent (bor_sem (bor_sep Px Qx)).
  Proof. move=> ??. rewrite bor_sep_sem. exact _. Qed.
  #[export] Instance empty_fml_timeless : Timeless (bor_sem empty_fml).
  Proof. rewrite empty_fml_sem. exact _. Qed.
  #[export] Instance false_fml_timeless : Timeless (bor_sem false_fml).
  Proof. rewrite false_fml_sem. exact _. Qed.

  (** Directed forms of the semantics equations, for [iApply] and
    [iDestruct]: rewriting an [⊣⊢] inside the Iris proof context trips over
    the [Proper] search for [envs]. *)
  Lemma false_fml_sem_1 : bor_sem false_fml ⊢ False.
  Proof. by rewrite false_fml_sem. Qed.
  Lemma pure_fml_sem_1 {φ} : bor_sem (pure_fml φ) ⊢ ⌜φ⌝.
  Proof. by rewrite pure_fml_sem. Qed.
  Lemma pure_fml_sem_2 {φ} : φ → ⊢ bor_sem (pure_fml φ).
  Proof. move=> ?. rewrite pure_fml_sem. by iPureIntro. Qed.
  Lemma sep_fml_sem_1 {Px Qx} :
    bor_sem (bor_sep Px Qx) ⊢ bor_sem Px ∗ bor_sem Qx.
  Proof. by rewrite bor_sep_sem. Qed.
  Lemma sep_fml_sem_2 {Px Qx} :
    bor_sem Px -∗ bor_sem Qx -∗ bor_sem (bor_sep Px Qx).
  Proof. rewrite bor_sep_sem. by iIntros "$$". Qed.
End type_fml.

(** ** Candidate interpretations

  [guard_fml] denotes a proposition that quantifies over the *guarding world
  satisfaction*, and that world satisfaction interprets every formula:
  [alerus_WGuard] is [llft_wsatG = WG ∗ shr_wsat ∗ box_wsat bor_sem ∗
  llft_inv_main] ([nola.alerus.lifetime.lifetime_full]).  So
  [bor_sem (guard_fml Px Qx)] would have to be given in terms of [bor_sem] at
  formulas that are *not* subformulas of [guard_fml Px Qx], with the
  occurrence on both sides of a [-∗] and no [▷] to guard it: neither a
  structural recursion over the formula language nor a contractive fixpoint.
  A [⊣⊢] semantics for it therefore does not exist.  The same goes for
  [idxbor_fml] and for [typing/function.v]'s [fn_fml].

  Nola's answer is magic derivability ([nola.bi.deriv]): such a formula is a
  *judgment*, its semantics at a derivability candidate [δ] is [δ J], and the
  knot is tied by [der = psg …], which gives only the post-fixpoint
  [der J ⊢ ⟦J⟧(der)].  So *eliminating* a stored guard is an entailment at the
  ambient interpretation, while *introducing* one asks for the guard at every
  candidate ([Deriv_factor']), with [dinto δ δ'] in hand to read the guards
  one already holds at that candidate.  [nola.iris.inv_deriv] stores
  [inv_acsr] - an accessor over [inv_wsat ⟦⟧(δ)] - in exactly this way.

  [AltSem] is that interface with [JUDG] abstracted away.  [alt_sem sem] says
  [sem] is a candidate interpretation, [alt_WGuard sem] is the guarding world
  satisfaction at it, and [alt_into sem] is Nola's [dinto bor_sem sem].  A
  side condition that has to hold "uniformly in δ'" is written
  [∀ sem, alt_sem sem → …].

  The [_at] fields repeat the equations of [BorSem], [EmptySem], [GsrcSem]
  and [TypeFml] at an arbitrary candidate.  In the intended model those
  constructors' [Ecsem] ignores [δ] altogether, so each is a [reflexivity];
  they are needed because a guard's endpoints are ordinary formulas whose
  meaning one has to know while proving the guard at a candidate. *)
Class AltSem (FML : oFunctor) Σ
  `{!alerusGS FML Σ, !AlerusSem FML Σ, !GsrcSem FML Σ, !TypeFml FML Σ,
    StBor0 : !StBor FML Σ, StBorSem0 : !StBorSem} := {
  (** [sem] is a candidate interpretation.  In the model, [Deriv ih sem]:
    [sem] is a good derivability predicate. *)
  alt_sem : Cand FML Σ → Prop;
  (** [alt_into sem sem']: a judgment stored at [sem] can be read at [sem'].
    Nola's [dinto δ δ'], which [Deriv_factor'] hands out. *)
  alt_into : Cand FML Σ → Cand FML Σ → Prop;
  (** The guarding world satisfaction at a candidate *)
  (** The ambient interpretation is a candidate and is its own guarding world
    satisfaction; every candidate maps into itself *)
  alt_here : alt_sem alt_amb;
  (** The ambient interpretation maps into itself.

    **Only** the ambient one.  In the model [alt_into δ δ'] is Nola's
    [dinto δ δ' = ∀ J, δ J ⊢ ⟦J⟧(δ')], and that at [δ' = δ] is *soundness*
    of [δ], which [nola/bi/deriv.v] proves for [der] ([der_sound],
    Theorem 4.3 of the thesis) and for no other candidate.  So a judgment
    can be eliminated at the ambient interpretation and nowhere else; a
    candidate only ever *receives* judgments stored at the ambient one,
    by instantiating the family that [dincl] is. *)
  alt_into_here : alt_into alt_amb alt_amb;
  (** Every candidate can read a judgment stored at the ambient
    interpretation.  In the model the candidates are the derivability
    candidates [δ'] with [dinto der δ'], which [Deriv_factor']'s induction
    hypothesis carries along. *)

  (** [alt_any sem]: [sem] is *some* interpretation, good or not.  In the
    model [∃ δ, cand_asem sem = AlerusSem_at δ], with no [Deriv].

    The constructors whose semantics is definitional mean the same at every
    interpretation, not just at every candidate, and [idxbor_fml_iff_at]
    needs exactly that: with [st_iff] no longer restricted to the good
    interpretations - which is what takes [Deriv], and so [Jsem], out of
    [idx_bor] - the alteration it asks for has to hold off the candidates
    too.  See [typing/inst.v]. *)
  alt_any : Cand FML Σ → Prop;
  alt_sem_any {sem} : alt_sem sem → alt_any sem;

  alt_any_ne {sem} : alt_any sem → NonExpansive sem;

  (** The non-judgment constructors mean the same at every candidate *)
  sep_sem_at_any {sem} : alt_any sem → ∀ Px Qx,
    sem (bor_sep Px Qx) ⊣⊢ sem Px ∗ sem Qx;
  false_sem_at_any {sem} : alt_any sem → sem false_fml ⊣⊢ False;
  empty_sem_at_any {sem} : alt_any sem → sem empty_fml ⊣⊢ True;
  pure_sem_at_any {sem} : alt_any sem → ∀ φ, sem (pure_fml φ) ⊣⊢ ⌜φ⌝;
  ex_sem_at_any {sem} : alt_any sem → ∀ A (Φ : A → FML $oi Σ),
    sem (ex_fml Φ) ⊣⊢ ∃ a : A, sem (Φ a);
  exs_sem_at_any {sem} : alt_any sem → ∀ 𝔄 (Φ : (~~𝔄) → FML $oi Σ),
    sem (exs_fml Φ) ⊣⊢ ∃ a : ~~𝔄, sem (Φ a);
  or_sem_at_any {sem} : alt_any sem → ∀ Px Qx,
    sem (or_fml Px Qx) ⊣⊢ sem Px ∨ sem Qx;
  pers_sem_at_any {sem} : alt_any sem → ∀ Px, sem (pers_fml Px) ⊣⊢ □ sem Px;
  alive_sem_at_any {sem} : alt_any sem → ∀ κ, sem (alive_fml κ) ⊣⊢ @[κ];
  dead_sem_at_any {sem} : alt_any sem → ∀ κ, sem (dead_fml κ) ⊣⊢ [†κ];
  cells_sem_at_any {sem} : alt_any sem → ∀ l cs fv,
    sem (cells_fml l cs fv) ⊣⊢ l ↦[^ cs ]!∗ fv;
  ccells_sem_at_any {sem} : alt_any sem → ∀ l fv,
    sem (ccells_fml l fv) ⊣⊢ l #↦!∗ fv;
  cmapstoany_sem_at_any {sem} : alt_any sem → ∀ l,
    sem (cmapstoany_fml l) ⊣⊢ l #↦∗_;
  freeable_sem_at_any {sem} : alt_any sem → ∀ n sz l,
    sem (freeable_fml n sz l) ⊣⊢ freeable_sz n sz l;
  vo_sem_at_any {sem} : alt_any sem → ∀ ξ x d, sem (vo_fml ξ x d) ⊣⊢ .VO[ξ] x d;
  pc_sem_at_any {sem} : alt_any sem → ∀ ξ x vπ d,
    sem (pc_fml ξ x vπ d) ⊣⊢ .PC[ξ] x vπ d;
  gsrc_sem_at_any {sem} : alt_any sem → ∀ s,
    sem (gsrc_fml s) ⊣⊢ gsrc_interp s;
  (** Reading a stored formula, at the *ambient* interpretation.  That is
    the only place it is needed: a guarded former reads it while building a
    guard, and a guard's body is handed the world satisfaction. *)
  store_fml_acc {Px} :
    bor_sem (store_fml Px) ⊢ □ |->[alerus_WGuard] bor_sem Px;
  (** Storing a formula whose semantics is persistent at every candidate *)
  store_fml_alloc {Px} :
    (∀ sem, alt_sem sem → Persistent (sem Px)) →
    bor_sem Px =[alerus_WGuard]=∗ bor_sem (store_fml Px);
  store_fml_pers_at_any {sem} : alt_any sem → ∀ Px,
    Persistent (sem (store_fml Px));
  (** Transporting a stored formula along an entailment that holds at every
    candidate the storing one maps into.  [Deriv_map] in the model. *)
  store_fml_map_at {sem} : alt_sem sem → ∀ Px Qx,
    □ (∀ sem' (_ : alt_sem sem') (_ : alt_into sem sem'), sem' Px -∗ sem' Qx) -∗
    sem (store_fml Px) -∗ sem (store_fml Qx);
  (** [dinv_fml] is the invariant *token*, at every candidate: the token
    does not mention the interpretation, only the formula. *)
  dinv_fml_sem_at_any {sem} : alt_any sem → ∀ Px,
    sem (dinv_fml Px) ⊣⊢ @dinv_tok FML Σ alerus_dinvGS Px;

  (** Reading a guard stored at [sem], at a candidate [sem] maps into.  In
    the model this is [dinto δ δ'] applied to the guard judgment. *)
  guard_fml_sem_into {sem sem'} :
    alt_sem sem → alt_sem sem' → alt_into sem sem' → ∀ Px Qx,
    sem (guard_fml Px Qx) ⊢ sem' Px &&{alt_WGuard sem'}&&> sem' Qx;
  (** Storing a guard.  In the model this is [Deriv_factor'] at [sem]. *)
  guard_fml_sem_2 {sem} : alt_sem sem → ∀ Px Qx,
    (∀ sem', ⌜alt_sem sem'⌝ → ⌜alt_into sem sem'⌝ →
      sem' Px &&{alt_WGuard sem'}&&> sem' Qx) ⊢ sem (guard_fml Px Qx);

  (** A stored guard is persistent.  In the model [δ J] is under a [□]. *)
  guard_fml_pers_at_any {sem} : alt_any sem → ∀ Px Qx,
    Persistent (sem (guard_fml Px Qx));
  (** An indexed borrow stored at a candidate is persistent.  [idx_bor] is a
    judgment in the same sense as [guard_fml] - it carries
    [□ (bor_sem Px' ↔ bor_sem Px)] - so only its persistence is available
    here; see the note in README.md. *)
  idxbor_fml_pers_at_any {sem} : alt_any sem → ∀ κ idx Px,
    Persistent (sem (idxbor_fml κ idx Px));
  (** The alteration a stored borrow carries.

    [nola/iris/borrow_deriv.v]'s relaxed borrower is
    [bor δ α Px := ∃ Qx, □ δ (jbupd Px Qx) ∗ □ δ (jbupd Qx Px) ∗ bor_tok α Qx]
    - the thesis's § 6.4 - and [nola/examples/rust_halt/]'s [ty_mutref]
    stores exactly that, which is what gives it [subty_mutref] with a premise
    restricted to the *good* candidates.  [dalter] is the pair of those two
    judgments at the ambient interpretation: readable there, and - crucially
    - re-storable, which the bare equivalence [□ (bor_sem Px ↔ bor_sem Qx)]
    would not be. *)
  dalter : FML $oi Σ → FML $oi Σ → iProp Σ;
  #[global] dalter_persistent :: ∀ Px Qx, Persistent (dalter Px Qx);
  dalter_refl {Px} : ⊢ dalter Px Px;
  dalter_trans {Px Qx Rx} : dalter Px Qx -∗ dalter Qx Rx -∗ dalter Px Rx;
  (** Reading one: [der_sound] in the model *)
  dalter_sem {Px Qx} : dalter Px Qx ⊢ □ (bor_sem Px ↔ bor_sem Qx);
  (** Building one: [Deriv_factor'] at the ambient interpretation, so the
    equivalence is wanted only at the candidates it maps into. *)
  dalter_of_into {Px Qx} :
    □ (∀ sem, ⌜alt_sem sem⌝ → ⌜alt_into alt_amb sem⌝ → sem Px ∗-∗ sem Qx) ⊢
      dalter Px Qx;
  (** Eliminating a stored indexed borrow at the ambient interpretation,
    together with the alteration it carries.  [der_sound] in the model. *)
  idxbor_fml_sem_1 {κ idx Px} :
    bor_sem (idxbor_fml κ idx Px) ⊢ ∃ Px', dalter Px' Px ∗ idx_bor κ idx Px';
  (** Re-storing one under an alteration *)
  idxbor_fml_alter {κ idx Px Qx} :
    dalter Px Qx -∗
    bor_sem (idxbor_fml κ idx Px) -∗ bor_sem (idxbor_fml κ idx Qx);
  (** Introducing one.  Splitting a full borrow into an index and a token
    gives an indexed borrow whose [iff] is reflexivity and whose token does
    not mention the interpretation, so it holds at every candidate - this is
    where an indexed borrow can be stored in the first place. *)
  idxbor_fml_of_bor {κ Px} :
    full_bor κ Px ⊢ ∃ idx, bor_sem (idxbor_fml κ idx Px) ∗ idx_bor_tok idx;
  (** [idx_bor_iff] at a candidate: an indexed borrow only cares about the
    semantics of its contents. *)
  (** [bor_wand] in the model: the alteration is read at the candidates the
    storing one maps into, not at every interpretation whatsoever. *)
  idxbor_fml_iff_at {sem} : alt_sem sem → ∀ κ idx Px Qx,
    □ (∀ sem' (_ : alt_sem sem') (_ : alt_into sem sem'),
         sem' Px ∗-∗ sem' Qx) -∗
    sem (idxbor_fml κ idx Px) -∗ sem (idxbor_fml κ idx Qx);
  (** Borrow-state ownership means the same at every candidate.  This is
    what [idx_bor_tok] is made of. *)
  bor_state_sem_at_any {sem} : alt_any sem → ∀ sn bs,
    sem (bor_state_fml sn bs) ⊣⊢ bor_sem (bor_state_fml sn bs);
  (** [dIdxBor_guard] for a stored indexed borrow, at a candidate:
    the lifetime logic's proof is parametric in [BorSem], so it replays at
    the candidate's own world satisfaction. *)
  idxbor_fml_guard_into {sem} :
    alt_sem sem → alt_into alt_amb sem → ∀ κ idx Px (G : iProp Σ),
    bor_sem (idxbor_fml κ idx Px) -∗
    (G &&{alt_WGuard sem}&&> @[κ]) -∗
    (G &&{alt_WGuard sem}&&> idx_bor_tok idx) -∗
    G &&{alt_WGuard sem}&&> (@[κ] ∗ sem Px);
  (** [llftl_idx_shorten] for a stored indexed borrow, at a candidate.  Like
    [dincl_glb_at] this is a lifetime-logic fact about a judgment, so it is
    [Deriv_map] in the model but cannot be derived here. *)
  idxbor_fml_shorten_at {sem} : alt_sem sem → ∀ κ κ' idx Px,
    st_incl κ' κ -∗
    sem (idxbor_fml κ idx Px) -∗ sem (idxbor_fml κ' idx Px);
  (** Lifetime inclusion is storable.

    [llft_incl κ κ'] is itself a guard over [alerus_WGuard], so it has no
    [⊣⊢] semantics either.  But the lifetime logic's proofs never look at the
    interpretation - they are parametric in [BorSem] - so an inclusion that
    holds at the ambient interpretation holds at every candidate.  In the
    model this is [Deriv_factor'] followed by replaying the same proof. *)
  (** The stored inclusion means the storable one, at every candidate *)
  incl_fml_sem_1 {κ κ'} : bor_sem (incl_fml κ κ') ⊢ st_incl κ κ';
  incl_fml_of_incl {sem} : alt_sem sem → ∀ κ κ',
    st_incl κ κ' ⊢ sem (incl_fml κ κ');
  incl_fml_pers_at_any {sem} : alt_any sem → ∀ κ κ',
    Persistent (sem (incl_fml κ κ'));
  (** An inclusion stored at a candidate is monotone in both arguments.
    [Deriv_map] in the model: the stored inclusion's semantics does not
    mention the interpretation, so the obligation is [st_incl]'s own
    transitivity. *)
  incl_fml_mono_at {sem} : alt_sem sem → ∀ κ0 κ κ' κ1,
    st_incl κ0 κ -∗ st_incl κ' κ1 -∗
    sem (incl_fml κ κ') -∗ sem (incl_fml κ0 κ1);
  (** A *structural* inclusion is storable: [llftl_incl_sub]'s proof
    mentions no interpretation, so it replays at every candidate.  Every
    inclusion the typing layer creates from nothing is of this shape. *)
  st_incl_of_sub {κ κ'} : κ' ⊆ κ → ⊢ st_incl κ κ';
  (** The storable inclusion eliminates at *every* candidate - that is what
    it is for.  In the model it is the family
    [□ ∀ δ good, @[κ] &&{alerus_WGuard_at δ}&&> @[κ']], and this field
    instantiates it. *)
  st_incl_at {sem} : alt_any sem → ∀ κ κ',
    st_incl κ κ' ⊢ @[κ] &&{alt_WGuard sem}&&> @[κ'];
  (** ...and it is *introduced* from exactly that family.

    This is the rule [typing/function.v]'s [fn_incl_of_all] asked for and
    the one the token form of [st_incl] could not give.  [type_call_iris']
    creates a fresh lifetime [ϝ] for the call and the inclusion it then has
    is *semantic* - a guard manufactured from the caller's local lifetime
    context, not a structural containment and not an eternalized lifetime.

    [alt_any] rather than [alt_sem] throughout: "good" is [Deriv], [Deriv]
    is defined from [Jsem], and [st_incl] sits inside [idx_bor], which is a
    judgment's semantics - so a family over the good candidates only would
    close the cycle [typing/inst.v] records.  Over *every* interpretation
    there is no cycle, and nothing is lost, because every proof the
    lifetime logic has about a guard is parametric in [BorSem]. *)
  st_incl_of_all {κ κ'} :
    (□ ∀ sem (_ : alt_any sem), @[κ] &&{alt_WGuard sem}&&> @[κ']) ⊢
      st_incl κ κ';
  (** The lifetime logic's greatest-lower-bound rule for stored inclusions.
    The other inclusion rules are closed facts, so [dincl_of_incl] covers
    them; this one transforms two stored inclusions, so like [dguard_trans]
    it is [Deriv_map] in the model - but its body is a lifetime-logic fact
    at the candidate's own world satisfaction, which the development cannot
    see, so it is asked for here. *)

  (** Eternalizing a lifetime gives a *storable* inclusion: the token
    [eternal_tok] it allocates does not mention the interpretation, so the
    guard it yields holds at every candidate. *)
  st_incl_eternalize {κ} : @[κ] =[alerus_wsat]=∗ st_incl static κ;
  (** [Ltok]'s share guards the local lifetime context at every candidate:
    [frac_key_wsat llctx_interp] is part of [alerus_WG], which every
    candidate's guarding world satisfaction contains and which does not
    mention the interpretation. *)
  Ltok_guard_frac_at {sem} : alt_any sem → ∀ γ L q,
    frac_key_tok γ L ⊢ frac_tok γ q &&{alt_WGuard sem}&&> llctx_interp L;
  (** [llftl_borrow_shared] at the formula level.  The shared borrow it
    allocates is a [sinv_tok], which does not mention the interpretation, and
    [sinv_tok_guard] turns it into a guard at *every* candidate - so this is
    one of the places where a guard can be stored in the first place. *)
  guard_fml_borrow_shared {κ Px} :
    bor_sem Px -∗ |=[alerus_WGuard]=>
      (□ ∀ sem (_ : alt_any sem), @[κ] &&{alt_WGuard sem}&&> sem Px) ∗
      ([†κ] -∗ |=[alerus_WGuard]=> bor_sem Px);
  (** [bor_to_guard] at the formula level.  A full borrow token [&{κ} Px] is
    plain CMRA ownership - it does not mention the interpretation - and
    [bor_to_guard] is parametric in [BorSem], so the guard it yields holds at
    every candidate.  This is the second place where a guard can be stored in
    the first place. *)
  guard_fml_of_bor {κ Px} :
    llft_ctx -∗ full_bor κ Px =[alerus_wsat]=∗
      bor_sem (guard_fml (alive_fml κ) Px);
}.

(** [alt_sem] is a class, so that a hypothesis [alt_sem sem] in the context
  makes [sem] non-expansive for [setoid_rewrite] and [f_equiv]. *)
Existing Class alt_sem.
Existing Class alt_any.

(** The definitional constructors, and the persistence of the judgment
  ones, hold at every interpretation; these are the instances at a
  candidate, under the names the development already uses. *)
Section alt_any.
  Context `{!alerusGS FML Σ, !AlerusSem FML Σ, !GsrcSem FML Σ, !TypeFml FML Σ,
    StBor0 : !StBor FML Σ, StBorSem0 : !StBorSem, !AltSem FML Σ}.
  Definition sep_sem_at {sem} (H : alt_sem sem) := sep_sem_at_any (alt_sem_any H).
  Definition false_sem_at {sem} (H : alt_sem sem) := false_sem_at_any (alt_sem_any H).
  Definition empty_sem_at {sem} (H : alt_sem sem) := empty_sem_at_any (alt_sem_any H).
  Definition pure_sem_at {sem} (H : alt_sem sem) := pure_sem_at_any (alt_sem_any H).
  Definition ex_sem_at {sem} (H : alt_sem sem) := ex_sem_at_any (alt_sem_any H).
  Definition exs_sem_at {sem} (H : alt_sem sem) := exs_sem_at_any (alt_sem_any H).
  Definition or_sem_at {sem} (H : alt_sem sem) := or_sem_at_any (alt_sem_any H).
  Definition alive_sem_at {sem} (H : alt_sem sem) := alive_sem_at_any (alt_sem_any H).
  Definition dead_sem_at {sem} (H : alt_sem sem) := dead_sem_at_any (alt_sem_any H).
  Definition cells_sem_at {sem} (H : alt_sem sem) := cells_sem_at_any (alt_sem_any H).
  Definition ccells_sem_at {sem} (H : alt_sem sem) := ccells_sem_at_any (alt_sem_any H).
  Definition cmapstoany_sem_at {sem} (H : alt_sem sem) := cmapstoany_sem_at_any (alt_sem_any H).
  Definition freeable_sem_at {sem} (H : alt_sem sem) := freeable_sem_at_any (alt_sem_any H).
  Definition vo_sem_at {sem} (H : alt_sem sem) := vo_sem_at_any (alt_sem_any H).
  Definition pc_sem_at {sem} (H : alt_sem sem) := pc_sem_at_any (alt_sem_any H).
  Definition gsrc_sem_at {sem} (H : alt_sem sem) := gsrc_sem_at_any (alt_sem_any H).
  Definition bor_state_sem_at {sem} (H : alt_sem sem) := bor_state_sem_at_any (alt_sem_any H).
  Definition guard_fml_pers_at {sem} (H : alt_sem sem) := guard_fml_pers_at_any (alt_sem_any H).
  Definition store_fml_pers_at {sem} (H : alt_sem sem) := store_fml_pers_at_any (alt_sem_any H).
  Definition dinv_fml_sem_at {sem} (H : alt_sem sem) := dinv_fml_sem_at_any (alt_sem_any H).
  Definition idxbor_fml_pers_at {sem} (H : alt_sem sem) := idxbor_fml_pers_at_any (alt_sem_any H).
  Definition incl_fml_pers_at {sem} (H : alt_sem sem) := incl_fml_pers_at_any (alt_sem_any H).
  Definition alt_sem_ne {sem} (H : alt_sem sem) := alt_any_ne (alt_sem_any H).
End alt_any.

Section alt_sem.
  Context `{!alerusGS FML Σ, !AlerusSem FML Σ, !GsrcSem FML Σ, !TypeFml FML Σ,
    StBor0 : !StBor FML Σ, StBorSem0 : !StBorSem, !AltSem FML Σ}.
  Implicit Type Px Qx Rx Sx : FML $oi Σ.

  #[export] Instance alt_sem_ne' {sem} `{Hs : !alt_sem sem} :
    NonExpansive sem := alt_sem_ne Hs.

  (** ** A guard held *as a formula*

    Everything the development does with a stored guard goes through these.
    [dguard_sem] drops one to an actual Leaf guard, which is all one needs
    to *open* it; every other lemma builds one stored guard out of others,
    and is [Deriv_map] in the intended model.  Each comes in a version at an
    arbitrary candidate interpretation, needed while proving a guard inside
    [dguard_of_all], and one at the ambient interpretation. *)

  Definition dguard Px Qx : iProp Σ := bor_sem (guard_fml Px Qx).

  #[export] Instance dguard_persistent {Px Qx} : Persistent (dguard Px Qx).
  Proof. rewrite /dguard. by apply (guard_fml_pers_at alt_here). Qed.
  #[export] Instance dguard_ne : NonExpansive2 dguard.
  Proof. solve_proper. Qed.
  #[export] Instance dguard_proper : Proper ((≡) ==> (≡) ==> (⊣⊢)) dguard.
  Proof. apply ne_proper_2, _. Qed.

  (** Elimination *)
  Lemma guard_fml_sem_1 {Px Qx} :
    bor_sem (guard_fml Px Qx) ⊢ bor_sem Px &&{alerus_WGuard}&&> bor_sem Qx.
  Proof.
    rewrite -alt_WGuard_here.
    exact: (guard_fml_sem_into alt_here alt_here alt_into_here).
  Qed.
  Lemma dguard_sem {Px Qx} :
    dguard Px Qx ⊢ bor_sem Px &&{alerus_WGuard}&&> bor_sem Qx.
  Proof. exact guard_fml_sem_1. Qed.

  (** Persistence of a stored guard at the ambient interpretation.  The
    [TypeFml] section cannot state this: [guard_fml] has no [⊣⊢] there. *)
  #[export] Instance guard_fml_persistent {Px Qx} :
    Persistent (bor_sem (guard_fml Px Qx)) := guard_fml_pers_at alt_here _ _.
  #[export] Instance store_fml_persistent {Px} :
    Persistent (bor_sem (store_fml Px)) := store_fml_pers_at alt_here _.

  (** *** A simple invariant, and the guard it is

    [dinv_fml] is persistent at every candidate because [dinv_tok] is. *)
  (** [bor_sem] is [alt_amb] only up to conversion, so the ambient form is
    taken by [exact] rather than by [rewrite]. *)
  Lemma dinv_fml_sem_1 {Px} :
    bor_sem (dinv_fml Px) ⊢ @dinv_tok FML Σ alerus_dinvGS Px.
  Proof.
    exact (bi.equiv_entails_1_1 _ _ (dinv_fml_sem_at alt_here Px)).
  Qed.
  Lemma dinv_fml_sem_2 {Px} :
    @dinv_tok FML Σ alerus_dinvGS Px ⊢ bor_sem (dinv_fml Px).
  Proof.
    exact (bi.equiv_entails_1_2 _ _ (dinv_fml_sem_at alt_here Px)).
  Qed.

  Lemma dinv_fml_pers_at {sem} (H : alt_any sem) {Px} :
    Persistent (sem (dinv_fml Px)).
  Proof. rewrite (dinv_fml_sem_at_any H). exact _. Qed.
  #[export] Instance dinv_fml_persistent {Px} :
    Persistent (bor_sem (dinv_fml Px)) := dinv_fml_pers_at (alt_sem_any alt_here).

  (** Allocating one: the content moves into the store world satisfaction,
    which sits inside [alerus_WGuard]. *)
  Lemma dinv_fml_alloc {Px} :
    bor_sem Px =[alerus_WGuard]=∗ bor_sem (dinv_fml Px).
  Proof.
    iIntros "Px W".
    iDestruct (wsat_split (W:=alerus_WGuard) (W':=alerus_store_wsat) with "W")
      as "[Wst Wr]".
    iMod (dinv_tok_alloc (FML:=FML) (sm:=bor_sem) Px with "Px Wst")
      as "[Wst #i]".
    iDestruct (wsat_join (W:=alerus_WGuard) with "Wst Wr") as "$".
    iModIntro. by iApply dinv_fml_sem_2.
  Qed.

  (** Opening one, at any candidate: the content comes back out, and has to
    go back in.  That is the whole difference from [store_fml_acc]. *)
  Lemma dinv_fml_acc_at {sem} (H : alt_any sem) {Px} :
    sem (dinv_fml Px) -∗ @dinv_wsat FML Σ alerus_dinvGS sem -∗
      sem Px ∗ (sem Px -∗ @dinv_wsat FML Σ alerus_dinvGS sem).
  Proof. rewrite (dinv_fml_sem_at_any H). exact dinv_tok_acc. Qed.

  (** **** A simple invariant *is* a guard

    Leaf's central move, and the reason an owning pointer can keep its
    pointee behind [dinv_fml] and still let [ty_guard_proph] reach it: the
    world satisfaction is guarded by anything ([guard_wsat_out]), and the
    invariant turns the world satisfaction into its content, reversibly
    ([guard_intro]). *)
  Lemma dinv_fml_guard {Px} :
    bor_sem (dinv_fml Px) ⊢ (True &&{alerus_WGuard}&&> bor_sem Px).
  Proof.
    iIntros "#i". iApply (guard_trans (Q:=alerus_store_wsat)).
    { iApply (guard_wsat_out (W':=alerus_store_wsat)). }
    iApply guard_intro. iIntros "!> W".
    rewrite /alerus_store_wsat.
    by iApply (dinv_fml_acc_at (alt_sem_any alt_here) with "i W").
  Qed.

  (** ...so holding the token outright gives a guard on the content against
    *any* left-hand side.  An owning pointer therefore keeps the token in
    its persistent component, where [ty_guard_proph] is handed it directly,
    rather than reaching for it through the guard it is given - which it
    could not do, [guard_acc] needing the left-hand side. *)
  Lemma dinv_fml_guard_any {R Px} :
    bor_sem (dinv_fml Px) ⊢ (R &&{alerus_WGuard}&&> bor_sem Px).
  Proof.
    iIntros "#i". iApply (guard_trans (Q:=True%I)); [iApply guard_true|].
    by iApply dinv_fml_guard.
  Qed.

  (** **** ...and the guard is itself storable, which the token is not

    [dinv_fml Px] names the formula it stores, so nothing turns
    [dinv_tok Px] into [dinv_tok Qx] and a former holding one admits no
    subtyping rule.  A *guard* does compose ([guard_trans]), so a former
    holding [guard_fml empty_fml Px] does - which is why [&shr{κ}] has a
    subtyping rule and an owning pointer behind a bare token has none.

    The two are interderivable in the direction that matters: the token
    gives the guard at every candidate ([dinv_fml_guard_at]), and
    [guard_fml_sem_2] stores it.  So an owning pointer can hold the guard
    and still be *allocated*, which is the only thing the token was there
    for.  This is the thesis's (5.5) read in the port's terms: its [ref°]
    stores a different type tied by two derivability assertions precisely
    so that [≤-ref] goes through, and a Leaf guard is that indirection
    already. *)
  Definition alt_store_wsat (S : Cand FML Σ) : iProp Σ :=
    @alerus_store_wsat FML Σ _ (cand_asem S).

  Lemma dinv_fml_guard_at {sem} (H : alt_sem sem) {Px} :
    sem (dinv_fml Px) ⊢ (True &&{alt_WGuard sem}&&> sem Px).
  Proof.
    have ? := dinv_fml_pers_at (alt_sem_any H) (Px:=Px).
    iIntros "#i". iApply (guard_trans (Q:=alt_store_wsat sem)).
    { iApply (guard_wsat_out (W':=alt_store_wsat sem)). }
    iApply guard_intro. iIntros "!> W".
    rewrite /alt_store_wsat /alerus_store_wsat.
    by iApply (dinv_fml_acc_at (alt_sem_any H) with "i W").
  Qed.

  Lemma eguard_fml_alloc {Px} :
    bor_sem Px =[alerus_WGuard]=∗ bor_sem (guard_fml empty_fml Px).
  Proof.
    iIntros "Px W". iMod (dinv_fml_alloc with "Px W") as "[$ #i]". iModIntro.
    iApply (guard_fml_sem_2 alt_here). iIntros (sem' Hs Hi).
    have ? := dinv_fml_pers_at (alt_sem_any Hs) (Px:=Px).
    iAssert (sem' (dinv_fml Px)) as "#i'".
    { rewrite (dinv_fml_sem_at_any (alt_sem_any Hs)). by iApply dinv_fml_sem_1. }
    rewrite (empty_sem_at_any (alt_sem_any Hs)).
    by iApply (dinv_fml_guard_at Hs).
  Qed.

  Lemma eguard_fml_empty : ⊢ True &&{alerus_WGuard}&&> bor_sem empty_fml.
  Proof.
    iApply guard_intro. iIntros "!> _". iSplit; [|by iIntros "_"].
    by iApply (bi.equiv_entails_1_2 _ _ (empty_sem_at alt_here)).
  Qed.

  Lemma eguard_fml_guard_any {R Px} :
    bor_sem (guard_fml empty_fml Px) ⊢ (R &&{alerus_WGuard}&&> bor_sem Px).
  Proof.
    iIntros "#g". iDestruct (guard_fml_sem_1 with "g") as "#g'".
    iApply (guard_trans with "[] g'").
    iApply (guard_trans (Q:=True%I)); [iApply guard_true|].
    iApply eguard_fml_empty.
  Qed.
  #[export] Instance idxbor_fml_persistent {κ idx Px} :
    Persistent (bor_sem (idxbor_fml κ idx Px)) :=
    idxbor_fml_pers_at alt_here _ _ _.

  (** Reading the alteration a stored borrow carries *)
  Lemma dalter_sem_1 {Px Qx : FML $oi Σ} :
    dalter Px Qx -∗ bor_sem Px -∗ bor_sem Qx.
  Proof.
    iIntros "#a P". iDestruct (dalter_sem with "a") as "#[F _]".
    by iApply "F".
  Qed.
  Lemma dalter_sem_2 {Px Qx : FML $oi Σ} :
    dalter Px Qx -∗ bor_sem Qx -∗ bor_sem Px.
  Proof.
    iIntros "#a Q". iDestruct (dalter_sem with "a") as "#[_ Bk]".
    by iApply "Bk".
  Qed.

  (** ** The relaxed borrow

    [nola/iris/borrow_deriv.v] states the borrow API at
    [bor δ α Px := ∃ Qx, □ δ (jbupd Px Qx) ∗ □ δ (jbupd Qx Px) ∗ bor_tok α Qx]
    rather than at the token, which is what lets a stored borrow be altered
    with a premise restricted to the good candidates.  This is that layer: a
    borrow of [Px] up to the alteration a stored one carries.

    Unlike upstream, the API does not have to be restated wholesale.
    [dFullBor_exact] turns a relaxed full borrow back into an exact one
    under an update - open it atomically, carry the contents across the
    alteration, close - so every existing [full_bor] lemma applies
    unchanged.  Only the lemmas that consume an [idx_bor] directly need a
    transported form. *)
  Definition dFullBor (κ : lft) (Px : FML $oi Σ) : iProp Σ :=
    ∃ Px', dalter Px' Px ∗ full_bor κ Px'.
  Definition dIdxBor (κ : lft) (idx : Idx) (Px : FML $oi Σ) : iProp Σ :=
    ∃ Px', dalter Px' Px ∗ idx_bor κ idx Px'.

  #[export] Instance dIdxBor_persistent {κ idx Px} :
    Persistent (dIdxBor κ idx Px) := _.

  Lemma dFullBor_of {κ Px} : full_bor κ Px ⊢ dFullBor κ Px.
  Proof. iIntros "b". iExists Px. iFrame "b". iApply dalter_refl. Qed.
  Lemma dIdxBor_of {κ idx Px} : idx_bor κ idx Px ⊢ dIdxBor κ idx Px.
  Proof. iIntros "#b". iExists Px. iFrame "b". iApply dalter_refl. Qed.
  Lemma dFullBor_alter {κ Px Qx} :
    dalter Px Qx -∗ dFullBor κ Px -∗ dFullBor κ Qx.
  Proof.
    iIntros "#a (%Rx & #a' & b)". iExists Rx. iFrame "b".
    iApply (dalter_trans with "a' a").
  Qed.
  Lemma dIdxBor_alter {κ idx Px Qx} :
    dalter Px Qx -∗ dIdxBor κ idx Px -∗ dIdxBor κ idx Qx.
  Proof.
    iIntros "#a (%Rx & #a' & #b)". iExists Rx. iFrame "b".
    iApply (dalter_trans with "a' a").
  Qed.

  (** A stored indexed borrow is a relaxed one *)
  Lemma idxbor_fml_dIdxBor {κ idx Px} :
    bor_sem (idxbor_fml κ idx Px) ⊢ dIdxBor κ idx Px.
  Proof. exact idxbor_fml_sem_1. Qed.

  Lemma dIdxBor_to_full {κ idx Px} :
    dIdxBor κ idx Px -∗ idx_bor_tok idx -∗ dFullBor κ Px.
  Proof.
    iIntros "(%Px' & #a & #b) tok". iExists Px'. iFrame "a".
    iApply (llftl_bor_idx_to_full with "b tok").
  Qed.
  Lemma dFullBor_idx {κ Px} :
    dFullBor κ Px ⊢ ∃ idx, dIdxBor κ idx Px ∗ idx_bor_tok idx.
  Proof.
    iIntros "(%Px' & #a & b)". rewrite llftl_bor_idx.
    iDestruct "b" as (idx) "[#b tok]". iExists idx. iFrame "tok".
    iExists Px'. by iFrame "a b".
  Qed.
  Lemma dIdxBor_shorten {κ κ' idx Px} :
    st_incl κ' κ -∗ dIdxBor κ idx Px -∗ dIdxBor κ' idx Px.
  Proof.
    iIntros "#i (%Px' & #a & #b)". iExists Px'. iFrame "a".
    iApply (llftl_idx_shorten with "i b").
  Qed.

  (** Back to an exact borrow.  This is what keeps the rest of the borrow
    API usable: open the borrow atomically, carry its contents across the
    alteration, and close it at the formula we wanted. *)
  Lemma dFullBor_exact {E κ Px} :
    llft_ctx -∗ dFullBor κ Px -∗ |=[llft_wsat]{E}=> full_bor κ Px.
  Proof.
    iIntros "#ctx (%Px' & #a & b)". rewrite /modw. iIntros "W".
    iMod (llftl_bor_acc_atomic E Px' κ with "ctx b W")
      as "[[P back]|[W #dead]]".
    - iDestruct (dalter_sem_1 with "a P") as "P".
      iMod ("back" $! Px with "[] P") as "[$ $]"; [|done].
      iIntros "[P _] !>". by iApply (dalter_sem_2 with "a P").
    - iMod (llftl_bor_fake E κ Px with "ctx dead W") as "[$ $]". done.
  Qed.

  (** [llftl_idx_bor_unnest], transported *)
  Lemma dIdxBor_unnest {E κ κ' idx Px} :
    llft_ctx -∗ dIdxBor κ idx Px -∗
    full_bor κ' (bor_state_fml idx.1
      (ra.Borrow (set_map ra.LtAtomSwell idx.2) {[ra.default_dead]})) -∗
    |=[llft_wsat]{E}=> dFullBor (κ ⊓ κ') Px.
  Proof.
    iIntros "#ctx (%Px' & #a & #b) f". rewrite /modw. iIntros "W".
    iMod (llftl_idx_bor_unnest E κ κ' idx Px' with "ctx b f W") as "[$ b']".
    iModIntro. iExists Px'. by iFrame "a b'".
  Qed.

  (** [llftl_idx_bor_guard'] and [llftl_bor_idx_acc_guarded], transported *)
  Lemma dIdxBor_guard {κ idx Px G} :
    llft_ctx -∗ dIdxBor κ idx Px -∗ (G &&{alerus_WGuard}&&> @[κ]) -∗
    (G &&{alerus_WGuard}&&> idx_bor_tok idx) -∗
    G &&{alerus_WGuard}&&> (@[κ] ∗ bor_sem Px).
  Proof.
    iIntros "#ctx (%Px' & #a & #b) #Gk #Gt".
    iDestruct (llftl_idx_bor_guard' with "ctx b Gk Gt") as "#G".
    iDestruct (dalter_sem with "a") as "#[F Bk]".
    iApply (guard_trans with "G"). iApply guard_intro.
    iIntros "!> [$ P]". iSplitL "P"; [by iApply "F"|].
    iIntros "[$ Q]". by iApply "Bk".
  Qed.
  Lemma dIdxBor_acc_guarded {E Gx κ idx Px} :
    llft_ctx -∗ dIdxBor κ idx Px -∗ idx_bor_tok idx -∗
    (bor_sem Gx &&{alerus_WGuard}&&> @[κ]) -∗
    bor_sem Gx -∗ |=[llft_wsat]{E}=>
      bor_sem Px ∗ (bor_sem Px -∗
        |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> idx_bor_tok idx ∗ bor_sem Gx).
  Proof.
    iIntros "#ctx (%Px' & #a & #b) tok #Gk G".
    iDestruct (llftl_bor_idx_acc_guarded with "ctx b tok Gk G") as "A".
    rewrite /modw. iIntros "W". iMod ("A" with "W") as "[W [P back]]".
    iDestruct (dalter_sem_1 with "a P") as "$". iFrame "W". iIntros "!> P".
    iApply "back". by iApply (dalter_sem_2 with "a P").
  Qed.

  (** A stored indexed borrow plus its token is a full borrow *)
  Lemma idxbor_fml_to_full {κ idx Px} :
    bor_sem (idxbor_fml κ idx Px) -∗ idx_bor_tok idx -∗
      ∃ Px', dalter Px' Px ∗ full_bor κ Px'.
  Proof.
    rewrite idxbor_fml_sem_1. iIntros "(%Px' & #a & b) tok". iExists Px'.
    iFrame "a". iApply (llftl_bor_idx_to_full with "b tok").
  Qed.

  (** Introduction *)
  Lemma dguard_of_all_at {sem} (H : alt_sem sem) {Px Qx} :
    (∀ sem', ⌜alt_sem sem'⌝ → ⌜alt_into sem sem'⌝ →
      sem' Px &&{alt_WGuard sem'}&&> sem' Qx) ⊢ sem (guard_fml Px Qx).
  Proof. exact: guard_fml_sem_2. Qed.
  (** [dguard_of_all_at] at the ambient interpretation.  Note it is not
    stated separately: writing the ambient candidate in a statement that
    also binds a candidate would have the binder shadow it, since any
    [AlerusSem] in scope is an instance. *)
  Notation dguard_of_all := (dguard_of_all_at alt_here).

  (** ** Building stored guards out of stored guards *)

  Lemma dguard_refl_at {sem} (H : alt_sem sem) {Px} :
    ⊢ sem (guard_fml Px Px).
  Proof. iApply (dguard_of_all_at H). iIntros (???). iApply guard_refl. Qed.

  Lemma dguard_true_at {sem} (H : alt_sem sem) {Px} :
    ⊢ sem (guard_fml Px empty_fml).
  Proof.
    iApply (dguard_of_all_at H). iIntros (sem' Hs ?).
    rewrite (empty_sem_at Hs). iApply guard_true.
  Qed.

  Lemma dguard_trans_at {sem} (H : alt_sem sem) {Px Qx Rx} :
    sem (guard_fml Px Qx) -∗ sem (guard_fml Qx Rx) -∗ sem (guard_fml Px Rx).
  Proof.
    have ? := guard_fml_pers_at H. iIntros "#g #g'". iApply (dguard_of_all_at H). iIntros (sem' Hs Hi).
    iApply (guard_trans with "[] []");
      by iApply (guard_fml_sem_into H Hs Hi).
  Qed.

  Lemma dguard_lhs_iff_at {sem} (H : alt_sem sem) {Px Px' Qx} :
    (∀ sem', alt_sem sem' → sem' Px ⊣⊢ sem' Px') →
    sem (guard_fml Px' Qx) ⊢ sem (guard_fml Px Qx).
  Proof.
    move=> eq. have ? := guard_fml_pers_at H. iIntros "#g". iApply (dguard_of_all_at H).
    iIntros (sem' Hs Hi). iApply (guard_lhs_iff (eq sem' Hs)).
    by iApply (guard_fml_sem_into H Hs Hi).
  Qed.
  Lemma dguard_rhs_iff_at {sem} (H : alt_sem sem) {Px Qx Qx'} :
    (∀ sem', alt_sem sem' → sem' Qx ⊣⊢ sem' Qx') →
    sem (guard_fml Px Qx) ⊢ sem (guard_fml Px Qx').
  Proof.
    move=> eq. have ? := guard_fml_pers_at H. iIntros "#g". iApply (dguard_of_all_at H).
    iIntros (sem' Hs Hi). iApply (guard_rhs_iff (eq sem' Hs)).
    by iApply (guard_fml_sem_into H Hs Hi).
  Qed.

  (** The two-sided form of [dguard_rhs_iff_at] *)
  Lemma dguard_rhs_iff_at' {sem} (H : alt_sem sem) {Px Qx Qx'} :
    (∀ sem', alt_sem sem' → sem' Qx ⊣⊢ sem' Qx') →
    sem (guard_fml Px Qx) ⊣⊢ sem (guard_fml Px Qx').
  Proof.
    move=> eq. iSplit; [iApply (dguard_rhs_iff_at H eq)|].
    iApply (dguard_rhs_iff_at H)=> sem' Hs. by rewrite (eq sem' Hs).
  Qed.
  Lemma dguard_lhs_iff_at' {sem} (H : alt_sem sem) {Px Px' Qx} :
    (∀ sem', alt_sem sem' → sem' Px ⊣⊢ sem' Px') →
    sem (guard_fml Px Qx) ⊣⊢ sem (guard_fml Px' Qx).
  Proof.
    move=> eq. iSplit; [iApply (dguard_lhs_iff_at H)=> sem' Hs|
      iApply (dguard_lhs_iff_at H (eq))]; by rewrite (eq sem' Hs).
  Qed.

  Lemma dguard_sep_l_at {sem} (H : alt_sem sem) {Px Qx} :
    ⊢ sem (guard_fml (bor_sep Px Qx) Px).
  Proof.
    iApply (dguard_of_all_at H). iIntros (sem' Hs _).
    rewrite (sep_sem_at Hs). iApply guard_sep_l.
  Qed.
  Lemma dguard_sep_r_at {sem} (H : alt_sem sem) {Px Qx} :
    ⊢ sem (guard_fml (bor_sep Px Qx) Qx).
  Proof.
    iApply (dguard_of_all_at H). iIntros (sem' Hs _).
    rewrite (sep_sem_at Hs). iApply guard_sep_r.
  Qed.
  Lemma dguard_lhs_sep_l_at {sem} (H : alt_sem sem) {Px Qx Rx} :
    sem (guard_fml Px Qx) ⊢ sem (guard_fml (bor_sep Px Rx) Qx).
  Proof.
    have ? := guard_fml_pers_at H. iIntros "#g". iApply (dguard_of_all_at H). iIntros (sem' Hs Hi).
    rewrite (sep_sem_at Hs). iApply guard_lhs_sep_l.
    by iApply (guard_fml_sem_into H Hs Hi).
  Qed.
  Lemma dguard_lhs_sep_r_at {sem} (H : alt_sem sem) {Px Qx Rx} :
    sem (guard_fml Px Qx) ⊢ sem (guard_fml (bor_sep Rx Px) Qx).
  Proof.
    have ? := guard_fml_pers_at H. iIntros "#g". iApply (dguard_of_all_at H). iIntros (sem' Hs Hi).
    rewrite (sep_sem_at Hs). iApply guard_lhs_sep_r.
    by iApply (guard_fml_sem_into H Hs Hi).
  Qed.
  Lemma dguard_rhs_sep_l_at {sem} (H : alt_sem sem) {Px Qx Rx} :
    sem (guard_fml Px (bor_sep Qx Rx)) ⊢ sem (guard_fml Px Qx).
  Proof.
    have ? := guard_fml_pers_at H. iIntros "#g". iApply (dguard_of_all_at H). iIntros (sem' Hs Hi).
    iDestruct (guard_fml_sem_into H Hs Hi with "g") as "g'".
    rewrite (sep_sem_at Hs). iApply (guard_rhs_sep_l with "g'").
  Qed.
  Lemma dguard_rhs_sep_r_at {sem} (H : alt_sem sem) {Px Qx Rx} :
    sem (guard_fml Px (bor_sep Qx Rx)) ⊢ sem (guard_fml Px Rx).
  Proof.
    have ? := guard_fml_pers_at H. iIntros "#g". iApply (dguard_of_all_at H). iIntros (sem' Hs Hi).
    iDestruct (guard_fml_sem_into H Hs Hi with "g") as "g'".
    rewrite (sep_sem_at Hs). iApply (guard_rhs_sep_r with "g'").
  Qed.

  Lemma dguard_false_at {sem} (H : alt_sem sem) {Px Qx} :
    sem (guard_fml Px false_fml) ⊢ sem (guard_fml Px Qx).
  Proof.
    have ? := guard_fml_pers_at H. iIntros "#g". iApply (dguard_of_all_at H). iIntros (sem' Hs Hi).
    iDestruct (guard_fml_sem_into H Hs Hi with "g") as "g'".
    rewrite (false_sem_at Hs). iApply (guard_false with "g'").
  Qed.

  (** Leaf's [guard_intro], at every candidate *)
  Lemma dguard_intro_at {sem} (H : alt_sem sem) {Px Qx} :
    (∀ sem', ⌜alt_sem sem'⌝ → □ (sem' Px -∗ sem' Qx ∗ (sem' Qx -∗ sem' Px)))
      ⊢ sem (guard_fml Px Qx).
  Proof.
    iIntros "#to". iApply (dguard_of_all_at H). iIntros (sem' ??).
    iApply guard_intro. by iApply "to".
  Qed.

  (** Leaf's conjunction rule, at every candidate *)
  Lemma dguard_and_at {sem} (H : alt_sem sem) {Px Qx Rx Sx} :
    (∀ sem', alt_sem sem' → point_prop (sem' Sx)) →
    (∀ sem', alt_sem sem' → sem' Qx ∧ sem' Rx ⊢ sem' Sx) →
    sem (guard_fml Px Qx) -∗ sem (guard_fml Px Rx) -∗ sem (guard_fml Px Sx).
  Proof.
    move=> pp to. have ? := guard_fml_pers_at H. iIntros "#g #g'". iApply (dguard_of_all_at H).
    iIntros (sem' Hs Hi).
    iApply (guard_and (point_prop0 := pp sem' Hs) (to sem' Hs));
      by iApply (guard_fml_sem_into H Hs Hi).
  Qed.

  (** The instances at the ambient interpretation *)
  Lemma dguard_refl {Px} : ⊢ dguard Px Px.
  Proof. exact: (dguard_refl_at alt_here). Qed.
  Lemma dguard_true {Px} : ⊢ dguard Px empty_fml.
  Proof. exact: (dguard_true_at alt_here). Qed.
  Lemma dguard_trans {Px Qx Rx} :
    dguard Px Qx -∗ dguard Qx Rx -∗ dguard Px Rx.
  Proof. exact: (dguard_trans_at alt_here). Qed.
  Lemma dguard_lhs_iff {Px Px' Qx} :
    (∀ sem', alt_sem sem' → sem' Px ⊣⊢ sem' Px') →
    dguard Px' Qx ⊢ dguard Px Qx.
  Proof. exact: (dguard_lhs_iff_at alt_here). Qed.
  Lemma dguard_rhs_iff {Px Qx Qx'} :
    (∀ sem', alt_sem sem' → sem' Qx ⊣⊢ sem' Qx') →
    dguard Px Qx ⊢ dguard Px Qx'.
  Proof. exact: (dguard_rhs_iff_at alt_here). Qed.
  Lemma dguard_sep_l {Px Qx} : ⊢ dguard (bor_sep Px Qx) Px.
  Proof. exact: (dguard_sep_l_at alt_here). Qed.
  Lemma dguard_sep_r {Px Qx} : ⊢ dguard (bor_sep Px Qx) Qx.
  Proof. exact: (dguard_sep_r_at alt_here). Qed.
  Lemma dguard_lhs_sep_l {Px Qx Rx} :
    dguard Px Qx ⊢ dguard (bor_sep Px Rx) Qx.
  Proof. exact: (dguard_lhs_sep_l_at alt_here). Qed.
  Lemma dguard_lhs_sep_r {Px Qx Rx} :
    dguard Px Qx ⊢ dguard (bor_sep Rx Px) Qx.
  Proof. exact: (dguard_lhs_sep_r_at alt_here). Qed.
  Lemma dguard_rhs_sep_l {Px Qx Rx} :
    dguard Px (bor_sep Qx Rx) ⊢ dguard Px Qx.
  Proof. exact: (dguard_rhs_sep_l_at alt_here). Qed.
  Lemma dguard_rhs_sep_r {Px Qx Rx} :
    dguard Px (bor_sep Qx Rx) ⊢ dguard Px Rx.
  Proof. exact: (dguard_rhs_sep_r_at alt_here). Qed.
  Lemma dguard_false {Px Qx} : dguard Px false_fml ⊢ dguard Px Qx.
  Proof. exact: (dguard_false_at alt_here). Qed.
  Lemma dguard_intro {Px Qx} :
    (∀ sem', ⌜alt_sem sem'⌝ → □ (sem' Px -∗ sem' Qx ∗ (sem' Qx -∗ sem' Px)))
      ⊢ dguard Px Qx.
  Proof. exact: (dguard_intro_at alt_here). Qed.
  Lemma dguard_and {Px Qx Rx Sx} :
    (∀ sem', alt_sem sem' → point_prop (sem' Sx)) →
    (∀ sem', alt_sem sem' → sem' Qx ∧ sem' Rx ⊢ sem' Sx) →
    dguard Px Qx -∗ dguard Px Rx -∗ dguard Px Sx.
  Proof. exact: (dguard_and_at alt_here). Qed.

  (** ** Persistence of the non-judgment connectives at a candidate *)

  Lemma pure_pers_at {sem} (H : alt_sem sem) φ :
    Persistent (sem (pure_fml φ)).
  Proof. rewrite (pure_sem_at H). exact _. Qed.
  Lemma false_pers_at {sem} (H : alt_sem sem) :
    Persistent (sem false_fml).
  Proof. rewrite (false_sem_at H). exact _. Qed.
  Lemma empty_pers_at {sem} (H : alt_sem sem) :
    Persistent (sem empty_fml).
  Proof. rewrite (empty_sem_at H). exact _. Qed.
  Lemma dead_pers_at {sem} (H : alt_sem sem) κ :
    Persistent (sem (dead_fml κ)).
  Proof. rewrite (dead_sem_at H). exact _. Qed.
  Lemma or_pers_at {sem} (H : alt_sem sem) Px Qx :
    Persistent (sem Px) → Persistent (sem Qx) →
    Persistent (sem (or_fml Px Qx)).
  Proof. move=> ??. rewrite (or_sem_at H). exact _. Qed.
  Lemma sep_pers_at {sem} (H : alt_sem sem) Px Qx :
    Persistent (sem Px) → Persistent (sem Qx) →
    Persistent (sem (bor_sep Px Qx)).
  Proof. move=> ??. rewrite (sep_sem_at H). exact _. Qed.
  Lemma ex_pers_at {sem} (H : alt_sem sem) A (Φ : A → FML $oi Σ) :
    (∀ a, Persistent (sem (Φ a))) → Persistent (sem (ex_fml Φ)).
  Proof. move=> ?. rewrite (ex_sem_at H). exact _. Qed.

  (** A stored guard out of a lifetime token, as the development reads it *)
  Lemma dguard_alive_sem {κ Qx} :
    dguard (alive_fml κ) Qx ⊢ @[κ] &&{alerus_WGuard}&&> bor_sem Qx.
  Proof. rewrite dguard_sem alive_fml_sem //. Qed.
  (** The same, with the right-hand side's semantics already computed.  Pass
    the [⊣⊢] of the [BorSem] field, e.g. [cells_fml_sem _ _ _]. *)
  Lemma dguard_alive_sem' {κ Qx} {Q : iProp Σ} :
    (bor_sem Qx ⊣⊢ Q) → dguard (alive_fml κ) Qx ⊢
      @[κ] &&{alerus_WGuard}&&> Q.
  Proof. move=> <-. exact dguard_alive_sem. Qed.

  (** Reading a guard stored at the ambient interpretation, at a candidate *)

  (** A location with no cells is allocated for free *)
  Lemma dguard_cmapstoany_nil {Px l n} :
    ⊢ dguard Px (cmapstoany_fml (l, repeat [] n)).
  Proof.
    have Heq : ∀ sem, alt_sem sem →
      sem empty_fml ⊣⊢ sem (cmapstoany_fml (l, repeat [] n)).
    { move=> sem Hsem. rewrite (empty_sem_at Hsem) (cmapstoany_sem_at Hsem).
      by rewrite -heap_cloc_mapsto_empty. }
    iApply (dguard_rhs_iff Heq). iApply dguard_true.
  Qed.

  (** A stored guard to an empty cell list is trivial *)
  Lemma dguard_cells_nil {Px l} : ⊢ dguard Px (cells_fml l [] []).
  Proof.
    have Heq : ∀ sem, alt_sem sem → sem empty_fml ⊣⊢ sem (cells_fml l [] []).
    { move=> sem Hsem. rewrite (empty_sem_at Hsem) (cells_sem_at Hsem) //. }
    iApply (dguard_rhs_iff Heq). iApply dguard_true.
  Qed.

  (** ** Lifetime inclusion as a stored guard *)

  (** Lifetime inclusion, held at *every* candidate interpretation.

    Not [dguard (alive_fml κ) (alive_fml κ')].  A stored guard lives at one
    interpretation, and nothing moves it to another: in the model that
    would need [δ J ⊢ δ' J], while [Deriv_factor'] gives only
    [δ J ⊢ ⟦J⟧(δ')].  But an inclusion from the lifetime context has to be
    usable while *building* a stored guard at a candidate, which is where
    the candidates come from.  So an inclusion is kept as the family of
    stored guards, one per candidate, and then never has to move.
    Everything that creates one creates the whole family: [dincl_of_incl]
    replays a closed lifetime-logic fact at each candidate, and
    [dincl_eternalize]'s token mentions no interpretation.

    Sealed, and [Typeclasses Opaque] below.  An inclusion occurs about a
    hundred times across the typing layer, and unfolded it is a [□ ∀ sem]
    under a class binder: leaving it transparent sends every unification
    and every [Persistent] search under that binder, which costs minutes
    per file. *)
  Local Definition dguard_all_def (Px Qx : FML $oi Σ) : iProp Σ :=
    □ ∀ sem (_ : alt_sem sem), sem (guard_fml Px Qx).
  Local Lemma dguard_all_aux : seal dguard_all_def. Proof. by eexists. Qed.
  Definition dguard_all := dguard_all_aux.(unseal).
  Local Lemma dguard_all_unseal : dguard_all = dguard_all_def.
  Proof. exact: seal_eq. Qed.

  #[export] Instance dguard_all_persistent {Px Qx} :
    Persistent (dguard_all Px Qx).
  Proof.
    rewrite dguard_all_unseal. have ? := guard_fml_pers_at alt_here. exact _.
  Qed.

  (** Reading one at a candidate, and at the ambient interpretation *)
  Lemma dguard_all_at {sem} (H : alt_sem sem) {Px Qx} :
    dguard_all Px Qx ⊢ sem (guard_fml Px Qx).
  Proof. rewrite dguard_all_unseal. iIntros "#g". iApply ("g" $! sem H). Qed.
  Lemma dguard_all_dguard {Px Qx} : dguard_all Px Qx ⊢ dguard Px Qx.
  Proof. exact (dguard_all_at alt_here). Qed.
  Lemma dguard_all_of_all {Px Qx} :
    □ (∀ sem (_ : alt_sem sem), sem (guard_fml Px Qx)) ⊢ dguard_all Px Qx.
  Proof. rewrite dguard_all_unseal. by iIntros "#g". Qed.
  Lemma dguard_all_trans {Px Qx Rx} :
    dguard_all Px Qx -∗ dguard_all Qx Rx -∗ dguard_all Px Rx.
  Proof.
    iIntros "#g #g'". iApply dguard_all_of_all. iIntros "!>" (sem H).
    iApply (dguard_trans_at H); by iApply (dguard_all_at H).
  Qed.
  Lemma dguard_all_rhs_iff {Px Qx Qx'} :
    (∀ sem, alt_sem sem → sem Qx ⊣⊢ sem Qx') →
    dguard_all Px Qx ⊢ dguard_all Px Qx'.
  Proof.
    move=> eq. iIntros "#g". iApply dguard_all_of_all. iIntros "!>" (sem H).
    iApply (dguard_rhs_iff_at H eq). by iApply (dguard_all_at H).
  Qed.
  Lemma dguard_all_lhs_iff {Px Px' Qx} :
    (∀ sem, alt_sem sem → sem Px ⊣⊢ sem Px') →
    dguard_all Px' Qx ⊢ dguard_all Px Qx.
  Proof.
    move=> eq. iIntros "#g". iApply dguard_all_of_all. iIntros "!>" (sem H).
    iApply (dguard_lhs_iff_at H eq). by iApply (dguard_all_at H).
  Qed.

  (** ** The *raw* family of guards

    [dguard_all] is a family of *stored* guards; reading one at a candidate
    gives a judgment, not a guard, and a judgment can only be eliminated at
    the ambient interpretation.  So anything that has to be *used* at a
    candidate - the lifetime logic's [st_incl] is the main case - must be the
    family of the guards themselves.  That is [fguardx].  It is strictly
    stronger: [fguardx_dguard_all] stores one, and nothing goes the other
    way. *)
  Local Definition fguardx_def (Px Qx : FML $oi Σ) : iProp Σ :=
    □ ∀ sem (_ : alt_any sem), sem Px &&{alt_WGuard sem}&&> sem Qx.
  Local Lemma fguardx_aux : seal fguardx_def. Proof. by eexists. Qed.
  Definition fguardx := fguardx_aux.(unseal).
  Local Lemma fguardx_unseal : fguardx = fguardx_def.
  Proof. exact: seal_eq. Qed.

  #[export] Instance fguardx_persistent {Px Qx} : Persistent (fguardx Px Qx).
  Proof. rewrite fguardx_unseal. exact _. Qed.

  Lemma fguardx_at_any {sem} (H : alt_any sem) {Px Qx} :
    fguardx Px Qx ⊢ sem Px &&{alt_WGuard sem}&&> sem Qx.
  Proof. rewrite fguardx_unseal. iIntros "#g". iApply ("g" $! sem H). Qed.
  Lemma fguardx_at {sem} (H : alt_sem sem) {Px Qx} :
    fguardx Px Qx ⊢ sem Px &&{alt_WGuard sem}&&> sem Qx.
  Proof. exact (fguardx_at_any (alt_sem_any H)). Qed.
  Lemma fguardx_of_all {Px Qx} :
    □ (∀ sem (_ : alt_any sem), sem Px &&{alt_WGuard sem}&&> sem Qx) ⊢
      fguardx Px Qx.
  Proof. rewrite fguardx_unseal. by iIntros "#g". Qed.
  Lemma fguardx_trans {Px Qx Rx} :
    fguardx Px Qx -∗ fguardx Qx Rx -∗ fguardx Px Rx.
  Proof.
    iIntros "#g #g'". iApply fguardx_of_all. iIntros "!>" (sem H).
    iApply (guard_trans with "[] []"); by iApply (fguardx_at_any H).
  Qed.
  Lemma fguardx_rhs_iff {Px Qx Qx'} :
    (∀ sem, alt_any sem → sem Qx ⊣⊢ sem Qx') →
    fguardx Px Qx ⊢ fguardx Px Qx'.
  Proof.
    move=> eq. iIntros "#g". iApply fguardx_of_all. iIntros "!>" (sem H).
    iApply (guard_rhs_iff (eq sem H)). by iApply (fguardx_at_any H).
  Qed.
  Lemma fguardx_lhs_iff {Px Px' Qx} :
    (∀ sem, alt_any sem → sem Px ⊣⊢ sem Px') →
    fguardx Px' Qx ⊢ fguardx Px Qx.
  Proof.
    move=> eq. iIntros "#g". iApply fguardx_of_all. iIntros "!>" (sem H).
    iApply (guard_lhs_iff (eq sem H)). by iApply (fguardx_at_any H).
  Qed.
  (** At the ambient interpretation *)
  Lemma fguardx_sem {Px Qx} :
    fguardx Px Qx ⊢ bor_sem Px &&{alerus_WGuard}&&> bor_sem Qx.
  Proof. rewrite -alt_WGuard_here. exact (fguardx_at alt_here). Qed.
  Lemma fguardx_alive_sem {κ Px} :
    fguardx (alive_fml κ) Px ⊢ @[κ] &&{alerus_WGuard}&&> bor_sem Px.
  Proof. rewrite fguardx_sem alive_fml_sem //. Qed.

  (** A raw family can be stored *)
  Lemma fguardx_dguard_all {Px Qx} : fguardx Px Qx ⊢ dguard_all Px Qx.
  Proof.
    iIntros "#g". iApply dguard_all_of_all. iIntros "!>" (sem H).
    iApply (dguard_of_all_at H). iIntros (sem' Hs _).
    by iApply (fguardx_at_any (alt_sem_any Hs)).
  Qed.
  Lemma fguardx_dguard {Px Qx} : fguardx Px Qx ⊢ dguard Px Qx.
  Proof. rewrite fguardx_dguard_all. exact dguard_all_dguard. Qed.

  (** ** Lifetime inclusion, stored

    An inclusion is *not* a stored guard: it is the lifetime logic's own
    [st_incl], the family [□ ∀ δ good, @[κ] &&{W δ}&&> @[κ']].  That is what
    a full borrow carries, and carrying the family rather than a guard at one
    interpretation is what makes a borrow storable - see
    [nola/alerus/lifetime/lifetime_full.v]'s [StBor] and the README.  Its
    closure properties come from [StBor] directly; only the two rules that
    reach outside the lifetime logic ([st_incl_of_incl] and
    [st_incl_eternalize]) are [AltSem] fields. *)
  Definition dincl (κ κ' : lft) : iProp Σ := st_incl κ κ'.

  #[export] Instance dincl_persistent {κ κ'} : Persistent (dincl κ κ').
  Proof. rewrite /dincl. exact _. Qed.

  (** Reading an inclusion at an interpretation, as a Leaf guard *)
  Lemma dincl_guard_at_any {sem} (H : alt_any sem) {κ κ'} :
    dincl κ κ' ⊢ @[κ] &&{alt_WGuard sem}&&> @[κ'].
  Proof. exact: st_incl_at. Qed.
  Lemma dincl_guard_at {sem} (H : alt_sem sem) {κ κ'} :
    dincl κ κ' ⊢ @[κ] &&{alt_WGuard sem}&&> @[κ'].
  Proof. exact (dincl_guard_at_any (alt_sem_any H)). Qed.

  (** The raw family of guards between two lifetime tokens **is** an
    inclusion.  This is [typing/function.v]'s [fn_incl_of_all], and with
    [st_incl] the family over every interpretation it is one line. *)
  Lemma dincl_fguardx {κ κ'} :
    fguardx (alive_fml κ) (alive_fml κ') ⊢ dincl κ κ'.
  Proof.
    iIntros "#g". rewrite /dincl. iApply st_incl_of_all. iIntros "!>" (sem H).
    rewrite -(alive_sem_at_any H κ) -(alive_sem_at_any H κ').
    by iApply (fguardx_at_any H).
  Qed.
  Lemma fguardx_of_dincl {κ κ'} :
    dincl κ κ' ⊢ fguardx (alive_fml κ) (alive_fml κ').
  Proof.
    iIntros "#g". iApply fguardx_of_all. iIntros "!>" (sem H).
    rewrite (alive_sem_at_any H κ) (alive_sem_at_any H κ').
    by iApply (dincl_guard_at_any H).
  Qed.
  Lemma dincl_sem {κ κ'} : dincl κ κ' ⊢ @[κ] &&{alerus_WGuard}&&> @[κ'].
  Proof. rewrite -alt_WGuard_here. exact (dincl_guard_at alt_here). Qed.

  (** An inclusion can be *stored*: at any candidate it is a guard between
    the two lifetime tokens, which is what [guard_fml] asks for. *)
  Lemma dincl_at {sem} (H : alt_sem sem) {κ κ'} :
    dincl κ κ' ⊢ sem (guard_fml (alive_fml κ) (alive_fml κ')).
  Proof.
    iIntros "#In". iApply (dguard_of_all_at H). iIntros (sem' Hs _).
    rewrite (alive_sem_at Hs) (alive_sem_at Hs).
    by iApply (dincl_guard_at Hs).
  Qed.
  Lemma incl_fml_sem {κ κ'} : bor_sem (incl_fml κ κ') ⊣⊢ dincl κ κ'.
  Proof.
    apply bi.equiv_entails; split;
      [exact incl_fml_sem_1|exact (incl_fml_of_incl alt_here _ _)].
  Qed.
  #[export] Instance incl_fml_persistent_at {sem} `{Hs : !alt_sem sem} {κ κ'} :
    Persistent (sem (incl_fml κ κ')) := incl_fml_pers_at Hs _ _.

  Lemma dincl_dguard {κ κ'} : dincl κ κ' ⊢ dguard (alive_fml κ) (alive_fml κ').
  Proof. exact (dincl_at alt_here). Qed.
  (** A stored guard between two lifetime tokens is an inclusion at the
    ambient interpretation.  [dbasically_dead] holds one of these. *)
  Lemma dguard_alive_incl {κ κ'} :
    dguard (alive_fml κ) (alive_fml κ') ⊢ llft_incl κ κ'.
  Proof. rewrite dguard_sem !alive_fml_sem //. Qed.

  Lemma dincl_of_sub {κ κ'} : κ' ⊆ κ → ⊢ dincl κ κ'.
  Proof. exact st_incl_of_sub. Qed.
  Lemma dincl_eternalize {κ} : @[κ] =[alerus_wsat]=∗ dincl static κ.
  Proof. exact st_incl_eternalize. Qed.
  Lemma dincl_refl {κ} : ⊢ dincl κ κ.
  Proof. exact st_incl_refl. Qed.
  Lemma dincl_trans {κ κ' κ''} : dincl κ κ' -∗ dincl κ' κ'' -∗ dincl κ κ''.
  Proof. exact st_incl_trans. Qed.
  Lemma dincl_glb {κ κ' κ''} :
    dincl κ κ' -∗ dincl κ κ'' -∗ dincl κ (κ' ⊓ κ'').
  Proof. exact st_incl_glb. Qed.
  Lemma dincl_intersect_l {κ κ'} : ⊢ dincl (κ ⊓ κ') κ.
  Proof. exact st_incl_meet_l. Qed.
  Lemma dincl_intersect_r {κ κ'} : ⊢ dincl (κ ⊓ κ') κ'.
  Proof. exact st_incl_meet_r. Qed.
  Lemma dincl_intersect_mono {κ1 κ1' κ2 κ2'} :
    dincl κ1 κ1' -∗ dincl κ2 κ2' -∗ dincl (κ1 ⊓ κ2) (κ1' ⊓ κ2').
  Proof.
    iIntros "#g1 #g2". iApply dincl_glb.
    - iApply (dincl_trans with "[] g1"). iApply dincl_intersect_l.
    - iApply (dincl_trans with "[] g2"). iApply dincl_intersect_r.
  Qed.

  (** [&uniq{κ}]'s "the lifetime is already dead" case, stored *)
  (** A [dincl], matching the formula [basically_dead_fml], which holds an
    [incl_fml]. *)
  Definition dbasically_dead (κ : lft) : iProp Σ :=
    ∃ κ', dincl κ κ' ∗ [†κ'].


  #[export] Instance dbasically_dead_persistent {κ} :
    Persistent (dbasically_dead κ).
  Proof. exact _. Qed.

  (** Storing the guard of a freshly allocated shared borrow *)
  Lemma fguardx_borrow_shared {κ Px} :
    bor_sem Px -∗ |=[alerus_WGuard]=>
      fguardx (alive_fml κ) Px ∗ ([†κ] -∗ |=[alerus_WGuard]=> bor_sem Px).
  Proof.
    iIntros "Px W". iMod (guard_fml_borrow_shared with "Px W") as "[$ [#g $]]".
    iModIntro. iApply fguardx_of_all. iIntros "!>" (sem H).
    rewrite (alive_sem_at_any H). by iApply "g".
  Qed.
  Lemma dguard_borrow_shared {κ Px} :
    bor_sem Px -∗ |=[alerus_WGuard]=>
      dguard_all (alive_fml κ) Px ∗ ([†κ] -∗ |=[alerus_WGuard]=> bor_sem Px).
  Proof.
    iIntros "Px W". iMod (fguardx_borrow_shared with "Px W") as "[$ [#g $]]".
    iModIntro. by iApply fguardx_dguard_all.
  Qed.

  (** [guard_cloc_combine_fancy] for stored guards: the combination is a
    fact about the heap, so it replays at every candidate. *)
  Lemma dguard_cloc_combine_fancy {Px} (l : cloc) (vl : list fancy_val) :
    dguard Px (cmapstoany_fml l) -∗ dguard Px (ccells_fml l vl) -∗
    dguard Px (cells_fml l.1 l.2 vl).
  Proof.
    have ? := guard_fml_pers_at alt_here.
    iIntros "#g1 #g2". iApply dguard_of_all. iIntros (sem' Hs Hi).
    iDestruct (guard_fml_sem_into alt_here Hs Hi with "g1") as "g1'".
    iDestruct (guard_fml_sem_into alt_here Hs Hi with "g2") as "g2'".
    rewrite (cells_sem_at Hs) (cmapstoany_sem_at Hs) (ccells_sem_at Hs).
    iApply (guard_cloc_combine_fancy with "g1' g2'").
  Qed.

  (** Storing the guard a full borrow gives *)
  Lemma dguard_of_bor {κ Px} :
    llft_ctx -∗ full_bor κ Px =[alerus_wsat]=∗ dguard (alive_fml κ) Px.
  Proof. exact guard_fml_of_bor. Qed.
End alt_sem.

(** [dguard_of_all_at] at the ambient interpretation *)
Notation dguard_of_all := (dguard_of_all_at alt_here).

Global Typeclasses Opaque dguard_all fguardx dincl.

(** ** Notation for formulas

  So that a type former's ghost assertion reads the way the original writes
  it.  [cif] gives Nola these for free; with [FML] abstract they are
  notations for the constructors of [TypeFml]. *)
Declare Scope fml_scope.
Delimit Scope fml_scope with FML.
Notation "'False'" := false_fml : fml_scope.
Notation "'True'" := empty_fml : fml_scope.
Notation "⌜ φ ⌝" := (pure_fml φ%type%stdpp) : fml_scope.
Notation "Px ∗ Qx" := (bor_sep Px%FML Qx%FML)
  (at level 80, right associativity) : fml_scope.
Notation "∃ x .. y , Px" :=
  (ex_fml (λ x, .. (ex_fml (λ y, Px%FML)) ..))
  (at level 10, x binder, y binder, Px at level 200) : fml_scope.
Notation "l ↦[^ cs ]!∗ fv" := (cells_fml l cs fv) (at level 20) : fml_scope.
Notation "l ↦!∗ fv" := (mapsto_fml l fv) (at level 20) : fml_scope.
Notation "l #↦!∗ fv" := (ccells_fml l fv) (at level 20) : fml_scope.
Notation "@[ κ ]" := (alive_fml κ) (format "@[ κ ]") : fml_scope.
Notation ".PCx[ ξ ]" := (pc_fml ξ) (at level 5, format ".PCx[ ξ ]")
  : fml_scope.
Notation ".VOx[ ξ ]" := (vo_fml ξ) (at level 5, format ".VOx[ ξ ]")
  : fml_scope.
Notation "Px ∨ Qx" := (or_fml Px%FML Qx%FML)
  (at level 85, right associativity) : fml_scope.
Notation "l #↦∗_" := (cmapstoany_fml l) (at level 20) : fml_scope.
Notation "&x{ κ , i } Px" := (idxbor_fml κ i Px%FML)
  (at level 20, format "&x{ κ ,  i }  Px") : fml_scope.
Notation "[†x κ ]" := (dead_fml κ) (format "[†x κ ]") : fml_scope.
(** The guard a type's lifetime inclusion becomes *)
Notation "κ ⊑x κ'" := (incl_fml κ κ')
  (at level 70) : fml_scope.

(** Normalising the semantics of the formula language.

  A type former's ghost assertion is now a formula, so a goal that used to
  read [ty_gho (own_ptr n ty) x d g tid] unfolds to [bor_sem] of a formula
  built out of the constructors above.  [fml_simpl] pushes [bor_sem] through
  them and gives back exactly the proposition the original development works
  with. *)
Create HintDb fml_sem.
Global Hint Rewrite @false_fml_sem @pure_fml_sem @alive_fml_sem
  @cells_fml_sem @ccells_fml_sem @freeable_fml_sem @pc_fml_sem
  @mapsto_fml_sem @bor_sep_sem @empty_fml_sem @or_fml_sem @vo_fml_sem
  @dead_fml_sem @cmapstoany_fml_sem @pers_fml_sem : fml_sem.
Ltac fml_simpl := autorewrite with fml_sem.
Ltac fml_simpl' := simpl; autorewrite with fml_sem.

(** The lifetime logic's notations.  [lifetime_full] cannot export these: the
  argument order it leaves behind after closing its section does not allow it. *)
Infix "⊑" := llft_incl (at level 70) : bi_scope.
Notation "&{ κ }" := (full_bor κ) (format "&{ κ }") : bi_scope.
Notation "&{ κ , i }" := (idx_bor κ i) (format "&{ κ , i }") : bi_scope.

(** A short name for the world satisfaction every guard is taken over, so that
  the typing layer can write [P &&{alerus_WGuard}&&> Q] where VerusBelt writes
  [P &&{↑NllftG}&&> Q]. *)
Notation Wguard := alerus_WGuard.

(** The mask the typing layer works at.

  VerusBelt uses [↑Nllft ∪ ↑SendN ∪ ↑nainvN ∪ ↑uniqN ∪ ↑timeN].  Of those,
  [↑Nllft] and [↑nainvN] have become world satisfactions, [↑SendN] is now
  [send_wsat], and [↑timeN] is gone with the time receipts.  What is left are
  the two genuinely invariant-based pieces - prophecies and unique borrows -
  together with the masks the lifetime logic still takes fancy updates at. *)
Definition NalerusE : coPset :=
  ↑NllftUsr ∪ ↑NllftUsr2 ∪ ↑prophN ∪ ↑uniqN.
