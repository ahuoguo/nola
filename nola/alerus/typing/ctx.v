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
From nola.iris Require Export sinv.
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
  therefore take [Context `{!alerusGS FML Σ, !HeapSem FML Σ}]. *)
Class alerusGS (FML : oFunctor) Σ : Type := AlerusGS {
  #[global] alerus_invGS :: invGS_gen HasNoLc Σ;
  #[global] alerus_llftGS :: llft_logicGS Σ;
  #[global] alerus_sinvGS :: sinvGS FML Σ;
  #[global] alerus_borSem :: BorSem FML Σ;
  #[global] alerus_borStateFml :: BorStateFml llft_name;
  #[global] alerus_shrBorSem :: ShrBorSem FML Σ;
  #[global] alerus_emptySem :: EmptySem FML Σ;
  #[global] alerus_heapGS :: heapGS FML Σ;
  #[global] alerus_na_invG :: na_invG Σ;
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
}.

Section alerus.
  Context `{!alerusGS FML Σ}.

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
  Definition alerus_WG : iProp Σ :=
    eternal_wsat alerus_eternal_name llft_alive ∗
    frac_wsat bor_sem ∗
    frac_key_wsat llctx_interp ∗
    frac_key_wsat lfts_interp.

  (** Fix the lifetime logic's two parameters *)
  #[export] Instance alerus_LlftWG : LlftWG Σ :=
    {| llft_shr_name := alerus_shr_name; llft_WG := alerus_WG |}.

  (** [↑NllftG] itself: the world satisfaction every guard is taken over *)
  Definition alerus_WGuard : iProp Σ := llft_wsatG.

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
    lrustGS_na_invGS := alerus_na_invG;
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
        frac_key_wsat lfts_interp).
  Proof. done. Qed.
  #[export] Instance wsat_incl_alerus_fracfml :
    WsatIncl alerus_WG (frac_wsat bor_sem)
      (eternal_wsat alerus_eternal_name llft_alive ∗
        frac_key_wsat llctx_interp ∗ frac_key_wsat lfts_interp).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - by iIntros "($ & $ & $ & $)".
    - by iIntros "($ & $ & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_llctx :
    WsatIncl alerus_WG (frac_key_wsat llctx_interp)
      (eternal_wsat alerus_eternal_name llft_alive ∗ frac_wsat bor_sem ∗
        frac_key_wsat lfts_interp).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - by iIntros "($ & $ & $ & $)".
    - by iIntros "($ & $ & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_lfts :
    WsatIncl alerus_WG (frac_key_wsat lfts_interp)
      (eternal_wsat alerus_eternal_name llft_alive ∗ frac_wsat bor_sem ∗
        frac_key_wsat llctx_interp).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - by iIntros "($ & $ & $ & $)".
    - by iIntros "($ & $ & $ & $)".
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

(** The formula language must express every guard source.

  Like [HeapSem] this is *not* a field of [alerusGS]: [gsrc_interp] is stated
  against the [NaSem] instance that [alerusGS] builds.  Typing files get it
  through [typeG]. *)
Class GsrcSem (FML : oFunctor) Σ `{!alerusGS FML Σ} := {
  gsrc_fml : gsrc → FML $oi Σ;
  gsrc_fml_sem s : bor_sem (gsrc_fml s) ⊣⊢ gsrc_interp s;
}.

Section gsrc.
  Context `{!alerusGS FML Σ, !GsrcSem FML Σ}.

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
Class TypeFml (FML : oFunctor) Σ `{!alerusGS FML Σ} := {
  (** Formulas form a COFE: [typing/fixpoint.v] takes the limit of a chain of
    type interpretations, which is now a chain of formulas. *)
  #[global] fml_cofe :: Cofe (FML $oi Σ);
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
  (** A guard over the guarding world satisfaction, for [&shr{κ}] *)
  guard_fml : FML $oi Σ → FML $oi Σ → FML $oi Σ;
  guard_fml_ne :: NonExpansive2 guard_fml;
  (** **This equation has no model**; see [AltSem] below, which replaces it
    with an elimination and an introduction.  It is kept for the moment so
    that the files that have not been migrated to [dguard] still build, and
    it is what every remaining use of [guard_fml_sem] is standing on. *)
  guard_fml_sem Px Qx :
    bor_sem (guard_fml Px Qx) ⊣⊢ (bor_sem Px &&{alerus_WGuard}&&> bor_sem Qx);
  (** A lifetime token, for [&shr{κ}] *)
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
  idxbor_fml_sem κ idx Px :
    bor_sem (idxbor_fml κ idx Px) ⊣⊢ idx_bor κ idx Px;
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
  Context `{!alerusGS FML Σ, !TypeFml FML Σ}.

  (** A points-to assertion over a plain location, as [own_ptr] uses it *)
  Definition mapsto_fml (l : loc) (fv : list fancy_val) : FML $oi Σ :=
    cells_fml l (repeat [] (length fv)) fv.
  Lemma mapsto_fml_sem {l fv} : bor_sem (mapsto_fml l fv) ⊣⊢ l ↦!∗ fv.
  Proof. by rewrite /mapsto_fml cells_fml_sem. Qed.

  (** [ex_fml] is proper *)
  #[export] Instance ex_fml_ne' {A} n :
    Proper (pointwise_relation A (dist n) ==> dist n) (@ex_fml _ _ _ _ A).
  Proof. move=> ?? eq. by apply ex_fml_ne. Qed.
  #[export] Instance ex_fml_proper' {A} :
    Proper (pointwise_relation A (≡) ==> (≡)) (@ex_fml _ _ _ _ A).
  Proof.
    move=> ?? eq. apply equiv_dist=> n. apply ex_fml_ne=> a.
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
  #[export] Instance guard_fml_persistent {Px Qx} :
    Persistent (bor_sem (guard_fml Px Qx)).
  Proof. rewrite guard_fml_sem. exact _. Qed.
  #[export] Instance idxbor_fml_persistent {κ idx Px} :
    Persistent (bor_sem (idxbor_fml κ idx Px)).
  Proof. rewrite idxbor_fml_sem. exact _. Qed.
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
  `{!alerusGS FML Σ, !EmptySem FML Σ, !GsrcSem FML Σ, !TypeFml FML Σ} := {
  (** [sem] is a candidate interpretation *)
  alt_sem : (FML $oi Σ → iProp Σ) → Prop;
  (** A judgment stored at the ambient interpretation can be read at [sem] *)
  alt_into : (FML $oi Σ → iProp Σ) → Prop;
  (** The guarding world satisfaction at a candidate *)
  alt_WGuard : (FML $oi Σ → iProp Σ) → iProp Σ;
  (** The ambient interpretation is a candidate, maps into itself, and is its
    own guarding world satisfaction *)
  alt_here : alt_sem bor_sem;
  alt_into_here : alt_into bor_sem;
  alt_WGuard_here : alt_WGuard bor_sem = alerus_WGuard;
  alt_sem_ne {sem} : alt_sem sem → NonExpansive sem;
  (** The non-judgment constructors mean the same at every candidate *)
  sep_sem_at {sem} : alt_sem sem → ∀ Px Qx,
    sem (bor_sep Px Qx) ⊣⊢ sem Px ∗ sem Qx;
  false_sem_at {sem} : alt_sem sem → sem false_fml ⊣⊢ False;
  empty_sem_at {sem} : alt_sem sem → sem empty_fml ⊣⊢ True;
  pure_sem_at {sem} : alt_sem sem → ∀ φ, sem (pure_fml φ) ⊣⊢ ⌜φ⌝;
  ex_sem_at {sem} : alt_sem sem → ∀ A (Φ : A → FML $oi Σ),
    sem (ex_fml Φ) ⊣⊢ ∃ a : A, sem (Φ a);
  or_sem_at {sem} : alt_sem sem → ∀ Px Qx,
    sem (or_fml Px Qx) ⊣⊢ sem Px ∨ sem Qx;
  alive_sem_at {sem} : alt_sem sem → ∀ κ, sem (alive_fml κ) ⊣⊢ @[κ];
  dead_sem_at {sem} : alt_sem sem → ∀ κ, sem (dead_fml κ) ⊣⊢ [†κ];
  cells_sem_at {sem} : alt_sem sem → ∀ l cs fv,
    sem (cells_fml l cs fv) ⊣⊢ l ↦[^ cs ]!∗ fv;
  ccells_sem_at {sem} : alt_sem sem → ∀ l fv,
    sem (ccells_fml l fv) ⊣⊢ l #↦!∗ fv;
  cmapstoany_sem_at {sem} : alt_sem sem → ∀ l,
    sem (cmapstoany_fml l) ⊣⊢ l #↦∗_;
  freeable_sem_at {sem} : alt_sem sem → ∀ n sz l,
    sem (freeable_fml n sz l) ⊣⊢ freeable_sz n sz l;
  vo_sem_at {sem} : alt_sem sem → ∀ ξ x d, sem (vo_fml ξ x d) ⊣⊢ .VO[ξ] x d;
  pc_sem_at {sem} : alt_sem sem → ∀ ξ x vπ d,
    sem (pc_fml ξ x vπ d) ⊣⊢ .PC[ξ] x vπ d;
  gsrc_sem_at {sem} : alt_sem sem → ∀ s,
    sem (gsrc_fml s) ⊣⊢ gsrc_interp s;
  (** Reading a stored guard at a candidate the ambient one maps into.  In
    the model this is [dinto δ δ'] applied to the guard judgment. *)
  guard_fml_sem_into {sem} : alt_sem sem → alt_into sem → ∀ Px Qx,
    bor_sem (guard_fml Px Qx) ⊢ sem Px &&{alt_WGuard sem}&&> sem Qx;
  (** Storing a guard.  In the model this is [Deriv_factor']. *)
  guard_fml_sem_2 {Px Qx} :
    (∀ sem, ⌜alt_sem sem⌝ → ⌜alt_into sem⌝ →
      sem Px &&{alt_WGuard sem}&&> sem Qx) ⊢ bor_sem (guard_fml Px Qx);
  (** A stored guard is persistent.  In the model [δ J] is under a [□]. *)
  guard_fml_pers {Px Qx} :: Persistent (bor_sem (guard_fml Px Qx));
  (** Lifetime inclusion is storable.

    [llft_incl κ κ'] is itself a guard over [alerus_WGuard], so it has no
    [⊣⊢] semantics either.  But the lifetime logic's proofs never look at the
    interpretation - they are parametric in [BorSem] - so an inclusion that
    holds at the ambient interpretation holds at every candidate.  In the
    model this is [Deriv_factor'] followed by replaying the same proof at
    [δ']. *)
  dincl_of_incl {κ κ'} : (⊢ @[κ] &&{alerus_WGuard}&&> @[κ']) →
    ⊢ bor_sem (guard_fml (alive_fml κ) (alive_fml κ'));
  (** [llftl_borrow_shared] at the formula level.  The shared borrow it
    allocates is a [sinv_tok], which does not mention the interpretation, and
    [sinv_tok_guard] turns it into a guard at *every* candidate - so this is
    one of the places where a guard can be stored in the first place. *)
  guard_fml_borrow_shared {κ Px} :
    bor_sem Px -∗ |=[alerus_WGuard]=>
      bor_sem (guard_fml (alive_fml κ) Px) ∗
      ([†κ] -∗ |=[alerus_WGuard]=> bor_sem Px);
}.

Section alt_sem.
  Context `{!alerusGS FML Σ, !EmptySem FML Σ, !GsrcSem FML Σ, !TypeFml FML Σ,
    !AltSem FML Σ}.

  Implicit Type Px Qx Rx Sx : FML $oi Σ.

  (** A guard held *as a formula*.

    Everything the development does with a stored guard goes through this
    name.  [dguard_sem] drops it to an actual Leaf guard, which is all one
    needs to *open* it; every other lemma below builds one stored guard out of
    others, and is [Deriv_map] in the intended model. *)
  Definition dguard Px Qx : iProp Σ := bor_sem (guard_fml Px Qx).

  #[export] Instance dguard_persistent {Px Qx} : Persistent (dguard Px Qx).
  Proof. rewrite /dguard. exact _. Qed.
  #[export] Instance dguard_ne : NonExpansive2 dguard.
  Proof. solve_proper. Qed.
  #[export] Instance dguard_proper : Proper ((≡) ==> (≡) ==> (⊣⊢)) dguard.
  Proof. apply ne_proper_2, _. Qed.

  (** Reading a stored guard at the ambient interpretation *)
  Lemma guard_fml_sem_1 {Px Qx} :
    bor_sem (guard_fml Px Qx) ⊢ bor_sem Px &&{alerus_WGuard}&&> bor_sem Qx.
  Proof.
    rewrite -alt_WGuard_here.
    exact: (guard_fml_sem_into alt_here alt_into_here).
  Qed.
  Lemma dguard_sem {Px Qx} :
    dguard Px Qx ⊢ bor_sem Px &&{alerus_WGuard}&&> bor_sem Qx.
  Proof. exact guard_fml_sem_1. Qed.

  (** Storing a guard that holds at every candidate interpretation *)
  Lemma dguard_of_all {Px Qx} :
    (∀ sem, ⌜alt_sem sem⌝ → ⌜alt_into sem⌝ →
      sem Px &&{alt_WGuard sem}&&> sem Qx) ⊢ dguard Px Qx.
  Proof. exact guard_fml_sem_2. Qed.

  (** Reading a stored guard at a candidate, as [iDestruct] wants it *)
  Lemma dguard_into {sem Px Qx} : alt_sem sem → alt_into sem →
    dguard Px Qx ⊢ sem Px &&{alt_WGuard sem}&&> sem Qx.
  Proof. move=> ??. exact: guard_fml_sem_into. Qed.

  (** ** Building stored guards out of stored guards *)

  Lemma dguard_refl {Px} : ⊢ dguard Px Px.
  Proof. iApply dguard_of_all. iIntros (???). iApply guard_refl. Qed.

  Lemma dguard_true {Px} : ⊢ dguard Px empty_fml.
  Proof.
    iApply dguard_of_all. iIntros (sem Hs _). rewrite (empty_sem_at Hs).
    iApply guard_true.
  Qed.

  Lemma dguard_trans {Px Qx Rx} :
    dguard Px Qx -∗ dguard Qx Rx -∗ dguard Px Rx.
  Proof.
    iIntros "#g #g'". iApply dguard_of_all. iIntros (sem Hs Hi).
    iApply (guard_trans with "[] []"); by iApply (dguard_into Hs Hi).
  Qed.

  Lemma dguard_lhs_iff {Px Px' Qx} :
    (∀ sem, alt_sem sem → sem Px ⊣⊢ sem Px') →
    dguard Px' Qx ⊢ dguard Px Qx.
  Proof.
    move=> eq. iIntros "#g". iApply dguard_of_all. iIntros (sem Hs Hi).
    iApply (guard_lhs_iff (eq sem Hs)). by iApply (dguard_into Hs Hi).
  Qed.
  Lemma dguard_rhs_iff {Px Qx Qx'} :
    (∀ sem, alt_sem sem → sem Qx ⊣⊢ sem Qx') →
    dguard Px Qx ⊢ dguard Px Qx'.
  Proof.
    move=> eq. iIntros "#g". iApply dguard_of_all. iIntros (sem Hs Hi).
    iApply (guard_rhs_iff (eq sem Hs)). by iApply (dguard_into Hs Hi).
  Qed.

  Lemma dguard_sep_l {Px Qx} : ⊢ dguard (bor_sep Px Qx) Px.
  Proof.
    iApply dguard_of_all. iIntros (sem Hs _). rewrite (sep_sem_at Hs).
    iApply guard_sep_l.
  Qed.
  Lemma dguard_sep_r {Px Qx} : ⊢ dguard (bor_sep Px Qx) Qx.
  Proof.
    iApply dguard_of_all. iIntros (sem Hs _). rewrite (sep_sem_at Hs).
    iApply guard_sep_r.
  Qed.
  Lemma dguard_lhs_sep_l {Px Qx Rx} :
    dguard Px Qx ⊢ dguard (bor_sep Px Rx) Qx.
  Proof.
    iIntros "#g". iApply dguard_of_all. iIntros (sem Hs Hi).
    rewrite (sep_sem_at Hs). iApply guard_lhs_sep_l.
    by iApply (dguard_into Hs Hi).
  Qed.
  Lemma dguard_lhs_sep_r {Px Qx Rx} :
    dguard Px Qx ⊢ dguard (bor_sep Rx Px) Qx.
  Proof.
    iIntros "#g". iApply dguard_of_all. iIntros (sem Hs Hi).
    rewrite (sep_sem_at Hs). iApply guard_lhs_sep_r.
    by iApply (dguard_into Hs Hi).
  Qed.
  Lemma dguard_rhs_sep_l {Px Qx Rx} :
    dguard Px (bor_sep Qx Rx) ⊢ dguard Px Qx.
  Proof.
    iIntros "#g". iApply dguard_of_all. iIntros (sem Hs Hi).
    iDestruct (dguard_into Hs Hi with "g") as "g'".
    rewrite (sep_sem_at Hs). iApply (guard_rhs_sep_l with "g'").
  Qed.
  Lemma dguard_rhs_sep_r {Px Qx Rx} :
    dguard Px (bor_sep Qx Rx) ⊢ dguard Px Rx.
  Proof.
    iIntros "#g". iApply dguard_of_all. iIntros (sem Hs Hi).
    iDestruct (dguard_into Hs Hi with "g") as "g'".
    rewrite (sep_sem_at Hs). iApply (guard_rhs_sep_r with "g'").
  Qed.

  Lemma dguard_false {Px Qx} : dguard Px false_fml ⊢ dguard Px Qx.
  Proof.
    iIntros "#g". iApply dguard_of_all. iIntros (sem Hs Hi).
    iDestruct (dguard_into Hs Hi with "g") as "g'".
    rewrite (false_sem_at Hs). iApply (guard_false with "g'").
  Qed.

  (** Leaf's [guard_intro], at every candidate *)
  Lemma dguard_intro {Px Qx} :
    (∀ sem, ⌜alt_sem sem⌝ → □ (sem Px -∗ sem Qx ∗ (sem Qx -∗ sem Px))) ⊢
      dguard Px Qx.
  Proof.
    iIntros "#to". iApply dguard_of_all. iIntros (sem ??).
    iApply guard_intro. by iApply "to".
  Qed.

  (** Leaf's conjunction rule, at every candidate *)
  Lemma dguard_and {Px Qx Rx Sx} :
    (∀ sem, alt_sem sem → point_prop (sem Sx)) →
    (∀ sem, alt_sem sem → sem Qx ∧ sem Rx ⊢ sem Sx) →
    dguard Px Qx -∗ dguard Px Rx -∗ dguard Px Sx.
  Proof.
    move=> pp to. iIntros "#g #g'". iApply dguard_of_all.
    iIntros (sem Hs Hi).
    iApply (guard_and (point_prop0 := pp sem Hs) (to sem Hs));
      by iApply (dguard_into Hs Hi).
  Qed.

  (** ** Lifetime inclusion as a stored guard *)

  Definition dincl (κ κ' : lft) : iProp Σ :=
    dguard (alive_fml κ) (alive_fml κ').

  #[export] Instance dincl_persistent {κ κ'} : Persistent (dincl κ κ').
  Proof. rewrite /dincl. exact _. Qed.

  Lemma dincl_sem {κ κ'} : dincl κ κ' ⊢ llft_incl κ κ'.
  Proof.
    iIntros "g". iDestruct (dguard_sem with "g") as "g".
    by rewrite !alive_fml_sem.
  Qed.
  Lemma dincl_of {κ κ'} : (⊢ llft_incl κ κ') → ⊢ dincl κ κ'.
  Proof. move=> ?. by apply dincl_of_incl. Qed.
  Lemma dincl_refl {κ} : ⊢ dincl κ κ.
  Proof. apply dguard_refl. Qed.
  Lemma dincl_trans {κ κ' κ''} : dincl κ κ' -∗ dincl κ' κ'' -∗ dincl κ κ''.
  Proof. apply dguard_trans. Qed.

  (** [&uniq{κ}]'s "the lifetime is already dead" case, stored *)
  Definition dbasically_dead (κ : lft) : iProp Σ :=
    ∃ κ', dincl κ κ' ∗ [†κ'].

  #[export] Instance dbasically_dead_persistent {κ} :
    Persistent (dbasically_dead κ).
  Proof. exact _. Qed.

  (** Storing the guard of a freshly allocated shared borrow *)
  Lemma dguard_borrow_shared {κ Px} :
    bor_sem Px -∗ |=[alerus_WGuard]=>
      dguard (alive_fml κ) Px ∗ ([†κ] -∗ |=[alerus_WGuard]=> bor_sem Px).
  Proof. exact guard_fml_borrow_shared. Qed.
End alt_sem.

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
Notation "κ ⊑x κ'" := (guard_fml (alive_fml κ) (alive_fml κ'))
  (at level 70) : fml_scope.

(** Normalising the semantics of the formula language.

  A type former's ghost assertion is now a formula, so a goal that used to
  read [ty_gho (own_ptr n ty) x d g tid] unfolds to [bor_sem] of a formula
  built out of the constructors above.  [fml_simpl] pushes [bor_sem] through
  them and gives back exactly the proposition the original development works
  with. *)
Create HintDb fml_sem.
Global Hint Rewrite @false_fml_sem @pure_fml_sem @guard_fml_sem @alive_fml_sem
  @cells_fml_sem @ccells_fml_sem @freeable_fml_sem @pc_fml_sem
  @mapsto_fml_sem @bor_sep_sem @empty_fml_sem @or_fml_sem @vo_fml_sem
  @idxbor_fml_sem @dead_fml_sem @cmapstoany_fml_sem : fml_sem.
Ltac fml_simpl := autorewrite with fml_sem.
Ltac fml_simpl' := simpl; autorewrite with fml_sem.

(** The lifetime logic's notations.  [lifetime_full] cannot export these: the
  argument order it leaves behind after closing its section does not allow it. *)
Infix "⊑" := llft_incl (at level 70) : bi_scope.
Notation "&{ κ }" := (full_bor κ) (format "&{ κ }") : bi_scope.
Notation "&{ κ , i }" := (idx_bor κ i) (format "&{ κ , i }") : bi_scope.

(** A short name for the world satisfaction every guard is taken over, so that
  the typing layer can write [P &&{Wguard}&&> Q] where VerusBelt writes
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
