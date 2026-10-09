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

  Definition alerus_WG : iProp Σ :=
    eternal_wsat alerus_eternal_name llft_alive ∗
    frac_wsat bor_sem ∗
    frac_key_wsat llctx_interp ∗
    frac_key_wsat lfts_interp ∗
    send_wsat.

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

  (** The global world satisfaction *)
  Definition alerus_wsat : iProp Σ :=
    llft_wsat ∗ cna_wsat alerus_WGuard bor_sem.

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
  #[export] Instance wsat_incl_alerus_llft :
    WsatIncl alerus_wsat llft_wsat (cna_wsat alerus_WGuard bor_sem).
  Proof. done. Qed.
  #[export] Instance wsat_incl_alerus_guard :
    WsatIncl alerus_wsat alerus_WGuard
      (llft_inv_other ∗ cna_wsat alerus_WGuard bor_sem).
  Proof.
    rewrite /WsatIncl /alerus_wsat /alerus_WGuard /llft_wsat. iSplit.
    - by iIntros "([$$] & $)".
    - by iIntros "([$ $] & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_cna :
    WsatIncl alerus_wsat (cna_wsat alerus_WGuard bor_sem ∗ alerus_WGuard)
      llft_inv_other.
  Proof.
    rewrite /WsatIncl /alerus_wsat /alerus_WGuard /llft_wsat. iSplit.
    - by iIntros "([$$] & $)".
    - by iIntros "([$ $] & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_send :
    WsatIncl alerus_WG send_wsat
      (eternal_wsat alerus_eternal_name llft_alive ∗ frac_wsat bor_sem ∗
        frac_key_wsat llctx_interp ∗ frac_key_wsat lfts_interp).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - by iIntros "($ & $ & $ & $ & $)".
    - by iIntros "($ & $ & $ & $ & $)".
  Qed.

  (** [alerus_WG] and its parts sit inside [alerus_WGuard] *)
  #[export] Instance wsat_incl_alerus_WG :
    WsatIncl alerus_WGuard alerus_WG
      (shr_wsat ∗ box_wsat bor_sem ∗ llft_inv_main).
  Proof. done. Qed.
  #[export] Instance wsat_incl_alerus_eternal :
    WsatIncl alerus_WG (eternal_wsat alerus_eternal_name llft_alive)
      (frac_wsat bor_sem ∗ frac_key_wsat llctx_interp ∗
        frac_key_wsat lfts_interp ∗ send_wsat).
  Proof. done. Qed.
  #[export] Instance wsat_incl_alerus_fracfml :
    WsatIncl alerus_WG (frac_wsat bor_sem)
      (eternal_wsat alerus_eternal_name llft_alive ∗
        frac_key_wsat llctx_interp ∗ frac_key_wsat lfts_interp ∗ send_wsat).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - by iIntros "($ & $ & $ & $ & $)".
    - by iIntros "($ & $ & $ & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_llctx :
    WsatIncl alerus_WG (frac_key_wsat llctx_interp)
      (eternal_wsat alerus_eternal_name llft_alive ∗ frac_wsat bor_sem ∗
        frac_key_wsat lfts_interp ∗ send_wsat).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - by iIntros "($ & $ & $ & $ & $)".
    - by iIntros "($ & $ & $ & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_lfts :
    WsatIncl alerus_WG (frac_key_wsat lfts_interp)
      (eternal_wsat alerus_eternal_name llft_alive ∗ frac_wsat bor_sem ∗
        frac_key_wsat llctx_interp ∗ send_wsat).
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
