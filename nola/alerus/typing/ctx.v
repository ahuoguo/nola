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
  Definition alerus_WG : iProp Σ :=
    eternal_wsat alerus_eternal_name llft_alive ∗
    frac_wsat bor_sem ∗
    frac_key_wsat llctx_interp.

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
    llft_wsat ∗ cna_wsat alerus_WGuard bor_sem ∗ send_wsat.

  (** The inclusions the rest of the development needs.  They are given
    explicitly rather than left to the structural instances, which would have
    to unfold [llft_wsat], [llft_wsatG] and the [LlftWG] projections. *)
  #[export] Instance wsat_incl_alerus_llft :
    WsatIncl alerus_wsat llft_wsat
      (cna_wsat alerus_WGuard bor_sem ∗ send_wsat).
  Proof. done. Qed.
  #[export] Instance wsat_incl_alerus_guard :
    WsatIncl alerus_wsat alerus_WGuard
      (llft_inv_other ∗ cna_wsat alerus_WGuard bor_sem ∗ send_wsat).
  Proof.
    rewrite /WsatIncl /alerus_wsat /alerus_WGuard /llft_wsat. iSplit.
    - by iIntros "([$$] & $ & $)".
    - by iIntros "([$ $] & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_cna :
    WsatIncl alerus_wsat (cna_wsat alerus_WGuard bor_sem ∗ alerus_WGuard)
      (llft_inv_other ∗ send_wsat).
  Proof.
    rewrite /WsatIncl /alerus_wsat /alerus_WGuard /llft_wsat. iSplit.
    - by iIntros "([$$] & $ & $)".
    - by iIntros "([$ $] & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_send :
    WsatIncl alerus_wsat send_wsat
      (llft_wsat ∗ cna_wsat alerus_WGuard bor_sem).
  Proof.
    rewrite /WsatIncl /alerus_wsat. iSplit.
    - by iIntros "($ & $ & $)".
    - by iIntros "($ & $ & $)".
  Qed.

  (** [alerus_WG] and its parts sit inside [alerus_WGuard] *)
  #[export] Instance wsat_incl_alerus_WG :
    WsatIncl alerus_WGuard alerus_WG
      (shr_wsat ∗ box_wsat bor_sem ∗ llft_inv_main).
  Proof. done. Qed.
  #[export] Instance wsat_incl_alerus_eternal :
    WsatIncl alerus_WG (eternal_wsat alerus_eternal_name llft_alive)
      (frac_wsat bor_sem ∗ frac_key_wsat llctx_interp).
  Proof. done. Qed.
  #[export] Instance wsat_incl_alerus_fracfml :
    WsatIncl alerus_WG (frac_wsat bor_sem)
      (eternal_wsat alerus_eternal_name llft_alive ∗
        frac_key_wsat llctx_interp).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - by iIntros "($ & $ & $)".
    - by iIntros "($ & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_llctx :
    WsatIncl alerus_WG (frac_key_wsat llctx_interp)
      (eternal_wsat alerus_eternal_name llft_alive ∗ frac_wsat bor_sem).
  Proof.
    rewrite /WsatIncl /alerus_WG. iSplit.
    - by iIntros "($ & $ & $)".
    - by iIntros "($ & $ & $)".
  Qed.
End alerus.

(** The lifetime logic's notations.  [lifetime_full] cannot export these: the
  argument order it leaves behind after closing its section does not allow it. *)
Infix "⊑" := llft_incl (at level 70) : bi_scope.
Notation "&{ κ }" := (full_bor κ) (format "&{ κ }") : bi_scope.
Notation "&{ κ , i }" := (idx_bor κ i) (format "&{ κ , i }") : bi_scope.

(** A short name for the world satisfaction every guard is taken over, so that
  the typing layer can write [P &&{Wguard}&&> Q] where VerusBelt writes
  [P &&{↑NllftG}&&> Q]. *)
Notation Wguard := alerus_WGuard.
