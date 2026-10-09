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
  (** The shared-borrow simple-invariant family, as a bare ghost name *)
  alerus_shr_name : gname;
  (** The eternalized-lifetime family *)
  alerus_eternal_name : gname;
}.

Section alerus.
  Context `{!alerusGS FML Σ}.

  (** The user's guarding world satisfaction: Leaf's [↑NllftG] minus the
    lifetime logic's own invariants.  Eternalized lifetime tokens live here,
    which is what makes [lft_eternalize] possible. *)
  Definition alerus_WG : iProp Σ :=
    eternal_wsat alerus_eternal_name llft_alive.

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

  (** The global world satisfaction.

    [llft_wsat = llft_wsatG ∗ llft_inv_other], so [alerus_WGuard] is included;
    [cna_wsat] and [frac_wsat] sit *beside* it, since the guards they store
    are taken over it. *)
  Definition alerus_wsat : iProp Σ :=
    llft_wsat ∗
    cna_wsat alerus_WGuard bor_sem ∗
    frac_wsat bor_sem ∗
    send_wsat.

  (** The inclusions the rest of the development needs *)
  #[export] Instance wsat_incl_alerus_llft :
    WsatIncl alerus_wsat llft_wsat
      (cna_wsat alerus_WGuard bor_sem ∗ frac_wsat bor_sem ∗ send_wsat).
  Proof. done. Qed.
  #[export] Instance wsat_incl_alerus_cna :
    WsatIncl alerus_wsat (cna_wsat alerus_WGuard bor_sem ∗ alerus_WGuard)
      (llft_inv_other ∗ frac_wsat bor_sem ∗ send_wsat).
  Proof.
    rewrite /WsatIncl /alerus_wsat /alerus_WGuard /llft_wsat. iSplit.
    - by iIntros "([$$] & $ & $ & $)".
    - by iIntros "([$ $] & $ & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_frac :
    WsatIncl alerus_wsat (frac_wsat bor_sem)
      (llft_wsat ∗ cna_wsat alerus_WGuard bor_sem ∗ send_wsat).
  Proof.
    rewrite /WsatIncl /alerus_wsat. iSplit.
    - by iIntros "($ & $ & $ & $)".
    - by iIntros "($ & $ & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_send :
    WsatIncl alerus_wsat send_wsat
      (llft_wsat ∗ cna_wsat alerus_WGuard bor_sem ∗ frac_wsat bor_sem).
  Proof.
    rewrite /WsatIncl /alerus_wsat. iSplit.
    - by iIntros "($ & $ & $ & $)".
    - by iIntros "($ & $ & $ & $)".
  Qed.
  #[export] Instance wsat_incl_alerus_eternal :
    WsatIncl alerus_WGuard alerus_WG
      (shr_wsat ∗ box_wsat bor_sem ∗ llft_inv_main).
  Proof. done. Qed.
End alerus.

(** The lifetime logic's notations.  [lifetime_full] cannot export these: the
  argument order it leaves behind after closing its section does not allow it. *)
Infix "⊑" := llft_incl (at level 70) : bi_scope.
Notation "&{ κ }" := (full_bor κ) (format "&{ κ }") : bi_scope.
Notation "&{ κ , i }" := (idx_bor κ i) (format "&{ κ , i }") : bi_scope.

(** Every guard in the typing layer is taken over [alerus_WGuard] *)
Notation "P &&{ }&&> Q" := (guard alerus_WGuard P Q)
  (at level 99, Q at level 200, format "P  &&{ }&&>  Q") : bi_scope.
