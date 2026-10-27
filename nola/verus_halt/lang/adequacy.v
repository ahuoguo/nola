(** * Adequacy of the total program logic

  Ported from VerusBelt ([lang/adequacy.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer).

  The original is forced to go through a bespoke [adequacy_util.wp_strong_
  adequacy] so that it can start the machine at step 1 holding [£ k] later
  credits, then feed them to [time_init]: the whole point is to have credits in
  hand to strip the laters a guard introduces.  Later-free there are no credits
  to hand out, [timeΣ] drops out of [lrustΣ], and plain
  [nola.bi.wpw.wpw_strong_adequacy_gen] suffices.  In exchange we get what the
  original cannot state at all: [lrust_total], termination adequacy for the
  total weakest precondition.

  The interpretation [NaSem] is supplied by the client *after* the ghost names
  exist, since the interpretation of a points-to formula mentions [heap_name];
  see [non_atomic_map_alloc_empty_any] and compare
  [nola.examples.rust_halt.adequacy.rust_wsat_alloc]. *)

From iris.program_logic Require Export adequacy weakestpre total_adequacy.
From iris.algebra Require Import auth.
From nola.bi Require Export wpw.
From nola.verus_halt Require Import na_inv_fork.
From nola.verus_halt.util Require Import non_atomic_cell_map atomic_lock_counter.
From nola.verus_halt.lang Require Export heap lifting.
From nola.verus_halt.lang Require Import proofmode notation.
From iris.prelude Require Import options.
Import WpwNotation.

Class lrustGpreS FML Σ : Type := LRustGpreS {
  lrustGpreS_inv :: invGpreS Σ;
  lrustGpreS_na_inv :: na_invG Σ;
  lrustGpreS_alc :: alc_logicG Σ;
  lrustGpreS_heap :: inG Σ (authR heapUR);
  lrustGpreS_heap_freeable :: inG Σ (authR heap_freeableUR);
  lrustGpreS_na_logic :: na_logicG loc val FML Σ;
}.

Definition lrustΣ FML `{!oFunctorContractive FML} : gFunctors :=
  #[invΣ; na_invΣ; alc_logicΣ;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR heap_freeableUR));
    na_logicΣ loc val FML].
Global Instance subG_lrustGpreS {FML Σ} `{!oFunctorContractive FML} :
  subG (lrustΣ FML) Σ → lrustGpreS FML Σ.
Proof. solve_inG. Qed.

(** Allocate the heap, with the interpretation left open *)
Lemma heap_init `{!lrustGpreS FML Σ, !invGS_gen hlc Σ} :
  ⊢ |==> ∃ hGS : heapGS FML Σ, ∀ naS : NaSem FML Σ, heap_ctx (∅, false).
Proof.
  iMod non_atomic_map_alloc_empty_any as (vγ) "→na".
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "●f";
    first by apply auth_auth_valid.
  iMod na_alloc as (tp) "pool".
  iMod atomic_lock_ctr_alloc as (lcγ) "ctr". iModIntro.
  iExists (HeapGS _ _ _ _ _ vγ fγ tp lcγ). iIntros (naS).
  iExists ∅. iFrame "●f ctr pool". iSplit; [by iApply "→na"|].
  iPureIntro. by move=> ??.
Qed.

(** Safety adequacy for the partial weakest precondition *)
Theorem lrust_adequacy `{!lrustGpreS FML Σ} {hlc s e φ} :
  (∀ (iG : invGS_gen hlc Σ) (hGS : heapGS FML Σ),
    ⊢ |={⊤}=> ∃ nhS : {naS : NaSem FML Σ & HeapSem FML Σ},
      let _ : lrustGS_gen hlc FML Σ :=
        LRustGS hlc FML Σ iG _ _ hGS (projT1 nhS) (projT2 nhS) in
      ∃ W : iProp Σ, W ∗ WP[W] e @ s; ⊤ {{ v,
        ∀ σ', heap_ctx σ' -∗ W ={⊤,∅}=∗ ⌜φ v σ'⌝ }}) →
  adequate s e (∅, false) φ.
Proof.
  move=> big. apply adequate_alt=> ?? /erased_steps_nsteps[?[??]].
  eapply (wpw_strong_adequacy_gen hlc Σ _); [|done]=> Hinv.
  iMod heap_init as (Hheap) "→ctx".
  iMod (big Hinv Hheap) as ([naS hS] W) "[W wp]".
  iDestruct ("→ctx" $! naS) as "ctx". iModIntro.
  iExists (λ σ _ _ _, heap_ctx (heapGS0:=Hheap) (NaSem0:=naS) σ)%I,
    [_], (λ _, True)%I, _, W=>/=.
  iFrame "W ctx". iSplitL "wp"; [by iFrame|].
  iIntros (??->??) "W ctx H _".
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[→φ H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->=>/=. case eq: (to_val e')=>/=.
  - iMod ("→φ" with "ctx W") as %?. iModIntro. iSplit; [|done].
    iIntros (??[=-><-]). move: eq. rewrite to_of_val=> [[->]]. by iPureIntro.
  - iApply fupd_mask_intro_discard; [done|]. iSplit; [|done]. iPureIntro.
    move=> ??[??]. subst. move: eq. by rewrite to_of_val.
Qed.

(** Termination adequacy for the total weakest precondition

  The original has no counterpart: [num_laters_per_step] is nonzero there, and
  a [twp] whose steps hand out later credits cannot be run by
  [twp_total]. *)
Theorem lrust_total `{!lrustGpreS FML Σ} {s e} :
  (∀ (iG : invGS_gen HasNoLc Σ) (hGS : heapGS FML Σ),
    ⊢ |={⊤}=> ∃ nhS : {naS : NaSem FML Σ & HeapSem FML Σ},
      let _ : lrustGS_gen HasNoLc FML Σ :=
        LRustGS HasNoLc FML Σ iG _ _ hGS (projT1 nhS) (projT2 nhS) in
      ∃ W Φ, W ∗ WP[W] e @ s; ⊤ [{ Φ }]) →
  sn erased_step ([e], (∅, false)).
Proof.
  move=> big. apply (twpw_total Σ lrust_lang s e (∅, false) 0)=> Hinv.
  iMod heap_init as (Hheap) "→ctx".
  iMod (big Hinv Hheap) as ([naS hS] W Φ) "[W twp]".
  iDestruct ("→ctx" $! naS) as "ctx". iModIntro.
  iExists (λ σ _ _ _, heap_ctx (heapGS0:=Hheap) (NaSem0:=naS) σ)%I,
    (λ _, 0%nat), (λ _, True)%I, _, W, Φ. iFrame "W ctx twp".
Qed.
