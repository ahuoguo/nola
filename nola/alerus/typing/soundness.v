(** * Soundness

  Ported from VerusBelt ([typing/soundness.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  The original proves *safety*: a well-typed program does not get stuck and
  has no data race.  Later-free the weakest precondition is total, so the
  same hypothesis gives **termination** as well, which the original cannot
  state - see [nola/alerus/lang/adequacy.v].

  The ghost state is allocated in the order the port forces: the heap first
  (the language's adequacy hands it over), then the lifetime logic, and only
  then the interpretation, because [bor_sem] is [⟦⟧ᶜ(der)] and its [Csem]
  mentions the ghost state.  Compare
  [nola/examples/rust_halt/adequacy.v]'s [rust_wsat_alloc]. *)

From iris.algebra Require Import gmap_view agree auth gset.
From iris.proofmode Require Import proofmode.
From nola.alerus.lang Require Import adequacy races proofmode notation.
From nola.alerus.typing Require Export level_ctx.
From nola.alerus.typing Require Import function programs product base_type
  type_context.
From nola.bi Require Import modw.
Import ModwNotation WpwNotation iPropAppNotation.

(** ** Allocating the world satisfaction

  Every component is allocated before the interpretation is known, and the
  interpretation is handed in afterwards. *)
Section alloc.
  Context `{!typingC CON} {JUDG Σ}
    `{!alerusGpreS (cifOF CON) Σ, !invGS_gen HasNoLc Σ,
      !typingJ CON JUDG Σ}.

  Lemma alerus_wsat_alloc (hGS : heapGS (cifOF CON) Σ) :
    ⊢ |={⊤}=> ∃ H : alerusGS (cifOF CON) Σ,
      ⌜@alerus_invGS _ _ H = _⌝ ∧ ⌜@alerus_heapGS _ _ H = hGS⌝ ∧
      proph_ctx ∗ uniq_ctx ∗
      ∀ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ))
        (_ : typingCS CON JUDG Σ) (_ : typingJS CON JUDG Σ),
        ⌜LRustGS HasNoLc (cifOF CON) Σ _
           (@lrustGpreS_na_inv _ _ alerus_preG_lrust)
           (@lrustGpreS_alc _ _ alerus_preG_lrust)
           _ alerus_NaSem heapSem_cif = alerus_lrustGS⌝ ∧ alerus_wsat.
  Proof.
    iMod alerus_names_alloc as (n) "W".
    (* [uniq_init] allocates the atomic pool against a [cnaGS]; any level's
      will do, because [send_wsat] is [cna_lifetimes atomic_pool_name ∅],
      whose [own] is at an [inG] of [cnaGpreS] and not at [cna_name]. *)
    pose (Hllft := an_llft n). pose (Hcna := an_cna n).
    iMod (proph_init ⊤) as (Hproph) "#PROPH"; [done|].
    iMod (uniq_init ⊤) as (Huniq) "[#UNIQ Wsend]"; [done|].
    iModIntro. iExists (alerusGS_of hGS Hproph Huniq n).
    do 2 (iSplit; [done|]). iFrame "PROPH UNIQ". iIntros (????).
    iSplit; [done|]. iSplitR "Wsend"; [|iExact "Wsend"].
    by iApply "W".
  Qed.
End alloc.

(** ** Soundness

  As in [nola/examples/rust_halt/adequacy.v], the statement is about a
  *typing judgment*, not about a function value: [fn] is the one type former
  whose interpretation the model does not yet give (it has to be stratified
  by an execution level first - see [typing/README.md]), and nothing else
  needs it. *)
Definition exit_cont : val := λ: [<>], #☠.

Section soundness.
  Context `{!typingC CON} {JUDG Σ}
    `{!alerusGpreS (cifOF CON) Σ, !typingJ CON JUDG Σ}.

  (** A closed, semantically well-typed program terminates.

    The original ([typing/soundness.v]) can only conclude safety: its
    weakest precondition is partial, because a guard there hands out a [▷]
    that only a later credit can pay for.  Here it is total. *)
  Theorem type_soundness {𝔅} (e : expr) (tr : predl_trans' [] 𝔅) :
    (∀ post xl mask π, tr post xl mask π) →
    (∀ H : alerusGS (cifOF CON) Σ,
      ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ))
        (_ : typingCS CON JUDG Σ) (_ : typingJS CON JUDG Σ),
      ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅)
          +[] e tr) →
    sn erased_step ([e], (∅, false)).
  Proof.
    move=> Htr big. apply: (lrust_total (s:=NotStuck)).
    move=> iG hGS.
    iMod (alerus_wsat_alloc (invGS_gen0 := iG) hGS)
      as (H) "[%eq1 [%eq2 (#PROPH & #UNIQ & →W)]]".
    subst. move: (big H)=> [Cs [Js [CS [JS ty]]]].
    iMod (invctx_alloc ⊤) as (tid) "I". iModIntro.
    iExists (existT _ heapSem_cif), alerus_wsat, (λ _, cont_postcondition).
    iDestruct ("→W" $! Cs Js CS JS) as "[%Heq $]".
    cbn [projT1 projT2]. rewrite Heq.
    iApply (ty $! tid -[] ⊤ (λ _ _ _, True) [] with
      "[] PROPH UNIQ [] [] I [] [] []"); try done.
    - by rewrite /llctx_interp.
    - by iIntros (? ?%elem_of_nil).
    - iApply proph_obs_true. move=> ?. apply Htr.
  Qed.

  (** The original's conclusion: no data race, and no thread gets stuck.

    It follows from the same hypothesis, through the partial weakest
    precondition that the total one implies. *)
  Theorem type_safety {𝔅} (e : expr) (tr : predl_trans' [] 𝔅) t σ :
    (∀ post xl mask π, tr post xl mask π) →
    (∀ H : alerusGS (cifOF CON) Σ,
      ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ))
        (_ : typingCS CON JUDG Σ) (_ : typingJS CON JUDG Σ),
      ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅)
          +[] e tr) →
    rtc erased_step ([e], (∅, false)) (t, σ) →
    nonracing_threadpool t σ ∧
      (∀ e', e' ∈ t → is_Some (to_val e') ∨ reducible e' σ).
  Proof.
    move=> Htr big Hrtc.
    cut (adequate NotStuck e (∅, false) (λ _ _, True)).
    { split; [by eapply adequate_nonracing|].
      move=> *. by eapply (adequate_not_stuck _ e). }
    apply: (lrust_adequacy (s:=NotStuck) (φ:=λ _ _, True)).
    move=> iG hGS.
    iMod (alerus_wsat_alloc (invGS_gen0 := iG) hGS)
      as (H) "[%eq1 [%eq2 (#PROPH & #UNIQ & →W)]]".
    subst. move: (big H)=> [Cs [Js [CS [JS ty]]]].
    iMod (invctx_alloc ⊤) as (tid) "I". iModIntro.
    iExists (existT _ heapSem_cif), alerus_wsat.
    iDestruct ("→W" $! Cs Js CS JS) as "[%Heq $]".
    cbn [projT1 projT2]. rewrite Heq.
    iApply (wp_wand with "[I]").
    { iApply twpw_wpw. iApply (ty $! tid -[] ⊤ (λ _ _ _, True) [] with
        "[] PROPH UNIQ [] [] I [] [] []"); try done;
        [by rewrite /llctx_interp|by iIntros (? ?%elem_of_nil)|].
      iApply proph_obs_true. move=> ?. apply Htr. }
    iIntros (v) "_". iIntros (σ') "ctx W".
    iApply fupd_mask_intro_discard; [set_solver|done].
  Qed.
End soundness.

(** The two theorems rest on nothing but the axiom Iris itself uses. *)
Print Assumptions type_soundness.
Print Assumptions type_safety.
