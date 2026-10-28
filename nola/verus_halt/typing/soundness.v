(** * Soundness

  Ported from VerusBelt ([typing/soundness.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  The original proves *safety*: a well-typed program does not get stuck and
  has no data race.  Later-free the weakest precondition is total, so the
  same hypothesis gives **termination** as well, which the original cannot
  state - see [nola/verus_halt/lang/adequacy.v].

  The ghost state is allocated in the order the port forces: the heap first
  (the language's adequacy hands it over), then the lifetime logic, and only
  then the interpretation, because [bor_sem] is [⟦⟧ᶜ(der)] and its [Csem]
  mentions the ghost state.  Compare
  [nola/examples/rust_halt/adequacy.v]'s [rust_wsat_alloc]. *)

From iris.algebra Require Import gmap_view agree auth gset.
From iris.proofmode Require Import proofmode.
From nola.verus_halt.lang Require Import adequacy races proofmode notation.
From nola.verus_halt.typing Require Export level_ctx.
From nola.verus_halt.typing Require Import function programs product base_type
  type_context.
From nola.bi Require Import modw.
Import ModwNotation WpwNotation iPropAppNotation.

(** ** Allocating the world satisfaction

  Every component is allocated before the interpretation is known, and the
  interpretation is handed in afterwards. *)
Section alloc.
  Context `{!typingC CON} {JUDG Σ}
    `{!verus_haltGpreS (cifOF CON) Σ, !invGS_gen HasNoLc Σ,
      !typingJ CON JUDG Σ}.

  Lemma verus_halt_wsat_alloc (hGS : heapGS (cifOF CON) Σ) :
    ⊢ |={⊤}=> ∃ H : verus_haltGS (cifOF CON) Σ,
      ⌜@verus_halt_invGS _ _ H = _⌝ ∧ ⌜@verus_halt_heapGS _ _ H = hGS⌝ ∧
      proph_ctx ∗ uniq_ctx ∗
      ∀ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ))
        (_ : typingCS CON JUDG Σ) (_ : typingJS CON JUDG Σ),
        ⌜LRustGS HasNoLc (cifOF CON) Σ _
           (@lrustGpreS_na_inv _ _ verus_halt_preG_lrust)
           (@lrustGpreS_alc _ _ verus_halt_preG_lrust)
           _ verus_halt_NaSem heapSem_cif = verus_halt_lrustGS⌝ ∧ verus_halt_wsat.
  Proof.
    iMod verus_halt_names_alloc as (Hllft n) "[_ W]".
    (* [uniq_init] allocates the atomic pool against a [cnaGS]; any level's
      will do, because [send_wsat] is [cna_lifetimes atomic_pool_name ∅],
      whose [own] is at an [inG] of [cnaGpreS] and not at [cna_name]. *)
    pose (Hcna := an_cna n).
    iMod (proph_init ⊤) as (Hproph) "#PROPH"; [done|].
    iMod (uniq_init ⊤) as (Huniq) "[#UNIQ Wsend]"; [done|].
    iModIntro. iExists (verus_haltGS_of Hllft hGS Hproph Huniq n).
    do 2 (iSplit; [done|]). iFrame "PROPH UNIQ". iIntros (????).
    iSplit; [done|]. iSplitR "Wsend"; [by iApply "W"|].
    (* [verus_haltGS_of] sets [verus_halt_Wx] to [emp]: this development
      is the single-level one. *)
    by iFrame "Wsend".
  Qed.
End alloc.

(** ** Soundness

  Two shapes, and the difference used to matter.

  [type_soundness] and [type_safety] are about a *typing judgment* for a
  closed expression, as in [nola/examples/rust_halt/adequacy.v].  That
  was not a preference: [fn] was the one type former whose
  interpretation the model did not give, so [typed_val main main_type c]
  - the hypothesis VerusBelt's own theorem takes - had no content here.

  [type_soundness_main] and [type_safety_main] below are VerusBelt's own
  shape, about a [main] *function value* that the runtime applies to a
  continuation.  They are available now because [FnFml] is inhabited
  ([typing/fn_inst.v]) and because [typing/function.v]'s
  [type_main_body] turns such a [main] into a closed [typed_body]. *)

Section soundness.
  Context `{!typingC CON} {JUDG Σ}
    `{!verus_haltGpreS (cifOF CON) Σ, !typingJ CON JUDG Σ}.

  (** A closed, semantically well-typed program terminates.

    The original ([typing/soundness.v]) can only conclude safety: its
    weakest precondition is partial, because a guard there hands out a [▷]
    that only a later credit can pay for.  Here it is total. *)
  Theorem type_soundness {𝔅} (e : expr) (tr : predl_trans' [] 𝔅) :
    (∀ post xl mask π, tr post xl mask π) →
    (∀ H : verus_haltGS (cifOF CON) Σ,
      ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ))
        (_ : typingCS CON JUDG Σ) (_ : typingJS CON JUDG Σ),
      ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅)
          +[] e tr) →
    sn erased_step ([e], (∅, false)).
  Proof.
    move=> Htr big. apply: (lrust_total (s:=NotStuck)).
    move=> iG hGS.
    iMod (verus_halt_wsat_alloc (invGS_gen0 := iG) hGS)
      as (H) "[%eq1 [%eq2 (#PROPH & #UNIQ & →W)]]".
    subst. move: (big H)=> [Cs [Js [CS [JS ty]]]].
    iMod (invctx_alloc ⊤) as (tid) "I". iModIntro.
    iExists (existT _ heapSem_cif), verus_halt_wsat, (λ _, cont_postcondition).
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
    (∀ H : verus_haltGS (cifOF CON) Σ,
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
    iMod (verus_halt_wsat_alloc (invGS_gen0 := iG) hGS)
      as (H) "[%eq1 [%eq2 (#PROPH & #UNIQ & →W)]]".
    subst. move: (big H)=> [Cs [Js [CS [JS ty]]]].
    iMod (invctx_alloc ⊤) as (tid) "I". iModIntro.
    iExists (existT _ heapSem_cif), verus_halt_wsat.
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

(** ** Soundness in VerusBelt's own shape

  [main] is a function value of [typing/function.v]'s [main_type] - no
  arguments, a trivial specification - and the program is
  [main [exit_cont]], the application the runtime performs.  This is
  upstream's [type_soundness]/[type_soundness_closed] statement, and it
  needs [fn] interpreted, which is why the port could not state it
  before.

  The hypothesis carries an [FnFml] alongside the interpretation,
  because [main_type]'s arrow level is [fn_lv_top], which is a field of
  it.  [typing/fn_inst.v] supplies one. *)
Section soundness_main.
  Context `{!typingC CON} {JUDG Σ}
    `{!verus_haltGpreS (cifOF CON) Σ, !typingJ CON JUDG Σ}.

  Theorem type_soundness_main (main : val) c :
    (∀ H : verus_haltGS (cifOF CON) Σ,
      ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ))
        (_ : typingCS CON JUDG Σ) (_ : typingJS CON JUDG Σ) (_ : FnFml),
      typed_val main main_type c) →
    sn erased_step ([main [exit_cont]%E], (∅, false)).
  Proof.
    move=> big.
    apply (type_soundness (𝔅:=unitₛ) _ (λ _ _ _ _, True%type)); [done|].
    move=> H. move: (big H)=> [Cs [Js [CS [JS [FF ty]]]]].
    exists Cs, Js, CS, JS. exact (type_main_body _ _ ty).
  Qed.

  Theorem type_safety_main (main : val) c t σ :
    (∀ H : verus_haltGS (cifOF CON) Σ,
      ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ))
        (_ : typingCS CON JUDG Σ) (_ : typingJS CON JUDG Σ) (_ : FnFml),
      typed_val main main_type c) →
    rtc erased_step ([main [exit_cont]%E], (∅, false)) (t, σ) →
    nonracing_threadpool t σ ∧
      (∀ e', e' ∈ t → is_Some (to_val e') ∨ reducible e' σ).
  Proof.
    move=> big. apply (type_safety (𝔅:=unitₛ) _ (λ _ _ _ _, True%type)); [done|].
    move=> H. move: (big H)=> [Cs [Js [CS [JS [FF ty]]]]].
    exists Cs, Js, CS, JS. exact (type_main_body _ _ ty).
  Qed.
End soundness_main.

(** The first two rest on nothing but the axiom Iris itself uses.  The
  [main]-shaped pair add functional extensionality, which comes in through
  [main_type]'s result type: [unit_ty] is a [mod_ty] over the empty product
  ([typing/product.v]), and the isomorphism it carries is proved by [fun_ext].
  Upstream's own [unit_ty] is the same. *)
Print Assumptions type_soundness.
Print Assumptions type_safety.
Print Assumptions type_soundness_main.
Print Assumptions type_safety_main.
