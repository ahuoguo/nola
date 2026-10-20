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
From nola.alerus.typing Require Export model_inst.
From nola.alerus.typing Require Import function programs product base_type
  type_context.
From nola.bi Require Import modw.
Import ModwNotation WpwNotation iPropAppNotation.

(** ** The ghost state, before allocation *)
Class alerusGpreS (FML : oFunctor) Σ : Type := AlerusGpreS {
  #[global] alerus_preG_lrust :: lrustGpreS FML Σ;
  #[global] alerus_preG_llft :: llft_logicGpreS Σ;
  #[global] alerus_preG_sinv :: sinvGpreS FML Σ;
  #[global] alerus_preG_proph :: prophPreG Σ;
  #[global] alerus_preG_uniq :: uniqPreG Σ;
  #[global] alerus_preG_cna :: cnaGpreS FML Σ;
  #[global] alerus_preG_frac :: fracGuardGpreS FML Σ;
  #[global] alerus_preG_eternal :: inG Σ (authUR (gsetUR lft));
  #[global] alerus_preG_llctx ::
    inG Σ (gmap_viewR gname (agreeR (leibnizO llctx)));
  #[global] alerus_preG_lfts ::
    inG Σ (gmap_viewR gname (agreeR (leibnizO (gmultiset lft))));
}.

Definition alerusΣ FML `{!oFunctorContractive FML} : gFunctors :=
  #[lrustΣ FML; llft_logicΣ; sinvΣ FML; prophΣ; uniqΣ; cnaΣ FML;
    fracGuardΣ FML; GFunctor (constRF (authUR (gsetUR lft)));
    fracKeyΣ llctx; fracKeyΣ (gmultiset lft)].

#[export] Instance subG_alerusGpreS {FML Σ} `{!oFunctorContractive FML} :
  subG (alerusΣ FML) Σ → alerusGpreS FML Σ.
Proof. solve_inG. Qed.

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
    iMod (frac_key_wsat_alloc (K:=llctx)) as (Hllctx) "Wllctx".
    iMod (frac_key_wsat_alloc (K:=gmultiset lft)) as (Hlfts) "Wlfts".
    iMod eternal_wsat_alloc as (γe) "We".
    iMod (frac_wsat_alloc (FML:=cifOF CON)) as (Hfrac) "Wfrac".
    iMod (llft_wsat_alloc (FML:=cifOF CON)) as (Hllft Hsinv shr) "Wllft".
    iMod (na_inv_wsat_alloc_name (FML:=cifOF CON)) as (γna) "Wna".
    iMod (cna_wsat_alloc (FML:=cifOF CON)) as (Hcna) "Wcna".
    iMod (proph_init ⊤) as (Hproph) "#PROPH"; [done|].
    iMod (uniq_init ⊤) as (Huniq) "[#UNIQ Wsend]"; [done|].
    iModIntro.
    iExists (AlerusGS _ _ _ Hllft Hsinv hGS
      (NaInvGS _ _ sinvGS_pre _ γna) _ Hproph Huniq Hcna Hfrac
      _ Hllctx Hlfts shr γe).
    do 2 (iSplit; [done|]). iFrame "PROPH UNIQ". iIntros (????).
    iSplit; [done|].
    iSplitR "Wsend"; last iExact "Wsend".
    iSplitL "Wllft We Wfrac Wllctx Wlfts"; last first.
    { iSplitL "Wcna"; first by iApply "Wcna".
      iApply "Wna". iApply ne_internal_ne; try exact _. }
    iApply ("Wllft" $! _ alerus_WG). rewrite /alerus_WG.
    iSplitL "We"; first iApply "We".
    iSplitL "Wfrac"; first (iApply "Wfrac"; iApply ne_internal_ne;
      try exact _).
    iSplitL "Wllctx"; first iExact "Wllctx".
    iExact "Wlfts".
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
End soundness.

(** The theorem rests on nothing but the axioms Iris itself uses. *)
Print Assumptions type_soundness.
