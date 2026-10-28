(** * Continuations

  Ported from VerusBelt ([typing/cont.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer), itself from RustHornBelt.

  [type_jump] loses the whole time-receipt dance: the original takes the
  [⧖ d] that [resolve_tctx] produces, turns the [Skip] of [jump: k el] into
  later credits with [wp_persistent_time_receipt], and spends them on
  [lc_step_fupdN_elim_later] to strip the [|={…}▷=>^d] in front of the
  resolution.  Later-free [resolve_tctx] is a plain update, so the [Skip] is
  just a step.

  [type_cont], the *recursive* continuation rule, is **not** ported as it
  stands.  Its proof is an [iLöb] over the continuation's own
  specification, and Löb induction is unavailable for a total weakest
  precondition - that is exactly the step-indexing a total WP gives up.  A
  recursive continuation is a loop, and a terminating loop needs a
  decreasing measure, which VerusBelt's judgment does not carry (it does
  not model Verus's [decreases] clauses either; see the VerusBelt paper,
  §6).  [type_cont_norec], the non-recursive rule, is ported and is what
  the let-continuation form in straight-line code needs.

  What a loop needs is in [typing/recursion.v]: [type_cont_wf] is
  [type_cont] with the Löb step replaced by well-founded recursion over a
  measure on the continuation's own arguments - the shape
  [nola/examples/rust_halt/verify/ack.v] uses, since that development has
  no continuation rule either and recurses at the Coq level.
  [typing/examples/loop.v] runs a loop through it and proves the loop
  terminates. *)

From iris.proofmode Require Import proofmode.
From nola.verus_halt.typing Require Import programs.
From nola.verus_halt.typing Require Export type ctx.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Class IntoVecVal {n} (el: list expr) (vl: vec val n) :=
  into_vec_val: el = map of_val vl.

Global Instance into_vec_val_nil: IntoVecVal [] [#].
Proof. done. Qed.

Global Instance into_vec_val_cons {n} e v el (vl: _ n) :
  IntoVal e v → IntoVecVal el vl → IntoVecVal (e :: el) (v ::: vl).
Proof. by move=>/= <-->. Qed.

Section typing.
  Context `{!typeG FML Σ}.

  (** Jumping to and defining a continuation. *)

  Lemma type_jump {𝔄l 𝔅l ℭl 𝔇 n} (T': vec val n → tctx 𝔅l) k el
      (vl: vec val n) tr trx tr_res Φ E L (T: tctx 𝔄l) (Tx: tctx ℭl)
      (I: invctx) (C: cctx 𝔇) :
    IntoVecVal el vl → k ◁cont{L, I, T'} tr ∈ C →
    tctx_extract_ctx E L (T' vl) T Tx trx → resolve_tctx E L Tx Φ →
    tr_res ≡ trx ∘ (λ post bcl mask π,
      let '(bl, cl) := psep bcl in Φ cl π (tr post bl mask π)) →
    ⊢ typed_body E L I C T (jump: k el) tr_res.
  Proof.
    move=> -> ? TT' Rslv Htr_res.
    iApply typed_body_impl.
    { move=> ???? Hpre. rewrite /equiv in Htr_res. by apply Htr_res in Hpre. }
    iApply typed_body_tctx_incl; [done|]. iIntros (? bcπl ?).
    move: (papp_ex bcπl)=> [?[?->]].
    iIntros (post ?) "#LFT #PROPH #UNIQ E L I C /=[T' Tx] Obs".
    iApply fupdw_twpw_cont. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]".
    iMod (Rslv with "LFT PROPH UNIQ E tok Tx W") as "(W & Obs' & tok)";
      [solve_ndisj|].
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    iCombine "Obs Obs'" as "#Obs2". do 2 wp_seq.
    iApply ("C" with "[%//] L I T' []"). iApply proph_obs_impl; [|done]=>/= ?.
    rewrite papp_sepl papp_sepr. case=> ? Imp. by apply Imp.
  Qed.

  Lemma type_cont_norec {𝔄l 𝔅l ℭ} bl (T': vec val (length bl) → tctx 𝔅l) trk
        L' I' (T: tctx 𝔄l) kb ec e tr E L I (C: cctx ℭ) :
    Closed (kb :b: bl +b+ []) ec → Closed (kb :b: []) e →
    (∀k: val, typed_body E L I (k ◁cont{L', I', T'} trk :: C) T
      (subst' kb k e) tr) -∗
    (∀(k: val) (vl: vec val (length bl)),
      typed_body E L' I' C (T' vl) (subst' kb k $ subst_v bl vl ec) trk) -∗
    typed_body E L I C T (letcont: kb bl := ec in e) tr.
  Proof.
    iIntros (??) "e ec %%%%% #LFT #PROPH #UNIQ #E L I C T Obs".
    have ->: (rec: kb bl := ec)%E = of_val (rec: _ _ := _) by unlock.
    wp_let. iApply ("e" with "LFT PROPH UNIQ E L I [ec C] T Obs").
    iIntros (?). rewrite elem_of_cons. iIntros ([->|?]); [|by iApply "C"].
    iIntros (???) "L' I' T' Obs". wp_rec.
    iApply ("ec" with "LFT PROPH UNIQ E L' I' C T' Obs").
  Qed.
End typing.
