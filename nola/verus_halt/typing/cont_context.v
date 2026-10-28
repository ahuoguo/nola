(** * Continuation contexts

  Ported from VerusBelt ([typing/cont_context.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.  The weakest precondition
  becomes the *total* one over [verus_halt_wsat], and [cctx_incl_cons] uses
  [Ltok] instead of [llctx_interp_make_guarded]'s arbitrary [G]. *)

From iris.proofmode Require Import proofmode.
From nola.verus_halt.lang Require Import notation.
From nola.verus_halt.typing Require Import type ctx lft_contexts type_context
  inv_context.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation WpwNotation.

Implicit Type 𝔄: syn_type.

Section cont_context.
  Context `{!typeG FML Σ}.

  Definition cont_postcondition: iProp Σ := True%I.

  Record cctx_elt 𝔄 := CCtxe {
    cctxe_k: val;
    cctxe_L: llctx;
    cctxe_I: invctx;
    cctxe_Al: syn_typel; 
    cctxe_n: nat;
    cctxe_T: vec val cctxe_n → tctx cctxe_Al;
    cctxe_tr: predl_trans' cctxe_Al 𝔄;
  }.
  Global Arguments CCtxe {_} _ _ _ {_ _} _ _.

  Definition cctx_elt_interp {𝔄} (tid: thread_id) iκs
    (post: (pred' (~~𝔄))) (c: cctx_elt 𝔄) : iProp Σ :=
    let 'CCtxe k L Ic T tr := c in ∀vl xl mask,
      llctx_interp L -∗ invctx_interp tid mask iκs Ic -∗ tctx_interp tid (T vl) xl -∗
        ⟨π, tr post xl mask π⟩ -∗
        WP[verus_halt_wsat] k (map of_val vl) [{ _, cont_postcondition }].

  Definition cctx_interp {𝔄} (tid: thread_id) iκs
    (post: pred' (~~𝔄)) (C: list (cctx_elt 𝔄)) : iProp Σ :=
    ∀c, ⌜c ∈ C⌝ -∗ cctx_elt_interp tid iκs post c.
End cont_context.
Add Printing Constructor cctx_elt.

Notation cctx 𝔄 := (list (cctx_elt 𝔄)).

Notation "k ◁cont{ L , I , T } tr" := (CCtxe k L I T tr)
  (at level 55, format "k  ◁cont{ L ,  I ,  T }  tr").

Section cont_context.
  Context `{!typeG FML Σ}.

  Global Instance cctx_interp_permut {𝔄} tid iκs (post: pred' (~~𝔄)) :
    Proper ((≡ₚ) ==> (⊣⊢)) (cctx_interp tid iκs post).
  Proof. solve_proper. Qed.

  Lemma cctx_interp_cons {𝔄} tid iκs postπ (c: cctx_elt 𝔄) C :
    cctx_interp tid iκs postπ (c :: C) ⊣⊢
    cctx_elt_interp tid iκs postπ c ∧ cctx_interp tid iκs postπ C.
  Proof.
    iSplit; iIntros "cC".
    - iSplit; [|iIntros (??)]; iApply "cC"; iPureIntro; by constructor.
    - iIntros (? In). move: In. rewrite elem_of_cons. case=> [->|?].
      + by iDestruct "cC" as "[? _]".
      + iDestruct "cC" as "[_ C]". by iApply "C".
  Qed.

  Lemma cctx_interp_nil {𝔄} tid iκs (post: pred' (~~𝔄)) :
    cctx_interp tid iκs post [] ⊣⊢ True.
  Proof. iSplit; [by iIntros|]. iIntros "_ % %In". inversion In. Qed.

  Lemma cctx_interp_app {𝔄} tid iκs postπ (C: cctx 𝔄) C' :
    cctx_interp tid iκs postπ (C ++ C') ⊣⊢
    cctx_interp tid iκs postπ C ∧ cctx_interp tid iκs postπ C'.
  Proof.
    elim C. { by rewrite/= cctx_interp_nil left_id. }
    move=>/= ?? IH. by rewrite !cctx_interp_cons IH assoc.
  Qed.

  Lemma cctx_interp_singleton {𝔄} tid iκs postπ (c: cctx_elt 𝔄) :
    cctx_interp tid iκs postπ [c] ⊣⊢ cctx_elt_interp tid iκs postπ c.
  Proof. by rewrite cctx_interp_cons cctx_interp_nil right_id. Qed.

  Definition cctx_incl {𝔄} (E: elctx) (C C': cctx 𝔄) : Prop :=
    ∀tid iκs postπ, llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗ cctx_interp tid iκs postπ C -∗ cctx_interp tid iκs postπ C'.

  Global Instance cctx_incl_preorder {𝔄} E : PreOrder (@cctx_incl 𝔄 E).
  Proof.
    split; [iIntros (????) "_ _ _ _ $"|].
    iIntros (??? In In' ???) "#LFT #PROPH #UNIQ #E ?".
    iApply (In' with "LFT PROPH UNIQ E"). by iApply (In with "LFT PROPH UNIQ E").
  Qed.

  Lemma incl_cctx_incl {𝔄} E (C1 C2: cctx 𝔄) : C1 ⊆ C2 → cctx_incl E C2 C1.
  Proof.
    iIntros (Sub ???) "_ _ _ _ C". iIntros (? In). move/Sub in In. by iApply "C".
  Qed.

  Lemma cctx_incl_nil {𝔄} E (C: cctx 𝔄) : cctx_incl E C [].
  Proof. iIntros "%%% _ _ _ _ _ % %In". inversion In. Qed.

  Lemma cctx_incl_cons {𝔄 𝔄l} k L n (T T': vec val n → tctx 𝔄l) tr tr' (I: invctx) (C C': cctx 𝔄) E :
    cctx_incl E C C' → (∀vl, tctx_incl E L (T' vl) (T vl) tr') →
    cctx_incl E (k ◁cont{L, I, T} tr :: C) (k ◁cont{L, I, T'} (tr' ∘ tr) :: C').
  Proof.
    iIntros (InC InT ???) "LFT PROPH UNIQ E kC". rewrite !cctx_interp_cons. iSplit.
    - iDestruct "kC" as "[k _]". iIntros (???) "L I T' Obs".
      iMod (Ltok_alloc with "L") as (γ) "tok".
      iDestruct (Ltok_split_1 with "tok") as "[t1 t2]".
      iMod (proj2 (InT _) with "LFT PROPH UNIQ E t1 T' Obs") as (?) "(t1 & T & Obs)".
      iDestruct (Ltok_split_2 with "t1 t2") as "tok".
      iMod (Ltok_withdraw with "tok") as "L".
      iApply ("k" with "L I T Obs").
    - iDestruct "kC" as "[_ ?]". by iApply (InC with "LFT PROPH UNIQ E").
  Qed.
End cont_context.

Global Hint Resolve cctx_incl_nil cctx_incl_cons : lrust_typing.
