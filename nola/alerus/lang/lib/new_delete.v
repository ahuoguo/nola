(** * Allocation and deallocation wrappers, later-free and total

  Ported from VerusBelt ([lang/lib/new_delete.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).  The only changes are the move to [twpw] and the
  replacement of the mask side condition [↑naN ⊆ E] on [wp_delete] by the
  world-satisfaction inclusion [WsatIncl W na_wsat Wr]. *)

From nola.alerus.lang Require Export notation.
From nola.alerus.lang Require Import heap proofmode lifting.
From nola.alerus.lang.lib Require Import memcpy.
From nola.alerus.util Require Import non_atomic_cell_map.
From iris.prelude Require Import options.
Import WpwNotation.

Definition new : val :=
  λ: ["n"],
    if: "n" ≤ #0 then #((42%positive, 1337):loc)
    else Alloc "n".

Definition delete : val :=
  λ: ["n"; "loc"],
    if: "n" ≤ #0 then #☠
    else Free "n" "loc".

Section specs.
  Context `{!lrustGS_gen hlc FML Σ}.

  Lemma twp_new {W s E} n :
    0 ≤ n →
    [[{ True }]][W] new [ #n ] @ s; E
    [[{ l, RET LitV $ LitLoc l;
        (†l…(Z.to_nat n) ∨ ⌜n = 0⌝) ∗
          l ↦∗ repeat (LitV LitPoison) (Z.to_nat n) }]].
  Proof.
    iIntros (? Φ) "_ →Φ". wp_lam. wp_op; case_bool_decide.
    - wp_if. assert (n = 0) as -> by lia. iApply "→Φ".
      rewrite heap_mapsto_vec_nil. auto.
    - wp_if. iApply (twp_alloc with "[//]"); [lia|].
      iIntros (l sz) "(%eq & † & ↦)". iApply "→Φ".
      have ->: Z.to_nat n = sz by lia. iFrame.
  Qed.
  Lemma wp_new {W s E} n :
    0 ≤ n →
    {{{ True }}}[W] new [ #n ] @ s; E
    {{{ l, RET LitV $ LitLoc l;
        (†l…(Z.to_nat n) ∨ ⌜n = 0⌝) ∗
          l ↦∗ repeat (LitV LitPoison) (Z.to_nat n) }}}.
  Proof.
    iIntros (??) "H →Φ". iApply (twp_wp_step with "→Φ").
    iApply (twp_new with "H"); [done|]. iIntros "%? →Φ !>". by iApply "→Φ".
  Qed.

  Lemma twp_delete `{!WsatIncl W na_wsat Wr} {s E} vl (n : Z) l :
    n = length vl →
    [[{ l ↦∗ vl ∗ (†l…(length vl) ∨ ⌜n = 0⌝) }]][W]
      delete [ #n; #l] @ s; E
    [[{ RET #☠; True }]].
  Proof.
    iIntros (? Φ) "(↦ & [†|%]) →Φ";
      wp_lam; wp_op; case_bool_decide; try lia;
      wp_if; try wp_free; by iApply "→Φ".
  Qed.
  Lemma wp_delete `{!WsatIncl W na_wsat Wr} {s E} vl (n : Z) l :
    n = length vl →
    {{{ ▷ l ↦∗ vl ∗ ▷ (†l…(length vl) ∨ ⌜n = 0⌝) }}}[W]
      delete [ #n; #l] @ s; E
    {{{ RET #☠; True }}}.
  Proof.
    iIntros (??) "[>↦ >†] →Φ". iApply (twp_wp_step with "→Φ").
    iApply (twp_delete with "[$↦ $†]"); [done|]. iIntros "_ →Φ !>".
    by iApply "→Φ".
  Qed.
End specs.

Notation "letalloc: x <- e1 'in' e2" :=
  ((Lam [BNamed x%string%E] (Seq (Var x <- e1) e2))
    [App (of_val new) [ #(LitInt 1)]])%E
  (at level 102, x at level 1, e1, e2 at level 150) : expr_scope.

Notation "letalloc: x <-{ n } ! e1 'in' e2" :=
  ((Lam [BNamed x%string%E%E]
    (Seq (Var x <-{n%Z%E} !e1) e2))
    [App (of_val new) [ Lit (LitInt n)]])%E
  (at level 102, x at level 1, e1, e2 at level 150,
    format "letalloc:  x  <-{ n }  ! e1  'in'  e2") : expr_scope.
