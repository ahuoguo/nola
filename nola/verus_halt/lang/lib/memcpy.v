(** * Memory copy, later-free and total

  Ported from VerusBelt ([lang/lib/memcpy.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  The original's [wp_memcpy_guarded] is where the time-receipt machinery is at
  its most visible: it takes [⧖d ∗ £(6*d)], splits the budget as [£(3*d+3*d)],
  feeds one half to [wp_read_na_guarded_cells] and the other to
  [wp_write_na_guarded_more_credits], and threads the leftover credits through
  a [iLöb] induction.  All of that was in service of stripping the laters the
  guards introduce.  Later-free the budget disappears, the proof becomes a
  structural induction on the length (which is what the *total* weakest
  precondition needs anyway - [iLöb] is unavailable), and the plain
  [twp_memcpy] of the unguarded case comes out as a corollary. *)

From nola.verus_halt.lang Require Export notation.
From nola.verus_halt.lang Require Import heap proofmode lifting.
From nola.verus_halt.util Require Import non_atomic_cell_map.
From nola.bi Require Import guard.
From iris.prelude Require Import options.
Import WpwNotation GuardNotation.

Definition memcpy : val :=
  rec: "memcpy" ["dst";"len";"src"] :=
    if: "len" ≤ #0 then #☠
    else "dst" <- !"src";;
         "memcpy" ["dst" +ₗ #1 ; "len" - #1 ; "src" +ₗ #1].

Notation "e1 <-{ n } ! e2" :=
  (App (of_val memcpy) [e1%E; Lit (LitInt n); e2%E])
  (at level 80, n at next level, format "e1  <-{ n }  ! e2") : expr_scope.

Notation "e1 <-{ n ',Σ' i } ! e2" :=
  (e1%E%E <- #(LitInt i);; e1 +ₗ #(LitInt 1) <-{n} !e2)%E
  (at level 80, n, i at next level, format "e1  <-{ n ,Σ  i }  ! e2")
  : expr_scope.

Section memcpy.
  Context `{!lrustGS_gen hlc FML Σ}.

  (** Copy [n] values from a guarded source into a guarded destination.

    The destination cells are owned ([l1 #↦∗ vl1]) but their *chain* is only
    guarded, which is why [Gw] is needed as well as [Gr]. *)
  Lemma twp_memcpy_guarded `{!WsatIncl W na_wsat Wr} {s E} (n : nat) :
    ∀ (l1 l2 : cloc) vl1 vl2 Gw Gr,
    length vl1 = n → length vl2 = n →
    [[{ l1 #↦∗ vl1 ∗
        (na_sem Gw &&{na_wsat}&&> l1 #↦∗_) ∗
        (na_sem Gr &&{na_wsat}&&> (l2.1 ↦[^ l2.2]∗ vl2)) ∗
        na_sem Gw ∗ na_sem Gr }]][W]
      #(l1.1) <-{n} !#(l2.1) @ s; E
    [[{ RET #☠; l1 #↦∗ vl2 ∗ na_sem Gw ∗ na_sem Gr }]].
  Proof.
    elim: n.
    { move=> l1 l2 vl1 vl2 Gw Gr /nil_length_inv -> /nil_length_inv ->.
      iIntros (Φ) "(↦ & _ & _ & Gw & Gr) →Φ". wp_rec. wp_op. wp_if.
      iApply "→Φ". iFrame. }
    move=> n IH [l1 cs1][l2 cs2][|v1 vl1][|v2 vl2] Gw Gr //= [len1][len2].
    iIntros (Φ) "(↦ & #gw & #gr & Gw & Gr) →Φ".
    destruct cs1 as [|c1 cs1]; [by iDestruct "↦" as "[]"|].
    rewrite heap_mapsto_cloc_vals_vec_cons. iDestruct "↦" as "[↦1 ↦l]".
    (* split the two guards into head and tail *)
    iDestruct (guard_rhs_sep_l (Q:=((l1, c1) #↦_)%I)
      (R:=((l1 +ₗ 1, cs1) #↦∗_)%I) with "gw") as "#gw1".
    iDestruct (guard_rhs_sep_r (Q:=((l1, c1) #↦_)%I)
      (R:=((l1 +ₗ 1, cs1) #↦∗_)%I) with "gw") as "#gw2".
    iAssert ((na_sem Gr &&{na_wsat}&&> (l2 ↦[^ hd [] cs2] v2)) ∗
             (na_sem Gr &&{na_wsat}&&>
                ((l2 +ₗ 1) ↦[^ tail cs2]∗ vl2)))%I as "[#gr1 #gr2]".
    { destruct cs2 as [|c2 cs2].
      - (* vacuous: the source chain is too short, so the guard is on [False] *)
        iSplit; by iApply (guard_false with "gr").
      - iSplit.
        + iApply (guard_rhs_sep_l (Q:=(l2 ↦[^ c2] v2)%I)
            (R:=((l2 +ₗ 1) ↦[^ cs2]∗ vl2)%I) with "gr").
        + iApply (guard_rhs_sep_r (Q:=(l2 ↦[^ c2] v2)%I)
            (R:=((l2 +ₗ 1) ↦[^ cs2]∗ vl2)%I) with "gr"). }
    wp_rec. wp_op. wp_if.
    wp_bind (!#l2)%E.
    iApply (twp_read_na_guarded_cells with "[$Gr]"); [iFrame "gr1"|].
    iIntros "Gr". wp_bind (#l1 <- v2)%E.
    iApply (twp_write_na_guarded with "[$Gw $↦1]"); [iFrame "gw1"|].
    iIntros "[↦1 Gw]". wp_seq. do 3 wp_op.
    have -> : (S n - 1)%Z = n by lia.
    iApply (IH (l1 +ₗ 1, cs1) (l2 +ₗ 1, tail cs2) vl1 vl2 Gw Gr
      with "[$↦l $Gw $Gr]")=>//=; [by iFrame "gw2 gr2"|].
    iIntros "(↦l & Gw & Gr)". iApply "→Φ". rewrite heap_mapsto_cloc_vals_vec_cons.
    iFrame.
  Qed.

  (** The unguarded copy, as in Iris's lrust *)
  Lemma twp_memcpy `{!WsatIncl W na_wsat Wr} {s E} l1 l2 vl1 vl2 (n : nat) :
    length vl1 = n → length vl2 = n →
    [[{ l1 ↦∗ vl1 ∗ l2 ↦∗ vl2 }]][W] #l1 <-{n} !#l2 @ s; E
    [[{ RET #☠; l1 ↦∗ vl2 ∗ l2 ↦∗ vl2 }]].
  Proof.
    move: l1 l2 vl1 vl2. elim: n.
    { move=> ?? vl1 vl2 /nil_length_inv -> /nil_length_inv ->.
      iIntros (Φ) "[↦1 ↦2] →Φ". wp_rec. wp_op. wp_if. iApply "→Φ". iFrame. }
    move=> n IH ??[|v1 vl1][|v2 vl2]//=[len1][len2]. iIntros (Φ) "[↦1 ↦2] →Φ".
    rewrite !heap_mapsto_vec_cons. iDestruct "↦1" as "[↦1 ↦1l]".
    iDestruct "↦2" as "[↦2 ↦2l]". wp_rec. wp_op. wp_if. wp_read. wp_write.
    do 3 wp_op. have -> : (S n - 1)%Z = n by lia.
    iApply (IH _ _ vl1 vl2 with "[$↦1l $↦2l]")=>//. iIntros "[??]".
    iApply "→Φ". iFrame.
  Qed.
End memcpy.
