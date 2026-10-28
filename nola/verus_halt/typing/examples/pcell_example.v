(** * [pcell_example], ported

  Ported from VerusBelt ([typing/examples/pcell_example.v], MIT, Hance,
  Elbeheiry, Matsushita, Dreyer).

  The upstream development's end-to-end example, and the port's: a
  [PCell] created from an owning pointer, borrowed uniquely, shared,
  read through, and the result passed to [assert] by a real function
  call, with two lifetimes opened and closed around it.

  It is unchanged from upstream apart from the execution level.  The
  arrow is [fn(∅) →{fn_lv_top} ()], the function literal is typed with
  [type_fn_top] and the call with [type_letcall_top] - the two rules at
  the ambient level, whose premises are ordinary [typed_body]s and
  which have no side condition left to discharge
  ([typing/function.v]).  Every other line, including the whole proof
  obligation at the end, is upstream's.

  This is what settles that the level does not get in the way of
  verifying a program: the port's rules compose exactly as VerusBelt's
  do, and the level shows only in the type. *)

From iris.proofmode Require Import proofmode.
From nola.verus_halt.typing Require Export type function product programs
  bool own cont uninit pcell product_split borrow.
From nola.verus_halt.typing.examples Require Import assert.
From nola.verus_halt.lang Require Import lang notation.

Section pcell_example.
  Context `{!typeG FML Σ} `{FnFml0 : !FnFml} `{!PcellFml}
    `{!AtomicInvFml} `{!LocalInvFml}.

  (*
  VerusBelt corresponding to the following simple Verus program:

  ```
  use vstd::prelude::*;
  use vstd::cell::pcell::*;

  verus!{

    fn pcell_example() {
        let pcell_pair = PCell::new(17);
        let pcell = pcell_pair.0;
        let Tracked(pointsto) = pcell_pair.1;

        let pcell_shr_ref = &pcell;
        let tracked pointsto_shr_ref = &pointsto;

        let intref = pcell_shr_ref.borrow(Tracked(pointsto_shr_ref));
        let x = *intref;

        assert(x == 17);
    }

  }
  ```

  The example illustrates:
    * Using PCell
    * Basic borrowing rules
    * Function call (to assert).  (The assert we use in this program is excecutable, so it's more like `assert_unchecked` than it's like the Verus specification assert.)
  *)
  
  Definition pcell_example : val :=
    fn: [] :=
      let: "p" := new [ #1 ] in   (* p : box int *)
      let: "int_init" := #17 in
      "p" <- "int_init" ;; (* write 17 *)
      let: "pcell_pair" := (PCellFromOwn ["p"]) in (* pcell_pair : box (PCell<int>, CellPointsTo) *)
      let: "pcell" := "pcell_pair" +ₗ #0 in
      let: "pointsto" := "pcell_pair" +ₗ #1 in
      
      (* There's no way to go straight to a shared borrow in VerusBelt;
         we create a unique borrow first, then turn it into a shared one. *)
      Newlft;;
      let: "pcell_uniq_ref" := UniqBor in
      let: "pcell_shr_ref" := Share in (* borrow pcell *)
      
      Newlft;;
      let: "pointsto_uniq_ref" := UniqBor in
      let: "pointsto_shr_ref" := Share in (* borrow pointsto *)
      
      (* borrow and read *)
      let: "intref" := PCellBorrow ["pcell"; "pointsto"] in
      let: "x" := !"intref" in
      
      (* compute x == 17 *)
      let: "seventeen" := #17 in
      let: "b" := ("x" = "seventeen") in
      letalloc: "b'" <- "b" in
      (* call assert *)
      let: "assert" := assert in
      letcall: "assert_ret" := "assert" ["b'"] in
      
      Endlft;;
      Endlft;;
      
      (* return unit *)
      let: "r" := new [ #0] in return: ["r"].
      
  
  (* We're going to use VerusBelt to prove the `pcell_example` function
     correct with a trivial precondition, that is, we show it is always safe to execute.
     
     In the comments, we discuss how this proof corresponds to what Verus actually does.
  *)
  Lemma pcell_example_type :
    typed_val
        pcell_example
        ((fn(∅) →{fn_lv_top} ())
          (λ (c: ~~ ()) 𝛷 '-[] , λ mask π, ∀ l, 𝛷 (l, ()) mask π))
        (pcell_example, ()).
  Proof.
    unfold pcell_example. unlock.
    opose proof (@type_fn_top
        _ _ _ _ _
        []
        ()
        ()
        ()
        (λ y: (), FP ∅ +[] () AtomicClosed)
        (λ (c: ~~ ()) 𝛷 '-[] , λ mask π, ∀ l, 𝛷 (l, ()) mask π)
        (_)%E
        [] _ _ _
    ) as Hfn.
    unlock in Hfn. apply Hfn. clear Hfn.
    intros c ϝ k wl.
    destruct wl. simpl_subst.
    
    (* The first part corresponds to the type-checking; this part is done by rustc. *)
    
    iApply (typed_body_impl with "[]"); last first. {
    
    iApply (type_new 1 with "[]"). { lia. } iIntros (v_p). simpl_subst.
    iApply type_int. iIntros (v_int_init). simpl_subst.
    iApply type_assign. { solve_typing. } { apply write_own; trivial. }
        { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
    iApply (type_let with "[]").
      { apply (typed_pcell_from_own _ int). }
      { solve_typing. } { reflexivity. } iIntros (v_pcell_pair). simpl_subst.
      
    iApply typed_body_tctx_incl. { apply tctx_incl_swap. }
    iApply typed_body_tctx_incl. { eapply tctx_incl_tail. apply tctx_split_own_prod. }
    iApply type_letpath. { solve_typing. } iIntros (v_pcell). simpl_subst.
    iApply type_letpath. { solve_typing. } iIntros (v_pointsto). simpl_subst.
    
    iApply (type_newlft []). iIntros (κ1).
    iApply (type_let with "[]").
      { eapply (type_uniqbor_instr _ _ _ _ _ (pcell_ty 1) κ1).
        - apply (lctx_lft_alive_local _ _ κ1 []). { apply elem_of_cons; left; trivial. } done.
        - solve_typing.
      }
      { solve_typing. } { reflexivity. }
      iIntros (v_pcell_uniq_ref). simpl_subst.
    iApply (type_let with "[]").
      { eapply (type_share_instr _ κ1 (pcell_ty 1)).
        apply (lctx_lft_alive_local _ _ κ1 []). { apply elem_of_cons; left; trivial. } done.
      }
      { solve_typing. } { reflexivity. }
      iIntros (v_pcell_shr_ref). simpl_subst.
      
    iApply (type_newlft []). iIntros (κ2).
    iApply (type_let with "[]").
      { eapply (type_uniqbor_instr _ _ _ _ _ (cell_points_to_ty int) κ2); solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (v_pointsto_uniq_ref). simpl_subst.
    iApply (type_let with "[]").
      { eapply (type_share_instr _ κ2 (cell_points_to_ty int)). solve_typing.
       (* apply (lctx_lft_alive_local _ _ κ2 []). { apply elem_of_cons; left; trivial. } done.*)
      }
      { solve_typing. } { reflexivity. }
      iIntros (v_pointsto_shr_ref). simpl_subst.
    
    iApply (type_let with "[]").
      { eapply (typed_pcell_borrow (κ1 ⊓ κ2) v_pcell v_pointsto int). }
      { solve_typing. } { reflexivity. }
    
    iIntros (v_intref). simpl_subst.
    
    iApply (type_let with "[]").
      { eapply (type_deref_instr (𝔅 := Zₛ) _ (int)); trivial.
        * apply int_stack_okay.
        * apply (read_shr int (κ1 ⊓ κ2)). { apply int_copy. } { solve_typing. }
      }
      { solve_typing. } { reflexivity. }
      
    iIntros (v_x). simpl_subst.
    
    iApply type_int. iIntros (v17). simpl_subst.
    iApply type_int_eq. { solve_typing. } iIntros (v_eq). simpl_subst.
    iApply (type_letalloc_1 bool_ty). { solve_typing. } 2: { trivial. }
        { eapply (_: ∀ x, x ≡ x). } iIntros (v_b'). simpl_subst.
        
    iApply type_let. { apply assert_type. } { solve_typing. } { reflexivity. }
    iIntros (v_assert). simpl_subst.
    
    iApply (@type_letcall_top FML Σ typeG0 FnFml0 () [boolₛ] () () _ _ _ ()
        (λ (p: ()), FP ∅ +[bool_ty] () AtomicClosed)).
      { solve_typing. } { apply lctx_ictx_alive_nil. solve_typing. }
      { solve_typing. } { solve_typing. }
    iIntros (v_assert_ret). simpl_subst.
    
    iApply (type_endlft _ _ _ _ κ2). { solve_typing. } {
      repeat (apply unblock_tctx_cons_just). apply unblock_tctx_nil.
    }
    iApply (type_endlft _ _ _ _ κ1). { solve_typing. } {
      repeat (apply unblock_tctx_cons_just). apply unblock_tctx_nil.
    }
    
    iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
    iIntros (v_unit_ret). simpl_subst.
    
    iApply type_jump.
      { rewrite list_elem_of_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
   }
      
   Unshelve.
   2: { intros. reflexivity. }
   2: { eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ). }
   
   (* Now that's we've type-checked it, we're effectively left with a predicate
      from the cumulative predicate transformers; it loosely corresponds to the weakest pre
      predicate that Verus would construct in its VC gen.
      Verus would then use Z3 to dispatch the obligations; obviously, we'll do it in Rocq, here.
      
      Since the program is pretty trivial, we mostly just need to unfold and destruct
      a bunch of stuff.
   *)
   
   intros post [] mask π.
   intros Ha l junk [loc i] Heq.
   inversion Heq. subst i. subst l.
   intros cells bor [[[l1 cells1] ξi] t].
   destruct bor as [[[[[[l cells0] x0] ξi'] d'] g'] idx].
   simpl. intros. subst x0. subst l.
   simpl in *.
   unfold trans_upper. simpl.
   intros H3 m z Hl Hcureq.
   destruct m as [[[[[[l' cells'] [cells2 x']] ξi''] d''] g''] idx'].
   destruct z as [[[l [cells3 zval]] k1] k2].
   intro. intros.
   intros. unfold uniq_bor_current.
   simpl in *.
   unfold uniq_bor_current in Hcureq. inversion Hcureq.
   
   (* Now we finally get to the "proof obligations" *)
   
   (* confirm 2 cell ids are equal; this must be the precondition to a PCell operation *)
   split; first by trivial.
   
   intros [zl z] Heqz loc4. inversion Heqz. subst z.
   
   (* 17=17, precondition for the assert *)
   split; first by trivial.
   
   intros [retl retu] [y0 [y1 [y2 [y3 [y4 [y5 [y6 [y7 [y8 [y9 [y10 [y11 []]]]]]]]]]]]].
   intros [<- [<- [<- [<- [<- [<- [<- [<- [<- [<- [<- [<- Hd]]]]]]]]]]]].
   unfold trans_tail. simpl.
   intros [w0 [w1 [w2 [w3 [w4 [w5 [w6 [w7 [w8 [w9 [w10 [w11 []]]]]]]]]]]]].
   intros [<- [<- [<- [<- [<- [<- [<- [<- [<- [<- [<- [<- He]]]]]]]]]]]].
   intros l0 junk0 Hconst. simpl. apply Ha.
  Qed. (* long Qed *)
   
End pcell_example.

(** The end-to-end instantiation - upstream's
  [pcell_example_executes_without_getting_stuck], through
  [type_soundness_closed] - needs the soundness theorem in the shape
  upstream states it, about a [main] *function value* that the runtime
  calls, rather than about a closed [typed_body].  That shape needs
  [fn] to be interpreted, which it now is; see [typing/soundness.v]. *)
