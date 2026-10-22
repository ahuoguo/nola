(** * The typing layer's interface, instantiated

  [model.v] builds the [cif] model of [typing/ctx.v]'s interface; this file
  bundles it into a [typeG] and gives the remaining formula-language
  classes, which live in the files that use them. *)

From nola.alerus.typing Require Export model.
From nola.alerus.typing Require Import type pcell atomic_inv local_inv.
From nola.iris Require Import cif.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation.

(** ** The typing layer's interface, instantiated

  With [AltSem] in place every class [typeG] bundles has an instance, so the
  development is no longer parametric: [typeG_cif] is the model. *)
Section typeG.
  Context `{!typingC CON} {JUDG Σ} `{!alerusGS (cifOF CON) Σ,
    !typingJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !typingCS CON JUDG Σ, !typingJS CON JUDG Σ}.

  #[export] Instance typeG_cif : typeG (cifOF CON) Σ := {|
    type_alerusGS := _;
    type_alerusSem := alerusSem_der;
    type_heapSem := heapSem_cif;
    type_gsrcSem := gsrcSem_cif;
    type_typeFml := typeFml_cif;
    type_stBor := stBor_cif (JUDG:=JUDG);
    type_stBorSem := stBorSem_alt;
    type_altSem := altSem_cif;
  |}.

  (** The Points-To Cell Logic's vector of cells *)
  #[export] Program Instance pcellFml_cif : PcellFml :=
    {| cellsvec_fml := cif_cellsvec |}.
  Next Obligation. move=> *. exact cif_cellsvec_sem. Qed.
  Next Obligation. move=> *. exact: cellsvec_sem_cif. Qed.

  (** Atomic invariants *)
  #[export] Program Instance atomicInvFml_cif : AtomicInvFml :=
    {| active_fml := cif_active; obs_fml := cif_obs;
       na_inv_tok_fml := cif_na_inv; na_otok_fml := cif_na_otok;
       handle_fml := cif_handle |}.
  Next Obligation. move=> ?. exact cif_active_sem. Qed.
  Next Obligation. move=> ?. exact cif_obs_sem. Qed.
  Next Obligation. move=> *. exact cif_na_inv_sem. Qed.
  Next Obligation. move=> *. exact cif_na_otok_sem. Qed.
  Next Obligation. move=> ?. exact cif_handle_sem. Qed.

  (** Cancellable non-atomic invariants *)
  #[export] Program Instance localInvFml_cif : LocalInvFml :=
    {| cna_active_fml := cif_cna_active; cna_inv_fml := cif_cna_inv;
       cna_otok_fml := cif_cna_otok |}.
  Next Obligation. move=> ?. exact cif_cna_active_sem. Qed.
  Next Obligation. move=> *. exact cif_cna_inv_sem. Qed.
  Next Obligation. move=> *. exact cif_cna_otok_sem. Qed.
End typeG.

(** [typeG_cif] needs an [alerusGS], and [typeG]'s first field projects one
  back out, so typeclass resolution can cycle

    [typeG ?FML ?Σ --typeG_cif--> alerusGS … --type_alerusGS--> typeG … --…]

  deepening forever.  It only bites once [typeG_cif] is in scope as a global
  instance - that is, in [typing/inst.v] and anything downstream - and there
  it is fatal: a single [exists] against a goal mentioning [typed_body] ran
  to 9.1GB over 25 minutes without finishing.  Cutting the cycle is enough;
  finding an [alerusGS] in the local context is not an instance application
  and is unaffected.  The other seven projections are cut too, since each
  would close a longer cycle the same way. *)
Global Hint Cut [ _* typeG_cif
  (type_alerusGS | type_alerusSem | type_heapSem | type_gsrcSem |
   type_typeFml | type_stBor | type_stBorSem | type_altSem) ]
  : typeclass_instances.
