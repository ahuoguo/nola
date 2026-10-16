(** * Atomic invariants

  Ported from VerusBelt ([typing/atomic_inv.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  The original holds the invariant's contents in an Iris invariant, so
  opening it yields a [▷] and the whole file is organised around the credits
  that strip it; here the contents are a *formula* held by a non-atomic
  invariant of [nola.alerus.na_inv_fork] whose world satisfaction is a
  component of [alerus_wsat], so opening is later-free and credit-free.  The
  cancellable layer ([external_na_inv], [Active]) is rebuilt on top of that.

  *** Not ported: [typed_atomic_lock].

  It acquires the global atomic lock, whose implementation is a spin loop
  with no total-WP proof - see the note in [typing/programs_util_atomic.v].
  [typed_atomic_unlock] is fine and is ported. *)

From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From Stdlib.Logic Require Import Classical_Prop PropExtensionality
  FunctionalExtensionality.
From nola.alerus.typing Require Export type.
From nola.alerus.typing Require Import type_context programs
  programs_util_own programs_util_atomic own ghost tracked shr_bor product
  inv_context lft_contexts.
From nola.alerus Require Import na_inv_fork.
From nola.alerus.util Require Import atomic_lock_counter.
From nola.alerus.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation WpwNotation.

Implicit Type 𝔄 𝔅: syn_type.

Section atomic_invariants.
  Context `{!typeG FML Σ}.

  Definition null_tid : thread_id := atomic_pool_name.

  (** ** The cancellable layer, rebuilt over later-free non-atomic
    invariants *)

  Definition Active (γ: gname) : iProp Σ := own γ (Excl ()).

  Lemma Active_alloc : ⊢ |==> ∃ γ, Active γ.
  Proof. by iApply own_alloc. Qed.
  Lemma Active_2_no γ : Active γ -∗ Active γ -∗ False.
  Proof. iIntros "A B". by iDestruct (own_valid_2 with "A B") as %?. Qed.

  (** The original's closer takes an arbitrary mask and gives it back with
    [↑N] added; the disjointness it needs comes from the two [na_own]s. *)
  Definition atomic_closer (γ: gname) (N: namespace) (Px : FML $oi Σ)
    : iProp Σ :=
    ∀ F, (bor_sem Px ∨ Active γ) -∗ na_own ATOMIC_POOL F =[alerus_wsat]=∗
      na_own ATOMIC_POOL (F ∪ ↑N).

  (** The formula constructors an atomic invariant's ghost assertion names *)
  Class AtomicInvFml := {
    active_fml : gname → FML $oi Σ;
    active_fml_sem γ : bor_sem (active_fml γ) ⊣⊢ Active γ;
    obs_fml : (proph_asn → Prop) → FML $oi Σ;
    obs_fml_sem φ : bor_sem (obs_fml φ) ⊣⊢ ⟨π, φ π⟩;
    na_inv_tok_fml : namespace → FML $oi Σ → FML $oi Σ;
    na_inv_tok_fml_sem N Px :
      bor_sem (na_inv_tok_fml N Px) ⊣⊢ na_inv_tok ATOMIC_POOL N Px;
    atomic_closer_fml : gname → namespace → FML $oi Σ → FML $oi Σ;
    atomic_closer_fml_sem γ N Px :
      bor_sem (atomic_closer_fml γ N Px) ⊣⊢ atomic_closer γ N Px;
    handle_fml : coPset → FML $oi Σ;
    handle_fml_sem c :
      bor_sem (handle_fml c) ⊣⊢ atomic_lock_handle atomic_lock_ctr_name c;
  }.
  Context `{!AtomicInvFml}.

  #[export] Instance na_inv_tok_fml_persistent N Px :
    Persistent (bor_sem (na_inv_tok_fml N Px)).
  Proof. rewrite na_inv_tok_fml_sem. exact _. Qed.

  Definition external_na_inv (γ: gname) (N: namespace) (Px : FML $oi Σ)
    : iProp Σ := na_inv_tok ATOMIC_POOL N (Px ∨ active_fml γ)%FML.

  #[export] Instance external_na_inv_persistent γ N Px :
    Persistent (external_na_inv γ N Px).
  Proof. exact _. Qed.

  Lemma external_na_inv_body_sem γ Px :
    bor_sem (Px ∨ active_fml γ)%FML ⊣⊢ bor_sem Px ∨ Active γ.
  Proof. by rewrite or_fml_sem active_fml_sem. Qed.

  Lemma external_na_inv_alloc N Px :
    bor_sem Px =[alerus_wsat]=∗ ∃ γ, external_na_inv γ N Px ∗ Active γ.
  Proof.
    iIntros "Px W". iMod Active_alloc as (γ) "A".
    iDestruct (na_inv_tok_alloc (p:=ATOMIC_POOL) (sm:=bor_sem)
      (Px ∨ active_fml γ)%FML N with "[Px]") as "T".
    { rewrite external_na_inv_body_sem. by iLeft. }
    iDestruct (bupdw_incl (W:=alerus_wsat) with "T") as "T'".
    iMod ("T'" with "W") as "[$ #tok]". iModIntro. iExists γ. by iFrame "A".
  Qed.

  (** Open an atomic invariant, knowing from a guard that it is not
    cancelled.  The original needs [↑nainvN ∪ F ⊆ E1] and later credits for
    the [▷] the Iris invariant introduces; here the guard is opened against
    [Wguard] and the invariant against [na_inv_wsat], which are different
    components of [alerus_wsat]. *)
  Lemma external_na_inv_acc_strong {G} γ N Px F :
    ↑N ⊆ F →
    external_na_inv γ N Px -∗ (G &&{Wguard}&&> Active γ) -∗ G -∗
    na_own ATOMIC_POOL F =[alerus_wsat]=∗
      na_own ATOMIC_POOL (F ∖ ↑N) ∗ G ∗ bor_sem Px ∗ atomic_closer γ N Px.
  Proof.
    move=> NF. iIntros "#inv #g G pool W".
    rewrite (na_own_subset NF). iDestruct "pool" as "[poolN pool]".
    iDestruct (wsat_split (W':=na_inv_wsat ATOMIC_POOL bor_sem) with "W")
      as "[Wn Wr]".
    iDestruct (na_inv_tok_acc (sm:=bor_sem) (F:=↑N) with "inv poolN Wn")
      as "(body & empty & Wn & close)"; [done|].
    iEval (rewrite external_na_inv_body_sem) in "body".
    iDestruct "body" as "[Px|A]"; last first.
    { iDestruct (wsat_split (W':=Wguard) with "Wr") as "[Wg Wr']".
      iDestruct (guard_acc with "g G Wg") as "[A' _]".
      iDestruct (Active_2_no with "A A'") as "[]". }
    iDestruct (wsat_join (W:=alerus_wsat) with "Wn Wr") as "W".
    iModIntro. iFrame "W pool G Px". iIntros (F') "body pool' W".
    iDestruct (wsat_split (W':=na_inv_wsat ATOMIC_POOL bor_sem) with "W")
      as "[Wn Wr]".
    iDestruct ("close" with "[body] empty Wn") as "[poolN Wn]".
    { by rewrite external_na_inv_body_sem. }
    iDestruct (wsat_join (W:=alerus_wsat) with "Wn Wr") as "$".
    iDestruct (na_own_disjoint with "pool' poolN") as %?.
    iModIntro. rewrite na_own_union; [|done]. iFrame.
  Qed.

  Lemma external_na_inv_cancel γ N Px F :
    ↑N ⊆ F →
    external_na_inv γ N Px -∗ Active γ -∗
    na_own ATOMIC_POOL F =[alerus_wsat]=∗ bor_sem Px ∗ na_own ATOMIC_POOL F.
  Proof.
    move=> NF. iIntros "#inv A pool W".
    iMod (external_na_inv_acc_strong γ N Px F NF with "inv [] A pool W")
      as "(W & pool & A & Px & close)"; [iApply guard_refl|].
    iMod ("close" $! (F ∖ ↑N) with "[A] pool W") as "[W pool]";
      [by iRight|].
    have ->: ((F ∖ ↑N) ∪ ↑N) = F.
    { rewrite difference_union_L union_comm_L.
      by apply subseteq_union_1_L. }
    iModIntro. by iFrame "W Px".
  Qed.

  (** ** The atomic invariant type

    [Send ty] is decided with excluded middle, exactly as in the original:
    for a non-[Send] type the contents can never leave the owning thread, and
    for a [Send] one they are kept at the null pool. *)
  Definition atomic_inv_body {𝔄 ℭ} (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → proph_asn → Prop) (c: ~~ℭ)
      (tid: thread_id) : FML $oi Σ :=
    ex_fml (λ x' : ~~𝔄, ex_fml (λ d' : nat, ex_fml (λ g' : nat,
      ex_fml (λ tid' : thread_id,
        (ty.(ty_ghox) x' d' g' tid' ∗
         obs_fml (λ π, pred (syn_abstract x') c π) ∗
         pure_fml ((Send ty ∧ tid' = null_tid) ∨
                   (¬ Send ty ∧ tid = tid')))%FML)))).

  Lemma atomic_inv_body_sem {𝔄 ℭ} (ty: type 𝔄) pred (c: ~~ℭ) tid :
    bor_sem (atomic_inv_body ty pred c tid) ⊣⊢
      ∃ (x': ~~𝔄) (d' g': nat) (tid': thread_id),
        ty_gho ty x' d' g' tid' ∗ ⟨π, pred (syn_abstract x') c π⟩ ∗
        ⌜(Send ty ∧ tid' = null_tid) ∨ (¬ Send ty ∧ tid = tid')⌝.
  Proof.
    rewrite /atomic_inv_body ex_fml_sem. apply bi.exist_proper=> x'.
    rewrite ex_fml_sem. apply bi.exist_proper=> d'.
    rewrite ex_fml_sem. apply bi.exist_proper=> g'.
    rewrite ex_fml_sem. apply bi.exist_proper=> tid'.
    by rewrite !bor_sep_sem obs_fml_sem pure_fml_sem.
  Qed.
  Lemma atomic_inv_body_sem_2 {𝔄 ℭ} (ty: type 𝔄) pred (c: ~~ℭ) tid
      x' d' g' tid' :
    ty_gho ty x' d' g' tid' -∗ ⟨π, pred (syn_abstract x') c π⟩ -∗
    ⌜(Send ty ∧ tid' = null_tid) ∨ (¬ Send ty ∧ tid = tid')⌝ -∗
      bor_sem (atomic_inv_body ty pred c tid).
  Proof.
    rewrite atomic_inv_body_sem. iIntros "? ? %".
    iExists x', d', g', tid'. by iFrame.
  Qed.

  Program Definition atomic_inv_ty {𝔄 ℭ} (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → proph_asn → Prop)
      : type (invₛ ℭ) := {|
    ty_size := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho_persx x d g tid := empty_fml;
    ty_ghox x d g tid := match x with (N, γ, c) =>
      (active_fml γ ∗
       na_inv_tok_fml N (atomic_inv_body ty pred c tid ∨ active_fml γ))%FML
      end;
    ty_phys x tid := [];
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move=> *. iIntros "$". by iIntros "$". Qed.
  Next Obligation. move=> *. by iIntros "$". Qed.
  Next Obligation. move=> ?? ty pred κ [[??]?] ???? Hin. set_solver. Qed.
  Next Obligation. move=> *. iIntros "_". by iApply empty_fml_sem_2. Qed.

  Lemma atomic_inv_ty_gho {𝔄 ℭ} (ty: type 𝔄) pred N γ (c: ~~ℭ) d g tid :
    ty_gho (atomic_inv_ty ty pred) (N, γ, c) d g tid ⊣⊢
      Active γ ∗ external_na_inv γ N (atomic_inv_body ty pred c tid).
  Proof. rewrite /ty_gho /= bor_sep_sem active_fml_sem na_inv_tok_fml_sem //. Qed.

  Program Definition atomic_closer_ty {𝔄 ℭ} (κ: lft) (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → proph_asn → Prop)
      : type (invₛ ℭ) := {|
    ty_size := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho_persx x d g tid := empty_fml;
    ty_ghox x d g tid := match x with (N, γ, c) =>
      (handle_fml (↑N) ∗
       atomic_closer_fml γ N (atomic_inv_body ty pred c tid))%FML end;
    ty_phys x tid := [];
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move=> *. iIntros "$". by iIntros "$". Qed.
  Next Obligation. move=> *. by iIntros "$". Qed.
  Next Obligation. move=> ?? κ ty pred ? [[??]?] ???? Hin. set_solver. Qed.
  Next Obligation. move=> *. iIntros "_". by iApply empty_fml_sem_2. Qed.

  Lemma atomic_closer_ty_gho {𝔄 ℭ} κ (ty: type 𝔄) pred N γ (c: ~~ℭ) d g tid :
    ty_gho (atomic_closer_ty κ ty pred) (N, γ, c) d g tid ⊣⊢
      atomic_lock_handle atomic_lock_ctr_name (↑N) ∗
      atomic_closer γ N (atomic_inv_body ty pred c tid).
  Proof.
    rewrite /ty_gho /= bor_sep_sem handle_fml_sem atomic_closer_fml_sem //.
  Qed.

  Lemma atomic_inv_ty_resolve E L {𝔄 ℭ} (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → proph_asn → Prop) :
    resolve E L (atomic_inv_ty ty pred) (const (const True)).
  Proof. apply resolve_just. Qed.

  (** The body does not mention [tid] when [ty] is [Send]: the right
    disjunct of its side condition is then absurd.  The original can argue
    this up to [⊣⊢] because an Iris invariant is proper in its content; here
    the invariant holds a *formula*, so the two bodies have to be equal, and
    they are - by propositional and functional extensionality. *)
  Local Lemma atomic_inv_body_send_irrel {𝔄 ℭ} (ty: type 𝔄) pred (c: ~~ℭ)
      tid tid' :
    Send ty → atomic_inv_body ty pred c tid = atomic_inv_body ty pred c tid'.
  Proof.
    move=> Hsend. rewrite /atomic_inv_body. f_equal. fun_ext=> x'.
    f_equal. fun_ext=> d'. f_equal. fun_ext=> g'. f_equal. fun_ext=> tid''.
    do 3 f_equal. apply propositional_extensionality.
    split; move=> [?|[Hns _]]; by [left|exfalso; apply Hns].
  Qed.

  Local Lemma gho_equiv_of_send {𝔄 ℭ} (ty: type 𝔄) pred
      (x: ~~(invₛ ℭ)) d g tid tid' :
    Send ty →
    ty_gho (atomic_inv_ty ty pred) x d g tid ⊣⊢
      ty_gho (atomic_inv_ty ty pred) x d g tid'.
  Proof.
    move=> Hsend. destruct x as [[N γ] c].
    by rewrite !atomic_inv_ty_gho
      (atomic_inv_body_send_irrel ty pred c tid tid' Hsend).
  Qed.
End atomic_invariants.
