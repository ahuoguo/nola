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

  (** The formula constructors an atomic invariant's ghost assertion names *)
  Class AtomicInvFml := {
    active_fml : gname → FML $oi Σ;
    active_fml_sem γ : bor_sem (active_fml γ) ⊣⊢ Active γ;
    obs_fml : (proph_asn → Prop) → FML $oi Σ;
    obs_fml_sem φ : bor_sem (obs_fml φ) ⊣⊢ ⟨π, φ π⟩;
    na_inv_tok_fml : namespace → FML $oi Σ → FML $oi Σ;
    na_inv_tok_fml_sem N Px :
      bor_sem (na_inv_tok_fml N Px) ⊣⊢ na_inv_tok ATOMIC_POOL N Px;
    (** The original's closer is a wand over the world satisfaction, which
      cannot be a formula: it would mention [bor_sem] at *every* formula.
      Following Nola's [obor_tok] ([nola.iris.borrow]), an opened invariant
      is a token of plain ghost ownership instead. *)
    na_otok_fml : namespace → FML $oi Σ → FML $oi Σ;
    na_otok_fml_sem N Px :
      bor_sem (na_otok_fml N Px) ⊣⊢ na_otok ATOMIC_POOL N Px;
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

  (** The token for an atomic invariant this thread has opened *)
  Definition atomic_closer (γ: gname) (N: namespace) (Px : FML $oi Σ)
    : iProp Σ := na_otok ATOMIC_POOL N (Px ∨ active_fml γ)%FML.
  Definition atomic_closer_fml (γ: gname) (N: namespace) (Px : FML $oi Σ)
    : FML $oi Σ := na_otok_fml N (Px ∨ active_fml γ)%FML.
  Lemma atomic_closer_fml_sem γ N Px :
    bor_sem (atomic_closer_fml γ N Px) ⊣⊢ atomic_closer γ N Px.
  Proof. apply na_otok_fml_sem. Qed.

  (** Close an atomic invariant with its open token.  This is the original's
    closer, now a lemma rather than a stored wand. *)
  Lemma atomic_close {γ N Px F} :
    atomic_closer γ N Px -∗ (bor_sem Px ∨ Active γ) -∗
    na_own ATOMIC_POOL F =[alerus_wsat]=∗ na_own ATOMIC_POOL (F ∪ ↑N).
  Proof.
    iIntros "otok body pool W".
    iDestruct (wsat_split (W':=na_inv_wsat ATOMIC_POOL bor_sem) with "W")
      as "[Wn Wr]".
    iDestruct (na_inv_tok_close with "otok [body] pool Wn")
      as "(_ & pool & Wn)".
    { by rewrite external_na_inv_body_sem. }
    iDestruct (wsat_join (W:=alerus_wsat) with "Wn Wr") as "$".
    by iFrame "pool".
  Qed.

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
    iDestruct (na_inv_tok_open (sm:=bor_sem) (F:=(↑N:coPset))
      with "inv poolN Wn") as "(body & empty & otok & Wn)"; [done|].
    iEval (rewrite external_na_inv_body_sem) in "body".
    iDestruct "body" as "[Px|A]"; last first.
    { iDestruct (wsat_split (W':=Wguard) with "Wr") as "[Wg Wr']".
      iDestruct (guard_acc with "g G Wg") as "[A' _]".
      iDestruct (Active_2_no with "A A'") as "[]". }
    iDestruct (wsat_join (W:=alerus_wsat) with "Wn Wr") as "W".
    iModIntro. by iFrame "W pool G Px otok".
  Qed.

  Lemma external_na_inv_cancel γ N Px F :
    ↑N ⊆ F →
    external_na_inv γ N Px -∗ Active γ -∗
    na_own ATOMIC_POOL F =[alerus_wsat]=∗ bor_sem Px ∗ na_own ATOMIC_POOL F.
  Proof.
    move=> NF. iIntros "#inv A pool W".
    iMod (external_na_inv_acc_strong γ N Px F NF with "inv [] A pool W")
      as "(W & pool & A & Px & close)"; [iApply guard_refl|].
    iMod (atomic_close with "close [A] pool W") as "[W pool]"; [by iRight|].
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
    exs_fml (λ x' : ~~𝔄, ex_fml (λ d' : nat, ex_fml (λ g' : nat,
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
    rewrite /atomic_inv_body exs_fml_sem. apply bi.exist_proper=> x'.
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
  Next Obligation. move=> ?? ty pred sem Hsm *. iIntros "$". by iIntros "$". Qed.
  Next Obligation. move=> ?? ty pred sem Hsm *. by iIntros "$". Qed.
  Next Obligation. move=> ?? ty pred κ [[??]?] ???? Hin. set_solver. Qed.
  Next Obligation.
    move=> ?? ty pred sem Hsm *. rewrite (empty_sem_at Hsm). exact _.
  Qed.
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
  Next Obligation. move=> ??? ty pred sem Hsm *. iIntros "$". by iIntros "$". Qed.
  Next Obligation. move=> ??? ty pred sem Hsm *. by iIntros "$". Qed.
  Next Obligation. move=> ?? κ ty pred ? [[??]?] ???? Hin. set_solver. Qed.
  Next Obligation.
    move=> ??? ty pred sem Hsm *. rewrite (empty_sem_at Hsm). exact _.
  Qed.
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

  Lemma atomic_inv_ty_send {𝔄 ℭ} (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → proph_asn → Prop) :
    Send ty → Send (atomic_inv_ty ty pred).
  Proof.
    move=> Hsend. split; [done|]. move=> tid tid' x d g G κs.
    rewrite (gho_equiv_of_send ty pred x d g tid tid' Hsend).
    iIntros "_ _ lfts _ G gho $ !>". iExists x, 0%nat.
    rewrite Nat.add_0_r. by iFrame "lfts G gho".
  Qed.

  Lemma atomic_inv_ty_sync {𝔄 ℭ} (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → proph_asn → Prop) :
    Send ty → Sync (atomic_inv_ty ty pred).
  Proof.
    move=> Hsend tid tid' [[N γ] c] d g. split; [done|].
    rewrite /= (atomic_inv_body_send_irrel ty pred c tid tid' Hsend).
    by split=> sem Hsem.
  Qed.

  (** Releasing the global atomic lock.  Acquiring it is [GlobalAtomicLock],
    a spin loop with no total-WP proof; see [typing/programs_util_atomic.v]. *)
  Lemma typed_atomic_unlock E L Il ϝ :
    typed_inv_instr E L (InvCtx Il ϝ (AtomicOpen 0)) +[]
      GlobalAtomicUnlock (InvCtx Il ϝ AtomicClosed) (const +[]) id.
  Proof.
    move=> tid post mask iκs xl. destruct xl.
    iIntros "#LFT #PROPH #UNIQ #E L I _ Obs".
    iDestruct "I" as (na_mask at_mask) "[%Hm [I1 [I2 [Iat1 Iat2]]]]".
    iDestruct (atomic_lock_ctr_top with "Iat1") as %->.
    iApply (twp_global_atomic_unlock with "[Iat1 Iat2]"); [by iFrame|].
    iIntros "_". iExists -[], mask. iFrame "L Obs".
    iExists na_mask, ⊤. iFrame "I1 I2". iPureIntro.
    destruct Hm as [? <-]. split; set_solver.
  Qed.

  (** Moving the contents into the pool the invariant keeps them in.  The
    original takes [£(d+1)] and a time receipt to strip the [▷] on the
    contents; here there is none. *)
  Local Lemma change_tid_in {𝔄} (ty : type 𝔄) x d g tid κs (G : iProp Σ) :
    ⊢ llft_ctx -∗ uniq_ctx -∗ ty_gho ty x d g tid -∗
      (∀ κ, ⌜κ ∈ κs⌝ -∗ (G &&{Wguard}&&> llft_alive κ)) -∗ G -∗
      cna_lifetimes tid κs =[alerus_wsat]{NalerusE}=∗
      ∃ tid' x' d',
        ⌜(Send ty ∧ tid' = null_tid) ∨ (¬ Send ty ∧ tid = tid')⌝ ∗
        ty_gho ty x' d' g tid' ∗ ⌜syn_abstract x' = syn_abstract x⌝ ∗
        G ∗ cna_lifetimes tid κs.
  Proof.
    destruct (classic (Send ty)) as [Hsend|Hns].
    - iIntros "LFT UNIQ gho #gs G lfts W".
      iDestruct (wsat_split (W':=alerus_wsat_core) with "W") as "[Wc Ws]".
      iMod (@send_change_tid _ _ _ _ ty Hsend tid null_tid x d g G κs
        with "LFT UNIQ lfts gs G gho Wc")
        as "(Wc & %x' & %off & gho & %Habs & lfts & G)".
      iDestruct (wsat_join (W:=alerus_wsat) with "Wc Ws") as "$".
      iModIntro. iExists null_tid, x', (d + off). iFrame "gho G lfts".
      iSplit; [|done]. iPureIntro. by left.
    - iIntros "LFT UNIQ gho _ G lfts $ !>". iExists tid, x, d.
      iFrame "gho G lfts". iSplit; [|done]. iPureIntro. by right.
  Qed.

  (** Moving the contents back out.  The null pool's [cna_lifetimes] is
    [send_wsat], which sits outside [alerus_wsat_core] precisely so that it
    can be taken out here while [Send] runs. *)
  Local Lemma change_tid_out {𝔄} (ty : type 𝔄) x d g tid tid' :
    ((Send ty ∧ tid' = null_tid) ∨ (¬ Send ty ∧ tid = tid')) →
    ⊢ llft_ctx -∗ uniq_ctx -∗ ty_gho ty x d g tid'
      =[alerus_wsat]{NalerusE}=∗
      ∃ x' d', ty_gho ty x' d' g tid ∗ ⌜syn_abstract x' = syn_abstract x⌝.
  Proof.
    move=> [[Hsend ->]|[_ <-]]; last first.
    { iIntros "_ _ gho $ !>". iExists x, d. by iFrame "gho". }
    iIntros "LFT UNIQ gho W".
    iDestruct (wsat_split (W':=send_wsat) with "W") as "[lfts Wc]".
    iMod (@send_change_tid _ _ _ _ ty Hsend null_tid tid x d g True ∅
      with "LFT UNIQ lfts [] [//] gho Wc")
      as "(Wc & %x' & %off & gho & %Habs & lfts & _)".
    { iIntros (κ) "%Hin". exfalso. by apply (gmultiset_not_elem_of_empty κ). }
    iDestruct (wsat_join (W:=alerus_wsat) with "lfts Wc") as "$".
    iModIntro. iExists x', (d + off). by iFrame "gho".
  Qed.

  Local Lemma mask_lemma (na_mask at_mask X : coPset) :
    na_mask ∪ at_mask = ⊤ → X ⊆ na_mask ∩ at_mask →
    na_mask ∪ (at_mask ∖ X) = ⊤.
  Proof.
    move=> eq sub. apply leibniz_equiv, set_equiv_subseteq. split=>//.
    rewrite -eq. etrans; [|by apply union_mono_l, difference_mono_l].
    move=> a /elem_of_union[?|?]; [set_solver|].
    case (decide (a ∈ na_mask)); set_solver.
  Qed.

  Lemma typed_atomic_inv_alloc {𝔄 ℭ} (p1 p2 : path) (ty : type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → proph_asn → Prop)
      (tyCN : type (ℭ * namespaceₛ)) E L I :
    lctx_ictx_alive E L I →
    typed_inv_instr E L I
      +[p1 ◁ own_ptr 0 (ghost_ty tyCN); p2 ◁ own_ptr 0 ty]
      (Seq Skip Skip) I
      (const +[p2 ◁ own_ptr 0 (atomic_inv_ty ty pred)])
      (λ post '-[(_, (c, N)); (_, v)], λ mask π,
        pred (syn_abstract v) c π ∧ ∀ l γ, post -[(l, (N, γ, c))] mask π).
  Proof.
    move=> IAlv. apply typed_instr_of_skip_own2_own; [done|done|].
    move=> l1 l2 x1 x2 d tid post mask iκs.
    iIntros "#LFT #PROPH #UNIQ #E L I _ Tra #Obs W".
    destruct I as [Il ϝ 𝛼]. destruct x1 as [c ns].
    iDestruct "I" as (na_mask at_mask) "[%Hm [[cna_lfts #ϝincl] Irest]]".
    iDestruct (lctx_ictx_alive_all_guards E L Il ϝ 𝛼 iκs IAlv
      with "L E ϝincl") as "#AllGuards".
    iDestruct (change_tid_in ty x2 d (S d) tid _ (llctx_interp L)
      with "LFT UNIQ Tra AllGuards L cna_lfts") as "A".
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "A") as "A'";
      [set_solver|].
    iMod ("A'" with "W")
      as "[W (%tid' & %x' & %d' & %TidsEq & gho' & %Habs & L & cna_lfts)]".
    iMod (external_na_inv_alloc ns (atomic_inv_body ty pred c tid)
      with "[gho'] W") as "[W (%γ & #inv & active)]".
    { iApply (atomic_inv_body_sem_2 with "gho' [] []").
      - iApply (proph_obs_impl with "Obs")=> π [Ha _]. by rewrite Habs.
      - iPureIntro. exact TidsEq. }
    iModIntro. iFrame "W L". iExists (ns, γ, c).
    iSplitL "cna_lfts Irest".
    { iExists na_mask, at_mask. by iFrame "cna_lfts ϝincl Irest". }
    rewrite atomic_inv_ty_gho. iFrame "active inv".
    iApply (proph_obs_impl with "Obs")=> ? [_ Ha]. apply Ha.
  Qed.

  Lemma typed_atomic_inv_destroy {𝔄 ℭ} (p : path) (ty : type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → proph_asn → Prop) E L Il ϝ n :
    typed_inv_instr E L (InvCtx Il ϝ (AtomicOpen n))
      +[p ◁ own_ptr 0 (atomic_inv_ty ty pred)] (Seq Skip Skip)
      (InvCtx Il ϝ (AtomicOpen n))
      (const +[p ◁ own_ptr 0 (tracked_ty ty)])
      (λ post '-[(_, (N, γ, c))], λ mask π,
        ↑N ⊆ mask ∧ ∀ l v, pred (syn_abstract v) c π → post -[(l, v)] mask π).
  Proof.
    apply typed_atomic_instr_own_own_t; [done|done|].
    move=> l [[ns γ] c] d tid post mask na_mask at_mask iκs Hm1 Hm2.
    iIntros "#LFT #PROPH #UNIQ #E L [ctr pool] cna_lfts #fincl gho #Obs W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [Hsub _]]; [solve_ndisj|].
    rewrite atomic_inv_ty_gho. iDestruct "gho" as "[active #inv]".
    iMod (external_na_inv_cancel γ ns _ at_mask with "inv active pool W")
      as "(W & P & pool)"; [set_solver|].
    rewrite atomic_inv_body_sem.
    iDestruct "P" as (x'' d' g' tid') "(gho & #Hpred & %Htids)".
    iDestruct (change_tid_out ty x'' d' g' tid tid' Htids with "LFT UNIQ gho")
      as "A".
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "A") as "A'";
      [set_solver|].
    iMod ("A'" with "W") as "[W (%x' & %d0 & gho & %Habs)]".
    iModIntro. iFrame "W". iExists (d0 `max` g'), x', mask, at_mask.
    iFrame "L ctr pool cna_lfts". iSplit; [done|].
    rewrite tracked_ty_gho. iSplitL "gho".
    { iDestruct (ty_gho_depth_mono with "gho") as "[$ _]"; lia. }
    iCombine "Obs Hpred" as "#Obs2".
    iApply (proph_obs_impl with "Obs2")=> π [[_ Ha] Hp]. apply Ha.
    by rewrite Habs.
  Qed.

  Lemma typed_atomic_inv_open {𝔄 ℭ} (p : path) (ty : type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → proph_asn → Prop) E L Il ϝ n κ :
    lctx_lft_alive E L κ →
    lctx_ictx_alive E L (InvCtx Il ϝ (AtomicOpen n)) →
    typed_inv_instr E L (InvCtx Il ϝ (AtomicOpen n))
      +[p ◁ own_ptr 0 (tracked_ty (&shr{κ} (atomic_inv_ty ty pred)))]
      (Seq Skip Skip) (InvCtx Il ϝ (AtomicOpen (n+1)))
      (const +[p ◁ own_ptr 0 (tracked_ty ty * atomic_closer_ty κ ty pred)])
      (λ post '-[(_, (_, (N, γ, c)))], λ mask π,
        ↑N ⊆ mask ∧ ∀ l v, pred (syn_abstract v) c π →
          post -[(l, (v, (N, γ, c)))] (mask ∖ ↑N) π).
  Proof.
    move=> Halive HaliveI. apply typed_atomic_instr_own_own_t; [done|done|].
    move=> l [l1 [[ns γ] c]] d tid post mask na_mask at_mask iκs Hm1 Hm2.
    iIntros "#LFT #PROPH #UNIQ #E L [ctr pool] cna_lfts #fincl shrgho #Obs W".
    rewrite tracked_ty_gho.
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "shrgho") as "[]"|].
    rewrite shr_bor_gho /=. iDestruct "shrgho" as "#(_ & KguardsGho & _)".
    iDestruct (Halive with "L E") as "#LguardsK".
    iDestruct (dguard_rhs_sep_l with "KguardsGho") as "#KguardsActive0".
    iDestruct (dguard_rhs_sep_r with "KguardsGho") as "#KguardsInv0".
    iDestruct (dguard_alive_sem' (active_fml_sem _) with "KguardsActive0")
      as "#KguardsActive".
    iDestruct (dguard_alive_sem' (na_inv_tok_fml_sem _ _) with "KguardsInv0")
      as "#KguardsInv".
    iDestruct (guard_trans with "LguardsK KguardsInv") as "#LguardsInv".
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "LguardsInv L Wg") as "[#inv back]".
    iDestruct ("back" with "inv") as "[Wg L]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [Hsub _]]; [solve_ndisj|].
    iMod (external_na_inv_acc_strong γ ns _ at_mask
      with "inv [] L pool W") as "(W & pool & L & P & closer)";
      [set_solver|iApply (guard_trans with "LguardsK KguardsActive")|].
    rewrite atomic_inv_body_sem.
    iDestruct "P" as (x'' d' g' tid') "(gho & #Hpred & %Htids)".
    iDestruct (change_tid_out ty x'' d' g' tid tid' Htids with "LFT UNIQ gho")
      as "A".
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "A") as "A'";
      [set_solver|].
    iMod ("A'" with "W") as "[W (%x' & %d0 & gho & %Habs)]".
    iDestruct (atomic_lock_ctr_inc _ _ _ (↑ns) with "ctr") as "[ctr handle]";
      [set_solver|].
    iModIntro. iFrame "W".
    iExists (d0 `max` g'), (x', (ns, γ, c)), (mask ∖ ↑ns), (at_mask ∖ ↑ns).
    iFrame "L ctr pool cna_lfts".
    iSplit.
    { iPureIntro. split; [apply mask_lemma; set_solver|set_solver]. }
    rewrite prod_ty_gho /= tracked_ty_gho atomic_closer_ty_gho.
    iSplitL "gho handle closer".
    { iSplitL "gho".
      - iDestruct (ty_gho_depth_mono with "gho") as "[$ _]"; lia.
      - iFrame "handle closer". }
    iCombine "Obs Hpred" as "#Obs2".
    iApply (proph_obs_impl with "Obs2")=> π [[_ Ha] Hp]. apply Ha.
    by rewrite Habs.
  Qed.

  Lemma typed_atomic_inv_close {𝔄 ℭ} (p1 p2 : path) (ty : type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → proph_asn → Prop) E L Il ϝ n κ :
    lctx_ictx_alive E L (InvCtx Il ϝ (AtomicOpen (n+1))) →
    typed_inv_instr E L (InvCtx Il ϝ (AtomicOpen (n+1)))
      +[p2 ◁ own_ptr 0 (tracked_ty ty);
        p1 ◁ own_ptr 0 (tracked_ty (atomic_closer_ty κ ty pred))]
      (Seq Skip Skip) (InvCtx Il ϝ (AtomicOpen n)) (const +[])
      (λ post '-[(_, v); (_, (N, γ, c))], λ mask π,
        pred (syn_abstract v) c π ∧ post -[] (mask ∪ ↑N) π).
  Proof.
    move=> IAlv. apply typed_atomic_instr_own2_emp.
    move=> l1 l2 v [[ns γ] c] d tid post mask na_mask at_mask iκs Hm1 Hm2.
    iIntros "#LFT #PROPH #UNIQ #E L [ctr pool] cna_lfts #fincl gho1 gho2
      #Obs W".
    iMod (proph_obs_sat with "PROPH Obs") as %[π0 [Hpred _]]; [solve_ndisj|].
    rewrite !tracked_ty_gho atomic_closer_ty_gho.
    iDestruct "gho2" as "[handle closer]".
    iDestruct (lctx_ictx_alive_all_guards E L Il ϝ (AtomicOpen (n+1)) iκs
      IAlv with "L E fincl") as "#AllGuards".
    iDestruct (change_tid_in ty v d (S d) tid _ (llctx_interp L)
      with "LFT UNIQ gho1 AllGuards L cna_lfts") as "A".
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "A") as "A'";
      [set_solver|].
    iMod ("A'" with "W")
      as "[W (%tid' & %x' & %d' & %TidsEq & gho' & %Habs & L & cna_lfts)]".
    iMod (atomic_close with "closer [gho'] pool W") as "[W pool]".
    { iLeft. iApply (atomic_inv_body_sem_2 with "gho' [] []").
      - iApply (proph_obs_impl with "Obs")=> π [Ha _]. by rewrite Habs.
      - iPureIntro. exact TidsEq. }
    iDestruct (atomic_lock_ctr_handle_disjoint with "ctr handle") as %disj.
    iDestruct (atomic_lock_ctr_dec _ n with "ctr handle") as "ctr".
    iModIntro. iFrame "W". iExists (mask ∪ ↑ns), (at_mask ∪ ↑ns).
    iFrame "L ctr pool cna_lfts".
    iSplit; [iPureIntro; split; set_solver|].
    iApply (proph_obs_impl with "Obs")=> ? [_ Ha]. apply Ha.
  Qed.
End atomic_invariants.

Global Hint Resolve atomic_inv_ty_resolve : lrust_typing.
