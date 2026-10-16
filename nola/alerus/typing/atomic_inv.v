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
From Stdlib.Logic Require Import Classical_Prop.
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
End atomic_invariants.
