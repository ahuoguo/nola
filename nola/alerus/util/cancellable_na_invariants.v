(** * Cancellable non-atomic invariants tied to lifetimes, later-free

  Ported from VerusBelt ([util/cancellable_na_invariants.v] together with its
  wrapper [util/cancellable.v], MIT, Hance, Elbeheiry, Matsushita, Dreyer),
  itself a fork of Iris's [base_logic/lib/na_invariants.v].

  An invariant here is in one of three states: *cancelled* (its [Active] token
  has been handed back inside), *closed* (it holds its content), or *open*
  (a thread holds the content, and the invariant records the lifetime κ whose
  liveness guards the [Active] token, so that nobody can cancel it meanwhile).

  Three things change against the original.

  - The Iris invariant [inv nainvN (…)] becomes a *simple* invariant
    ([nola.iris.sinv]) whose world satisfaction is threaded explicitly, so
    opening yields [sm Px] with no later and no namespace mask.
  - The guard index [;d] and the matching [£(d+1)] disappear:
    [guarded_active] no longer carries a credit, and [na_inv_acc] /
    [na_inv_destroy] no longer take one.  In the original those credits exist
    only to strip the laters [guards_open_later] introduces when the guard is
    used to rule out the cancelled state.
  - Leaf's side condition [↑N ## F] - the guarded mask must be disjoint from
    the invariant's - becomes [WsatIncl W (cna_wsat WG sm ∗ WG) Wr]: the guard
    is taken over [WG], which is *separate* from the world satisfaction holding
    the invariants.  That separation is what lets the guard be opened while the
    invariant is open.  It also means [cna_wsat] must not be part of [WG]:
    [WG] is the lifetime logic's [llft_wsatG], and [cna_wsat] sits beside
    [llft_wsat] in the global world satisfaction.

  The naming follows [util/cancellable.v]'s [cna_] wrappers throughout, so that
  nothing clashes with Iris's own [na_invariants] (which
  [nola.alerus.na_inv_fork] reuses for the atomic pool). *)

From nola.bi Require Export guard modw.
From nola.iris Require Export sinv iprop.
From nola.alerus.lifetime Require Export lifetime_full.
From iris.algebra Require Import gset coPset dfrac_agree auth gmultiset excl.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
Import GuardNotation ModwNotation iPropAppNotation.

(** A pool name packs the pool's token name and its lifetime-multiset name *)
Definition cna_pool_name := gname.

(** The data a simple invariant stores: the [Active] name, the pool, and the
  content formula.  The pair of names cannot be recovered from the invariant's
  index, so it is stored alongside the formula - hence the product functor. *)
Notation cnaOF FML := (prodOF (constOF (leibnizO (gname * gname))) FML).

Class cnaGS (FML : oFunctor) Σ : Type := CnaGS {
  #[global] cna_tokG :: inG Σ (prodR coPset_disjR (gset_disjR positive));
  #[global] cna_exclG :: inG Σ (exclR unitO);
  #[global] cna_multisetG :: inG Σ (authR (gmultisetUR lft));
  #[global] cna_lftG :: inG Σ (dfrac_agreeR (leibnizO (option lft)));
  #[global] cna_sinvG :: sinvGpreS (cnaOF FML) Σ;
  cna_name : gname;
}.

Definition cnaΣ FML `{!oFunctorContractive FML} : gFunctors :=
  #[ GFunctor (constRF (prodR coPset_disjR (gset_disjR positive)));
     GFunctor (constRF (exclR unitO));
     GFunctor (constRF (authR (gmultisetUR lft)));
     GFunctor (constRF (dfrac_agreeR (leibnizO (option lft))));
     sinvΣ (cnaOF FML) ].

Section cna.
  #[local] Set Default Proof Using "All".
  Context {Σ : gFunctors} {FML : oFunctor}.
  Context `{!cnaGS FML Σ, !llft_logicGS Σ}.

  (** The simple-invariant family holding the invariants.  As in
    [nola.alerus.lifetime.lifetime_full], this is a plain definition rather
    than a [Context] of class type, so that it does not silently become the
    instance for some other [sinvGS]. *)
  Definition cna_sinvGS : sinvGS (cnaOF FML) Σ :=
    SinvGS (cnaOF FML) Σ cna_sinvG cna_name.
  Local Notation sinv_tok' := (sinv_tok (sinvGS0:=cna_sinvGS)).
  Local Notation sinv_wsat' := (sinv_wsat (sinvGS0:=cna_sinvGS)).

  Implicit Type (p : cna_pool_name) (γ : gname) (i : positive)
    (Px : FML $oi Σ) (sm : FML $oi Σ → iProp Σ) (κ : lft)
    (κs : gmultiset lft) (W WG : iProp Σ).

  (** ** Name packing, as in the original *)
  Local Definition γf1 (γ : gname) : gname :=
    match prod_decode_fst γ with Some x => x | _ => γ end.
  Local Definition γf2 (γ : gname) : gname :=
    match prod_decode_snd γ with Some x => x | _ => γ end.
  Local Definition γa := γf1.  (* [Active] tokens *)
  Local Definition γk := γf2.  (* lifetime agreement tokens *)
  Local Definition γp := γf1.  (* pool tokens *)
  Local Definition γm := γf2.  (* lifetime multiset tokens *)

  (** ** The lifetime multiset owned by a pool *)
  Definition cna_lifetimes p κs : iProp Σ := own (γm p) (● κs).
  Local Definition cna_lft_single p κ : iProp Σ := own (γm p) (◯ {[+ κ +]}).

  Local Lemma cna_lfts_elem_of {p κ κs} :
    cna_lifetimes p κs -∗ cna_lft_single p κ -∗ ⌜κ ∈ κs⌝.
  Proof.
    iIntros "● ◯". iCombine "● ◯" as "●◯".
    iDestruct (own_valid with "●◯") as %[?%gmultiset_included _]
      %auth_both_valid_discrete.
    iPureIntro. multiset_solver.
  Qed.
  Local Lemma cna_lfts_insert {p κ κs} :
    cna_lifetimes p κs ==∗ cna_lifetimes p ({[+ κ +]} ⊎ κs) ∗ cna_lft_single p κ.
  Proof.
    iIntros "●". iMod (own_update with "●") as "[$$]"; [|done].
    apply (auth_update_alloc _ ({[+ κ +]} ⊎ κs) {[+ κ +]}).
    apply gmultiset_local_update. multiset_solver.
  Qed.
  Local Lemma cna_lfts_delete {p κ κs} :
    cna_lifetimes p κs -∗ cna_lft_single p κ ==∗ ∃ κs',
      cna_lifetimes p κs' ∗ ⌜κs = {[+ κ +]} ⊎ κs'⌝.
  Proof.
    iIntros "● ◯". iCombine "● ◯" as "●◯".
    iDestruct (own_valid with "●◯") as %[in' _]%auth_both_valid_discrete.
    move: in'=> /gmultiset_included in'.
    iMod (own_update with "●◯") as "●".
    { apply (auth_update_dealloc _ _ (κs ∖ {[+ κ +]})).
      apply gmultiset_local_update. multiset_solver. }
    iModIntro. iExists (κs ∖ {[+ κ +]}). iFrame "●". iPureIntro.
    multiset_solver.
  Qed.
  Local Lemma cna_lifetimes_alloc : ⊢ |==> ∃ γ, own (A:=authR (gmultisetUR lft))
    γ (● ∅).
  Proof. iApply own_alloc. by apply auth_auth_valid. Qed.

  (** ** The half-tokens recording which lifetime an open invariant uses *)
  Local Definition lft_tok γ (o : option lft) : iProp Σ :=
    own γ (to_frac_agree (A:=leibnizO (option lft)) (1/2)%Qp o).

  Local Lemma lft_tok_alloc {o} : ⊢ |==> ∃ γ, lft_tok γ o ∗ lft_tok γ o.
  Proof.
    rewrite /lft_tok. iMod (own_alloc
      (to_frac_agree (A:=leibnizO (option lft)) (1/2) o ⋅
       to_frac_agree (A:=leibnizO (option lft)) (1/2) o)) as (γ) "[??]".
    { rewrite frac_agree_op_valid Qp.half_half. done. }
    iModIntro. iExists γ. iFrame.
  Qed.
  Local Lemma lft_tok_agree {γ o o'} :
    lft_tok γ o -∗ lft_tok γ o' -∗ ⌜o = o'⌝.
  Proof.
    rewrite /lft_tok. iIntros "a b". iCombine "a b" as "ab".
    iDestruct (own_valid with "ab") as %v. iPureIntro.
    rewrite dfrac_agree_op_valid in v. apply v.
  Qed.
  Local Lemma lft_tok_update {γ o o' o''} :
    lft_tok γ o -∗ lft_tok γ o' ==∗ lft_tok γ o'' ∗ lft_tok γ o''.
  Proof.
    rewrite /lft_tok. iIntros "a b". iCombine "a b" as "ab". rewrite -own_op.
    iMod (own_update with "ab") as "$"; [|done].
    apply frac_agree_update_2, Qp.half_half.
  Qed.

  (** ** The cancellation token *)
  Definition cna_active γ : iProp Σ := own (γa γ) (Excl ()).

  Local Lemma cna_active_alloc : ⊢ |==> ∃ γ, own γ (Excl ()).
  Proof. by iApply own_alloc. Qed.
  Local Lemma cna_active_2_no {γ} :
    cna_active γ -∗ cna_active γ -∗ False.
  Proof.
    iIntros "a b". iCombine "a b" as "ab".
    by iDestruct (own_valid with "ab") as %[].
  Qed.

  (** ** Pool tokens *)
  Definition cna_own p (E : coPset) : iProp Σ := own (γp p) (CoPset E, GSet ∅).
  Local Definition cna_lock p i : iProp Σ := own (γp p) (ε, GSet {[i]}).

  #[export] Instance cna_own_timeless {p E} : Timeless (cna_own p E).
  Proof. rewrite /cna_own. exact _. Qed.
  #[export] Instance cna_own_empty_persistent {p} : Persistent (cna_own p ∅).
  Proof. rewrite /cna_own. exact _. Qed.

  Lemma cna_own_disjoint p E1 E2 :
    cna_own p E1 -∗ cna_own p E2 -∗ ⌜E1 ## E2⌝.
  Proof.
    iApply bi.wand_intro_r.
    rewrite /cna_own -own_op own_valid -coPset_disj_valid_op. by iIntros ([? _]).
  Qed.
  Lemma cna_own_union p E1 E2 :
    E1 ## E2 → cna_own p (E1 ∪ E2) ⊣⊢ cna_own p E1 ∗ cna_own p E2.
  Proof.
    move=> ?. rewrite /cna_own -own_op -pair_op. by rewrite coPset_disj_union.
  Qed.
  Lemma cna_own_union2 p E1 E2 :
    cna_own p E1 -∗ cna_own p E2 -∗ cna_own p (E1 ∪ E2).
  Proof.
    iIntros "a b". iDestruct (cna_own_disjoint with "a b") as %?.
    rewrite cna_own_union //. iFrame.
  Qed.
  Lemma cna_own_acc E2 E1 p :
    E2 ⊆ E1 → cna_own p E1 -∗ cna_own p E2 ∗ (cna_own p E2 -∗ cna_own p E1).
  Proof.
    move=> sub. have ->: E1 = E2 ∪ (E1 ∖ E2) by exact: union_difference_L.
    rewrite cna_own_union; [|set_solver]. iIntros "[$$]". auto.
  Qed.
  Lemma cna_own_empty p : ⊢ |==> cna_own p ∅.
  Proof. apply: own_unit. Qed.

  (** ** The invariant itself *)

  (** The record kept while an invariant is open: the lifetime κ whose
    liveness guards the cancellation token.  The original also carried
    [£(d+1)] here, to pay for the laters of a guard at index [d]. *)
  Definition cna_guarded_active WG γ p : iProp Σ :=
    ∃ κ, (llft_alive κ &&{WG}&&> cna_active γ) ∗ cna_lft_single p κ ∗
      lft_tok (γk γ) (Some κ).

  (** The three states *)
  Definition cna_body WG sm i (x : (gname * gname) * (FML $oi Σ)) : iProp Σ :=
      (cna_active x.1.1 ∗ lft_tok (γk x.1.1) None ∗ lft_tok (γk x.1.1) None)
    ∨ (sm x.2 ∗ cna_lock x.1.2 i ∗
        lft_tok (γk x.1.1) None ∗ lft_tok (γk x.1.1) None)
    ∨ (cna_own x.1.2 {[i]} ∗ cna_guarded_active WG x.1.1 x.1.2).

  (** World satisfaction for cancellable non-atomic invariants *)
  Definition cna_wsat WG sm : iProp Σ := sinv_wsat' (cna_body WG sm).

  (** The token for a cancellable non-atomic invariant *)
  Definition cna_inv γ p (N : namespace) Px : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ sinv_tok' i ((γ, p), Px).

  #[export] Instance cna_inv_persistent {γ p N Px} :
    Persistent (cna_inv γ p N Px).
  Proof. exact _. Qed.
  #[export] Instance cna_inv_ne {γ p N} : NonExpansive (cna_inv γ p N).
  Proof.
    move=> n Px Qx eq. rewrite /cna_inv. do 3 f_equiv.
    apply sinv_tok_ne. by split.
  Qed.
  #[export] Instance cna_inv_proper {γ p N} :
    Proper ((≡) ==> (⊣⊢)) (cna_inv γ p N).
  Proof. apply ne_proper, _. Qed.

  (** ** Accessing the pool *)
  Lemma cna_own_subset {p E F} : F ⊆ E →
    cna_own p E ⊣⊢ cna_own p F ∗ cna_own p (E ∖ F).
  Proof.
    move=> ?. rewrite {1}(union_difference_L F E); [|done].
    by rewrite cna_own_union; [|set_solver].
  Qed.
  Lemma cna_own_in {p i E} : i ∈ E →
    cna_own p E ⊣⊢ cna_own p {[i]} ∗ cna_own p (E ∖ {[i]}).
  Proof. move=> ?. apply cna_own_subset. set_solver. Qed.

  (** Directed forms, for [iDestruct]: rewriting an [⊣⊢] inside the Iris
    context trips over the [Proper] search for [envs]. *)
  Lemma cna_own_split {p E F} : F ⊆ E →
    cna_own p E -∗ cna_own p F ∗ cna_own p (E ∖ F).
  Proof. move=> sub. rewrite (cna_own_subset (p:=p) sub). by iIntros "$". Qed.
  Lemma cna_own_split_in {p i E} : i ∈ E →
    cna_own p E -∗ cna_own p {[i]} ∗ cna_own p (E ∖ {[i]}).
  Proof. move=> inE. rewrite (cna_own_in (p:=p) inE). by iIntros "$". Qed.

  Local Lemma cna_lock_2_no {p i} : cna_lock p i -∗ cna_lock p i -∗ False.
  Proof.
    iIntros "l l'". iCombine "l l'" gives %[_ val%gset_disj_valid_op].
    set_solver.
  Qed.

  (** Allocate a lock with an index fresh both for [N] and for a given set *)
  Local Lemma cna_lock_alloc p N (I : gset positive) :
    ⊢ |==> ∃ i, ⌜i ∈ (↑N:coPset) ∧ i ∉ I⌝ ∧ cna_lock p i.
  Proof.
    iMod (own_unit (prodUR coPset_disjUR (gset_disjUR positive)) (γp p))
      as "ε".
    iMod (own_updateP with "ε") as ([m1 m2]) "[%cond l]".
    { apply prod_updateP'.
      - apply cmra_updateP_id, (reflexivity (R:=eq)).
      - apply (gset_disj_alloc_empty_updateP_strong'
          (λ i, i ∈ (↑N:coPset) ∧ i ∉ I))=> E.
        destruct (fresh_inv_name (E ∪ I) N) as [i [??]].
        exists i. set_solver. }
    move: cond=>/=[<-[i[->?]]]. iModIntro. iExists i. by iSplit.
  Qed.

  (** ** Allocation *)

  (** Allocate a pool *)
  Lemma cna_pool_alloc : ⊢ |==> ∃ p, cna_own p ⊤ ∗ cna_lifetimes p ∅.
  Proof.
    iMod (own_alloc (CoPset ⊤, GSet ∅)) as (γ1) "a"; [done|].
    iMod cna_lifetimes_alloc as (γ2) "b". iModIntro.
    iExists (prod_encode γ1 γ2).
    rewrite /cna_own /cna_lifetimes /γp /γm /γf1 /γf2.
    repeat (rewrite prod_decode_encode_fst || rewrite prod_decode_encode_snd).
    iFrame.
  Qed.

  (** Allocate a cancellable non-atomic invariant.

    The original takes [▷ P] and goes through [inv_alloc]; here the content is
    a formula handed to the world satisfaction, with no later. *)
  Lemma cna_alloc {WG sm} p N Px :
    sm Px =[cna_wsat WG sm]=∗ ∃ γ, cna_inv γ p N Px ∗ cna_active γ.
  Proof.
    rewrite /cna_wsat. iIntros "Px W".
    iMod cna_active_alloc as (γ1) "Active".
    iMod (lft_tok_alloc (o:=None)) as (γ2) "[tok1 tok2]".
    set γ := prod_encode γ1 γ2.
    iAssert (cna_active γ ∗ lft_tok (γk γ) None ∗ lft_tok (γk γ) None)%I
      with "[Active tok1 tok2]" as "(Active & tok1 & tok2)".
    { rewrite /cna_active /γa /γk /γf1 /γf2 /γ.
      repeat (rewrite prod_decode_encode_fst || rewrite prod_decode_encode_snd).
      iFrame. }
    iDestruct (sinv_tok_alloc_suspend (sinvGS0:=cna_sinvGS)
      ((γ, p), Px) with "W") as (I) "→".
    iMod (cna_lock_alloc p N I) as (i [??]) "lock".
    iMod ("→" $! i with "[//]") as "[#tok →W]". iModIntro.
    iSplitL "Px lock tok1 tok2 →W".
    { iApply "→W". rewrite /cna_body /=. iRight. iLeft. iFrame. }
    iExists γ. iFrame "Active". iExists i. by iSplit.
  Qed.

  (** ** Opening, closing and cancelling *)

  (** Split and rejoin the ambient world satisfaction.  Done through lemmas
    rather than [rewrite], since rewriting an [⊣⊢] inside the Iris context
    trips over the [Proper] search for [envs]. *)
  Local Lemma cna_wsat_split {W WG sm Wr}
    `{!WsatIncl W (cna_wsat WG sm ∗ WG) Wr} : W ⊢ cna_wsat WG sm ∗ WG ∗ Wr.
  Proof.
    rewrite (wsat_incl W (cna_wsat WG sm ∗ WG) Wr). by iIntros "[[$$]$]".
  Qed.
  Local Lemma cna_wsat_join {W WG sm Wr}
    `{!WsatIncl W (cna_wsat WG sm ∗ WG) Wr} :
    cna_wsat WG sm -∗ WG -∗ Wr -∗ W.
  Proof.
    rewrite (wsat_incl W (cna_wsat WG sm ∗ WG) Wr). by iIntros "$$$".
  Qed.

  (** What [cna_inv_acc] hands back.  It captures the lock, the part of the
    pool outside [i], and the half token recording [κ]. *)
  Definition cna_closer W κ p N sm Px : iProp Σ :=
    ∀ F' κs', sm Px -∗ cna_own p F' -∗ cna_lifetimes p κs' =[W]=∗
      ∃ κs'', ⌜κs' = {[+ κ +]} ⊎ κs'' ∧ F' ## ↑N⌝ ∗
        cna_own p (F' ∪ ↑N) ∗ cna_lifetimes p κs''.

  (** Open a cancellable non-atomic invariant.

    The original needs [£(d+1)] and guards at index [d]; here the guard on [G]
    is used, with no credit, only to rule out the cancelled state - which is
    possible because it is taken over [WG], separate from [cna_wsat]. *)
  Lemma cna_inv_acc `{!WsatIncl W (cna_wsat WG sm ∗ WG) Wr}
      {γ p N Px κs κ G F} :
    ↑N ⊆ F →
    cna_inv γ p N Px -∗ cna_own p F -∗ cna_lifetimes p κs -∗
    (G &&{WG}&&> cna_active γ) -∗ (llft_alive κ &&{WG}&&> cna_active γ) -∗
    G =[W]=∗
      sm Px ∗ G ∗ cna_own p (F ∖ ↑N) ∗ cna_lifetimes p ({[+ κ +]} ⊎ κs) ∗
      cna_closer W κ p N sm Px.
  Proof.
    move=> NF. iIntros "[%i[%iN #tok]] F κs #g1 #g2 G W".
    iDestruct (cna_wsat_split with "W") as "(Wc & Wg & Wr)".
    iDestruct (cna_own_split NF with "F") as "[FN Frest]".
    iDestruct (cna_own_split_in iN with "FN") as "[Fi Fj]".
    iDestruct (sinv_tok_acc (sinvGS0:=cna_sinvGS) with "tok Wc")
      as "[body →Wc]". rewrite {1}/cna_body /=.
    iDestruct "body" as "[(Active & t1 & t2)|[(Px & lock & t1 & t2)|(Fi' & ga)]]".
    - iDestruct (guard_acc with "g1 G Wg") as "[Active2 _]".
      iDestruct (cna_active_2_no with "Active Active2") as "[]".
    - iMod (cna_lfts_insert (κ:=κ) with "κs") as "[κs single]".
      iMod (lft_tok_update (o'':=Some κ) with "t1 t2") as "[t1 t2]".
      iDestruct ("→Wc" with "[Fi single t1]") as "Wc".
      { rewrite /cna_body /=. iRight. iRight. iFrame "Fi". iExists κ.
        iFrame "g2 single t1". }
      iDestruct (cna_wsat_join (W:=W) with "Wc Wg Wr") as "$". iModIntro.
      iFrame "Px G Frest κs". iIntros (F' κs') "Px F' κs' W".
      iDestruct (cna_wsat_split with "W") as "(Wc & Wg & Wr)".
      iDestruct (sinv_tok_acc (sinvGS0:=cna_sinvGS) with "tok Wc")
        as "[body →Wc]". rewrite {1}/cna_body /=.
      iDestruct "body"
        as "[(_ & t1' & _)|[(_ & _ & t1' & _)|(Fi & [%κ' (_ & single & t1')])]]".
      + by iDestruct (lft_tok_agree with "t2 t1'") as %?.
      + by iDestruct (lft_tok_agree with "t2 t1'") as %?.
      + iDestruct (lft_tok_agree with "t2 t1'") as %eq. inversion eq. subst κ'.
        iMod (lft_tok_update (o'':=None) with "t1' t2") as "[t1 t2]".
        iDestruct ("→Wc" with "[Px lock t1 t2]") as "Wc".
        { rewrite /cna_body /=. iRight. iLeft. iFrame. }
        iMod (cna_lfts_delete with "κs' single") as (κs'') "[κs' %eqκs]".
        iDestruct (cna_own_union2 with "Fi Fj") as "FN".
        rewrite -union_difference_L; [|set_solver].
        iDestruct (cna_own_disjoint with "F' FN") as %?.
        iDestruct (cna_own_union2 with "F' FN") as "FF".
        iDestruct (cna_wsat_join (W:=W) with "Wc Wg Wr") as "$". iModIntro.
        iExists κs''. iFrame "FF κs'". iPureIntro. by split.
    - iDestruct (cna_own_disjoint with "Fi Fi'") as %?. set_solver.
  Qed.

  (** Open through a lifetime guard, as in [util/cancellable.v]'s
    [cna_inv_acc_with_lifetime_guard].  The original also took [£(d+1)]. *)
  Lemma cna_inv_acc_with_lifetime_guard `{!WsatIncl W (cna_wsat WG sm ∗ WG) Wr}
      {γ p N Px κs κ G F} :
    ↑N ⊆ F →
    cna_inv γ p N Px -∗ cna_own p F -∗ cna_lifetimes p κs -∗
    (G &&{WG}&&> llft_alive κ) -∗ (llft_alive κ &&{WG}&&> cna_active γ) -∗
    G =[W]=∗
      cna_own p (F ∖ ↑N) ∗ cna_lifetimes p ({[+ κ +]} ⊎ κs) ∗ G ∗ sm Px ∗
      cna_closer W κ p N sm Px.
  Proof.
    move=> ?. iIntros "inv F κs #g #g2 G W".
    iDestruct (guard_trans with "g g2") as "#g3".
    iMod (cna_inv_acc with "inv F κs g3 g2 G W")
      as "(W & Px & G & F & κs & cl)"; [done|].
    iModIntro. iFrame.
  Qed.

  (** Close an opened invariant *)
  Lemma cna_close {W κ p N sm Px F κs} :
    cna_closer W κ p N sm Px -∗ sm Px -∗ cna_own p F -∗
    cna_lifetimes p κs =[W]=∗ ∃ κs',
      ⌜κs = {[+ κ +]} ⊎ κs' ∧ F ## ↑N⌝ ∗ cna_own p (F ∪ ↑N) ∗
      cna_lifetimes p κs'.
  Proof.
    iIntros "closer Px F κs W". by iApply ("closer" with "Px F κs W").
  Qed.

  (** Cancel a cancellable non-atomic invariant and take its content back *)
  Lemma cna_destroy `{!WsatIncl W (cna_wsat WG sm ∗ WG) Wr} {γ p N Px κs G} :
    cna_inv γ p N Px -∗ cna_lifetimes p κs -∗ cna_active γ -∗
    (∀ κ, ⌜κ ∈ κs⌝ -∗ (G &&{WG}&&> llft_alive κ)) -∗ G =[W]=∗
      cna_lifetimes p κs ∗ G ∗ sm Px.
  Proof.
    iIntros "[%i[%iN #tok]] κs Active #gs G W".
    iDestruct (cna_wsat_split with "W") as "(Wc & Wg & Wr)".
    iDestruct (sinv_tok_acc (sinvGS0:=cna_sinvGS) with "tok Wc")
      as "[body →Wc]". rewrite {1}/cna_body /=.
    iDestruct "body"
      as "[(Active2 & t1 & t2)|[(Px & lock & t1 & t2)|(Fi & [%κ (#g & single & t1)])]]".
    - iDestruct (cna_active_2_no with "Active Active2") as "[]".
    - iDestruct ("→Wc" with "[Active t1 t2]") as "Wc".
      { rewrite /cna_body /=. iLeft. iFrame. }
      iDestruct (cna_wsat_join (W:=W) with "Wc Wg Wr") as "$". iModIntro. iFrame.
    - iDestruct (cna_lfts_elem_of with "κs single") as %?.
      iDestruct ("gs" $! κ with "[//]") as "#gκ".
      iDestruct (guard_trans with "gκ g") as "gA".
      iDestruct (guard_acc with "gA G Wg") as "[Active2 _]".
      iDestruct (cna_active_2_no with "Active Active2") as "[]".
  Qed.
End cna.
