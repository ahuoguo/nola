(** * The Points-To Cell Logic, later-free

  Ported from VerusBelt ([util/non_atomic_cell_map.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), with the laters removed.

  Two changes against the original:

  - The propositions guarding a cell used to be stored in ghost state through
    [agree (later (iProp Σ))].  The [later] was there only for
    impredicativity; as in [nola.alerus.boxes] we store a *syntactic formula*
    [FML $oi Σ] instead, so the agreement lemmas conclude [Gx ≡ Gx'] rather
    than [▷ (G ≡ G')].  That is where the five laters in the original came
    from, and they all disappear.

  - The guards carried a later count [d] and a matching later-credit budget
    [£ d], spent through [lc_fupd_elim_laterN] (14 times in the original) to
    strip the laters that opening a guard introduced.  With the later-free
    guard of [nola.bi.guard] there is nothing to strip, so both the index and
    the credits are gone.  The guards are taken over an explicit world
    satisfaction [W] instead of an invariant mask. *)

From iris.prelude Require Import options.
From nola.bi Require Export guard.
From nola.iris Require Export guard.
From nola.alerus.lang Require Import lang.
From nola.alerus.util Require Import cellmap.
Require Import stdpp.base.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes excl gmap_view.
From nola.iris Require Export iprop.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import base ltac_tactics proofmode coq_tactics.
Import GuardNotation iPropAppNotation.

Local Open Scope nat_scope.

(** Non-atomic map. **)

Definition ReadWriteState := lock_state.

(** The parameters the original took as an invariant namespace.

  - [na_sem] interprets the stored formulas.  The original stored propositions
    directly, under a [later].
  - [na_wsat] is the world satisfaction the guards are taken over; the
    original used the invariant mask [↑naN].
  - [na_emptyx] is a formula standing for [True]: the original stored the
    proposition [True%I] in ghost state while a write is in progress on a
    plain location, and formulas are syntactic. *)
Class NaSem (FML : oFunctor) (Σ : gFunctors) := {
  na_sem : FML $oi Σ → iProp Σ;
  na_sem_ne :: NonExpansive na_sem;
  na_wsat : iProp Σ;
  na_emptyx : FML $oi Σ;
  na_emptyx_sem : na_sem na_emptyx ⊣⊢ True;
}.

(* The original guarded over an invariant namespace [naN]; guards are now
  taken over an explicit world satisfaction, so no namespace is needed. *)

(* begin hide *)

Section NonAtomicInternals.

  Context `{!EqDecision L, !Countable L}.
  Context {V: Type}.
  
  Implicit Types (σ: gmap L (ReadWriteState * V)).

  Local Definition erase_count_map {L} {V} `{!EqDecision L, !Countable L} (σ: gmap L (ReadWriteState * V)) : gmap L V := snd <$> σ.
    
  Local Definition heap_count_r (σ: gmap L (ReadWriteState * V)) (l : L) : nat :=
      match σ !! l with
        | None => 0
        | Some (WSt, v) => 0
        | Some (RSt n, v) => n
      end.
      
  Local Definition heap_count_w (σ: gmap L (ReadWriteState * V)) (l : L) : nat :=
      match σ !! l with
        | None => 0
        | Some (WSt, v) => 1
        | Some (RSt n, v) => 0
      end.
  
  Local Definition m_count {B} (m : gmap (L * nat) B) (l : L) : nat :=
      length (filter (λ p , p.1.1 = l) (map_to_list m)).
      
  Local Definition counts_agree_r {B} (σ: gmap L (ReadWriteState * V)) (m : gmap (L * nat) B)
    : Prop := ∀ l, heap_count_r σ l = m_count m l.
    
  Local Definition counts_agree_w {B} (σ: gmap L (ReadWriteState * V)) (m : gmap (L * nat) B)
    : Prop := ∀ l, heap_count_w σ l = m_count m l.
    
  Local Lemma length_filter_ex {A}
    (P : A → Prop) (dec: ∀ x : A, Decision (P x)) (l : list A)
    : length (filter P l) ≠ 0%nat → ∃ a , P a ∧ a ∈ l.
  Proof.
    induction l as [|a l IHl].
    - intros lf. contradiction.
    - intros lf. rewrite filter_cons in lf.
      destruct (decide (P a)) as [h|h].
      + exists a. rewrite elem_of_cons. intuition.
      + destruct (IHl lf) as [a2 [pa al]]. exists a2. rewrite elem_of_cons. intuition.
  Qed.
  
  Local Lemma length_filter_ex_rev {A}
    (P : A → Prop) (dec: ∀ x : A, Decision (P x)) (l : list A) (a: A)
    : P a → a ∈ l → length (filter P l) ≠ 0%nat.
  Proof.
    intros pa a_in_l lzero.
    rewrite length_zero_iff_nil in lzero.
    assert (a ∈ filter P l) as H.
    { rewrite list_elem_of_filter. split; trivial. }
    rewrite lzero in H. rewrite elem_of_nil in H. trivial.
  Qed.
  
  Local Lemma m_count_get1 {B} (m : gmap (L * nat) B) (l : L)
      : (m_count m l ≠ 0%nat) → ∃ i j , m !! (l, i) = Some j.
  Proof.
    unfold m_count. intros ne0.
    destruct (length_filter_ex _ _ _ ne0) as [[[l1 i1] x] [sat is_in]].
    rewrite elem_of_map_to_list in is_in.
    exists i1. exists x. simpl in sat. subst l. trivial.
  Qed.
  
  Local Lemma counts_agree_insert_writing {B: Type} σ (m : gmap (L * nat) B) l v :
    σ !! l = Some (RSt 0, v) →
    counts_agree_r σ m →
    counts_agree_r (<[l:=(WSt, v)]> σ) m.
  Proof.
    unfold counts_agree_r. intros is_in hc l1. have hcl := hc l1.
    unfold heap_count_r. unfold heap_count_r in hcl. destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert_eq. rewrite is_in in hcl. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
    
  Local Lemma counts_agree_insert_reading0 {B} σ (m : gmap (L * nat) B) l v v' :
    σ !! l = Some (WSt, v) →
    counts_agree_r σ m →
    counts_agree_r (<[l:=(RSt 0, v')]> σ) m.
  Proof.
    unfold counts_agree_r. intros is_in hc l1. have hcl := hc l1.
    unfold heap_count_r. unfold heap_count_r in hcl. destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert_eq. rewrite is_in in hcl. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma counts_agree_w_update_reading {B} σ (m : gmap (L * nat) B) l v v' n n' :
    σ !! l = Some (RSt n, v) →
    counts_agree_w σ m →
    counts_agree_w (<[l:=(RSt n', v')]> σ) m.
  Proof.
    unfold counts_agree_w. intros is_in hc l1. have hcl := hc l1.
    unfold heap_count_w. unfold heap_count_w in hcl. destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert_eq. rewrite is_in in hcl. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma m_get_fresh_index {B} (m : gmap (L * nat) B) (l: L) :
      ∃ i , m !! (l, i) = None.
  Proof.
    assert (exists x , x ∉ ((λ a , a.1.2) <$> map_to_list m)) as [x H].
    { exists (fresh ((λ a , a.1.2) <$> map_to_list m)). apply infinite_is_fresh. }
    exists x. destruct (m !! (l, x)) as [u|] eqn:mlx; trivial.
    exfalso. apply H. rewrite <- elem_of_map_to_list in mlx.
    rewrite list_elem_of_fmap. exists ((l, x), u). intuition.
  Qed.
       
  Local Lemma erase_count_map_same_update_read_count (σ: gmap L (ReadWriteState * V)) l v n m :
      σ !! l = Some (RSt n, v) →
      erase_count_map (<[l:=(RSt m, v)]> σ) = erase_count_map σ.
  Proof.
    intro is_in. unfold erase_count_map. rewrite fmap_insert. simpl.
    apply map_eq. intros l1. destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert_eq. rewrite lookup_fmap. rewrite is_in. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma m_count_insert_plus1 {B} (m : gmap (L * nat) B) l i G
    (is_fresh : m !! (l, i) = None)
    : m_count m l + 1 = m_count (<[(l, i):=G]> m) l.
  Proof.
    unfold m_count. setoid_rewrite map_to_list_insert; trivial.
      rewrite filter_cons. simpl. destruct (decide (l=l)); last by contradiction.
      unfold length. lia.
  Qed.
  
  Local Lemma m_count_insert_ne_helper {B} (m : gmap (L * nat) B) l l1 i G
    (ne : l ≠ l1)
    (mot_in: m !! (l, i) = None)
    : m_count m l1 = m_count (<[(l, i):=G]> m) l1.
  Proof.
    unfold m_count. setoid_rewrite map_to_list_insert; trivial.
      rewrite filter_cons. simpl. destruct (decide (l=l)); last by contradiction.
      destruct (decide (l = l1)); trivial; contradiction.
  Qed.
    
  Local Lemma m_count_insert_ne {B} (m : gmap (L * nat) B) l l1 i G
    (ne : l ≠ l1)
    : m_count m l1 = m_count (<[(l, i):=G]> m) l1.
  Proof.
    assert (delete (l, i) m !! (l, i) = None) as H by apply lookup_delete_eq.
    destruct (m !! (l, i)) as [G2|] eqn:m_in.
     - have t1 := m_count_insert_ne_helper (delete (l, i) m) l l1 i G ne H.
       have t2 := m_count_insert_ne_helper (delete (l, i) m) l l1 i G2 ne H.
       rewrite insert_delete_id in t2; trivial.
       rewrite insert_delete_eq in t1.
       rewrite t2 in t1. trivial.
     - apply m_count_insert_ne_helper; trivial.
  Qed.
    
  Local Lemma m_count_delete_minus1 {B} (m : gmap (L * nat) B) l i G
    (is_in : m !! (l, i) = Some G)
    : m_count m l - 1 = m_count (delete (l, i) m) l.
  Proof.
    assert (delete (l, i) m !! (l, i) = None) as H by apply lookup_delete_eq.
    have j := m_count_insert_plus1 (delete (l, i) m) l i G H.
    rewrite insert_delete_id in j; trivial. lia.
  Qed.
    
  Local Lemma m_count_delete_ne {B} (m : gmap (L * nat) B) l l1 i
    (ne : l ≠ l1)
    : m_count m l1 = m_count (delete (l, i) m) l1.
  Proof.
    destruct (m !! (l, i)) as [G|] eqn:de.
     - have j := m_count_insert_ne (delete (l, i) m) l l1 i G ne.
       rewrite j. rewrite insert_delete_id; trivial.
     - rewrite delete_id; trivial.
  Qed.
      
  Local Lemma counts_agree_insert_read {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l v n i G
      (is_read : σ !! l = Some (RSt n, v))
      (is_fresh : m !! (l, i) = None)
      (ca: counts_agree_r σ m)
    : counts_agree_r (<[l:=(RSt (n + 1), v)]> σ) (<[(l, i):=G]> m).
  Proof.
    intros l1. have cal := ca l1. unfold heap_count_r in *.
    destruct (decide (l = l1)) as [h|h].
     - subst l1. rewrite lookup_insert_eq. rewrite is_read in cal. rewrite cal.
       apply m_count_insert_plus1; trivial.
     - rewrite lookup_insert_ne; trivial. rewrite <- m_count_insert_ne; trivial.
  Qed.

  Local Lemma counts_agree_delete_read {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l v n i G
      (is_read : σ !! l = Some (RSt n, v))
      (is_in_m: m !! (l, i) = Some G)
      (n_ge_1: n ≥ 1)
      (ca: counts_agree_r σ m)
   : counts_agree_r (<[l:=(RSt (n - 1), v)]> σ) (delete (l, i) m).
  Proof.
    intros l1. have cal := ca l1. unfold heap_count_r in *.
    destruct (decide (l = l1)) as [h|h].
     - subst l1. rewrite lookup_insert_eq. rewrite is_read in cal. rewrite cal.
       apply m_count_delete_minus1 with (G := G); trivial.
     - rewrite lookup_insert_ne; trivial. rewrite <- m_count_delete_ne; trivial.
  Qed.
  
  Local Lemma counts_agree_insert_write {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l v i G
      (is_read : σ !! l = Some (RSt 0, v))
      (is_fresh : m !! (l, i) = None)
      (ca: counts_agree_w σ m)
    : counts_agree_w (<[l:=(WSt, v)]> σ) (<[(l, i):=G]> m).
  Proof.
    intros l1. have cal := ca l1. unfold heap_count_w in *.
    destruct (decide (l = l1)) as [h|h].
     - subst l1. rewrite lookup_insert_eq. rewrite is_read in cal. rewrite cal.
       rewrite <- m_count_insert_plus1; trivial. lia.
     - rewrite lookup_insert_ne; trivial. rewrite <- m_count_insert_ne; trivial.
  Qed.
  
  Local Lemma counts_agree_delete_write {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l v v' i G
      (is_read : σ !! l = Some (WSt, v))
      (is_in_m: m !! (l, i) = Some G)
      (ca: counts_agree_w σ m)
   : counts_agree_w (<[l:=(RSt 0, v')]> σ) (delete (l, i) m).
  Proof.
    intros l1. have cal := ca l1. unfold heap_count_w in *.
    destruct (decide (l = l1)) as [h|h].
     - subst l1. rewrite lookup_insert_eq. rewrite is_read in cal.
       replace 0 with (m_count m l - 1) by lia.
       apply m_count_delete_minus1 with (G := G); trivial.
     - rewrite lookup_insert_ne; trivial. rewrite <- m_count_delete_ne; trivial.
  Qed.

  Local Lemma counts_agree_r_alloc {B}
    (σ: gmap L (ReadWriteState * V))
    (m : gmap (L * nat) B) l v :
    σ !! l = None →
    counts_agree_r σ m →
    counts_agree_r (<[l:=(RSt 0, v)]> σ) m.
  Proof.
    intros is_none ca l1. have cal := ca l1. unfold heap_count_r in *.
    destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert_eq. rewrite is_none in cal. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma counts_agree_w_alloc {B}
    (σ: gmap L (ReadWriteState * V))
    (m : gmap (L * nat) B) l v :
    σ !! l = None →
    counts_agree_w σ m →
    counts_agree_w (<[l:=(RSt 0, v)]> σ) m.
  Proof.
    intros is_none ca l1. have cal := ca l1. unfold heap_count_w in *.
    destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert_eq. rewrite is_none in cal. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma counts_agree_r_delete {B}
    (σ: gmap L (ReadWriteState * V))
    (m : gmap (L * nat) B) l v :
    σ !! l = Some (RSt 0, v) →
    counts_agree_r σ m →
    counts_agree_r (delete l σ) m.
  Proof.
    intros is_none ca l1. have cal := ca l1. unfold heap_count_r in *.
    destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_delete_eq. rewrite is_none in cal. trivial.
    - rewrite lookup_delete_ne; trivial.
  Qed.
    
  Local Lemma counts_agree_w_delete {B}
    (σ: gmap L (ReadWriteState * V))
    (m : gmap (L * nat) B) l v :
    σ !! l = Some (RSt 0, v) →
    counts_agree_w σ m →
    counts_agree_w (delete l σ) m.
  Proof.
    intros is_none ca l1. have cal := ca l1. unfold heap_count_w in *.
    destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_delete_eq. rewrite is_none in cal. trivial.
    - rewrite lookup_delete_ne; trivial.
  Qed.
  
  Local Lemma m_count_ge_1_from {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l i G
      (m_has : m !! (l, i) = Some G)
      : m_count m l ≥ 1.
  Proof.
    enough (m_count m l ≠ 0) by lia.
    unfold m_count. 
    apply length_filter_ex_rev with (a := (l, i, G)); trivial.
    rewrite elem_of_map_to_list. trivial.
  Qed.
   
  Local Lemma counts_agree_ge1_is_reading {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l i G
      (m_has : m !! (l, i) = Some G)
      (ca: counts_agree_r σ m)
      : ∃ n v0 , σ !! l = Some (RSt n, v0) ∧ n ≥ 1.
  Proof.
    have cal := ca l.
    have j := m_count_ge_1_from σ m l i G m_has.
    have j2 := j.
    rewrite <- cal in j. unfold heap_count_r in j, cal.
    destruct (σ !! l) as [[r v]|]; last by lia.
    exists (m_count m l). exists v. intuition. f_equal. f_equal.
    destruct r as [|n]. { lia. } { subst n. trivial. }
  Qed.
  
  Local Lemma counts_agree_ge1_is_writing {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l i G
      (m_has : m !! (l, i) = Some G)
      (ca: counts_agree_w σ m)
      : ∃ v0 , σ !! l = Some (WSt, v0).
  Proof.
    have cal := ca l.
    have j := m_count_ge_1_from σ m l i G m_has.
    have j2 := j.
    rewrite <- cal in j. unfold heap_count_w in j, cal.
    destruct (σ !! l) as [[r v]|]; last by lia.
    exists v. intuition. f_equal. f_equal.
    destruct r as [|n]. { trivial. } { lia. }
  Qed.
End NonAtomicInternals.

(* end hide *)

Definition cell_id := positive.

Class na_logicG L V `{!EqDecision L, !Countable L, !Inhabited V}
  (FML : oFunctor) Σ := {
  #[local] na1_inG :: cmap_logicG L cell_id V Σ ;
  #[local] na2_inG :: inG Σ (gmap_viewR (L * nat) (agreeR (FML $oi Σ))) ;
  #[local] na3_inG :: inG Σ (gmap_viewR (L * nat) (agreeR
      (prodO (leibnizO (option (list cell_id * cell_id))) (FML $oi Σ))
     ))
}.

Definition na_logicΣ L V `{!EqDecision L, !Countable L, !Inhabited V}
  (FML : oFunctor) `{!oFunctorContractive FML} : gFunctors := #[
  cmap_logicΣ L cell_id V;
  GFunctor (gmap_viewRF (L * nat) (agreeRF FML));
  GFunctor (gmap_viewRF (L * nat)
    (agreeRF (prodOF (leibnizO (option (list cell_id * cell_id))) FML)))
].

Global Instance subG_na_logicΣ L V `{!EqDecision L, !Countable L, !Inhabited V}
  (FML : oFunctor) `{!oFunctorContractive FML} Σ :
  subG (na_logicΣ L V FML) Σ → na_logicG L V FML Σ.
Proof.
  (* why is this not automatic? *)
  split. 
    - apply subG_cmap_logicΣ. unfold na_logicΣ in H.
      have H2 := subG_inv _ _ _ H. destruct H2 as [H3 H4].
      apply H3.
    - unfold na_logicΣ in H.
      have H2 := subG_inv _ _ _ H. destruct H2 as [H3 H4].
      solve_inG.
    - unfold na_logicΣ in H.
      have H2 := subG_inv _ _ _ H. destruct H2 as [H3 H4].
      solve_inG.
Qed.


Section NonAtomicMap.
  Local Set Default Proof Using "Type*".

  Context `{!EqDecision L, !Countable L}.
  Context `{!Inhabited V}.

  Context {Σ: gFunctors} {FML : oFunctor}.
  Context `{!na_logicG L V FML Σ, !NaSem FML Σ}.

  (** Local names matching the original's section variables *)
  Local Notation sm := na_sem.
  Local Notation W := na_wsat.
  Local Notation emptyx := na_emptyx.
  Local Notation emptyx_sem := na_emptyx_sem.

  (** [point_prop] of a cell chain, so that [guard_and] applies *)
  Local Existing Instance cmap_pt_seq_point_prop.

  Implicit Types (ι: gname) (l: L) (v: V).
  Implicit Types (lc: L + cell_id).
  Implicit Types (cv: cell_id + V).
  Implicit Types (cells: list cell_id).
  Implicit Types (Gx: FML $oi Σ).
  Implicit Types (σ: gmap L (ReadWriteState * V)).

  Local Definition ιf1 (ι: gname) : gname :=
    match prod_decode_fst ι with Some x => x | _ => ι end.
  Local Definition ιf2 (ι: gname) : gname :=
    match prod_decode_snd ι with Some x => x | _ => ι end.

  Local Definition ιh (ι: gname) : gname := ιf1 ι.
  Local Definition ιi (ι: gname) : gname := ιf1 (ιf2 ι).
  Local Definition ιj (ι: gname) : gname := ιf2 (ιf2 ι).

  Local Definition points_to_seq_def (ι: gname) (lc: L+cell_id)
      (cells: list cell_id) (cv: cell_id+V) : iProp Σ :=
      cellmap.pt_seq L cell_id V (ιh ι) lc cells cv.
  Local Definition points_to_seq_aux : seal (@points_to_seq_def).
  Proof. by eexists. Qed.
  Definition points_to_seq ι lc cells cv : iProp Σ.
  Proof. exact (points_to_seq_aux.(unseal) ι lc cells cv). Defined.
  Local Definition points_to_seq_unseal :
      @points_to_seq = @points_to_seq_def := points_to_seq_aux.(seal_eq).

  Notation "l @↦[ ι ][^ cells ] v" := (points_to_seq ι l cells v)
    (at level 20, format "l  @↦[ ι ][^ cells ]  v") : bi_scope.
  Notation "l @↦[ ι ] v" := (points_to_seq ι l [] v)
    (at level 20, format "l  @↦[ ι ]  v") : bi_scope.

  (** The write bank's camera.  The original stored [laterO (iPropO Σ)]. *)
  Local Definition wR :=
    (agreeR (prodO (leibnizO (option (list cell_id * cell_id))) (FML $oi Σ))).

  Local Definition points_to_w_intermediate_def (ι: gname) (l: L)
      (o: option (list cell_id * cell_id)) Gx : iProp Σ :=
    (∃ i, own (ιj ι) (gmap_view_frag (V:=wR) (l, i) (DfracOwn 1)
      (to_agree (o, Gx)))).

  (** The original carried [∃ d, £ d ∗ (G &&{↑naN; d}&&> …)]: a guard with [d]
    laters and the credits to strip them.  The later-free guard needs neither. *)
  Local Definition points_to_r_intermediate_def (ι: gname) (l: L)
      (cells: list cell_id) (v: V) Gx : iProp Σ :=
    (∃ i, own (ιi ι) (gmap_view_frag (l, i) (DfracOwn 1) (to_agree Gx))) ∗
    (sm Gx &&{W}&&> (inl l @↦[ι][^ cells] inr v)).

  Local Definition points_to_w_intermediate_aux :
    seal (@points_to_w_intermediate_def).
  Proof. by eexists. Qed.
  Definition points_to_w_intermediate ι l
    (o: option (list cell_id * cell_id)) Gx : iProp Σ.
  Proof. exact (points_to_w_intermediate_aux.(unseal) ι l o Gx). Defined.
  Local Definition points_to_w_intermediate_unseal :
      @points_to_w_intermediate = @points_to_w_intermediate_def :=
    points_to_w_intermediate_aux.(seal_eq).

  Local Definition points_to_r_intermediate_aux :
    seal (@points_to_r_intermediate_def).
  Proof. by eexists. Qed.
  Definition points_to_r_intermediate ι l cells v Gx : iProp Σ.
  Proof. exact (points_to_r_intermediate_aux.(unseal) ι l cells v Gx). Defined.
  Local Definition points_to_r_intermediate_unseal :
      @points_to_r_intermediate = @points_to_r_intermediate_def :=
    points_to_r_intermediate_aux.(seal_eq).

  Local Definition read_bank ι (σ: gmap L (ReadWriteState * V)) : iProp Σ :=
    ∃ (m : gmap (L * nat) (FML $oi Σ)),
      own (ιi ι) (gmap_view_auth (DfracOwn 1) (to_agree <$> m))
      ∗ ⌜ counts_agree_r σ m ⌝
      ∗ [∗ map] k ↦ Gx ∈ m, sm Gx ∗ ∃ v cells,
          (sm Gx &&{W}&&> (inl (k.1)) @↦[ι][^ cells ] inr v).

  Local Definition write_bank ι (σ: gmap L (ReadWriteState * V)) : iProp Σ :=
    ∃ (m : gmap (L * nat)
        (option (list cell_id * cell_id) * (FML $oi Σ))),
      own (ιj ι) (gmap_view_auth (V:=wR) (DfracOwn 1) (to_agree <$> m))
      ∗ ⌜ counts_agree_w σ m ⌝
      ∗ [∗ map] k ↦ '(o, Gx) ∈ m, sm Gx ∗ ∃ v, match o with
          | None => inl (k.1) @↦[ι] inr v
          | Some (cells, cell) =>
              (sm Gx &&{W}&&> inl (k.1) @↦[ι][^cells] inl cell) ∗
              inr cell @↦[ι] inr v
      end.

  Local Definition non_atomic_map_def (ι: gname)
      (σ: gmap L (ReadWriteState * V)) : iProp Σ :=
      cellmap.heap L cell_id V (ιh ι) (erase_count_map σ)
        ∗ read_bank ι σ ∗ write_bank ι σ.

  Local Definition non_atomic_map_aux : seal (@non_atomic_map_def).
  Proof. by eexists. Qed.
  Definition non_atomic_map ι σ : iProp Σ.
  Proof. exact (non_atomic_map_aux.(unseal) ι σ). Defined.
  Local Definition non_atomic_map_unseal :
      @non_atomic_map = @non_atomic_map_def := non_atomic_map_aux.(seal_eq).

  Local Ltac unseal := rewrite
    ?non_atomic_map_unseal /non_atomic_map_def
    ?points_to_seq_unseal /points_to_seq_def
    ?points_to_r_intermediate_unseal /points_to_r_intermediate_def
    ?points_to_w_intermediate_unseal /points_to_w_intermediate_def.

  (** ** The read bank *)

  Lemma read_bank_contradiction ι σ l n v1 cells v :
      n ≠ 0 →
      σ !! l = Some (RSt n, v1) →
      read_bank ι σ -∗ (inl l @↦[ι][^ cells] inr v) -∗ W -∗ False.
  Proof.
    move=> h Hσl. iDestruct 1 as (m) "[oh [%ca big]]". iIntros "pt W".
    have ca_l := ca l. unfold heap_count_r in ca_l. rewrite Hσl in ca_l.
    rewrite ca_l in h.
    have ij := m_count_get1 m l h. destruct ij as [i [Gx mli]].
    iDestruct (big_sepM_delete with "big") as "[[g gu] _]"; [apply mli|].
    iDestruct "gu" as (v0 cells0) "gu".
    iDestruct (guard_acc with "gu g W") as "[pt2 _]". unseal.
    by iDestruct (cmap_locs_ne with "pt pt2") as "%Hl".
  Qed.

  (** Here [G] is supplied by the client and never stored in ghost state, so
    it can be an arbitrary proposition rather than a formula. *)
  Lemma read_bank_contradiction_guarded_cells ι σ l n v1 cells c v (G : iProp Σ) :
      n ≠ 0 →
      σ !! l = Some (RSt n, v1) →
      read_bank ι σ -∗
      (G &&{W}&&> inl l @↦[ι][^ cells] inl c) -∗
      G -∗
      (inr c @↦[ι] inr v) -∗ W -∗ False.
  Proof.
    move=> h Hσl. iDestruct 1 as (m) "[oh [%ca big]]".
    iIntros "#guard G pt W".
    have ca_l := ca l. unfold heap_count_r in ca_l. rewrite Hσl in ca_l.
    rewrite ca_l in h.
    have ij := m_count_get1 m l h. destruct ij as [i [Gx0 mli]].
    iDestruct (big_sepM_delete with "big") as "[[G0 gu] _]"; [apply mli|].
    iDestruct "gu" as (v0 cells0) "#guard0".
    iDestruct (guard_lhs_sep_l (R:=sm Gx0) with "guard") as "guard'".
    iDestruct (guard_lhs_sep_r (R:=G) with "guard0") as "guard0'".
    iDestruct (guard_and_pers_with_excl (S:=False%I)
      with "[] guard' guard0' [$G $G0] pt W") as "(_ & _ & _ & [])".
    iIntros "!> [And pt]".
    iDestruct (cmap_pt_and_gives_prefix with "[And]") as "%IsPrefix"; [unseal; done|].
    destruct IsPrefix as [cells2 IsPrefix]. rewrite IsPrefix.
    iDestruct "And" as "[_ prefix]". unseal.
    iDestruct (cmap_pt_seq_cons_app with "prefix") as "[a b]".
    by iDestruct (cmap_cells_ne with "pt b") as "%A".
  Qed.

  Lemma read_bank_begin ι σ l n v0 cells v Gx :
      σ !! l = Some (RSt n, v0) →
      read_bank ι σ -∗
      (sm Gx &&{W}&&> (inl l @↦[ι][^ cells] inr v)) -∗
      sm Gx ==∗
      points_to_r_intermediate ι l cells v Gx ∗
        read_bank ι (<[ l := (RSt (n+1), v0) ]> σ).
  Proof.
    move=> is_read. iIntros "na #guard g".
    iDestruct "na" as (m) "[oi [%ca big]]".
    destruct (m_get_fresh_index m l) as [i is_fresh].
    iMod (@own_update Σ _ na2_inG (ιi ι) _ ((
      gmap_view_auth (V := (agreeR (FML $oi Σ)))
        (DfracOwn 1) (to_agree <$> (<[ (l,i) := Gx ]> m))
    ⋅ gmap_view_frag (V := (agreeR (FML $oi Σ)))
        (l, i) (DfracOwn 1) (to_agree Gx)
    )) with "oi") as "[oi ptr]".
    { rewrite fmap_insert. apply gmap_view_alloc; [|done..].
      by rewrite lookup_fmap is_fresh. }
    iModIntro. iFrame "oi".
    rewrite points_to_r_intermediate_unseal /points_to_r_intermediate_def.
    iFrame "ptr guard". iSplitR.
    { iPureIntro. by apply counts_agree_insert_read. }
    rewrite big_sepM_insert; [|done]. iFrame "big g". by iExists v, cells.
  Qed.

  Local Lemma points_to_heap_agree' ι l cells v σ :
    (inl l @↦[ι][^ cells ] inr v) ∗
      cellmap.heap L cell_id V (ιh ι) (erase_count_map σ) ⊢
      ⌜ ∃ st, σ !! l = Some (st, v) ⌝.
  Proof.
    unseal. iIntros "[pt heap]". iDestruct (cmap_read with "heap pt") as "%Hv".
    iPureIntro. unfold erase_count_map in Hv. rewrite lookup_fmap in Hv.
    destruct (σ !! l) as [p|].
    - unfold "<$>", option_fmap, option_map in Hv.
      exists (p.1). destruct p; f_equal. f_equal. by inversion Hv.
    - inversion Hv.
  Qed.

  (** The original concluded under [▷ |={E}=>]: the later came from
    [Next G ≡ Next G'], the fancy update from opening the guard.  Now the
    agreement is [Gx ≡ Gx'] and the guard is opened against [W]. *)
  Lemma read_bank_end ι σ l cells v Gx :
      read_bank ι σ -∗
      points_to_r_intermediate ι l cells v Gx -∗
      cellmap.heap L cell_id V (ιh ι) (erase_count_map σ) -∗
      W ==∗ ∃ n, sm Gx
        ∗ ⌜n ≥ 1 ∧ σ !! l = Some (RSt n, v)⌝
        ∗ read_bank ι (<[ l := (RSt (n-1), v) ]> σ)
        ∗ cellmap.heap L cell_id V (ιh ι) (erase_count_map σ)
        ∗ W.
  Proof.
    rewrite points_to_r_intermediate_unseal /points_to_r_intermediate_def.
    iIntros "na [ptr #guard] oh W".
    iDestruct "na" as (m) "[oi [%ca big]]".
    iDestruct "ptr" as (i) "ptr".
    iAssert (∃ n Gx' v0,
      ⌜ σ !! l = Some (RSt n, v0) ∧ n ≥ 1 ∧ m !! (l, i) = Some Gx'⌝
      ∗ Gx ≡ Gx')%I as (n Gx' v0) "[%p #equ]".
    { iCombine "oi ptr" as "oi".
      iDestruct (own_valid with "oi") as "oi_val".
      rewrite gmap_view_both_validI_total.
      iDestruct "oi_val" as (v') "[%_vf1 [%_vf2 [%sm' [val1 val2]]]]".
      have [Gx' dest_eqn] : ∃ Gx', m !! (l, i) = Some Gx'.
      { destruct (m !! (l, i)) as [Gx'|] eqn:E'; [by eexists|].
        exfalso. move: sm'. rewrite lookup_fmap E' /=. by inversion 1. }
      move: sm'. rewrite lookup_fmap dest_eqn /= => sm'. inversion sm'. subst v'.
      rewrite to_agree_includedI.
      destruct (counts_agree_ge1_is_reading σ m l i Gx' dest_eqn)
        as [n [v0 is_read]]; [done|].
      iExists n, Gx', v0. iFrame "val2". iPureIntro. intuition. }
    iExists n. destruct p as [in_sig [n_ge1 in_m]].
    iDestruct (big_sepM_delete with "big") as "[[g gu] big]"; [apply in_m|].
    iDestruct "gu" as (v1 cells1) "_". iRewrite -"equ" in "g".
    iDestruct (guard_acc with "guard g W") as "[pt back]".
    iDestruct (points_to_heap_agree' ι l cells v σ with "[$pt $oh]")
      as "%in_sig2".
    iDestruct ("back" with "pt") as "[W G]".
    iCombine "oi ptr" as "oi".
    iMod (@own_update Σ _ na2_inG (ιi ι) _ ((
      gmap_view_auth (V := (agreeR (FML $oi Σ)))
        (DfracOwn 1) (to_agree <$> (delete (l, i) m))
    )) with "oi") as "oi".
    { rewrite fmap_delete. apply gmap_view_delete. }
    have veq : v = v0.
    { destruct in_sig2 as [n0 in_sig2]. rewrite in_sig in in_sig2.
      by inversion in_sig2. }
    subst v0. iModIntro. iFrame "G". iSplitR; [iPureIntro; intuition|].
    iFrame "oi big oh W". iPureIntro.
    apply (counts_agree_delete_read _ _ _ _ _ _ Gx'); trivial.
  Qed.

  Lemma read_bank_no_op_to_wst ι σ l v :
      σ !! l = Some (RSt 0, v) →
      read_bank ι σ ⊢ read_bank ι (<[l:=(WSt, v)]> σ).
  Proof.
    iIntros (Hin) "rb". iDestruct "rb" as (m) "[oi [%ca big]]".
    iFrame. iPureIntro. by apply counts_agree_insert_writing.
  Qed.

  Lemma read_bank_no_op_to_rst0 ι σ l v v' :
      σ !! l = Some (WSt, v) →
      read_bank ι σ ⊢ read_bank ι (<[l:=(RSt 0, v')]> σ).
  Proof.
    iIntros (Hin) "rb". iDestruct "rb" as (m) "[oi [%ca big]]".
    iFrame. iPureIntro. by eapply counts_agree_insert_reading0.
  Qed.

  Lemma read_bank_insert ι l v σ :
    (σ !! l = None) →
    read_bank ι σ ⊢ read_bank ι (<[ l := (RSt 0, v) ]> σ).
  Proof.
    iIntros (not_in) "rb". iDestruct "rb" as (m) "[oi [%ca big]]".
    iExists m. iFrame. iPureIntro. by apply (counts_agree_r_alloc σ m l v).
  Qed.

  Lemma read_bank_delete ι l v σ :
    (σ !! l = Some (RSt 0, v)) →
    read_bank ι σ ⊢ read_bank ι (delete l σ).
  Proof.
    iIntros (not_in) "rb". iDestruct "rb" as (m) "[oi [%ca big]]".
    iExists m. iFrame. iPureIntro. by apply (counts_agree_r_delete σ m l v).
  Qed.

  (** ** The write bank *)

  Lemma write_bank_contradiction ι σ l v1 v :
      σ !! l = Some (WSt, v1) →
      write_bank ι σ -∗ (inl l @↦[ι] inr v) -∗ W -∗ False.
  Proof.
    move=> Hσl. iDestruct 1 as (m) "[oh [%ca big]]". iIntros "pt W".
    have ca_l := ca l. unfold heap_count_w in ca_l. rewrite Hσl in ca_l.
    have ca_l' : m_count m l ≠ 0 by lia.
    have ij := m_count_get1 m l ca_l'. destruct ij as [i [[o Gx] mli]].
    iDestruct (big_sepM_delete with "big") as "[a _]"; [apply mli|].
    simpl. iDestruct "a" as "[G a]". destruct o as [[cells cell]|].
    - iDestruct "a" as (v0) "[#guard pt2]".
      iDestruct (guard_acc with "guard G W") as "[pt3 _]". unseal.
      repeat rewrite <- pt_seq_singleton.
      by iDestruct (cmap_locs_ne with "pt pt3") as "%Hl".
    - iDestruct "a" as (v0) "pt2". unseal.
      repeat rewrite <- pt_seq_singleton.
      by iDestruct (cmap_locs_ne with "pt pt2") as "%Hl".
  Qed.

  Lemma write_bank_contradiction_guarded_all ι σ l v1 cells v (G : iProp Σ) :
      σ !! l = Some (WSt, v1) →
      write_bank ι σ -∗
      (G &&{W}&&> inl l @↦[ι][^ cells] inr v) -∗
      G -∗ W -∗ False.
  Proof.
    move=> Hσl. iDestruct 1 as (m) "[oh [%ca big]]". iIntros "#guard G W".
    have ca_l := ca l. unfold heap_count_w in ca_l. rewrite Hσl in ca_l.
    have ca_l' : m_count m l ≠ 0 by lia.
    have ij := m_count_get1 m l ca_l'. destruct ij as [i [[o Gx0] mli]].
    iDestruct (big_sepM_delete with "big") as "[a _]"; [apply mli|].
    simpl. iDestruct "a" as "[G0 a]". destruct o as [[cells0 cell0]|].
    - iDestruct "a" as (v0) "[#guard0 pt0]".
      iDestruct (guard_lhs_sep_l (R:=sm Gx0) with "guard") as "guard'".
      iDestruct (guard_lhs_sep_r (R:=G) with "guard0") as "guard0'".
      iDestruct (guard_and_pers_with_excl (S:=False%I)
        with "[] guard' guard0' [$G $G0] pt0 W") as "(_ & _ & _ & [])".
      iIntros "!> [And pt]". unseal.
      repeat rewrite <- pt_seq_singleton.
      iApply (cmap_pt_and_gives_contra _ _ _ (ιh ι) (inl l) cells cells0 cell0
        v v0 with "And [pt]"). { rewrite <- pt_seq_singleton. iFrame. }
    - iDestruct (guard_acc with "guard G W") as "[pt0 _]".
      iDestruct "a" as (v0) "pt1". unseal.
      repeat rewrite <- pt_seq_singleton.
      by iDestruct (cmap_locs_ne with "pt0 pt1") as "%Hl".
  Qed.

  Lemma write_bank_contradiction_guarded_cells ι σ l v1 cells c v
      (G : iProp Σ) :
      σ !! l = Some (WSt, v1) →
      write_bank ι σ -∗
      (G &&{W}&&> inl l @↦[ι][^ cells] inl c) -∗
      G -∗
      (inr c @↦[ι] inr v) -∗ W -∗ False.
  Proof.
    move=> Hσl. iIntros "wb #guard G pt W".
    iApply (write_bank_contradiction_guarded_all ι σ l v1 (cells ++ [c]) v
      (G ∗ inr c @↦[ι] inr v)%I Hσl with "wb [] [$G $pt] W").
    unseal. iApply guard_and; [apply cmap_pt_and_cons_back| |].
    - iApply guard_lhs_sep_l. unseal. iApply "guard".
    - iApply guard_sep_r.
  Qed.

  Lemma write_bank_begin ι σ l v0 v :
      σ !! l = Some (RSt 0, v0) →
      write_bank ι σ -∗ inl l @↦[ι] inr v ==∗
      points_to_w_intermediate ι l None emptyx ∗
        write_bank ι (<[ l := (WSt, v0) ]> σ).
  Proof.
    move=> is_read. iIntros "na pt". iDestruct "na" as (m) "[oi [%ca big]]".
    destruct (m_get_fresh_index m l) as [i is_fresh].
    iMod (@own_update Σ _ na3_inG (ιj ι) _ ((
      gmap_view_auth (V := wR)
        (DfracOwn 1) (to_agree <$> (<[ (l,i) := (None, emptyx) ]> m))
    ⋅ gmap_view_frag (V := wR)
        (l, i) (DfracOwn 1) (to_agree (None, emptyx))
    )) with "oi") as "[oi ptr]".
    { rewrite fmap_insert. apply (gmap_view_alloc (V:=wR)); [|done..].
      by rewrite lookup_fmap is_fresh. }
    iModIntro. iFrame "oi".
    rewrite points_to_w_intermediate_unseal /points_to_w_intermediate_def.
    iFrame "ptr". iSplitR.
    { iPureIntro. by apply counts_agree_insert_write. }
    rewrite big_sepM_insert; [|done]. iFrame "big".
    rewrite emptyx_sem. iSplit; [done|]. by iExists v.
  Qed.

  Lemma write_bank_begin_guarded_cells ι σ l cells c v0 v Gx :
      σ !! l = Some (RSt 0, v0) →
      write_bank ι σ -∗
      (sm Gx &&{W}&&> inl l @↦[ι][^ cells] inl c) -∗
      sm Gx -∗
      (inr c @↦[ι] inr v) ==∗
      points_to_w_intermediate ι l (Some (cells, c)) Gx ∗
        write_bank ι (<[ l := (WSt, v0) ]> σ).
  Proof.
    move=> is_read. iIntros "na #guard G pt".
    iDestruct "na" as (m) "[oi [%ca big]]".
    destruct (m_get_fresh_index m l) as [i is_fresh].
    iMod (@own_update Σ _ na3_inG (ιj ι) _ ((
      gmap_view_auth (V := wR)
        (DfracOwn 1) (to_agree <$> (<[ (l,i) := (Some (cells, c), Gx) ]> m))
    ⋅ gmap_view_frag (V := wR)
        (l, i) (DfracOwn 1) (to_agree (Some (cells, c), Gx))
    )) with "oi") as "[oi ptr]".
    { rewrite fmap_insert. apply (gmap_view_alloc (V:=wR)); [|done..].
      by rewrite lookup_fmap is_fresh. }
    iModIntro. iFrame "oi".
    rewrite points_to_w_intermediate_unseal /points_to_w_intermediate_def.
    iFrame "ptr". iSplitR.
    { iPureIntro. by apply counts_agree_insert_write. }
    rewrite big_sepM_insert; [|done]. iFrame "big G guard". by iExists v.
  Qed.

  Lemma write_bank_end ι σ l v' Gx :
      write_bank ι σ -∗
      points_to_w_intermediate ι l None Gx
      ==∗ ∃ v1 v2,
      ⌜σ !! l = Some (WSt, v1)⌝ ∗
      inl l @↦[ι] inr v2 ∗
      write_bank ι (<[ l := (RSt 0, v') ]> σ).
  Proof.
    rewrite points_to_w_intermediate_unseal /points_to_w_intermediate_def.
    iIntros "wb wim".
    iDestruct "wb" as (m) "[oj [%ca big]]".
    iDestruct "wim" as (i) "wim".
    iAssert (∃ Gx' v1,
      ⌜σ !! l = Some (WSt, v1) ∧ m !! (l, i) = Some (None, Gx')⌝
      ∗ Gx ≡ Gx')%I as (Gx' v1) "[%p #equ]".
    { iCombine "oj wim" as "oj".
      iDestruct (own_valid with "oj") as "oj_val".
      rewrite gmap_view_both_validI_total.
      iDestruct "oj_val" as (vv) "[%_vf1 [%_vf2 [%sm' [val1 val2]]]]".
      have [oG' dest_eqn] : ∃ oG', m !! (l, i) = Some oG'.
      { destruct (m !! (l, i)) as [oG'|] eqn:E'; [by eexists|].
        exfalso. move: sm'. rewrite lookup_fmap E' /=. by inversion 1. }
      move: sm'. rewrite lookup_fmap dest_eqn /= => sm'. inversion sm'. subst vv.
      rewrite to_agree_includedI.
      destruct (counts_agree_ge1_is_writing σ m l i oG' dest_eqn)
        as [v0 is_write]; [done|].
      destruct oG' as [o' Gx']. iExists Gx', v0.
      rewrite prod_equivI. iDestruct "val2" as "[%val3 #val4]".
      simpl in val3. subst o'.
      iSplit; [iPureIntro; by split|]. iFrame "val4". }
    destruct p as [in_sig in_m].
    iDestruct (big_sepM_delete with "big") as "[g big]"; [apply in_m|].
    iCombine "oj wim" as "oj".
    iMod (@own_update Σ _ na3_inG (ιj ι) _ ((
      gmap_view_auth (V := wR) (DfracOwn 1) (to_agree <$> (delete (l, i) m))
    )) with "oj") as "oj".
    { rewrite fmap_delete. apply (gmap_view_delete (V := wR)). }
    iDestruct "g" as "[G' pt]". iDestruct "pt" as (v2) "pt".
    iModIntro. iExists v1, v2. iSplit; [done|]. iFrame "pt oj big".
    iPureIntro. by eapply (counts_agree_delete_write _ _ _ _ _ _).
  Qed.

  Lemma write_bank_end_guarded_cells ι σ l cells c v' Gx :
      write_bank ι σ -∗
      points_to_w_intermediate ι l (Some (cells, c)) Gx
      ==∗ ∃ v1 v2,
      sm Gx ∗
      (sm Gx &&{W}&&> inl l @↦[ι][^ cells] inl c) ∗
      ⌜σ !! l = Some (WSt, v1)⌝ ∗
      inr c @↦[ι] inr v2 ∗
      write_bank ι (<[ l := (RSt 0, v') ]> σ).
  Proof.
    rewrite points_to_w_intermediate_unseal /points_to_w_intermediate_def.
    iIntros "wb wim".
    iDestruct "wb" as (m) "[oj [%ca big]]".
    iDestruct "wim" as (i) "wim".
    iAssert (∃ Gx' v1,
      ⌜σ !! l = Some (WSt, v1)
        ∧ m !! (l, i) = Some (Some (cells, c), Gx')⌝
      ∗ Gx ≡ Gx')%I as (Gx' v1) "[%p #equ]".
    { iCombine "oj wim" as "oj".
      iDestruct (own_valid with "oj") as "oj_val".
      rewrite gmap_view_both_validI_total.
      iDestruct "oj_val" as (vv) "[%_vf1 [%_vf2 [%sm' [val1 val2]]]]".
      have [oG' dest_eqn] : ∃ oG', m !! (l, i) = Some oG'.
      { destruct (m !! (l, i)) as [oG'|] eqn:E'; [by eexists|].
        exfalso. move: sm'. rewrite lookup_fmap E' /=. by inversion 1. }
      move: sm'. rewrite lookup_fmap dest_eqn /= => sm'. inversion sm'. subst vv.
      rewrite to_agree_includedI.
      destruct (counts_agree_ge1_is_writing σ m l i oG' dest_eqn)
        as [v0 is_write]; [done|].
      destruct oG' as [o' Gx']. iExists Gx', v0.
      rewrite prod_equivI. iDestruct "val2" as "[%val3 #val4]".
      simpl in val3. subst o'.
      iSplit; [iPureIntro; by split|]. iFrame "val4". }
    destruct p as [in_sig in_m].
    iDestruct (big_sepM_delete with "big") as "[g big]"; [apply in_m|].
    iDestruct "g" as "[G gu]". iRewrite -"equ" in "G".
    iDestruct "gu" as (v2) "[#guard pt]".
    iAssert (sm Gx &&{W}&&> inl l @↦[ι][^ cells] inl c)%I as "#guard2".
    { iRewrite "equ". iApply "guard". }
    iCombine "oj wim" as "oj".
    iMod (@own_update Σ _ na3_inG (ιj ι) _ ((
      gmap_view_auth (V := wR) (DfracOwn 1) (to_agree <$> (delete (l, i) m))
    )) with "oj") as "oj".
    { rewrite fmap_delete. apply (gmap_view_delete (V := wR)). }
    iModIntro. iExists v1, v2. iFrame "G guard2 pt oj big".
    iSplit; [done|].
    iPureIntro. by eapply (counts_agree_delete_write _ _ _ _ _ _).
  Qed.

  Lemma write_bank_no_op ι σ l n v n' v' :
      σ !! l = Some (RSt n, v) →
      write_bank ι σ ⊢ write_bank ι (<[l:=(RSt n', v')]> σ).
  Proof.
    iIntros (Hin) "wb". iDestruct "wb" as (m) "[oj [%ca big]]".
    iFrame. iPureIntro. by eapply counts_agree_w_update_reading.
  Qed.

  Lemma write_bank_insert ι l v σ :
    (σ !! l = None) →
    write_bank ι σ ⊢ write_bank ι (<[ l := (RSt 0, v) ]> σ).
  Proof.
    iIntros (not_in) "wb". iDestruct "wb" as (m) "[oj [%ca big]]".
    iExists m. iFrame. iPureIntro. by apply (counts_agree_w_alloc σ m l v).
  Qed.

  Lemma write_bank_delete ι l v σ :
    (σ !! l = Some (RSt 0, v)) →
    write_bank ι σ ⊢ write_bank ι (delete l σ).
  Proof.
    iIntros (not_in) "wb". iDestruct "wb" as (m) "[oj [%ca big]]".
    iExists m. iFrame. iPureIntro. by apply (counts_agree_w_delete σ m l v).
  Qed.

  (** ** The non-atomic map *)

  Global Instance points_to_timeless ι lc cells cv :
    Timeless (lc @↦[ι][^ cells] cv).
  Proof. unseal. destruct cv; apply _. Qed.

  Lemma non_atomic_map_alloc_empty : ⊢ |==> ∃ ι, non_atomic_map ι ∅.
  Proof.
    unseal. iIntros.
    iMod (cmap_init) as (ιh0) "H".
    iMod (@own_alloc Σ _ na2_inG (gmap_view_auth (DfracOwn 1) ∅))
      as (ιi0) "H2". { apply gmap_view_auth_valid. }
    iMod (@own_alloc Σ _ na3_inG (gmap_view_auth (DfracOwn 1) ∅))
      as (ιj0) "H3". { apply gmap_view_auth_valid. }
    iModIntro. iExists (prod_encode ιh0 (prod_encode ιi0 ιj0)).
    rewrite /non_atomic_map /read_bank /write_bank /ιh /ιi /ιj /ιf1 /ιf2.
    repeat (rewrite prod_decode_encode_fst || rewrite prod_decode_encode_snd).
    replace (erase_count_map ∅) with (∅: gmap L V) by done. iFrame "H".
    iSplitL "H2".
    - iExists ∅. iFrame. iSplit; [|done]. iPureIntro.
      rewrite /counts_agree_r /heap_count_r /m_count=> l.
      by rewrite lookup_empty.
    - iExists ∅. iFrame. iSplit; [|done]. iPureIntro.
      rewrite /counts_agree_w /heap_count_w /m_count=> l.
      by rewrite lookup_empty.
  Qed.

  Lemma points_to_heap_agree ι l cells v σ :
    (inl l @↦[ι][^ cells] inr v) -∗ non_atomic_map ι σ -∗
      ⌜ ∃ st, σ !! l = Some (st, v) ⌝.
  Proof.
    unseal. iIntros "pt na". iDestruct "na" as "[oh _]".
    iApply points_to_heap_agree'. unseal. iFrame.
  Qed.

  (** The original needed a fancy update here only to run the contradiction
    lemmas, which were themselves [={E}=∗ False]; later-free they conclude
    [False] directly, so this is a plain entailment. *)
  Lemma points_to_heap_reading0 ι l v σ :
    (inl l @↦[ι] inr v) -∗ non_atomic_map ι σ -∗ W -∗
      ⌜ σ !! l = Some (RSt 0, v) ⌝
        ∗ (inl l @↦[ι] inr v) ∗ non_atomic_map ι σ ∗ W.
  Proof.
    iIntros "pt na W".
    iAssert (⌜∃ st, σ !! l = Some (st, v)⌝)%I as (st) "%Hσl".
    { by iApply (points_to_heap_agree with "pt na"). }
    unseal. iDestruct "na" as "[h [rb wb]]".
    destruct st.
    - iExFalso. iApply (write_bank_contradiction with "wb [pt] W");
        [apply Hσl|]. unseal. iFrame "pt".
    - destruct n.
      + iFrame. done.
      + iExFalso.
        iApply (read_bank_contradiction _ _ _ (S n) with "rb [pt] W");
          [lia|apply Hσl|]. unseal. iFrame "pt".
  Qed.

  Lemma points_to_heap_reading0_guarded_cells `{!EqDecision V} ι l cells c v σ
      (G : iProp Σ) :
    (G &&{W}&&> inl l @↦[ι][^ cells] inl c) -∗ G -∗ (inr c @↦[ι] inr v) -∗
      non_atomic_map ι σ -∗ W -∗
      ⌜ σ !! l = Some (RSt 0, v) ⌝
        ∗ G ∗ (inr c @↦[ι] inr v) ∗ non_atomic_map ι σ ∗ W.
  Proof.
    iIntros "#guard G pt na W".
    iAssert (⌜∃ st, σ !! l = Some (st, v)⌝)%I with "[G pt na W]" as (st) "%Hσl".
    { iDestruct (guard_acc with "guard G W") as "[prefix _]".
      iApply (points_to_heap_agree ι l (cells ++ [c]) v σ with "[prefix pt] na").
      unseal. rewrite cmap_pt_seq_cons_back. iFrame. }
    unseal. iDestruct "na" as "[h [rb wb]]".
    destruct st.
    - iExFalso.
      iApply (write_bank_contradiction_guarded_cells with "wb [] G [pt] W");
        [apply Hσl| |]; unseal; iFrame "#"; iFrame.
    - destruct n.
      + iFrame. done.
      + iExFalso.
        iApply (read_bank_contradiction_guarded_cells _ _ _ (S n)
          with "rb [] G [pt] W"); [lia|apply Hσl| |];
          unseal; iFrame "#"; iFrame.
  Qed.

  Lemma points_to_heap_readingN_guarded_all `{!EqDecision V} ι l cells v σ
      (G : iProp Σ) :
    (G &&{W}&&> inl l @↦[ι][^ cells] inr v) -∗ G -∗
      non_atomic_map ι σ -∗ W -∗
      ⌜ ∃ n, σ !! l = Some (RSt n, v) ⌝
        ∗ G ∗ non_atomic_map ι σ ∗ W.
  Proof.
    iIntros "#guard G na W".
    iAssert (⌜∃ st, σ !! l = Some (st, v)⌝)%I with "[G na W]" as (st) "%Hσl".
    { iDestruct (guard_acc with "guard G W") as "[pt _]".
      iApply (points_to_heap_agree with "pt na"). }
    unseal. iDestruct "na" as "[h [rb wb]]".
    destruct st.
    - iExFalso.
      iApply (write_bank_contradiction_guarded_all with "wb [] G W");
        [apply Hσl|]. unseal. iFrame "#".
    - iFrame. iPureIntro. by exists n.
  Qed.

  (** ** The main interface *)

  Lemma na_write_begin ι l v σ :
    (inl l @↦[ι] inr v) -∗ non_atomic_map ι σ -∗ W ==∗
        ⌜ σ !! l = Some (RSt 0, v) ⌝
        ∗ points_to_w_intermediate ι l None emptyx
        ∗ non_atomic_map ι (<[ l := (WSt, v) ]> σ) ∗ W.
  Proof.
    iIntros "pt na W".
    iDestruct (points_to_heap_reading0 with "pt na W")
      as "(%is_read & pt & na & W)".
    unseal. iDestruct "na" as "[oh [rb wb]]".
    iMod (cmap_write _ _ _ _ _ _ _ v with "oh pt") as "[oh pt]".
    replace (<[l:=v]> (erase_count_map σ))
      with (erase_count_map (<[ l := (WSt, v) ]> σ));
      last by rewrite /erase_count_map fmap_insert.
    iMod (write_bank_begin with "wb [pt]") as "[wim wb]"; [apply is_read| |].
    { unseal. iFrame. }
    iModIntro. unseal. iFrame "wim oh wb W". iSplit; [done|].
    by iApply read_bank_no_op_to_wst.
  Qed.

  Lemma na_write_begin_guarded_cells `{!EqDecision V} ι l cells c v σ Gx :
    (sm Gx &&{W}&&> inl l @↦[ι][^ cells] inl c) -∗ sm Gx -∗
      (inr c @↦[ι] inr v) -∗ non_atomic_map ι σ -∗ W ==∗
        ⌜ σ !! l = Some (RSt 0, v) ⌝
        ∗ points_to_w_intermediate ι l (Some (cells, c)) Gx
        ∗ non_atomic_map ι (<[ l := (WSt, v) ]> σ) ∗ W.
  Proof.
    iIntros "#guard G pt na W".
    iDestruct (points_to_heap_reading0_guarded_cells
      with "guard G pt na W") as "(%is_read & G & pt & na & W)".
    unseal. iDestruct "na" as "[oh [rb wb]]".
    iDestruct (guard_acc with "guard G W") as "[prefix back]".
    iCombine "prefix pt" as "pt". rewrite -cmap_pt_seq_cons_back.
    iMod (cmap_write _ _ _ _ _ _ _ v with "oh pt") as "[oh pt]".
    rewrite cmap_pt_seq_cons_back. iDestruct "pt" as "[prefix pt]".
    iDestruct ("back" with "prefix") as "[W G]".
    replace (<[l:=v]> (erase_count_map σ))
      with (erase_count_map (<[ l := (WSt, v) ]> σ));
      last by rewrite /erase_count_map fmap_insert.
    iMod (write_bank_begin_guarded_cells with "wb [] G [pt]") as "[wim wb]";
      [apply is_read| | |].
    { unseal. iApply "guard". } { unseal. iApply "pt". }
    iModIntro. unseal. iFrame "wim oh wb W". iSplit; [done|].
    by iApply read_bank_no_op_to_wst.
  Qed.

  Lemma na_write_finish ι l v' σ Gx :
    points_to_w_intermediate ι l None Gx -∗ non_atomic_map ι σ ==∗
        ⌜ ∃ v, σ !! l = Some (WSt, v) ⌝
        ∗ inl l @↦[ι] inr v'
        ∗ non_atomic_map ι (<[ l := (RSt 0, v') ]> σ).
  Proof.
    iIntros "pt na". unseal. iDestruct "na" as "[oh [rb wb]]".
    iMod (write_bank_end _ _ l v' with "wb [pt]") as (v1 v2) "[%Hst [pt wb]]".
    { unseal. iFrame. }
    unseal. iMod (cmap_write _ _ _ _ _ _ _ _ v' with "oh pt") as "[oh pt]".
    replace (<[l:=v']> (erase_count_map σ))
      with (erase_count_map (<[ l := (RSt 0, v') ]> σ));
      last by rewrite /erase_count_map fmap_insert.
    iModIntro. iFrame "pt oh wb". iSplit. { by iExists v1. }
    by iApply read_bank_no_op_to_rst0.
  Qed.

  (** The original's [▷ |={E}=>] disappears: [write_bank_end_guarded_cells] no
    longer needs a later to strip the stored agreement. *)
  Lemma na_write_finish_guarded_cells ι l cells c v' σ Gx :
    points_to_w_intermediate ι l (Some (cells, c)) Gx -∗
      non_atomic_map ι σ -∗ W ==∗
        ⌜ ∃ v, σ !! l = Some (WSt, v) ⌝
        ∗ sm Gx
        ∗ inr c @↦[ι] inr v'
        ∗ non_atomic_map ι (<[ l := (RSt 0, v') ]> σ) ∗ W.
  Proof.
    iIntros "wim na W". unseal. iDestruct "na" as "[oh [rb wb]]".
    iMod (write_bank_end_guarded_cells _ _ l _ _ v' with "wb [wim]")
      as (v1 v2) "[G [#guard [%Hst [pt wb]]]]". { unseal. iFrame "wim". }
    iDestruct (guard_acc with "guard G W") as "[prefix back]".
    unseal. iCombine "prefix pt" as "pt". rewrite -cmap_pt_seq_cons_back.
    iMod (cmap_write _ _ _ _ _ _ _ _ v' with "oh pt") as "[oh pt]".
    replace (<[l:=v']> (erase_count_map σ))
      with (erase_count_map (<[ l := (RSt 0, v') ]> σ));
      last by rewrite /erase_count_map fmap_insert.
    rewrite cmap_pt_seq_cons_back. iDestruct "pt" as "[prefix pt]".
    iDestruct ("back" with "prefix") as "[W G]".
    iModIntro. iFrame "G pt oh wb W". iSplit. { by iExists v1. }
    by iApply read_bank_no_op_to_rst0.
  Qed.

  Lemma na_read_begin `{!EqDecision V} ι l cells v σ Gx :
    (sm Gx &&{W}&&> (inl l @↦[ι][^ cells] inr v)) -∗ sm Gx -∗
      non_atomic_map ι σ -∗ W ==∗
        ∃ n , ⌜ σ !! l = Some (RSt n, v) ⌝
        ∗ points_to_r_intermediate ι l cells v Gx
        ∗ non_atomic_map ι (<[ l := (RSt (n + 1), v) ]> σ) ∗ W.
  Proof.
    iIntros "#guard G na W".
    iDestruct (points_to_heap_readingN_guarded_all with "guard G na W")
      as "(%is_read & G & na & W)".
    rewrite non_atomic_map_unseal /non_atomic_map_def.
    iDestruct "na" as "[oh [rb wb]]". destruct is_read as [n is_read].
    iMod (read_bank_begin with "rb guard G") as "[rim rb]"; [apply is_read|].
    iModIntro. iExists n. iFrame "rim rb W". iSplit; [done|].
    rewrite (erase_count_map_same_update_read_count _ _ _ _ _ is_read).
    iFrame "oh". by iApply (write_bank_no_op with "wb").
  Qed.

  Lemma na_read_end ι l cells v σ Gx :
    points_to_r_intermediate ι l cells v Gx -∗ non_atomic_map ι σ -∗ W ==∗
        ∃ n , ⌜ σ !! l = Some (RSt n, v) ∧ n ≥ 1 ⌝
        ∗ sm Gx
        ∗ non_atomic_map ι (<[ l := (RSt (n - 1), v) ]> σ) ∗ W.
  Proof.
    rewrite non_atomic_map_unseal /non_atomic_map_def.
    iIntros "ptr [oh [rb wb]] W".
    iMod (read_bank_end ι σ l cells v Gx with "rb ptr oh W")
      as (n) "[G [%Hσ [rb [oh W]]]]".
    destruct Hσ as [Hn is_read].
    iModIntro. iExists n. iFrame "G W". iSplit; [by iPureIntro|].
    rewrite (erase_count_map_same_update_read_count _ _ _ _ _ is_read).
    iFrame "oh rb". by iApply (write_bank_no_op with "wb").
  Qed.

  Lemma atomic_write ι l v v' σ :
    (inl l @↦[ι] inr v) -∗ non_atomic_map ι σ -∗ W ==∗
        ⌜ σ !! l = Some (RSt 0, v) ⌝
        ∗ (inl l @↦[ι] inr v')
        ∗ non_atomic_map ι (<[ l := (RSt 0, v') ]> σ) ∗ W.
  Proof.
    iIntros "pt h W".
    iMod (na_write_begin with "pt h W") as "[%sig [pt [heap W]]]".
    iMod (na_write_finish _ _ v' with "pt heap") as "[%sig2 [pt heap]]".
    iModIntro. iFrame "pt W". rewrite insert_insert_eq. iFrame "heap".
    iPureIntro. apply sig.
  Qed.

  (** The original was [|={E}=> ▷ |={E}=>]; the step came from
    [na_write_finish_guarded_cells]. *)
  Lemma atomic_write_guarded_cells `{!EqDecision V} ι l v cells c v' σ Gx :
    (sm Gx &&{W}&&> inl l @↦[ι][^ cells] inl c) -∗ sm Gx -∗
      (inr c @↦[ι] inr v) -∗ non_atomic_map ι σ -∗ W ==∗
        ⌜ σ !! l = Some (RSt 0, v) ⌝
        ∗ sm Gx
        ∗ (inr c @↦[ι] inr v')
        ∗ non_atomic_map ι (<[ l := (RSt 0, v') ]> σ) ∗ W.
  Proof.
    iIntros "#guard G pt h W".
    iMod (na_write_begin_guarded_cells with "guard G pt h W")
      as "[%sig [pt [heap W]]]".
    iMod (na_write_finish_guarded_cells _ _ _ _ v' with "pt heap W")
      as "[%sig2 [G [pt [heap W]]]]".
    iModIntro. iFrame "pt G W". rewrite insert_insert_eq. iFrame "heap".
    iPureIntro. apply sig.
  Qed.

  Lemma atomic_read `{!EqDecision V} ι l cells v σ (G : iProp Σ) :
    (G &&{W}&&> (inl l @↦[ι][^ cells] inr v)) -∗ G -∗
      non_atomic_map ι σ -∗ W -∗
        ∃ n , ⌜ σ !! l = Some (RSt n, v) ⌝ ∗ G ∗ non_atomic_map ι σ ∗ W.
  Proof.
    iIntros "#guard G na W".
    iDestruct (points_to_heap_readingN_guarded_all with "guard G na W")
      as "(%is_read & G & na & W)".
    destruct is_read as [n is_read]. iExists n. by iFrame.
  Qed.

  Lemma non_atomic_map_insert ι l v σ :
    (σ !! l = None) →
    non_atomic_map ι σ ==∗
      (inl l @↦[ι] inr v) ∗ non_atomic_map ι (<[ l := (RSt 0, v) ]> σ).
  Proof.
    unseal. intros not_in. iIntros "[oh [rb wb]]".
    iDestruct (read_bank_insert ι l v σ with "rb") as "rb"; [done|].
    iDestruct (write_bank_insert ι l v σ with "wb") as "wb"; [done|].
    iMod (cmap_alloc _ _ _ _ _ l v with "oh") as "[oh pt]".
    { by rewrite /erase_count_map lookup_fmap not_in. }
    replace ((<[l:=v]> (erase_count_map σ)) : gmap L V)
      with (erase_count_map (<[ l := (RSt 0, v) ]> σ));
      last by rewrite /erase_count_map fmap_insert.
    iModIntro. iFrame.
  Qed.

  Lemma non_atomic_map_delete ι l v σ :
    (inl l @↦[ι] inr v) -∗ non_atomic_map ι σ -∗ W ==∗
      ⌜ σ !! l = Some (RSt 0, v) ⌝ ∗ non_atomic_map ι (delete l σ) ∗ W.
  Proof.
    iIntros "pt na W".
    iDestruct (points_to_heap_reading0 with "pt na W")
      as "(%is_in & pt & na & W)".
    unseal. iDestruct "na" as "[oh [rb wb]]".
    iDestruct (read_bank_delete ι l v σ with "rb") as "rb"; [done|].
    iDestruct (write_bank_delete ι l v σ with "wb") as "wb"; [done|].
    iMod (cmap_delete with "oh pt") as "oh".
    replace ((delete l (erase_count_map σ)))
      with (erase_count_map (delete l σ));
      last by rewrite /erase_count_map fmap_delete.
    iModIntro. iFrame. done.
  Qed.

  (** ** The cell algebra

    These are thin wrappers around [nola.alerus.util.cellmap] and port
    verbatim; the original's [factoring_props.point_prop] is
    [nola.iris.point.point_prop]. *)

  Lemma pt_seq_cons ι lc cell cells cv :
      lc @↦[ι][^ cell :: cells] cv ⊣⊢
        lc @↦[ι] (inl cell) ∗ (inr cell) @↦[ι][^ cells] cv.
  Proof. unseal. done. Qed.

  Lemma pt_seq_cons_and ι lc cell cells cv :
      lc @↦[ι] (inl cell) ∧ (inr cell) @↦[ι][^cells] cv ⊢
        lc @↦[ι][^ cell :: cells] cv.
  Proof. unseal. apply cmap_pt_and_cons. Qed.

  Lemma pt_seq_cons_back_and ι lc cell cells cv :
      lc @↦[ι][^cells] (inl cell) ∧ (inr cell) @↦[ι] cv ⊢
        lc @↦[ι][^ cells ++ [cell]] cv.
  Proof.
      generalize lc. clear lc. induction cells; intro lc.
        - simpl. apply pt_seq_cons_and.
        - simpl. iIntros "And". iApply (pt_seq_cons_and). iSplit.
          + rewrite pt_seq_cons. iDestruct "And" as "[[$ _] _]".
          + iApply IHcells. iSplit.
            * rewrite pt_seq_cons. iDestruct "And" as "[[_ $] _]".
            * iDestruct "And" as "[_ $]".
  Qed.

  Lemma pt_seq_snoc ι lc cell cells cv :
    lc @↦[ι][^ cells ++ [cell]] cv ⊣⊢
      lc @↦[ι][^cells] inl cell ∗ inr cell @↦[ι] cv.
  Proof.
    rewrite points_to_seq_unseal /points_to_seq_def.
    by rewrite cellmap.cmap_pt_seq_cons_back.
  Qed.

  (** Cell-And *)
  Lemma pt_seq_app_and ι lc cells1 cell cells2 cv :
      lc @↦[ι][^cells1] (inl cell) ∧ (inr cell) @↦[ι][^cells2] cv
          ⊣⊢ lc @↦[ι][^ cells1 ++ cell :: cells2] cv.
  Proof.
      iSplit.
        - iStopProof. generalize lc. clear lc. induction cells1.
          + iIntros (lc) "_ A". iApply (pt_seq_cons_and with "A").
          + iIntros (lc) "_ A". simpl. iApply pt_seq_cons_and. iSplit.
            * iDestruct "A" as "[A _]". rewrite pt_seq_cons.
              iDestruct "A" as "[$ _]".
            * iApply IHcells1; first done. iSplit.
              -- iDestruct "A" as "[A _]". rewrite pt_seq_cons.
                 iDestruct "A" as "[_ $]".
              -- iDestruct "A" as "[_ $]".
        - iIntros "A". iSplit.
          + iStopProof. generalize lc. clear lc. induction cells1.
            * iIntros (lc). simpl. rewrite pt_seq_cons. iIntros "[$ _]".
            * iIntros (lc). simpl. do 2 rewrite pt_seq_cons.
              iIntros "[A B]". iFrame "A". iApply IHcells1. iFrame "B".
          + iStopProof. generalize lc. clear lc. induction cells1.
            * iIntros (lc). simpl. rewrite pt_seq_cons. iIntros "[_ $]".
            * iIntros (lc). simpl. rewrite pt_seq_cons. iIntros "[_ B]".
              iApply IHcells1. iFrame "B".
  Qed.

  (** Cell-Sep *)
  Lemma pt_seq_app_sep ι lc cells1 cell cells2 cv :
      lc @↦[ι][^cells1] (inl cell) ∗ (inr cell) @↦[ι][^cells2] cv
          ⊣⊢ lc @↦[ι][^ cells1 ++ cell :: cells2] cv.
  Proof.
      iSplit.
        - iIntros "[A B]". iApply pt_seq_app_and. iSplit; iFrame.
        - iIntros "A".
          iStopProof. generalize lc. clear lc. induction cells1.
          + iIntros (lc). simpl. rewrite pt_seq_cons. iIntros "$".
          + iIntros (lc). simpl. do 2 rewrite pt_seq_cons. iIntros "[$ B]".
            iApply IHcells1. iFrame "B".
  Qed.

  Lemma pt_seq_andM_sepM ι (rows: gmap L ((list cell_id) * (cell_id + V))) :
      ([∧ map] l ↦ '(cells, cv) ∈ rows, (inl l) @↦[ι][^cells] cv)%I ⊢
      [∗ map] l ↦ '(cells, cv) ∈ rows, (inl l) @↦[ι][^cells] cv.
  Proof. unseal. apply cmap_andM_sepM. Qed.

  Local Lemma pt_untether' ι lc cell :
      lc @↦[ι] (inl cell) ==∗
        ∃ (v: V), lc @↦[ι] (inr v)
          ∗ (∀ l cells, inl l @↦[ι][^ cells] inr v ==∗
               inl l @↦[ι][^ cells] inl cell).
  Proof.
    unseal. iIntros "pts". iMod (cmap_untether with "pts") as (v) "[pts back]".
    iModIntro. iExists v. rewrite pt_seq_singleton. iFrame "pts".
    iIntros (l cells) "pt". by iMod (cmap_retether with "pt back").
  Qed.

  Lemma pt_untether ι lc cells cell :
      lc @↦[ι][^cells] (inl cell) ==∗
        ∃ (v: V), lc @↦[ι][^cells] (inr v)
          ∗ (∀ l cells, inl l @↦[ι][^ cells] inr v ==∗
               inl l @↦[ι][^ cells] inl cell).
  Proof.
      destruct (cellmap.case_last_c cell_id cells)
        as [[_ Hcells]|[prefix [last [_ Hcells]]]].
       - subst cells. apply pt_untether'.
       - subst cells. rewrite pt_seq_snoc. iIntros "[A B]".
         iMod (pt_untether' with "B") as (v) "[B back]".
         iModIntro. iExists v. rewrite pt_seq_snoc. iFrame.
  Qed.

  Lemma pt_seq_point_prop ι lc cells cv :
      point_prop (lc @↦[ι][^ cells] cv).
  Proof. unseal. apply cmap_pt_seq_point_prop. Qed.

  (** Cell-Fresh *)
  Lemma pt_alloc_cell' ι lc cv :
      lc @↦[ι] cv ==∗ ∃ c, lc @↦[ι][^ [c]] cv.
  Proof.
    destruct lc as [l|c].
    - destruct cv as [c'|v].
      + (* untether the existing cell; insert the new cell; retether *)
        iIntros "pt". iMod (pt_untether with "pt") as (v) "[pt retether]".
        iMod (cmap_alloc_unt _ _ _ (ιh ι) v) as (c) "[pt2 unt]".
        iMod (cmap_retether with "[pt] unt") as "pt". { unseal. iFrame. }
        iDestruct ("retether" $! l [c] with "[pt pt2]") as "J".
          { unseal. rewrite cmap_pt_seq_cons. rewrite pt_seq_singleton. iFrame. }
        iExists c. done.
      + (* insert new cell immediately *)
        iIntros "pt".
        iMod (cmap_alloc_unt _ _ _ (ιh ι) v) as (c) "[pt2 unt]".
        iMod (cmap_retether with "[pt] unt") as "pt". { unseal. iFrame. }
        iModIntro. iExists c. unseal. rewrite pt_seq_singleton. iFrame.
    - iIntros "pt". unseal.
      iMod (cmap_alloc_cell_after_cell with "pt") as (new_c) "[pt1 pt2]".
      iModIntro. iExists new_c. iFrame.
  Qed.

  Lemma pt_alloc_cell ι lc cells cv :
      lc @↦[ι][^ cells] cv ==∗ ∃ c, lc @↦[ι][^ c :: cells] cv.
  Proof.
      destruct cells as [|cell cells].
      - apply pt_alloc_cell'.
      - iIntros "a". rewrite pt_seq_cons. iDestruct "a" as "[pt rest]".
        iMod (pt_alloc_cell' with "pt") as (c) "pt".
        iModIntro. iExists c.
        do 3 rewrite pt_seq_cons. iDestruct "pt" as "[$ $]". iFrame.
  Qed.

  Lemma pt_delete_cell ι l c cells cv :
      inl l @↦[ι][^ c :: cells] cv ==∗ inl l @↦[ι][^ cells] cv.
  Proof.
      destruct cells as [|cell cells].
      - iIntros "pt".
        unseal. rewrite !cmap_pt_seq_cons. rewrite !pt_seq_singleton.
        iDestruct "pt" as "[pt1 pt2]".
        by iMod (cmap_delete_cell with "pt1 pt2") as "pt".
      - iIntros "pt".
        unseal. rewrite !cmap_pt_seq_cons. rewrite !pt_seq_singleton.
        iDestruct "pt" as "[pt1 [pt2 pt3]]".
        iMod (cmap_delete_cell with "pt1 pt2") as "pt".
        by iFrame.
  Qed.

End NonAtomicMap.

Global Notation "l @↦[ ι ][^ cells ] v" := (points_to_seq ι l cells v)
    (at level 20, format "l  @↦[ ι ][^ cells ]  v") : bi_scope.

Global Notation "l @↦[ ι ] v" := (points_to_seq ι l [] v)
    (at level 20, format "l  @↦[ ι ]  v") : bi_scope.

(** ** Allocation independent of the interpretation

  [non_atomic_map ι ∅] is independent of [NaSem]: the read and write banks are
  indexed by the (empty) heap, so the [na_sem]-carrying big separating
  conjunctions are vacuous.  Stating the allocation with the [NaSem] instance
  universally quantified *inside* lets a client fix the interpretation after
  the ghost names exist - which it must, since the interpretation of a
  points-to formula mentions the very name allocated here.  Compare
  [nola.iris.sinv.sinv_wsat_alloc]. *)
Section NonAtomicMapAlloc.
  Context `{!EqDecision L, !Countable L}.
  Context `{!Inhabited V}.
  Context {Σ: gFunctors} {FML : oFunctor}.
  Context `{!na_logicG L V FML Σ}.

  Lemma non_atomic_map_alloc_empty_any :
    ⊢ |==> ∃ ι, ∀ naS : NaSem FML Σ, non_atomic_map (NaSem0:=naS) ι ∅.
  Proof.
    iMod (cmap_init) as (ιh0) "H".
    iMod (@own_alloc Σ _ na2_inG (gmap_view_auth (DfracOwn 1) ∅))
      as (ιi0) "H2". { apply gmap_view_auth_valid. }
    iMod (@own_alloc Σ _ na3_inG (gmap_view_auth (DfracOwn 1) ∅))
      as (ιj0) "H3". { apply gmap_view_auth_valid. }
    iModIntro. iExists (prod_encode ιh0 (prod_encode ιi0 ιj0)). iIntros (naS).
    rewrite non_atomic_map_unseal /non_atomic_map_def /read_bank /write_bank
      /ιh /ιi /ιj /ιf1 /ιf2.
    repeat (rewrite prod_decode_encode_fst || rewrite prod_decode_encode_snd).
    replace (erase_count_map ∅) with (∅: gmap L V) by done. iFrame "H".
    iSplitL "H2".
    - iExists ∅. iFrame. iSplit; [|done]. iPureIntro.
      rewrite /counts_agree_r /heap_count_r /m_count=> l.
      by rewrite lookup_empty.
    - iExists ∅. iFrame. iSplit; [|done]. iPureIntro.
      rewrite /counts_agree_w /heap_count_w /m_count=> l.
      by rewrite lookup_empty.
  Qed.
End NonAtomicMapAlloc.
