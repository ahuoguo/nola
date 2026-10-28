(** * Storage-protocol types, later-free

  Ported from VerusBelt ([typing/protocol.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), over the later-free storage protocol of
  [nola/verus_halt/storage_protocol_logic.v].

  ** What changed, and why

  *** [storable_ty] keeps its depth pair but loses its receipt

  Upstream a storable value is [ty_gho ty x d g tid ∗ ⧖(S d `max` g)]: the
  type's ghost assertion *plus a persistent time receipt* pinning the two
  depth indices, because the protocol's invariant hands the contents back
  under a [▷] and the client needs the receipt to strip it.  Later-free
  there is no [▷] to strip, so the receipt is gone and [storable_ty] is the
  bare ghost assertion at the depths the value records.  The depth pair
  itself stays - [storableₛ]'s interpretation is [~~𝔄 * (nat * nat)] here as
  upstream, and the three rules still speak of it - because the pair is what
  lets a *stored* value be read back at depths unrelated to the reader's.

  *** The protocol's state is a world satisfaction held in an invariant

  [storage_protocol_logic.v] threads [sp_wsat γ f] by hand, as [box_wsat] and
  [shr_wsat] are threaded.  A *type* cannot do that: [typed_instr] fixes the
  world satisfaction to [verus_halt_wsat].  So [storage_resource_ty] holds
  the protocol's state in a [dinv_fml] - Nola's later-free simple invariant,
  whose world satisfaction sits inside [verus_halt_WGuard] - and the rules
  reach it through [dinv_fml_acc_at] (for an owned resource) or
  [dinv_fml_guard_any] (for a shared one).  That is the exact later-free
  counterpart of upstream's [fupd_mask_subseteq {[γ]}], and it is why the
  side condition [{[γ]} ⊆ ↑NllftG] disappears from every rule.

  [guard_wsat_trans] in [nola/bi/guard.v] is what makes the shared case go
  through: a guard taken over [sp_wsat γ f] becomes a guard over
  [verus_halt_WGuard], because the invariant turns the latter into the
  former reversibly.  Leaf has to do this with [guards_from_ownI] and a
  [▷^n] bookkeeping pass; here it is one lemma with no indices.

  *** Only the client's [own]s are asked for as formulas

  A constructor's semantics is a fixed function of selector, data and
  children ([typing/model.v]'s [Ecsem]), so it cannot produce an [own] at a
  camera the *client* chose, and [verus_haltCON] is one global signature.
  [typing/ra.v] meets the same wall and answers it with [RaFml]: ask for the
  formula as a class with its semantics pinned, and leave it to whoever has a
  concrete [CON].  [SpFml] below is that class, and it asks for exactly two
  things - the protocol's authority and a share of its state.  Everything
  else is built from [TypeFml]'s own constructors: the protocol's world
  satisfaction is an [exs_fml] over [sp_authx], [pure_fml] and the stored
  type's formulas, and [sp_sto] needs no constructor at all, since
  [sp_sto γ f] is [⌜wf_prop_map f⌝ ∗ sp_own γ ε] and the pure conjunct is
  *provable* here rather than assumed.

  *** The exchanges against a shared resource

  [typed_sp_exchange_with_shr] and its nondeterministic sibling need
  [sp_own γ q] (from a shared borrow, hence behind a guard) and
  [sp_wsat γ f] (from the invariant, hence behind the world satisfaction
  that guard closes over) *at the same time*, and two guards over one
  world satisfaction cannot both be open: [guard_open_two] reaches the
  non-separating conjunction and no further, exactly as Leaf's
  [lguards_open_two_simultaneously] does.  What separates the two again is
  [nola/verus_halt/own_sep.v]'s [own_auth_frag_sep] - the half of Leaf's
  [guarding/own_and_own_sep.v] Iris never upstreamed, proved here rather
  than waited for - and [storage_protocol_logic.v]'s
  [sp_exchange_with_guard] is the result.

  [typed_sp_validate_with_shr] needs no such thing: a unique borrow is
  opened by moving its contents *out* of the world satisfaction rather
  than by a guard, so the world comes back and the shared guard can be
  opened against what the unique borrow gave. *)

From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap.
From nola.verus_halt Require Import inved storage_protocol storage_protocol_logic.
From nola.iris Require Import guard.
From nola.verus_halt.lang.lib Require Import new_delete.
From nola.verus_halt.typing Require Import lft_contexts programs ghost own
  product tracked shr_bor uniq_bor uniq_util freeable_util type_context
  programs_util programs_util_own.
From nola.verus_halt.typing Require Export type ctx.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation WpwNotation.

Implicit Type 𝔄 𝔅: syn_type.

Section Storable.
  Context `{!typeG FML Σ}.

  (** ** [storable_ty]

    Upstream's [gt_gho] is [ty_gho ty x0 d g tid ∗ ⧖(S d `max` g)].  The
    receipt is the whole of what is dropped. *)
  Program Definition storable_ty {𝔄} (ty: type 𝔄) : ghost_type (storableₛ 𝔄) :=
    {| gt_ghox x tid :=
         let '(x0, dg) := x in ty.(ty_ghox) x0 dg.1 dg.2 tid |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.

  Lemma storable_ty_gho {𝔄} (ty: type 𝔄) x d g tid :
    ty_gho (storable_ty ty) x d g tid ⊣⊢ ty_gho ty x.1 x.2.1 x.2.2 tid.
  Proof. by destruct x as [x0 [d0 g0]]. Qed.

  (** [storable_ty] holds exactly [ty]'s ghost assertion at the depths the
    value records, so the two thread-locality instances are [ty]'s read at
    those depths.  [Send] still asks for [Sync], for upstream's reason:
    [send_change_tid] may shift the depth by an offset, and the value here
    *names* its depths, so the shift would change the value. *)
  Global Instance storable_ty_send {𝔄} (ty : type 𝔄) :
    Send ty → Sync ty → Send (storable_ty ty).
  Proof.
    move=> Hsend Hsync. split; [done|].
    move=> tid tid' [x0 [d0 g0]] d g G κs.
    have [_ [Hg _]] := sync_tid (ty:=ty) tid tid' x0 d0 g0.
    iIntros "_ _ lfts _ K A $ !>". iExists (x0, (d0, g0)), 0%nat.
    iFrame "lfts K". iSplit; [|done].
    rewrite !storable_ty_gho /=. by rewrite -Hg.
  Qed.

  Global Instance storable_ty_sync {𝔄} (ty : type 𝔄) :
    Sync ty → Sync (storable_ty ty).
  Proof.
    move=> Hsync tid tid' [x0 [d0 g0]] d g.
    have [_ [Hg _]] := Hsync tid tid' x0 d0 g0.
    split; [done|]. split; [exact Hg|done].
  Qed.

  Global Instance storable_ty_copy {𝔄} (ty : type 𝔄) :
    Copy ty → Copy (storable_ty ty).
  Proof.
    move=> [Hpers Hconc]. split.
    - move=> [x0 [d0 g0]] *. rewrite storable_ty_gho /=. exact _.
    - move=> [x0 [d0 g0]] *. rewrite storable_ty_gho /=. by iIntros "_".
  Qed.

  (** ** The three storable rules

    All three are upstream's, with the receipt bookkeeping removed.  The
    *value*-level statements are unchanged, pair and all. *)

  Lemma storable_new {𝔄} E L I p (ty : type 𝔄) :
    typed_instr E L I
      +[p ◁ own_ptr 0 (tracked_ty ty)]
      (Seq Skip Skip)
      (const +[p ◁ own_ptr 0 (storable_ty ty)])
      (λ post '-[(l, x)], λ mask π, ∀ l n, post -[(l, (x, n))] mask π).
  Proof.
    apply typed_instr_of_skip_own_own_t; [done|done|].
    move=> l1 x1 d tid iκs post mask.
    iIntros "_ _ _ _ L I gho Obs $ !>". iExists d, (x1, (d, S d)).
    iFrame "L I". rewrite storable_ty_gho /=. iFrame "gho".
    iApply (proph_obs_impl with "Obs")=> ? Ha. apply Ha.
  Qed.

  Lemma storable_into_inner {𝔄} E L I p (ty : type 𝔄) :
    typed_instr E L I
      +[p ◁ own_ptr 0 (storable_ty ty)]
      (Seq Skip Skip)
      (const +[p ◁ own_ptr 0 (tracked_ty ty)])
      (λ post '-[(l, (x, n))], λ mask π, ∀ l, post -[(l, x)] mask π).
  Proof.
    apply typed_instr_of_skip_own_own_t; [done|done|].
    move=> l1 [x0 [d0 g0]] d tid iκs post mask.
    iIntros "_ _ _ _ L I gho Obs $ !>". iExists (d0 `max` g0), x0.
    iFrame "L I". rewrite storable_ty_gho /= tracked_ty_gho. iSplitL "gho".
    { iApply (ty_gho_depth_mono with "gho"); lia. }
    iApply (proph_obs_impl with "Obs")=> ? Ha. apply Ha.
  Qed.
  (** Upstream opens the shared borrow with credits to strip the [▷] that
    the guard's right-hand side carries, reads the persistent part out and
    puts it back.  Here the guard is later-free, so the opening is one
    [guard_acc] and the only work left is the one real difference between
    the two types: a [ghost_type]'s persistent part is [True], and
    [tracked_ty ty]'s is [ty]'s, so it has to be read off the ghost
    assertion ([ty_gho_pers_dup]) and stored ([store_ty_gho_pers]). *)
  Lemma storable_borrow {𝔄} κ E L I p (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p ◁ (&shr{κ} (storable_ty ty))]
      (Seq Skip Skip)
      (const +[p ◁ (&shr{κ} (tracked_ty ty))])
      (λ post '-[(l, (x, n))], λ mask π, ∀ l, post -[(l, x)] mask π).
  Proof.
    move=> Alv. apply typed_instr_of_skip.
    move=> [l [x0 [d0 g0]]] v d tid post mask iκs.
    iIntros "_ _ _ #E L I %Hp [gho %Hphys] #Obs W".
    iDestruct (shr_bor_gho_elim with "gho") as (dd gg Hdd Hgg)
      "#(cells & g & _)". simpl.
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (dguard_alive_sem with "g") as "#g0".
    iDestruct (guard_trans with "Alv g0") as "#G1".
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W")
      as "[Wg Wr]".
    iDestruct (guard_acc with "G1 L Wg") as "[inner →Wg]".
    iDestruct (ty_gho_pers_dup with "inner") as "[#pers inner]".
    iDestruct ("→Wg" with "inner") as "[Wg L]".
    iMod (store_ty_gho_pers ty x0 d0 g0 tid with "pers Wg") as "[Wg #St]".
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    iModIntro. iFrame "W L I". iExists -[(l, x0)]. iSplitL.
    - iSplitL; [|done]. iExists v, (S (d0 `max` g0)). iSplit; [done|]. iSplitR; [|done].
      iApply (shr_bor_gho_intro_st κ (tracked_ty ty) (l, x0)
        (S (d0 `max` g0)) (S (d0 `max` g0)) d0 g0 tid); [lia|lia| | |].
      + iExact "cells".
      + iExact "g".
      + iExact "St".
    - iApply (proph_obs_impl with "Obs")=> ? Ha. apply Ha.
  Qed.
End Storable.

Section StorageProtocol.
  Context `{!typeG FML Σ}.
  Context {𝔄 𝔅 ℭ : syn_type}.
  Context `{G𝔄: !inG Σ (@Ucmra' _ (~~𝔄) 𝔄_equiv 𝔄_dist 𝔄_pcore 𝔄_op 𝔄_valid 𝔄_validn 𝔄_unit 𝔄_mixin1 𝔄_mixin2 𝔄_mixin3)}.
  Context `{G𝔅: !inG Σ (@Ucmra' _ (~~𝔅) 𝔅_equiv 𝔅_dist 𝔅_pcore 𝔅_op 𝔅_valid 𝔅_validn 𝔅_unit 𝔅_mixin1 𝔅_mixin2 𝔅_mixin3)}.
  (** Upstream asks for a third [inG], on [~~ℭ].  All that is ever used of
    it is the equivalence [Proper_ty] is stated over and the unit
    [typed_sp_validate] names when the map is empty. *)
  Context `{ℭ_equiv : Equiv (~~ℭ)} `{ℭ_unit : Unit (~~ℭ)}.
  Context {R : SPRel (~~𝔄) (~~𝔅)}.
  Context `{equ_p: @Equivalence (~~𝔄) (≡)}.
  Context `{equ_b: @Equivalence (~~𝔅) (≡)}.
  Context {storage_mixin : StorageMixin (~~𝔄) (~~𝔅)}.
  Context `{sp_i: !sp_logicG storage_mixin Σ}.
  Context `{CountableK: @Countable K EqK}.
  Hypothesis (𝔄_const : ∀ (x : ~~𝔄) π1 π2, @vπ 𝔄 x π1 = @vπ 𝔄 x π2).
  Variable (tyC : ghost_type ℭ) (F : ~~𝔅 → gmap K (~~ℭ)).
  (** Upstream's [Proper_ty], at *every* candidate interpretation.  It has to
    be: the protocol's state is read inside a stored guard, which a shared
    borrow of [storage_resource_ty] holds, and a stored guard is a claim
    about every candidate ([typing/ctx.v]'s [dguard_of_all]). *)
  Hypothesis Proper_tyC : ∀ sem, alt_sem sem → ∀ tid,
    Proper ((≡) ==> (⊣⊢)) (λ c, sem (gt_ghox tyC c tid)).
  Context `{Proper_F: !Proper ((≡) ==> (≡)) F}.
  Hypothesis Fempty : F ε = ∅.
  Hypothesis Fcompose :
    ∀ a b, ✓(a ⋅ b) → F a ##ₘ F b ∧ F (a ⋅ b) = F a ∪ F b.

  (** ** The map a base value denotes, read at a candidate *)
  Definition sp_fun (sem : FML $oi Σ → iProp Σ) (tid : thread_id)
    : (~~𝔅) → iProp Σ := λ s, ([∗ map] _ ↦ c ∈ F s, sem (gt_ghox tyC c tid))%I.

  (** Upstream discharges [wf_prop_map] inside [typed_sp_alloc], from
    [Proper_ty], [Fempty] and [Fcompose].  Here it holds at every candidate
    and so is proved once, which is also what lets [sp_sto] be *derived*
    rather than asked for as a formula: [sp_sto γ f] is
    [⌜wf_prop_map f⌝ ∗ sp_own γ ε] and the pure conjunct is now a theorem. *)
  Lemma sp_fun_wf {sem} (H : alt_sem sem) tid : wf_prop_map (sp_fun sem tid).
  Proof.
    rewrite /wf_prop_map /sp_fun. split_and!.
    - move=> x y Heq. apply big_opM_proper_2; [by apply Proper_F|].
      move=> ? c1 c2 _ _ Hc. by apply (Proper_tyC sem H tid).
    - rewrite Fempty. by rewrite big_sepM_empty.
    - move=> b1 b2 Hv. have [Hdisj Heq] := Fcompose b1 b2 Hv.
      rewrite Heq. by rewrite big_sepM_union.
  Qed.

  Lemma sp_sto_of_own {sem} (H : alt_sem sem) tid γ p :
    sp_own γ p ⊢ sp_sto γ (sp_fun sem tid) ∗ sp_own γ p.
  Proof.
    have Heq : (ε : ~~𝔄) ⋅ p ≡ p :=
      protocol_unit_left_id _ _ storage_mixin p.
    rewrite /sp_sto -{1}(sp_own_proper γ _ _ Heq) sp_own_op.
    iIntros "[$ $]". iPureIntro. exact (sp_fun_wf H tid).
  Qed.

  (** ** The protocol's world satisfaction, as a formula

    Everything but [sp_authx] is [TypeFml]'s own: a separating fold over the
    stored type's formulas, a pure conjunct, and [exs_fml] over the pair. *)
  Definition big_sep_fml (l : list (FML $oi Σ)) : FML $oi Σ :=
    foldr bor_sep empty_fml l.

  Lemma big_sep_fml_sem_at {sem} (H : alt_sem sem) l :
    sem (big_sep_fml l) ⊣⊢ [∗ list] Px ∈ l, sem Px.
  Proof.
    induction l as [|Px l IH]; [by rewrite /= (empty_sem_at H)|].
    by rewrite /= (sep_sem_at H) IH.
  Qed.

  Definition sp_cells_fml (tid : thread_id) (s : ~~𝔅) : FML $oi Σ :=
    big_sep_fml ((λ kc, gt_ghox tyC kc.2 tid) <$> map_to_list (F s)).

  Lemma sp_cells_fml_sem_at {sem} (H : alt_sem sem) tid s :
    sem (sp_cells_fml tid s) ⊣⊢ sp_fun sem tid s.
  Proof.
    rewrite /sp_cells_fml /sp_fun (big_sep_fml_sem_at H) big_opM_map_to_list
      big_sepL_fmap //.
  Qed.

  (** ** The one thing the formula language cannot supply

    [typing/ra.v]'s [RaFml], for the protocol: the authority and a share. *)
  Class SpFml := {
    sp_authx : gname → (~~𝔄) → FML $oi Σ;
    sp_authx_sem_at {sem} : alt_sem sem → ∀ γ p,
      sem (sp_authx γ p) ⊣⊢ own γ (● Inved p);
    sp_ownx : gname → (~~𝔄) → FML $oi Σ;
    sp_ownx_sem_at {sem} : alt_sem sem → ∀ γ p,
      sem (sp_ownx γ p) ⊣⊢ sp_own γ p;
  }.
  Context `{SpFml0 : !SpFml}.

  Lemma sp_ownx_sem γ p : bor_sem (sp_ownx γ p) ⊣⊢ sp_own γ p.
  Proof. exact (sp_ownx_sem_at alt_here γ p). Qed.

  Definition sp_wsat_fml (γ : gname) (tid : thread_id) : FML $oi Σ :=
    exs_fml (𝔄 := 𝔄 * 𝔅) (λ pb,
      (sp_authx γ pb.1 ∗
        (pure_fml (sp_rel pb.1 pb.2) ∗ sp_cells_fml tid pb.2))%FML).

  Lemma sp_wsat_fml_sem_at {sem} (H : alt_sem sem) γ tid :
    sem (sp_wsat_fml γ tid) ⊣⊢ sp_wsat γ (sp_fun sem tid).
  Proof.
    rewrite /sp_wsat_fml /sp_wsat (exs_sem_at H). f_equiv=> pb.
    by rewrite !(sep_sem_at H) (pure_sem_at H) (sp_authx_sem_at H)
      (sp_cells_fml_sem_at H).
  Qed.

  (** ** The storage-resource type

    Upstream's ghost assertion is
    [⌜{[γ]} ⊆ ↑NllftG⌝ ∗ sp_sto γ f ∗ sp_own γ p]: a namespace side
    condition, the protocol's persistent part, and a share.  Here the
    namespace is gone with the mask, [sp_sto] is derivable
    ([sp_sto_of_own]), and what takes their place is the *invariant token*
    that makes [sp_wsat γ f] reachable from the ambient world. *)
  Set Printing Coercions.
  Program Definition storage_resource_ty : type (ghostₛ (positiveₛ * 𝔄)) :=
    ty_of_gt ({|
      gt_ghox v tid :=
        (dinv_fml (sp_wsat_fml v.1 tid) ∗ sp_ownx v.1 v.2)%FML;
    |} : ghost_type (ghostₛ (positiveₛ * 𝔄))).
  Next Obligation.
    move=> v. unfold indep_interp_of_syn_type in v.
    fold indep_interp_of_syn_type in v. destruct v as [γ v].
    move=> π1 π2. specialize (𝔄_const v π1 π2). simpl. by f_equal.
  Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.

  (** Unfolding it, at every candidate.  Both conjuncts are
    interpretation-independent, which is what lets a *shared* borrow of this
    type be opened at a candidate. *)
  Lemma storage_resource_ty_gho_at {sem} (H : alt_sem sem) v d g tid :
    sem (ty_ghox storage_resource_ty v d g tid) ⊣⊢
      @dinv_tok FML Σ verus_halt_dinvGS (sp_wsat_fml v.1 tid) ∗
      sp_own v.1 v.2.
  Proof.
    destruct v as [γ p].
    by rewrite /= (sep_sem_at H) (dinv_fml_sem_at_any (alt_sem_any H))
      (sp_ownx_sem_at H).
  Qed.
  Lemma storage_resource_ty_gho v d g tid :
    ty_gho storage_resource_ty v d g tid ⊣⊢
      @dinv_tok FML Σ verus_halt_dinvGS (sp_wsat_fml v.1 tid) ∗
      sp_own v.1 v.2.
  Proof. exact (storage_resource_ty_gho_at alt_here v d g tid). Qed.

  (** ** Reaching the protocol's world satisfaction

    The invariant token guards its contents against anything
    ([dinv_fml_guard_at]), so the protocol's world satisfaction is a guard's
    right-hand side at every candidate.  This is what [guard_wsat_trans]
    then composes with [sp_guard]. *)
  Lemma sp_dinv_guard_at {sem} (H : alt_sem sem) {R0 : iProp Σ} γ tid :
    @dinv_tok FML Σ verus_halt_dinvGS (sp_wsat_fml γ tid) ⊢
      (R0 &&{alt_WGuard sem}&&> sp_wsat γ (sp_fun sem tid)).
  Proof.
    iIntros "i".
    iDestruct (dinv_fml_guard_at H (Px := sp_wsat_fml γ tid) with "[i]")
      as "#g".
    { by iApply (bi.equiv_entails_1_2 _ _
        (dinv_fml_sem_at_any (alt_sem_any H) (sp_wsat_fml γ tid))). }
    iApply (guard_rhs_iff (sp_wsat_fml_sem_at H γ tid)).
    iApply (guard_trans (Q := True%I) with "[] g"). iApply guard_true.
  Qed.

  (** The owned case: open the invariant straight out of the ambient world.
    This is upstream's [fupd_mask_subseteq {[γ]}], later-free. *)
  Lemma sp_wsat_acc γ tid :
    @dinv_tok FML Σ verus_halt_dinvGS (sp_wsat_fml γ tid) -∗
    verus_halt_wsat -∗
      sp_wsat γ (sp_fun bor_sem tid) ∗
      (sp_wsat γ (sp_fun bor_sem tid) -∗ verus_halt_wsat).
  Proof.
    iIntros "#i W".
    iDestruct (sp_dinv_guard_at alt_here (R0 := True%I) γ tid with "i")
      as "#g".
    rewrite alt_WGuard_here.
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W")
      as "[Wg Wr]".
    iDestruct (guard_acc with "g [//] Wg") as "[$ →Wg]".
    iIntros "SP". iDestruct ("→Wg" with "SP") as "[Wg _]".
    iApply (wsat_join (W:=verus_halt_wsat) with "Wg Wr").
  Qed.

  (** ** [Send] and [Sync]

    Upstream needs [Send tyC] for both; here only [Sync tyC] is used, since
    all that changes with the thread is the formula the invariant names. *)
  Lemma sp_cells_fml_tid (Hsync : Sync (ty_of_gt tyC)) tid tid' s :
    sp_cells_fml tid s ≡ sp_cells_fml tid' s.
  Proof.
    rewrite /sp_cells_fml /big_sep_fml.
    induction (map_to_list (F s)) as [|[k c] l IH]; [done|]. simpl.
    f_equiv; [|exact IH]. have [_ [Hg _]] := Hsync tid tid' c 0 0. exact Hg.
  Qed.

  Lemma sp_wsat_fml_tid (Hsync : Sync (ty_of_gt tyC)) γ tid tid' :
    sp_wsat_fml γ tid ≡ sp_wsat_fml γ tid'.
  Proof.
    rewrite /sp_wsat_fml. f_equiv=> pb. f_equiv. f_equiv.
    exact (sp_cells_fml_tid Hsync tid tid' pb.2).
  Qed.

  Global Instance storage_resource_ty_sync :
    Sync (ty_of_gt tyC) → Sync storage_resource_ty.
  Proof.
    move=> Hsync tid tid' [γ p] d g. split; [done|]. split; [|done].
    simpl. f_equiv.
    exact (ne_proper dinv_fml _ _ (sp_wsat_fml_tid Hsync γ tid tid')).
  Qed.

  Global Instance storage_resource_ty_send :
    Sync (ty_of_gt tyC) → Send storage_resource_ty.
  Proof.
    move=> Hsync. have Hs := storage_resource_ty_sync Hsync.
    split; [done|]. move=> tid tid' [γ p] d g G κs.
    have [_ [Hg _]] :=
      @sync_tid _ _ _ _ storage_resource_ty Hs tid tid' (γ, p) d g.
    iIntros "_ _ lfts _ K A $ !>". iExists (γ, p), 0%nat.
    iFrame "lfts K". iSplit; [|done]. rewrite Nat.add_0_r. by rewrite -Hg.
  Qed.

  Lemma storage_resource_resolve E L :
    resolve E L storage_resource_ty (const (const True)).
  Proof. apply resolve_just. Qed.

  (** ** The rules

    Every one of them is upstream's, with three things gone: the mask
    [{[γ]} ⊆ ↑NllftG], the time receipts, and the [▷] over [f].  What takes
    their place is [sp_wsat_acc]: the invariant token the type carries hands
    the protocol's world satisfaction out of the ambient one and takes it
    back.  The *statements* - the predicate transformers included - are
    unchanged. *)

  Notation "SP_Alloc: p s" := (new [ #0])%E
    (at level 102, p,s at level 1): expr_scope.

  Lemma typed_sp_alloc (p s : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
    +[p ◁ own_ptr 0 (ghost_ty tyA); s ◁ own_ptr 0 (tracked_ty (ty_of_gt tyC))]
    (SP_Alloc: p s)
    (λ v, +[v ◁ own_ptr 0 storage_resource_ty])
    (λ post '-[(_, a); (_, c)], λ mask π, ∃ b k,
      F b = {[ k := c ]} ∧ sp_rel a b ∧ ∀ l γ, post -[(l, (γ, a))] mask π).
  Proof.
    move=> tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl a] [[pl' c] []]].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs")
      as "(%π & %b & %k & %Hb & %Hrel & _)"=>//.
    iDestruct "TY" as "(_ & TY' & _)".
    iDestruct "TY'" as "(%v' & %d' & % & Hgho' & %)".
    destruct d' as [|d'];
      [by iDestruct (false_fml_sem_1 with "Hgho'") as "[]"|].
    rewrite own_ptr_gho /= tracked_ty_gho.
    iDestruct "Hgho'" as "(_ & _ & HghoC)".
    iMod (sp_alloc a b (sp_fun bor_sem tid) Hrel (sp_fun_wf alt_here tid)
      with "[HghoC]") as "(%γ & _ & own & SP)".
    { rewrite /sp_fun Hb big_sepM_singleton. iExact "HghoC". }
    iDestruct (dinv_fml_alloc (Px := sp_wsat_fml γ tid) with "[SP]") as "A".
    { by iApply (bi.equiv_entails_1_2 _ _
        (sp_wsat_fml_sem_at alt_here γ tid)). }
    iDestruct (bupdw_incl (W:=verus_halt_wsat) with "A") as "A'".
    iMod ("A'" with "W") as "[W #i]". rewrite dinv_fml_sem_1.
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, (γ, a))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
      rewrite /ty_own own_ptr_gho /= storage_resource_ty_gho /=.
      rewrite heap_mapsto_fancy_vec_nil freeable_sz_full.
      iSplitL; [|done]. iFrame "↦ i own". by iRight.
    - iApply (proph_obs_impl with "Obs"). move=> ? [?[?[?[? Ha]]]]. apply Ha.
  Qed.

  Notation "SP_Join: a b" := (new [ #0])%E
    (at level 102, a,b at level 1): expr_scope.

  Lemma typed_sp_join (p1 p2 : path) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty; p2 ◁ own_ptr 0 storage_resource_ty]
    (SP_Join: p1 p2)
    (λ v, +[v ◁ own_ptr 0 storage_resource_ty])
    (λ post '-[(_, (γ1, a1)); (_, (γ2, a2))], λ mask π,
      γ1 = γ2 ∧ ∀ l, post -[(l, (γ1, a1 ⋅ a2))] mask π).
  Proof.
    move=> tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs"=>/=.
    destruct vπl as [[pl1 [γ1 a1]] [[pl2 [γ2 a2]] []]].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & _)"=>//.
    iDestruct "TY" as "(H1 & H2 & _)".
    iDestruct "H1" as "(%v1 & %d1 & % & Hown1 & %)".
    iDestruct "H2" as "(%v2 & %d2 & % & Hown2 & %)".
    destruct d1 as [|d1];
      [by iDestruct (false_fml_sem_1 with "Hown1") as "[]"|].
    destruct d2 as [|d2];
      [by iDestruct (false_fml_sem_1 with "Hown2") as "[]"|].
    rewrite !own_ptr_gho /= !storage_resource_ty_gho /=.
    iDestruct "Hown1" as "(_ & _ & #i & own1)".
    iDestruct "Hown2" as "(_ & _ & _ & own2)".
    iAssert (sp_own γ1 (a1 ⋅ a2)) with "[own1 own2]" as "own".
    { rewrite sp_own_op. iFrame. }
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, (γ1, a1 ⋅ a2))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
      rewrite /ty_own own_ptr_gho /= storage_resource_ty_gho /=
        heap_mapsto_fancy_vec_nil freeable_sz_full.
      iSplitL; [|done]. iFrame "↦ i own". by iRight.
    - iApply (proph_obs_impl with "Obs"). by move=> ? [_ Ha].
  Qed.

  Notation "SP_Split: p p1 p2" := (new [ #0])%E
    (at level 102, p, p1, p2 at level 1): expr_scope.

  Lemma typed_sp_split (self p1 p2 : path) (ty : type 𝔄) E L I :
    typed_instr E L I
    +[self ◁ own_ptr 0 storage_resource_ty; p1 ◁ own_ptr 0 (ghost_ty ty);
      p2 ◁ own_ptr 0 (ghost_ty ty)]
    (SP_Split: self p1 p2)
    (λ v, +[v ◁ own_ptr 0 (prod_ty storage_resource_ty storage_resource_ty)])
    (λ post '-[(_, (γ, x)); (_, x1); (_, x2)], λ mask π,
      x = x1 ⋅ x2 ∧ ∀ l, post -[(l, ((γ, x1), (γ, x2)))] mask π).
  Proof.
    move=> tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs"=>/=.
    destruct vπl as [[pl [γ x]] [[plx1 x1] [[plx2 x2] []]]].
    simpl in x1, x2.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & -> & _)"=>//.
    iDestruct "TY" as "(H & _ & _ & _)".
    iDestruct "H" as "(%v & %d & % & Hown & %)".
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite own_ptr_gho /= storage_resource_ty_gho /= sp_own_op.
    iDestruct "Hown" as "(_ & _ & #i & own1 & own2)".
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, ((γ, x1), (γ, x2)))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
      rewrite /ty_own own_ptr_gho /= prod_ty_gho !storage_resource_ty_gho /=
        heap_mapsto_fancy_vec_nil freeable_sz_full.
      iSplitL; [|done]. iFrame "↦ i own1 own2". by iRight.
    - iApply (proph_obs_impl with "Obs"). by move=> ? [_ Ha].
  Qed.

  Notation "SP_Update: p1 p2" := (new [ #0])%E
    (at level 102, p1,p2 at level 1): expr_scope.

  Lemma typed_sp_update (p1 p2 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty; p2 ◁ own_ptr 0 (ghost_ty tyA)]
    (SP_Update: p1 p2)
    (λ v, +[v ◁ own_ptr 0 storage_resource_ty])
    (λ post '-[(_, (γ, p)); (_, new_p)], λ mask π,
      storage_protocol_update p new_p ∧ ∀ l, post -[(l, (γ, new_p))] mask π).
  Proof.
    move=> tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs"=>/=.
    destruct vπl as [[pl [γ p]] [[plnew_p new_p] []]]. simpl in γ,p,new_p.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & %upd & _)"=>//.
    iDestruct "TY" as "(H & _ & _)".
    iDestruct "H" as "(%v & %d & % & Hown & %)".
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite own_ptr_gho /= storage_resource_ty_gho /=.
    iDestruct "Hown" as "(_ & _ & #i & own)".
    iDestruct (sp_sto_of_own alt_here tid with "own") as "[#sto own]".
    iDestruct (sp_wsat_acc with "i W") as "[SP →W]".
    iMod (sp_update p new_p γ _ upd with "sto own SP") as "[own SP]".
    iDestruct ("→W" with "SP") as "W". iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, (γ, new_p))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
      rewrite /ty_own own_ptr_gho /= storage_resource_ty_gho /=
        heap_mapsto_fancy_vec_nil freeable_sz_full.
      iSplitL; [|done]. iFrame "↦ i own". by iRight.
    - iApply (proph_obs_impl with "Obs"). by move=> ? [_ Ha].
  Qed.

  Notation "SP_Exchange: p1 p2 p3 p4" := (new [ #0])%E
    (at level 102, p1,p2,p3,p4 at level 1): expr_scope.

  Lemma typed_sp_exchange (p1 p2 p3 p4 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty;
      p2 ◁ own_ptr 0 (tracked_ty (ty_of_gt tyC));
      p3 ◁ own_ptr 0 (ghost_ty tyA);
      p4 ◁ own_ptr 0 (ghost_ty (ty_of_gt tyC))]
    (SP_Exchange: p1 p2 p3 p4)
    (λ v, +[v ◁ own_ptr 0
      (prod_ty storage_resource_ty (tracked_ty (ty_of_gt tyC)))])
    (λ post '-[(_, (γ, p)); (_, s); (_, new_p); (_, new_s)], λ mask π,
      ∃ b new_b k, F b = {[ k := s ]} ∧ F new_b = {[ k := new_s ]} ∧
        storage_protocol_exchange p new_p b new_b ∧
        ∀ l, post -[(l, ((γ, new_p), new_s))] mask π).
  Proof.
    move=> tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs"=>/=.
    destruct vπl as
      [[pl [γ p]] [[pls s] [[plnew_p new_p] [[plnew_s new_s] []]]]].
    simpl in γ,p,s,new_p,new_s.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs")
      as "(%π & %b & %new_b & %k & %Hb & %Hnew_b & %exchng & _)"=>//.
    iDestruct "TY" as "(Hp & Hs & _ & _)".
    iDestruct "Hp" as "(%v & %d & % & Hown & %)".
    iDestruct "Hs" as "(%v0 & %d0 & % & Hown' & %)".
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    destruct d0 as [|d0];
      [by iDestruct (false_fml_sem_1 with "Hown'") as "[]"|].
    rewrite !own_ptr_gho /= storage_resource_ty_gho /= tracked_ty_gho.
    iDestruct "Hown" as "(_ & _ & #i & own)".
    iDestruct "Hown'" as "(_ & _ & HghoC)".
    iDestruct (sp_sto_of_own alt_here tid with "own") as "[#sto own]".
    iDestruct (sp_wsat_acc with "i W") as "[SP →W]".
    iMod (sp_exchange p new_p b new_b γ _ exchng with "sto own [HghoC] SP")
      as "[[own HghoC] SP]".
    { rewrite /sp_fun Hb big_sepM_singleton. iExact "HghoC". }
    rewrite /sp_fun Hnew_b big_sepM_singleton.
    iDestruct ("→W" with "SP") as "W". iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, ((γ, new_p), new_s))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
      rewrite /ty_own own_ptr_gho /= prod_ty_gho storage_resource_ty_gho
        tracked_ty_gho /= heap_mapsto_fancy_vec_nil freeable_sz_full.
      iSplitL; [|done]. iFrame "↦ i own HghoC". by iRight.
    - iApply (proph_obs_impl with "Obs"). by move=> ? [?[?[?[?[?[? Ha]]]]]].
  Qed.

  Notation "SP_Deposit: p1 p2 p3" := (new [ #0])%E
    (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_sp_deposit (p1 p2 p3 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty;
      p2 ◁ own_ptr 0 (tracked_ty (ty_of_gt tyC));
      p3 ◁ own_ptr 0 (ghost_ty tyA)]
    (SP_Deposit: p1 p2 p3)
    (λ v, +[v ◁ own_ptr 0 storage_resource_ty])
    (λ post '-[(_, (γ, p)); (_, s); (_, new_p)], λ mask π,
      ∃ b k, F b = {[ k := s ]} ∧ storage_protocol_deposit p new_p b ∧
        ∀ l, post -[(l, (γ, new_p))] mask π).
  Proof.
    move=> tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs"=>/=.
    destruct vπl as [[pl [γ p]] [[pls s] [[plnew_p new_p] []]]].
    simpl in γ,p,s,new_p.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs")
      as "(%π & %b & %k & %Hb & %dep & _)"=>//.
    iDestruct "TY" as "(Hp & Hs & _ & _)".
    iDestruct "Hp" as "(%v & %d & % & Hown & %)".
    iDestruct "Hs" as "(%v0 & %d0 & % & Hown' & %)".
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    destruct d0 as [|d0];
      [by iDestruct (false_fml_sem_1 with "Hown'") as "[]"|].
    rewrite !own_ptr_gho /= storage_resource_ty_gho /= tracked_ty_gho.
    iDestruct "Hown" as "(_ & _ & #i & own)".
    iDestruct "Hown'" as "(_ & _ & HghoC)".
    iDestruct (sp_sto_of_own alt_here tid with "own") as "[#sto own]".
    iDestruct (sp_wsat_acc with "i W") as "[SP →W]".
    iMod (sp_deposit p new_p b γ _ dep with "sto own [HghoC] SP")
      as "[own SP]".
    { rewrite /sp_fun Hb big_sepM_singleton. iExact "HghoC". }
    iDestruct ("→W" with "SP") as "W". iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, (γ, new_p))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
      rewrite /ty_own own_ptr_gho /= storage_resource_ty_gho /=
        heap_mapsto_fancy_vec_nil freeable_sz_full.
      iSplitL; [|done]. iFrame "↦ i own". by iRight.
    - iApply (proph_obs_impl with "Obs"). by move=> ? [?[?[?[? Ha]]]].
  Qed.

  Notation "SP_Withdraw: p1 p2 p3" := (new [ #0])%E
    (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_sp_withdraw (p1 p2 p3 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty; p2 ◁ own_ptr 0 (ghost_ty tyA);
      p3 ◁ own_ptr 0 (ghost_ty (ty_of_gt tyC))]
    (SP_Withdraw: p1 p2 p3)
    (λ v, +[v ◁ own_ptr 0
      (prod_ty storage_resource_ty (tracked_ty (ty_of_gt tyC)))])
    (λ post '-[(_, (γ, p)); (_, new_p); (_, new_s)], λ mask π,
      ∃ b k, F b = {[ k := new_s ]} ∧ storage_protocol_withdraw p new_p b ∧
        ∀ l, post -[(l, ((γ, new_p), new_s))] mask π).
  Proof.
    move=> tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs"=>/=.
    destruct vπl as [[pl [γ p]] [[plnew_p new_p] [[plnew_s new_s] []]]].
    simpl in γ,p,new_p,new_s.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs")
      as "(%π & %b & %k & %Hb & %wd & _)"=>//.
    iDestruct "TY" as "(Hp & _ & _ & _)".
    iDestruct "Hp" as "(%v & %d & % & Hown & %)".
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite own_ptr_gho /= storage_resource_ty_gho /=.
    iDestruct "Hown" as "(_ & _ & #i & own)".
    iDestruct (sp_sto_of_own alt_here tid with "own") as "[#sto own]".
    iDestruct (sp_wsat_acc with "i W") as "[SP →W]".
    iMod (sp_withdraw p new_p b γ _ wd with "sto own SP")
      as "[[own HghoC] SP]".
    rewrite /sp_fun Hb big_sepM_singleton.
    iDestruct ("→W" with "SP") as "W". iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, ((γ, new_p), new_s))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
      rewrite /ty_own own_ptr_gho /= prod_ty_gho storage_resource_ty_gho
        tracked_ty_gho /= heap_mapsto_fancy_vec_nil freeable_sz_full.
      iSplitL; [|done]. iFrame "↦ i own HghoC". by iRight.
    - iApply (proph_obs_impl with "Obs"). by move=> ? [?[?[?[? Ha]]]].
  Qed.

  Notation "SP_ExchangeNonDet: p1 p2 p3" := (new [ #0])%E
    (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_sp_exchange_nondeterministic (p1 p2 p3 : path) (n : nat)
      (ty : type (vecₛ (𝔄 * 𝔅) n)) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty;
      p2 ◁ own_ptr 0 (tracked_ty (ty_of_gt tyC));
      p3 ◁ own_ptr 0 (ghost_ty ty)]
    (SP_ExchangeNonDet: p1 p2 p3)
    (λ v, +[v ◁ own_ptr 0
      (prod_ty storage_resource_ty (tracked_ty (ty_of_gt tyC)))])
    (λ post '-[(_, (γ, p)); (_, s); (_, new_pbs)], λ mask π, 0 < n ∧
      ∃ b k, F b = {[ k := s ]} ∧
        storage_protocol_exchange_nondeterministic p b
          (λ new_p new_b, (new_p, new_b) ∈ vec_to_list new_pbs) ∧
        ∀ l, Forall (λ '(new_p, new_b), ∃ new_s,
          F new_b = {[ k := new_s ]} ∧
          post -[(l, ((γ, new_p), new_s))] mask π) (vec_to_list new_pbs)).
  Proof.
    move=> tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs"=>/=.
    fold indep_interp_of_syn_type.
    destruct vπl as [[pl [γ p]] [[pls s] [[pl' new_pbs] []]]].
    simpl in γ,p,s,new_pbs.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs")
      as "(%π & %Hlt & %b & %k & %Hb & %exchng & %Hforall)"=>//.
    iDestruct "TY" as "(Hp & Hs & _ & _)".
    iDestruct "Hp" as "(%v & %d & % & Hown & %)".
    iDestruct "Hs" as "(%v0 & %d0 & % & Hown' & %)".
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    destruct d0 as [|d0];
      [by iDestruct (false_fml_sem_1 with "Hown'") as "[]"|].
    rewrite !own_ptr_gho /= storage_resource_ty_gho /= tracked_ty_gho.
    iDestruct "Hown" as "(_ & _ & #i & own)".
    iDestruct "Hown'" as "(_ & _ & HghoC)".
    iDestruct (sp_sto_of_own alt_here tid with "own") as "[#sto own]".
    iDestruct (sp_wsat_acc with "i W") as "[SP →W]".
    iMod (sp_exchange_nondeterministic p b
      (λ new_p new_b, (new_p, new_b) ∈ vec_to_list new_pbs) γ _ exchng
      with "sto own [HghoC] SP")
      as "[(%new_p & %new_b & %Hin & own & HghoC) SP]".
    { rewrite /sp_fun Hb big_sepM_singleton. iExact "HghoC". }
    iDestruct ("→W" with "SP") as "W".
    destruct n as [|n]; [lia|]. specialize (Hforall inhabitant).
    rewrite Forall_forall in Hforall. have Hin' := Hin.
    apply Hforall in Hin' as (new_s & Hnew_b & _).
    rewrite /sp_fun Hnew_b big_sepM_singleton.
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, ((γ, new_p), new_s))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
      rewrite /ty_own own_ptr_gho /= prod_ty_gho storage_resource_ty_gho
        tracked_ty_gho /= heap_mapsto_fancy_vec_nil freeable_sz_full.
      iSplitL; [|done]. iFrame "↦ i own HghoC". by iRight.
    - iApply (proph_obs_impl with "Obs"). move=> ? [_ [? [? [_ [_ Hpost]]]]].
      specialize (Hpost l). rewrite Forall_forall in Hpost.
      apply Hpost in Hin as (new_s' & Hnew_b' & Hpostπ).
      rewrite Hnew_b' in Hnew_b. rewrite map_eq_iff in Hnew_b.
      move: (Hnew_b k). rewrite lookup_singleton_eq=> Hlookup.
      by apply lookup_singleton_Some in Hlookup as [-> ->].
  Qed.

  (** ** The shared rules

    Upstream's four shared rules all begin the same way: open the shared
    borrow with credits to strip the [▷] that Leaf's guard carries, and
    pay a [lc_fupd_add_laterN] proportional to the type's depth.  Here the
    opening is one [guard_acc] and there is no index to pay.

    What they do need is the invariant token out in the open, since a
    *stored* guard is a claim about every candidate interpretation and
    nothing can be opened there.  It is persistent, so one opening of the
    shared borrow at the ambient interpretation suffices to keep it. *)
  Lemma sp_shr_dinv {κ} E L (Alv : lctx_lft_alive E L κ) v dd gg tid :
    elctx_interp E -∗ llctx_interp L -∗
    dguard (alive_fml κ) (ty_ghox storage_resource_ty v dd gg tid) -∗
    verus_halt_wsat -∗
      llctx_interp L ∗ verus_halt_wsat ∗
      @dinv_tok FML Σ verus_halt_dinvGS (sp_wsat_fml v.1 tid).
  Proof.
    iIntros "#E L #shr W".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (dguard_alive_sem' (storage_resource_ty_gho _ _ _ _)
      with "shr") as "#g0".
    iDestruct (guard_trans with "Alv g0") as "#G1".
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W")
      as "[Wg Wr]".
    iDestruct (guard_acc with "G1 L Wg") as "[[#i own] →Wg]".
    iDestruct ("→Wg" with "[own]") as "[Wg $]"; [by iFrame "i own"|].
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "$".
    iFrame "i".
  Qed.

  Notation "SP_Guard: p1 p2" := (new [ #0])%E
    (at level 102, p1,p2 at level 1): expr_scope.

  Lemma typed_sp_guard (p1 p2 : path) E L I κ :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ storage_resource_ty;
      p2 ◁ own_ptr 0 (ghost_ty (ty_of_gt tyC))]
    (SP_Guard: p1 p2)
    (λ v, +[v ◁ shr_bor κ (tracked_ty (ty_of_gt tyC))])
    (λ post '-[(l, (γ, p)); (_, s)], λ mask π,
      ∃ b k, F b = {[ k := s ]} ∧ storage_protocol_guards p b ∧
        ∀ l, post -[(l, s)] mask π).
  Proof.
    move=> Alv tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ #E L $ TY #Obs"=>/=.
    destruct vπl as [[pl [γ p]] [[pls s] []]]. simpl in γ,p,s.
    iDestruct "TY" as "(H & _ & _)".
    iDestruct "H" as "(%v & %d & % & Hshr & %)".
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd gg Hdd Hgg)
      "#(_ & shr & _)".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs")
      as "(%π & %b & %k & %Hb & %gds & _)"=>//.
    iDestruct (sp_shr_dinv E L Alv (γ, p) dd gg tid with "E L shr W")
      as "(L & W & #i)".
    (** The stored guard on the contents, at *every* candidate.  This is
      [sp_guard] read through the invariant by [guard_wsat_trans]. *)
    iAssert (dguard (alive_fml κ)
      (ty_ghox (tracked_ty (ty_of_gt tyC)) s dd gg tid)) as "#gC".
    { iApply dguard_of_all. iIntros (sem' Hs Hi).
      iDestruct (guard_fml_sem_into alt_here Hs Hi with "shr") as "#G".
      iDestruct (guard_rhs_iff (storage_resource_ty_gho_at Hs (γ,p) dd gg tid)
        with "G") as "#G'".
      iDestruct (guard_rhs_sep_r with "G'") as "#Gown".
      iDestruct (sp_dinv_guard_at Hs (R0 := sp_own γ p) γ tid with "i")
        as "#gd".
      iDestruct (guard_wsat_trans with "gd []") as "#gf".
      { iApply (sp_guard_wf p b γ (sp_fun sem' tid) gds (sp_fun_wf Hs tid)). }
      iApply (guard_rhs_iff (Q := sp_fun sem' tid b)).
      { rewrite /sp_fun Hb big_sepM_singleton //. }
      iApply (guard_trans with "Gown gf"). }
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W")
      as "[Wg Wr]".
    iMod (store_ty_gho_pers (tracked_ty (ty_of_gt tyC)) s dd gg tid
      with "[] Wg") as "[Wg #St]".
    { by iApply empty_fml_sem_2. }
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[((l, []), s)]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, (S (dd `max` gg)); iSplitR=>//=.
      iSplitR; [|done].
      iApply (shr_bor_gho_intro_st κ (tracked_ty (ty_of_gt tyC)) ((l, []), s)
        (S (dd `max` gg)) (S (dd `max` gg)) dd gg); [lia|lia| | |].
      + iApply dguard_cells_nil.
      + iApply "gC".
      + iApply "St".
    - iApply (proph_obs_impl with "Obs"). by move=> ? [?[?[?[? Ha]]]].
  Qed.

  Notation "SP_Weaken: p1 p2" := (new [ #0])%E
    (at level 102, p1, p2 at level 1): expr_scope.

  Lemma typed_sp_weaken κ (p1 p2 : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ storage_resource_ty; p2 ◁ own_ptr 0 (ghost_ty tyA)]
    (SP_Weaken: p1 p2)
    (λ v, +[v ◁ shr_bor κ storage_resource_ty])
    (λ post '-[(l1, (γ, x1)); (l2, x2)], λ mask π,
      x2 ≼ x1 ∧ ∀ l, post -[(l, (γ, x2))] mask π).
  Proof.
    move=> Alv tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ #E L $ TY #Obs"=>/=.
    destruct vπl as [[pl [γ x1]] [[ply x2] []]]. simpl in x2.
    iDestruct "TY" as "(H & _ & _)".
    iDestruct "H" as "(%v & %d & % & Hshr & %)".
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd gg Hdd Hgg)
      "#(_ & shr & _)".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & %Hincl & _)"=>//.
    iDestruct (sp_shr_dinv E L Alv (γ, x1) dd gg tid with "E L shr W")
      as "(L & W & #i)".
    iAssert (dguard (alive_fml κ)
      (ty_ghox storage_resource_ty (γ, x2) dd gg tid)) as "#gw".
    { iApply dguard_of_all. iIntros (sem' Hs Hi).
      iDestruct (guard_fml_sem_into alt_here Hs Hi with "shr") as "#G".
      iDestruct (guard_rhs_iff (storage_resource_ty_gho_at Hs (γ,x1) dd gg tid)
        with "G") as "#G'".
      iDestruct (guard_rhs_sep_r with "G'") as "#Gown".
      iDestruct (guard_and_own (γ:=γ) (a:=◯ Inved x2) with "Gown Gown")
        as "#Gy".
      { (* [P ∧ P] is [P], so this is [sp_own_mono] and nothing more *)
        iIntros "H". iDestruct (bi.and_elim_l with "H") as "H".
        by iApply (sp_own_mono with "H"). }
      iDestruct (guard_rhs_pers with "i Gy") as "#Gi".
      iApply (guard_rhs_iff (Q := (@dinv_tok FML Σ verus_halt_dinvGS
        (sp_wsat_fml γ tid) ∗ sp_own γ x2)%I)).
      { by rewrite (storage_resource_ty_gho_at Hs (γ,x2) dd gg tid). }
      iExact "Gi". }
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W")
      as "[Wg Wr]".
    iMod (store_ty_gho_pers storage_resource_ty (γ, x2) dd gg tid
      with "[] Wg") as "[Wg #St]".
    { by iApply empty_fml_sem_2. }
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[((l, []), (γ, x2))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, (S (dd `max` gg)); iSplitR=>//=.
      iSplitR; [|done].
      iApply (shr_bor_gho_intro_st κ storage_resource_ty ((l, []), (γ, x2))
        (S (dd `max` gg)) (S (dd `max` gg)) dd gg); [lia|lia| | |].
      + iApply dguard_cells_nil.
      + iApply "gw".
      + iApply "St".
    - iApply (proph_obs_impl with "Obs"). by move=> ? [_ Ha].
  Qed.

  Notation "SP_JoinSharedDet: p1 p2 p3" := (new [ #0])%E
    (at level 102, p1, p2, p3 at level 1): expr_scope.

  (** Upstream splits on [d1 ≤ d2] and spends the larger depth's credits to
    align the two guards' later indices before combining them.  Later-free
    there are no indices, so the two cases collapse into one. *)
  Lemma typed_sp_join_shared_to_target κ (p1 p2 p3 : path) (ty : type 𝔄)
      E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ storage_resource_ty; p2 ◁ shr_bor κ storage_resource_ty;
      p3 ◁ own_ptr 0 (ghost_ty ty)]
    (SP_JoinSharedDet: p1 p2 p3)
    (λ v, +[v ◁ shr_bor κ storage_resource_ty])
    (λ post '-[(l1, (γ1, x1)); (l2, (γ2, x2)); (_, y)], λ mask π,
      γ1 = γ2 ∧ (∀ p, x1 ≼ p ∧ x2 ≼ p → y ≼ p) ∧
      ∀ l, post -[(l, (γ1, y))] mask π).
  Proof.
    move=> Alv tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ #E L $ TY #Obs"=>/=.
    destruct vπl as [[pl1 [γ1 x1]] [[pl2 [γ2 x2]] [[pl3 y] []]]]. simpl in y.
    iDestruct "TY" as "(H1 & H2 & _ & _)".
    iDestruct "H1" as "(%v1 & %d1 & % & Hshr1 & %)".
    iDestruct "H2" as "(%v2 & %d2 & % & Hshr2 & %)".
    iDestruct (shr_bor_gho_elim with "Hshr1") as (dd1 gg1 ? ?)
      "#(_ & shr1 & _)".
    iDestruct (shr_bor_gho_elim with "Hshr2") as (dd2 gg2 ? ?)
      "#(_ & shr2 & _)".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & %Hy & _)"=>//.
    iDestruct (sp_shr_dinv E L Alv (γ1, x1) dd1 gg1 tid with "E L shr1 W")
      as "(L & W & #i)".
    iAssert (dguard (alive_fml κ)
      (ty_ghox storage_resource_ty (γ1, y) dd1 gg1 tid)) as "#gy".
    { iApply dguard_of_all. iIntros (sem' Hs Hi).
      iDestruct (guard_fml_sem_into alt_here Hs Hi with "shr1") as "#G1".
      iDestruct (guard_fml_sem_into alt_here Hs Hi with "shr2") as "#G2".
      iDestruct (guard_rhs_iff
        (storage_resource_ty_gho_at Hs (γ1,x1) dd1 gg1 tid) with "G1")
        as "#G1'".
      iDestruct (guard_rhs_iff
        (storage_resource_ty_gho_at Hs (γ1,x2) dd2 gg2 tid) with "G2")
        as "#G2'".
      iDestruct (guard_rhs_sep_r with "G1'") as "#Gown1".
      iDestruct (guard_rhs_sep_r with "G2'") as "#Gown2".
      iDestruct (guard_and_own (γ:=γ1) (a:=◯ Inved y) with "Gown1 Gown2")
        as "#Gy".
      { by iApply (sp_own_and_specific x1 x2 y γ1). }
      iDestruct (guard_rhs_pers with "i Gy") as "#Gi".
      iApply (guard_rhs_iff (Q := (@dinv_tok FML Σ verus_halt_dinvGS
        (sp_wsat_fml γ1 tid) ∗ sp_own γ1 y)%I)).
      { by rewrite (storage_resource_ty_gho_at Hs (γ1,y) dd1 gg1 tid). }
      iExact "Gi". }
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W")
      as "[Wg Wr]".
    iMod (store_ty_gho_pers storage_resource_ty (γ1, y) dd1 gg1 tid
      with "[] Wg") as "[Wg #St]".
    { by iApply empty_fml_sem_2. }
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[((l, []), (γ1, y))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, (S (dd1 `max` gg1)); iSplitR=>//=.
      iSplitR; [|done].
      iApply (shr_bor_gho_intro_st κ storage_resource_ty ((l, []), (γ1, y))
        (S (dd1 `max` gg1)) (S (dd1 `max` gg1)) dd1 gg1); [lia|lia| | |].
      + iApply dguard_cells_nil.
      + iApply "gy".
      + iApply "St".
    - iApply (proph_obs_impl with "Obs"). by move=> ? [_ [_ Ha]].
  Qed.

  Notation "SP_Validate: p1" := (new [ #0])%E
    (at level 102, p1 at level 1): expr_scope.

  Lemma typed_sp_validate κ (p1 : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ storage_resource_ty]
    (SP_Validate: p1)
    (λ v, +[v ◁ own_ptr 0
      (prod_ty (ghost_ty tyA) (ghost_ty (ty_of_gt tyC)))])
    (λ post '-[(l1, (γ, p))], λ mask π, ∀ l b q, sp_rel (p ⋅ q) b →
      (∀ k s, F b !! k = Some s → post -[(l, (q, s))] mask π) ∧
      (F b = ∅ → post -[(l, (q, ε))] mask π)).
  Proof.
    move=> Alv tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ #E L $ TY #Obs"=>/=.
    destruct vπl as [[pl [γ p]] []].
    iDestruct "TY" as "(H & _)".
    iDestruct "H" as "(%v & %d & % & Hshr & %)".
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd gg ? ?) "#(_ & shr & _)".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (dguard_alive_sem' (storage_resource_ty_gho _ _ _ _)
      with "shr") as "#g0".
    iDestruct (guard_trans with "Alv g0") as "#G1".
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W")
      as "[Wg Wr]".
    iDestruct (guard_acc with "G1 L Wg") as "[[#i own] →Wg]".
    iDestruct (sp_own_valid with "own") as "%Hv".
    iDestruct ("→Wg" with "[own]") as "[Wg L]"; [by iFrame "i own"|].
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    destruct Hv as (q & b & Hrel).
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    destruct (decide (F b = ∅)) as [Hempty|Hnempty].
    - iExists -[(l, (q, ε))]. iFrame "L". iSplitL.
      + iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
        rewrite /ty_own own_ptr_gho /= prod_ty_gho !ghost_ty_gho
          heap_mapsto_fancy_vec_nil freeable_sz_full.
        iSplitL; [|done]. iFrame "↦". iSplitL; [by iRight|done].
      + iApply (proph_obs_impl with "Obs")=> ? Hpost.
        move: Hempty. by eapply Hpost.
    - apply map_choose in Hnempty as (k & s & Hlookup).
      iExists -[(l, (q, s))]. iFrame "L". iSplitL.
      + iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
        rewrite /ty_own own_ptr_gho /= prod_ty_gho !ghost_ty_gho
          heap_mapsto_fancy_vec_nil freeable_sz_full.
        iSplitL; [|done]. iFrame "↦". iSplitL; [by iRight|done].
      + iApply (proph_obs_impl with "Obs")=> ? Hpost.
        move: Hlookup. by eapply Hpost.
  Qed.

  (** ** The two exchanges against a shared resource

    Upstream opens the shared borrow with credits, pays a
    [lc_fupd_add_laterN] proportional to the type's depth and then a
    further [lc_fupd_elim_later] for the [▷] over [f].  Here the two
    guards - one on the shared share, one on the protocol's world
    satisfaction - go straight into
    [sp_exchange_with_guard{,_nondeterministic}], and there is no index to
    pay.  The invariant token comes from the *owned* operand, where it is
    persistent and needs no opening at all. *)
  Lemma sp_shr_guards {κ} E L (Alv : lctx_lft_alive E L κ) v dd gg tid :
    elctx_interp E -∗ llctx_interp L -∗
    dguard (alive_fml κ) (ty_ghox storage_resource_ty v dd gg tid) -∗
      llctx_interp L ∗ (llctx_interp L &&{Wguard}&&> sp_own v.1 v.2).
  Proof.
    iIntros "#E L #shr".
    iDestruct (Alv with "L E") as "#Alv". iFrame "L".
    iDestruct (dguard_alive_sem' (storage_resource_ty_gho _ _ _ _)
      with "shr") as "#g0".
    iDestruct (guard_trans with "Alv g0") as "#G1".
    iApply (guard_rhs_sep_r with "G1").
  Qed.

  Lemma sp_dinv_guard {R0 : iProp Σ} γ tid :
    @dinv_tok FML Σ verus_halt_dinvGS (sp_wsat_fml γ tid) ⊢
      (R0 &&{Wguard}&&> sp_wsat γ (sp_fun bor_sem tid)).
  Proof. rewrite -alt_WGuard_here. exact (sp_dinv_guard_at alt_here γ tid). Qed.

  Notation "SP_ExchangeWithShr: p1 p2 p3 p4 p5" := (new [ #0])%E
    (at level 102, p1,p2,p3,p4,p5 at level 1): expr_scope.

  Lemma typed_sp_exchange_with_shr κ (p1 p2 p3 p4 p5 : path) (tyA : type 𝔄)
      E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty;
      p2 ◁ shr_bor κ storage_resource_ty;
      p3 ◁ own_ptr 0 (tracked_ty (ty_of_gt tyC));
      p4 ◁ own_ptr 0 (ghost_ty tyA);
      p5 ◁ own_ptr 0 (ghost_ty (ty_of_gt tyC))]
    (SP_ExchangeWithShr: p1 p2 p3 p4 p5)
    (λ v, +[v ◁ own_ptr 0
      (prod_ty storage_resource_ty (tracked_ty (ty_of_gt tyC)))])
    (λ post '-[(_, (γ, p)); (_, (γ', p')); (_, s); (_, new_p); (_, new_s)],
      λ mask π, γ = γ' ∧ ∃ b new_b k,
        F b = {[ k := s ]} ∧ F new_b = {[ k := new_s ]} ∧
        storage_protocol_exchange (p ⋅ p') (new_p ⋅ p') b new_b ∧
        ∀ l, post -[(l, ((γ, new_p), new_s))] mask π).
  Proof.
    move=> Alv tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ #E L $ TY #Obs"=>/=.
    destruct vπl as [[pl [γ p]] [[pl' [γ' p']]
      [[pls s] [[pln new_p] [[plns new_s] []]]]]].
    simpl in γ,p,γ',p',s,new_p,new_s.
    iDestruct "TY" as "(Hp & Hp' & Hs & _ & _)".
    iDestruct "Hp" as "(%v & %d & % & Hown & %)".
    iDestruct "Hp'" as "(%v' & %d' & % & Hshr & %)".
    iDestruct "Hs" as "(%v0 & %d0 & % & Hown'' & %)".
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    destruct d0 as [|d0];
      [by iDestruct (false_fml_sem_1 with "Hown''") as "[]"|].
    rewrite !own_ptr_gho /= storage_resource_ty_gho /= tracked_ty_gho.
    iDestruct "Hown" as "(_ & _ & #i & own)".
    iDestruct "Hown''" as "(_ & _ & HghoC)".
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd gg ? ?) "#(_ & shr & _)".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs")
      as "(%π & <- & %b & %new_b & %k & %Hb & %Hnew_b & %exchng & _)"=>//.
    iDestruct (sp_shr_guards E L Alv (γ, p') dd gg tid with "E L shr")
      as "[L #gq]".
    iDestruct (sp_dinv_guard (R0 := llctx_interp L) γ tid with "i") as "#gd".
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W")
      as "[Wg Wr]".
    iMod (sp_exchange_with_guard p new_p p' b new_b γ (sp_fun bor_sem tid)
      (llctx_interp L) Wguard exchng (sp_fun_wf alt_here tid)
      with "gq gd L own [HghoC] Wg") as "(own & HghoC & L & Wg)".
    { rewrite /sp_fun Hb big_sepM_singleton. iExact "HghoC". }
    rewrite /sp_fun Hnew_b big_sepM_singleton.
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, ((γ, new_p), new_s))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
      rewrite /ty_own own_ptr_gho /= prod_ty_gho storage_resource_ty_gho
        tracked_ty_gho /= heap_mapsto_fancy_vec_nil freeable_sz_full.
      iSplitL; [|done]. iFrame "↦ i own HghoC". by iRight.
    - iApply (proph_obs_impl with "Obs").
      by move=> ? [_ [?[?[?[?[?[? Ha]]]]]]].
  Qed.

  Notation "SP_ExchangeWithShrNonDet: p1 p2 p3 p4" := (new [ #0])%E
    (at level 102, p1,p2,p3,p4 at level 1): expr_scope.

  Lemma typed_sp_exchange_with_shr_nondeterministic κ (p1 p2 p3 p4 : path) n
      (ty : type (vecₛ (𝔄 * 𝔅) n)) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty;
      p2 ◁ shr_bor κ storage_resource_ty;
      p3 ◁ own_ptr 0 (tracked_ty (ty_of_gt tyC));
      p4 ◁ own_ptr 0 (ghost_ty ty)]
    (SP_ExchangeWithShrNonDet: p1 p2 p3 p4)
    (λ v, +[v ◁ own_ptr 0
      (prod_ty storage_resource_ty (tracked_ty (ty_of_gt tyC)))])
    (λ post '-[(_, (γ, p)); (_, (γ', p')); (_, s); (_, new_pbs)], λ mask π,
      γ = γ' ∧ ∃ b k, F b = {[ k := s ]} ∧
        storage_protocol_exchange_nondeterministic (p ⋅ p') b
          (λ new_p_big new_b, ∃ new_p, new_p_big = new_p ⋅ p' ∧
            (new_p, new_b) ∈ vec_to_list new_pbs) ∧
        ∀ l, Forall (λ '(new_p, new_b), ∃ new_s,
          F new_b = {[ k := new_s ]} ∧
          post -[(l, ((γ, new_p), new_s))] mask π) (vec_to_list new_pbs)).
  Proof.
    move=> Alv tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ #E L $ TY #Obs"=>/=.
    fold indep_interp_of_syn_type.
    destruct vπl as [[pl [γ p]] [[pl' [γ' p']] [[pls s] [[pln new_pbs] []]]]].
    simpl in γ,p,γ',p',s,new_pbs.
    iDestruct "TY" as "(Hp & Hp' & Hs & _ & _)".
    iDestruct "Hp" as "(%v & %d & % & Hown & %)".
    iDestruct "Hp'" as "(%v' & %d' & % & Hshr & %)".
    iDestruct "Hs" as "(%v0 & %d0 & % & Hown'' & %)".
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    destruct d0 as [|d0];
      [by iDestruct (false_fml_sem_1 with "Hown''") as "[]"|].
    rewrite !own_ptr_gho /= storage_resource_ty_gho /= tracked_ty_gho.
    iDestruct "Hown" as "(_ & _ & #i & own)".
    iDestruct "Hown''" as "(_ & _ & HghoC)".
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd gg ? ?) "#(_ & shr & _)".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs")
      as "(%π & <- & %b & %k & %Hb & %exchng & %Hforall)"=>//.
    iDestruct (sp_shr_guards E L Alv (γ, p') dd gg tid with "E L shr")
      as "[L #gq]".
    iDestruct (sp_dinv_guard (R0 := llctx_interp L) γ tid with "i") as "#gd".
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W")
      as "[Wg Wr]".
    iMod (sp_exchange_with_guard_nondeterministic p p' b
      (λ new_p new_b, (new_p, new_b) ∈ vec_to_list new_pbs) γ
      (sp_fun bor_sem tid) (llctx_interp L) Wguard exchng
      (sp_fun_wf alt_here tid) with "gq gd L own [HghoC] Wg")
      as "[(%new_p & %new_b & %Hin & own & HghoC) (L & Wg)]".
    { rewrite /sp_fun Hb big_sepM_singleton. iExact "HghoC". }
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    have Hin' := Hin. specialize (Hforall inhabitant).
    rewrite Forall_forall in Hforall.
    apply Hforall in Hin' as (new_s & Hnew_b & _).
    rewrite /sp_fun Hnew_b big_sepM_singleton.
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, ((γ, new_p), new_s))]. iFrame "L". iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
      rewrite /ty_own own_ptr_gho /= prod_ty_gho storage_resource_ty_gho
        tracked_ty_gho /= heap_mapsto_fancy_vec_nil freeable_sz_full.
      iSplitL; [|done]. iFrame "↦ i own HghoC". by iRight.
    - iApply (proph_obs_impl with "Obs").
      move=> ? [_ [? [? [_ [_ Hpost]]]]].
      specialize (Hpost l). rewrite Forall_forall in Hpost.
      apply Hpost in Hin as (new_s' & Hnew_b' & Hpostπ).
      rewrite Hnew_b' in Hnew_b. rewrite map_eq_iff in Hnew_b.
      move: (Hnew_b k). rewrite lookup_singleton_eq=> Hlookup.
      by apply lookup_singleton_Some in Hlookup as [-> ->].
  Qed.

  Notation "SP_ValidateWithShr: pu ps" := (new [ #0])%E
    (at level 102, pu,ps at level 1): expr_scope.

  (** Upstream's longest proof, and for a reason that is gone: it begins
    two lifetimes, halves a fractional guard, borrows the halves and
    spends the credits that buys on stripping the [▷]s over the borrowed
    contents.  Here a unique borrow is opened by moving its contents *out*
    of the world satisfaction, so the world comes back and the shared
    guard can then be opened against what the unique borrow gave - which
    is the one thing [typed_sp_exchange_with_shr] cannot do, since there
    both sides are behind guards. *)
  Lemma typed_sp_validate_with_shr κ (pu ps : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[pu ◁ uniq_bor κ storage_resource_ty;
      ps ◁ shr_bor κ storage_resource_ty]
    (SP_ValidateWithShr: pu ps)
    (λ v, +[v ◁ own_ptr 0
      (prod_ty (ghost_ty tyA) (ghost_ty (ty_of_gt tyC)))])
    (λ post '-[(l1, (γ1, a1), _, _, _, _); (l2, (γ2, a2))], λ mask π,
      γ1 = γ2 ∧ ∀ l b q, sp_rel (a1 ⋅ a2 ⋅ q) b →
        (∀ k s, F b !! k = Some s → post -[(l, (q, s))] mask π) ∧
        (F b = ∅ → post -[(l, (q, ε))] mask π)).
  Proof.
    move=> Alv tid postπ mask iκs vπl.
    iIntros "#LFT #PROPH UNIQ #E L $ TY #Obs"=>/=.
    destruct vπl as
      [[[[[[pl1 [γ1 a1]] ξi] du] gu] idx] [[pl2 [γ2 a2]] []]].
    iDestruct "TY" as "(H1 & H2 & _)".
    iDestruct "H1" as "(%v1 & %d1 & % & Huniq & %)".
    iDestruct "H2" as "(%v2 & %d2 & % & Hshr & %)".
    rewrite uniq_bor_gho.
    iDestruct "Huniq"
      as "(#Incl & %Hle & (ξVo & ξTok & #ξBor) & #PtBase & #Pers)".
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd gg ? ?) "#(_ & shr & _)".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & _)"=>//.
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (dguard_alive_sem' (storage_resource_ty_gho _ _ _ _)
      with "shr") as "#g0".
    iDestruct (guard_trans with "Alv g0") as "#G1".
    iDestruct (guard_rhs_sep_r with "G1") as "#gq".
    iMod (Ltok_alloc with "L W") as "[W (%γL & #key & f)]".
    iAssert (frac_tok γL (1/2) &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "[] Alv"). iApply (Ltok_guard_frac with "key"). }
    iAssert (bor_sem (gsrc_fml (GFrac γL (1/2))) &&{Wguard}&&> @[κ])%I
      as "#Gκ'".
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γL (1/2)))). iApply "Gκ". }
    iAssert (frac_tok γL (1/2) &&{Wguard}&&> sp_own γ1 a2)%I as "#Gq2".
    { iApply (guard_trans with "[] gq"). iApply (Ltok_guard_frac with "key"). }
    iDestruct (Ltok_split_1 with "[$key $f]") as "[[_ fa] [_ fb]]".
    iDestruct (idxbor_fml_dIdxBor with "ξBor") as "#ξBor1".
    iDestruct (dIdxBor_acc_guarded (E:=⊤) (Gx:=gsrc_fml (GFrac γL (1/2)))
      (κ:=κ) (idx:=idx) with "LFT ξBor1 ξTok Gκ' [fa]") as "A";
      [by iApply (gsrc_fml_sem_2 (s := GFrac γL (1/2)))|].
    iDestruct (fupdw_incl_mask (W:=verus_halt_wsat) (E':=⊤) with "A")
      as "A'"; [done|].
    iMod ("A'" with "W") as "[W [Pinner Gback]]".
    iEval (rewrite uniq_body_fml_sem) in "Pinner".
    iDestruct "Pinner" as (x1 e1 h1) "(ξPc & gho & pt)".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
    subst e1 h1.
    rewrite storage_resource_ty_gho /=. iDestruct "gho" as "[#i own1]".
    (* the shared share, read against the other half of the share *)
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W")
      as "[Wg Wr]".
    iDestruct (guard_acc with "Gq2 fb Wg") as "[own2 →Wg]".
    iAssert (sp_own γ1 (a1 ⋅ a2)) with "[own1 own2]" as "own".
    { rewrite sp_own_op. iFrame "own1 own2". }
    iDestruct (sp_own_valid with "own") as "%Hv".
    rewrite sp_own_op. iDestruct "own" as "[own1 own2]".
    iDestruct ("→Wg" with "own2") as "[Wg fb]".
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    (* and the unique borrow goes back unchanged *)
    iDestruct ("Gback" with "[ξPc own1 pt]") as "B".
    { rewrite uniq_body_fml_sem. iExists (γ1, a1), du, gu. iFrame "ξPc pt".
      rewrite storage_resource_ty_gho /=. by iFrame "i own1". }
    iDestruct (fupdw_incl_mask (W:=verus_halt_wsat) (E':=⊤) with "B")
      as "B'"; [done|].
    iMod ("B'" with "W") as "[W [ξTok fa]]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γL (1/2)) with "fa") as "fa".
    iAssert (Ltok γL L 1) with "[fa fb]" as "tok".
    { rewrite Ltok_split. iFrame "key fa fb". }
    iMod (Ltok_withdraw with "tok W") as "[W L]".
    destruct Hv as (qq & b & Hrel).
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    destruct (decide (F b = ∅)) as [Hempty|Hnempty].
    - iExists -[(l, (qq, ε))]. iFrame "L". iSplitL.
      + iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
        rewrite /ty_own own_ptr_gho /= prod_ty_gho !ghost_ty_gho
          heap_mapsto_fancy_vec_nil freeable_sz_full.
        iSplitL; [|done]. iFrame "↦". iSplitL; [by iRight|done].
      + iApply (proph_obs_impl with "Obs")=> ? [_ Hpost].
        move: Hempty. by eapply Hpost.
    - apply map_choose in Hnempty as (k & sv & Hlookup).
      iExists -[(l, (qq, sv))]. iFrame "L". iSplitL.
      + iSplitL; [|done]. iExists _, 1%nat; iSplitR=>//=.
        rewrite /ty_own own_ptr_gho /= prod_ty_gho !ghost_ty_gho
          heap_mapsto_fancy_vec_nil freeable_sz_full.
        iSplitL; [|done]. iFrame "↦". iSplitL; [by iRight|done].
      + iApply (proph_obs_impl with "Obs")=> ? [_ Hpost].
        move: Hlookup. by eapply Hpost.
  Qed.
End StorageProtocol.

(** * A note on what this cost

  All eighteen of upstream's rules are here.  The two that look hardest -
  the exchanges against a shared resource - turned on one resource-level
  fact, [own_sep.v]'s [own_auth_frag_sep], and the one that *is* upstream's
  longest proof, [typed_sp_validate_with_shr], turned out to be among the
  shortest here: its length upstream is two lifetimes, a halved fractional
  guard and the credits they buy, all of it spent on laters that do not
  exist in this port. *)
