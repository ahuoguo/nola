(** * The *separating* conjunction rule for [own]

  Ported from the Leaf library ([guarding/own_and_own_sep.v], MIT, Hance et
  al.), and shortened: Iris has since upstreamed the [iRes_project]
  machinery Leaf had to build by hand, so what is left is the one
  [uPred.unseal] argument and the transport around it.

  ** Why this file exists

  [nola/verus_halt/own_and.v] records that Iris upstreamed Leaf's
  *conjunction* rules - [own_and], [own_forall] and friends - so the port
  could drop the 830 lines that proved them.  It did not upstream the
  separating one:

    [own γ a ∧ (own γ b ∗ P) ⊢ own γ b ∗ (own γ a ∧ P)]

  and that one does not follow from them.  [own_and] produces a common
  *upper bound* of the two conjuncts; this says how a resource *splits*,
  which no upper bound can give.

  It is what lets two guards over one world satisfaction be opened at once.
  Opening either consumes the world the other needs, so
  [nola/bi/guard.v]'s [guard_open_two] can only reach the non-separating
  conjunction of the two right-hand sides - and then this rule separates
  them, provided the two resources are disjoint in the sense the side
  condition names.  [storage_protocol_logic.v]'s exchange against a guard
  is the one client, and it is why [typing/protocol.v]'s
  [typed_sp_exchange_with_shr] exists.

  ** The side condition

  At the resource level it reads: whatever [a] is below, once [b] has been
  taken out of it, [a] is still below the rest.  Stated over the camera it
  is the [cond] of [own_andsep_to_sepand], in [option A] because a resource
  may hold nothing at all at [γ].  For [auth] it is routine - an
  authoritative element contributes nothing to a fragment - and
  [auth_frag_sep] below is that instance. *)

From nola Require Export prelude.
From iris.algebra Require Export auth.
From iris.base_logic.lib Require Export own iprop.
From iris.base_logic Require Import upred.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

Section ownM_sep.
  Context {Σ : gFunctors}.
  Implicit Type (x y : iResUR Σ) (P : iProp Σ).

  (** Leaf's [uPred_ownM_andsep_to_sepand], verbatim in substance.  The
    whole content is that the [∗] on the right may be re-split: [y] keeps
    the piece it came from, and [a] is below what is left over. *)
  Lemma uPred_ownM_andsep_to_sepand x y P
    (cond : ∀ n (p1 p2 : iResUR Σ), ✓{n} (p1 ⋅ p2) → x ≼{n} p1 ⋅ p2 →
      y ≼{n} p1 → ∃ m, y ⋅ m ≡{n}≡ p1 ∧ x ≼{n} m ⋅ p2) :
    uPred_ownM x ∧ (uPred_ownM y ∗ P) ⊢ uPred_ownM y ∗ (uPred_ownM x ∧ P).
  Proof.
    uPred.unseal. split=> n p val t.
    destruct t as [tx s].
    destruct s as (p1 & p2 & eq & ty & tp).
    have val2 : ✓{n} (p1 ⋅ p2) by rewrite -eq.
    have incl2 : x ≼{n} p1 ⋅ p2 by rewrite -eq.
    have [m [ym xle]] := cond n p1 p2 val2 incl2 ty.
    exists y, (m ⋅ p2). split_and!.
    - by rewrite eq -ym assoc.
    - rewrite /uPred_holds /=. reflexivity.
    - split; [done|]. eapply uPred_mono; [exact tp| |done].
      exists m. by rewrite comm.
  Qed.
End ownM_sep.

Section own_sep.
  Context `{i : !inG Σ A}.
  Implicit Type (γ : gname) (a : A).

  (** [iRes_project] is non-expansive.  Iris proves everything else about
    it that is wanted here - [iRes_project_op], [iRes_project_singleton],
    [iRes_project_below] - but not this. *)
  #[local] Instance iRes_project_ne γ :
    NonExpansive (own.iRes_project (i:=i) γ).
  Proof.
    move=> n x y Hxy. rewrite /own.iRes_project.
    f_equiv. apply (Hxy (inG_id i) γ).
  Qed.

  #[local] Instance iRes_singleton_ne' γ :
    NonExpansive (own.iRes_singleton (i:=i) γ) := own.iRes_singleton_ne γ.

  #[local] Lemma iRes_project_monoN n γ (x y : iResUR Σ) :
    x ≼{n} y → own.iRes_project (i:=i) γ x ≼{n} own.iRes_project γ y.
  Proof.
    move=> [d Hd]. exists (own.iRes_project γ d).
    by rewrite Hd own.iRes_project_op.
  Qed.

  (** A singleton is below whatever its camera value is below.  This is
    the converse of Iris's [iRes_project_above], and it is the step Leaf
    spends a hundred lines of [discrete_fun_insert] surgery on; with
    [iRes_project_below] it is five. *)
  #[local] Lemma iRes_singleton_of_project n γ a (z : iResUR Σ) :
    Some a ≼{n} own.iRes_project (i:=i) γ z → own.iRes_singleton γ a ≼{n} z.
  Proof.
    rewrite option_includedN=> Hin.
    destruct Hin as [?|(x & y & Hx & Hy & Hxy)]; [done|]. simplify_eq.
    have Hbelow := own.iRes_project_below γ z y Hy.
    etrans; [|exact (cmra_included_includedN _ _ _ Hbelow)].
    destruct Hxy as [Heq|[d Hd]].
    - exists ε. by rewrite right_id Heq.
    - exists (own.iRes_singleton γ d).
      by rewrite Hd own.iRes_singleton_op.
  Qed.

  (** ** The rule

    The side condition is the camera-level reading of "[b] contributes
    nothing to what [a] is below": it lives in [option A] because a
    resource may hold nothing at all at [γ]. *)
  Lemma own_andsep_to_sepand γ a b (P : iProp Σ)
    (cond : ∀ n (c : option A), Some a ≼{n} Some b ⋅ c → Some a ≼{n} c) :
    own γ a ∧ (own γ b ∗ P) ⊢ own γ b ∗ (own γ a ∧ P).
  Proof.
    rewrite own.own_eq /own.own_def.
    apply uPred_ownM_andsep_to_sepand.
    move=> n p1 p2 _ Hin1 [m Hm]. exists m. split; [by rewrite Hm|].
    apply iRes_singleton_of_project, cond.
    have Hle : own.iRes_singleton γ a ≼{n}
      own.iRes_singleton γ b ⋅ (m ⋅ p2).
    { destruct Hin1 as [d Hd]. exists d. by rewrite assoc -Hm. }
    apply (iRes_project_monoN n γ) in Hle.
    by rewrite own.iRes_project_singleton own.iRes_project_op
      own.iRes_project_singleton in Hle.
  Qed.
End own_sep.

(** * The [auth] instance

  An authoritative element's fragment component is the unit
  ([auth_auth] is [view_auth], whose frag projection is [ε]), so a
  fragment below [● st ⋅ c] is below [c] - *provided* [q] is not itself
  below the unit, which is what rules out [c] holding nothing at all.
  That proviso is not idle: without it the rule is false, since
  [own γ (◯ ε)] does sit inside [own γ (● st)]. *)
Section auth_sep.
  Context {C : ucmra} `{i : !inG Σ (authR C)}.

  Lemma auth_frag_andsep_cond (q st : C)
      (Hq : ∀ n (d : C), (ε : C) ≡{n}≡ q ⋅ d → False) n
      (c : option (authUR C)) :
    Some (◯ q) ≼{n} Some (● st) ⋅ c → Some (◯ q) ≼{n} c.
  Proof.
    move=> Hin. destruct c as [c0|].
    - rewrite -Some_op option_includedN in Hin.
      destruct Hin as [?|(x & y & Hx & Hy & Hxy)]; [done|]. simplify_eq.
      rewrite option_includedN. right. exists (◯ q), c0.
      split_and!; [done|done|right].
      destruct c0 as [ca cf]. destruct Hxy as [Heq|[[da df] Hd]].
      { exfalso. destruct Heq as [Ha _]. move: Ha=>/=.
        destruct ca; by inversion 1. }
      destruct Hd as [_ Hf]. move: Hf=>/=. rewrite !left_id=> Hf.
      exists (View ca df). split; simpl; [by rewrite left_id|exact Hf].
    - rewrite right_id option_includedN in Hin.
      destruct Hin as [?|(x & y & Hx & Hy & Hxy)]; [done|]. simplify_eq.
      exfalso. destruct Hxy as [Heq|[[da df] Hd]].
      { destruct Heq as [Ha _]. move: Ha=>/=. by inversion 1. }
      destruct Hd as [_ Hf]. move: Hf=>/= Hf. exact (Hq n df Hf).
  Qed.

  (** The rule, for an authority and a fragment at one ghost name *)
  Lemma own_auth_frag_sep γ (q st : C) (P : iProp Σ)
      (Hq : ∀ n (d : C), (ε : C) ≡{n}≡ q ⋅ d → False) :
    own γ (◯ q) ∧ (own γ (● st) ∗ P) ⊢ own γ (● st) ∗ (own γ (◯ q) ∧ P).
  Proof.
    apply own_andsep_to_sepand=> n c.
    exact (auth_frag_andsep_cond q st Hq n c).
  Qed.
End auth_sep.
