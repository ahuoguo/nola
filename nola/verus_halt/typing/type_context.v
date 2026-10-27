(** * Type contexts

  Ported from VerusBelt ([typing/type_context.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  Three things change, all of them removals.

  - The time receipts go.  [tctx_elt_interp] no longer carries [⧖d] beside
    [ty_own ty x d d tid], and the blocked case no longer carries [⧖d ∗ ⧗1]
    or the [▷] on the prophecy equalizer.  The [⧗1] existed only to be cashed
    in for later credits by [cumulative_persistent_time_receipt_get_credits],
    and the [▷] was what those credits paid for.
  - Every [={F}=∗ ∃d, ⧖d ∗ |={F}▷=>^(d*(d+1)) |={F}=>] collapses to one
    [=[verus_halt_wsat]{F}=∗].  [resolve_tctx], [resolve_unblock_tctx] and
    [unblock_tctx] all have this shape, and [lemma_max_mul] - which exists to
    combine two such step counts - disappears with it.
  - Shared access to [L] is [Ltok γ L q] rather than an arbitrary [G] with a
    guard; see [nola.verus_halt.typing.ctx]. *)

From iris.proofmode Require Import proofmode.
From nola.verus_halt.typing Require Import type ctx lft_contexts.
From nola.bi Require Import guard modw.
From nola.iris Require Import point.
Import GuardNotation ModwNotation WpwNotation.

Implicit Type (𝔄 𝔅 ℭ: syn_type) (𝔄l 𝔅l ℭl 𝔇l: syn_typel).

Definition path := expr.
Bind Scope expr_scope with path.

Inductive blocked_type `{!typeG FML Σ} : syn_type → Type :=
  blocked_type_ctor (𝔄₀: syn_type) (ty: type 𝔄₀) : blocked_type (blockedₛ 𝔄₀).

Definition blocked_type_elim `{!typeG FML Σ} {𝔄 T} (bty: blocked_type 𝔄) (x: ~~ 𝔄)
    (f: ∀ (𝔄₀ : syn_type) , type 𝔄₀ → ~~ (blockedₛ 𝔄₀) → T)
    : T :=
  match bty in (blocked_type s) return (~~ s → T) with
  | blocked_type_ctor 𝔄₀ ty => f 𝔄₀ ty
  end x.
  
Inductive tctx_elt `{!typeG FML Σ} 𝔄 : Type :=
| TCtx_hasty (p: path) (ty: type 𝔄)
| TCtx_blocked (p: path) (κ: lft) (ty: blocked_type 𝔄).

Notation tctx := (hlist tctx_elt).

Notation "p ◁ ty" := (TCtx_hasty _ p ty%T) (at level 55).
Notation "p ◁{ κ } ty" := (TCtx_blocked _ p κ ty%T)
   (at level 55, format "p  ◁{ κ }  ty").

(* [pred] is used by [Nat] *)
Notation pred' A := (A → Mask → proph_asn → Prop) (only parsing).
Notation predl 𝔄l := (pred' (plist indep_interp_of_syn_type 𝔄l)).
Notation predl_trans 𝔄l 𝔅l := (predl 𝔅l → predl 𝔄l).
Notation predl_trans' 𝔄l 𝔅 := (pred' (~~𝔅) → predl 𝔄l).

Global Instance pred'_equiv A : Equiv (pred' A) :=
  pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (↔))).
Global Instance predl_trans_equiv 𝔄l 𝔅l : Equiv (predl_trans 𝔄l 𝔅l) :=
  pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (↔)))).
Global Instance predl_trans'_equiv 𝔄l 𝔅 : Equiv (predl_trans' 𝔄l 𝔅) :=
  pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (↔)))).

(*Notation predₛ 𝔄 := (funₛ 𝔄 (funₛ maskₛ (funₛ proph_asnₛ Propₛ)))%ST.
Notation predlₛ 𝔄l := (predₛ (Π! 𝔄l))%ST.
Notation predl_trans'ₛ 𝔄l 𝔅 := (funₛ (predₛ 𝔅) (predlₛ 𝔄l))%ST.*)

Definition trans_app {𝔄l 𝔅l ℭl 𝔇l} (tr: predl_trans 𝔄l 𝔅l) (tr': predl_trans ℭl 𝔇l)
  : predl_trans (𝔄l ++ ℭl) (𝔅l ++ 𝔇l) := λ post acl π,
  let '(al, cl) := psep acl in tr (λ bl π, tr' (λ dl π, post (bl -++ dl) π) cl π) al π.

Global Instance trans_app_proper {𝔄l 𝔅l ℭl 𝔇l} tr tr' :
  Proper ((≡) ==> (≡)) tr →
  Proper ((≡) ==> (≡)) tr' →
  Proper ((≡) ==> (≡)) (@trans_app 𝔄l 𝔅l ℭl 𝔇l tr tr').
Proof. intros Htr Htr' ????. unfold trans_app. apply Htr=>?. apply Htr'=>? //. Qed.

Definition trans_lower {𝔄l 𝔅l ℭl} (tr: predl_trans 𝔄l 𝔅l)
  : predl_trans (ℭl ++ 𝔄l) (ℭl ++ 𝔅l) := λ post cal,
  let '(cl, al) := psep cal in tr (λ bl, post (cl -++ bl)) al.

Definition trans_upper {𝔄l 𝔅l ℭl} (tr: predl_trans 𝔄l 𝔅l)
  : predl_trans (𝔄l ++ ℭl) (𝔅l ++ ℭl) := λ post acl,
  let '(al, cl) := psep acl in tr (λ bl, post (bl -++ cl)) al.

Definition trans_tail {ℭ 𝔄l 𝔅l} (tr: predl_trans 𝔄l 𝔅l)
  : predl_trans (ℭ :: 𝔄l) (ℭ :: 𝔅l) :=
  λ post '(c -:: al), tr (λ bl, post (c -:: bl)) al.

Section type_context.
  Context `{!typeG FML Σ}.

  Fixpoint eval_path (p: path) : option val := match p with
    | BinOp OffsetOp e (#(LitInt n))%E => match eval_path e with
        Some #(LitLoc l) => Some #(l +ₗ n) | _ => None end
    | e => to_val e end.

  Lemma eval_path_of_val (v: val) : eval_path v = Some v.
  Proof. case v; [done|]=>/= *. by rewrite (decide_True_pi _). Qed.

  Lemma twp_eval_path W s E p v :
    eval_path p = Some v → ⊢ WP[W] p @ s; E [{ v', ⌜v' = v⌝ }].
  Proof.
    move: v. elim: p=>//.
    - move=> > [= ?]. by iApply twp_value.
    - move=> > ?? /of_to_val ?. by iApply twp_value.
    - case=>// e Wp. case=>//. case=>//= ?. move: Wp.
      case (eval_path e)=>//. case=>//. case=>// ? Wp _ ?[=<-].
      wp_bind e. iApply twp_wand; [by iApply Wp|]. iIntros. subst. by wp_op.
  Qed.

  Lemma eval_path_closed p v : eval_path p = Some v → Closed [] p.
  Proof.
    move: v. elim p=>//.
    - move=> >. rewrite /eval_path=> /of_to_val <-. apply is_closed_of_val.
    - case=>// e IH. case=>//. case=>//= ? _. move: IH. case (eval_path e)=>//.
      case=>//. case=>// ? IH ? _. move: (IH _ eq_refl). apply _.
  Qed.

  (** Type Context Element Interpretation *)
  Definition tctx_elt_interp {𝔄} (tid: thread_id) (t: tctx_elt 𝔄) (x: ~~ 𝔄)
    : iProp Σ := match t with
    | p ◁ ty => ∃v d, ⌜eval_path p = Some v⌝ ∗ ty_own ty x d d tid [FVal v]
    | p ◁{κ} bty => blocked_type_elim bty x (λ 𝔄₀ ty x₀ ,
      ∃v, ⌜eval_path p = Some v⌝ ∗
        ([†κ] =[verus_halt_wsat]{⊤}=∗ ∃x' d,
          (blockedπ x₀ :== @vπ 𝔄₀ x') ∗ (ty_own ty x' d d tid [FVal v]))
      )
     end%I.

  (* Block tctx_elt_interp from reducing with simpl when t is a constructor. *)
  Global Arguments tctx_elt_interp : simpl never.
End type_context.

(** Type Context Interpretation *)
Notation tctx_interp tid :=
  (big_sepHL_1 (λ 𝔄 t x, tctx_elt_interp (𝔄:=𝔄) tid t x)).

Section lemmas.
  Context `{!typeG FML Σ}.
  
  Lemma tctx_hasty_val {𝔄} (v: val) (ty: type 𝔄) vπ tid :
    tctx_elt_interp tid (v ◁ ty) vπ ⊣⊢ ∃d, ty_own ty vπ d d tid [FVal v].
  Proof.
    rewrite /tctx_elt_interp eval_path_of_val. iSplit.
    - iIntros "H". iDestruct "H" as (??[=->]) "?". iExists _. iFrame.
    - iDestruct 1 as (d) "?". iExists _, _. by iFrame.
  Qed.

  Lemma tctx_elt_interp_hasty_path {𝔄} p1 p2 (ty: type 𝔄) tid vπ :
    eval_path p1 = eval_path p2 →
    tctx_elt_interp tid (p1 ◁ ty) vπ ⊣⊢ tctx_elt_interp tid (p2 ◁ ty) vπ.
  Proof. move=> Hp. rewrite /tctx_elt_interp. by setoid_rewrite Hp. Qed.

  Lemma tctx_hasty_val' {𝔄} tid p v (ty: type 𝔄) vπ:
    Some v = eval_path p →
    tctx_elt_interp tid (p ◁ ty) vπ ⊣⊢ ∃d, ty_own ty vπ d d tid [FVal v].
  Proof.
    move=> ?. rewrite -tctx_hasty_val. apply tctx_elt_interp_hasty_path.
    by rewrite eval_path_of_val.
  Qed.

  Lemma twp_hasty {𝔄} W s E tid p (ty: type 𝔄) vπ Φ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗
    (∀v d, ⌜Some v = eval_path p⌝ -∗ ty_own ty vπ d d tid [FVal v] -∗ Φ v) -∗
    WP[W] p @ s; E [{ Φ }].
  Proof.
    iIntros "(%&%&%&?) ToΦ".
    iApply (twp_wand with "[]"); [by iApply twp_eval_path|].
    iIntros (?->). by iApply "ToΦ".
  Qed.

  Lemma closed_hasty {𝔄} tid p (ty: type 𝔄) vπ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗ ⌜Closed [] p⌝.
  Proof. iIntros "(%&%&%&_)!%". by eapply eval_path_closed. Qed.

  (** resolveing a Type Context *)

  Definition resolve_tctx {𝔄l} (E: elctx) (L: llctx) (T: tctx 𝔄l)
    (Φ: plist indep_interp_of_syn_type 𝔄l → proph_asn → Prop → Prop) : Prop :=
    ∀γ q F tid xl, Nverus_haltE ⊆ F →
      llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗ Ltok γ L q -∗
      tctx_interp tid T xl =[verus_halt_wsat]{F}=∗
        ⟨ π , ∀φ, Φ xl π φ → φ ⟩ ∗ Ltok γ L q.

  Lemma resolve_tctx_just {𝔄l} E L (T: tctx 𝔄l) : resolve_tctx E L T (const (const id)).
  Proof.
    move=> > ?. iIntros "_ _ _ _ tok _ $ !>". iFrame "tok".
    iApply proph_obs_true. done.
  Qed.

  Lemma resolve_tctx_nil E L : resolve_tctx E L +[] (const (const id)).
  Proof. apply resolve_tctx_just. Qed.
  
  Lemma resolve_tctx_cons_hasty {𝔄 𝔅l} E L p (ty: type 𝔄) Φ (T: tctx 𝔅l) Ψ :
    resolve E L ty Φ → resolve_tctx E L T Ψ →
    resolve_tctx E L (p ◁ ty +:: T) (λ '(a -:: bl) π φ, Φ a π → Ψ bl π φ).
  Proof.
    iIntros (Rslv Rslv' ????[??]?).
    iIntros "#LFT #PROPH #UNIQ #E tok /=[(%&%&_& A) T] W".
    iDestruct "A" as "[ty #phys]". iDestruct (Ltok_split_1 with "tok") as "[t1 t2]".
    iMod (Rslv with "LFT PROPH UNIQ E t1 ty W") as "(W & #Obs & t1)";
      [set_solver|].
    iMod (Rslv' with "LFT PROPH UNIQ E t2 T W") as "($ & #Obs' & t2)"; [done|].
    iModIntro. iDestruct (Ltok_split_2 with "t1 t2") as "$".
    iCombine "Obs Obs'" as "?".
    iApply proph_obs_impl; [|done]=>/= ?[? Imp]? Imp'. apply Imp, Imp'. trivial.
  Qed.

  Lemma resolve_tctx_cons_just {𝔄 𝔅l} E L (t: tctx_elt 𝔄) (T: tctx 𝔅l) Φ :
    resolve_tctx E L T Φ → resolve_tctx E L (t +:: T) (λ '(_ -:: bl), Φ bl).
  Proof.
    iIntros (Rslv ????[??]?) "LFT PROPH UNIQ E tok /=[_ T]".
    by iApply (Rslv with "LFT PROPH UNIQ E tok T").
  Qed.

  Lemma resolve_tctx_cons_just_hasty {𝔄 𝔅l} E L p (ty: type 𝔄) (T: tctx 𝔅l) Φ :
    resolve E L ty (const (const True)) → resolve_tctx E L T Φ →
    resolve_tctx E L (p ◁ ty +:: T) (λ '(_ -:: bl), Φ bl).
  Proof. move=> ?. apply resolve_tctx_cons_just. Qed.

  Lemma resolve_tctx_cons_just_blocked {𝔄 𝔅l} E L p κ (ty: type 𝔄) (T: tctx 𝔅l) Φ :
    resolve_tctx E L T Φ → resolve_tctx E L (p ◁{κ} (blocked_type_ctor 𝔄 ty) +:: T) (λ '(_ -:: bl), Φ bl).
  Proof. apply resolve_tctx_cons_just. Qed.

  (** Type Context Inclusion *)

  Definition tctx_incl {𝔄l 𝔅l} (E: elctx) (L: llctx) (T: tctx 𝔄l) (T': tctx 𝔅l)
    (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    Proper ((≡) ==> (≡)) tr ∧
    ∀γ q tid xl mask post,
      llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗ Ltok γ L q -∗
      tctx_interp tid T xl -∗ ⟨π, tr post xl mask π⟩
      =[verus_halt_wsat]{⊤}=∗
      ∃xl', Ltok γ L q ∗ tctx_interp tid T' xl' ∗ ⟨π, post xl' mask π⟩.

  Lemma tctx_incl_impl {𝔄l 𝔅l} (T: tctx 𝔄l) (T': tctx 𝔅l)
                       (tr tr': predl_trans 𝔄l 𝔅l) E L :
    tctx_incl E L T T' tr' → (∀post xl mask π, tr post xl mask π → tr' post xl mask π) →
    Proper ((≡) ==> (≡)) tr →
    tctx_incl E L T T' tr.
  Proof.
    move=> [? In] Imp. split; [done|].
    iIntros (??????) "LFT PROPH UNIQ E tok T #Obs".
    iApply (In with "LFT PROPH UNIQ E tok T []").
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  Lemma tctx_incl_ext {𝔄l 𝔅l} (T: tctx 𝔄l) (T': tctx 𝔅l) tr tr' E L :
    tctx_incl E L T T' tr' → (∀post xl mask π, tr post xl mask π ↔ tr' post xl mask π) →
    tctx_incl E L T T' tr.
  Proof.
    move=> In Eq. eapply tctx_incl_impl; [done| |].
    - move=> ????. by rewrite Eq.
    - move=> ??????. rewrite !Eq. by apply In.
 Qed.

  Lemma tctx_incl_refl {𝔄l} (T: tctx 𝔄l) E L : tctx_incl E L T T id.
  Proof.
    split; [by apply _|]. move=> ?? ? vπl ??. iIntros "_ _ _ _ $ T Obs $ !>".
    iExists vπl. by iFrame.
  Qed.

  Lemma tctx_incl_trans {𝔄l 𝔅l ℭl} tr tr' (T1: tctx 𝔄l) (T2: tctx 𝔅l) (T3: tctx ℭl) E L :
    tctx_incl E L T1 T2 tr → tctx_incl E L T2 T3 tr' → tctx_incl E L T1 T3 (tr ∘ tr').
  Proof.
    move=> In In'. split.
    { eapply compose_proper; [apply In|apply In']. }
    iIntros "*". iIntros "#LFT #PROPH #UNIQ #E tok T Obs W".
    destruct In as [? In]. destruct In' as [? In'].
    iMod (In with "LFT PROPH UNIQ E tok T Obs W") as "[W (%&tok&T&Obs)]".
    iMod (In' with "LFT PROPH UNIQ E tok T Obs W") as "[$ (%vπl''&?&?&?)]".
    iModIntro. iExists vπl''. by iFrame.
  Qed.

  Lemma tctx_incl_app {𝔄l 𝔅l ℭl 𝔇l}
    (T1: tctx 𝔄l) (T1': tctx 𝔅l) (T2: tctx ℭl) (T2': tctx 𝔇l) tr tr' E L :
    tctx_incl E L T1 T1' tr → tctx_incl E L T2 T2' tr' →
    tctx_incl E L (T1 h++ T2) (T1' h++ T2') (trans_app tr tr').
  Proof.
    move=> [? In1] [? In2]. split; [apply _|].
    move=>??? vπl ??. move: (papp_ex vπl)=> [?[?->]].
    iIntros "#LFT #PROPH #UNIQ #E tok [T1 T2] Obs W".
    iMod (In1 with "LFT PROPH UNIQ E tok T1 [Obs] W")
      as "[W (%wπl & tok & T1' & Obs)]".
    { iApply proph_obs_eq; [|done]=> ?.
      rewrite /trans_app.
      (* rewrite papply_app *)
      rewrite papp_sepl.
      rewrite papp_sepr.
      done. }
    iMod (In2 with "LFT PROPH UNIQ E tok T2 Obs W")
      as "[$ (%wπl' & tok & T2' &?)]".
    iModIntro. iExists (wπl -++ wπl'). iFrame "tok T1' T2'".
    iApply proph_obs_eq; [|done]=>/= ?. done.
  Qed.

  Lemma tctx_incl_frame_l {𝔄l 𝔅l ℭl} (T: tctx 𝔄l) (T': tctx 𝔅l) (Tf: tctx ℭl) tr E L :
    tctx_incl E L T T' tr → tctx_incl E L (Tf h++ T) (Tf h++ T') (trans_lower tr).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { apply tctx_incl_app; [|done]. apply tctx_incl_refl. }
    done.
  Qed.
  Lemma tctx_incl_frame_r {𝔄l 𝔅l ℭl} (T: tctx 𝔄l) (T': tctx 𝔅l) (Tf: tctx ℭl) tr E L :
    tctx_incl E L T T' tr → tctx_incl E L (T h++ Tf) (T' h++ Tf) (trans_upper tr).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { apply tctx_incl_app; [done|]. apply tctx_incl_refl. }
    done.
  Qed.
  Lemma tctx_incl_tail {𝔄 𝔄l 𝔅l} (t: tctx_elt 𝔄) (T1: tctx 𝔄l) (T2: tctx 𝔅l) tr E L :
    tctx_incl E L T1 T2 tr → tctx_incl E L (t +:: T1) (t +:: T2) (trans_tail tr).
  Proof.
    move=> ?. eapply tctx_incl_ext. { by apply (tctx_incl_frame_l _ _ +[_]). }
    by move=> ?[??].
  Qed.

  Lemma tctx_incl_swap {𝔄 𝔅 𝔄l} (t: tctx_elt 𝔄) (t': tctx_elt 𝔅) (T: tctx 𝔄l) E L :
    tctx_incl E L (t +:: t' +:: T) (t' +:: t +:: T)
      (λ post '(a -:: b -:: al), post (b -:: a -:: al)).
  Proof.
    split; [by intros ??? [? [? ?]]|].
    iIntros (???(vπ & vπ' & wπl)??) "_ _ _ _ $ (?&?&?) ? $ !>".
    iExists (vπ' -:: vπ -:: wπl). iFrame.
  Qed.

  Lemma tctx_incl_resolve_head {𝔄 𝔅l} (t: tctx_elt 𝔄) (T: tctx 𝔅l) E L :
    tctx_incl E L (t +:: T) T (λ post '(_ -:: bl), post bl).
  Proof.
    split; [by intros ??? [? ?]|].
    iIntros (???[??]??) "_ _ _ _ $ [_ T] ? $ !>". iExists _. by iFrame "T".
  Qed.

  Lemma tctx_incl_resolve_lower {𝔄l 𝔅l} (T: tctx 𝔄l) (T': tctx 𝔅l) E L :
    tctx_incl E L (T h++ T') T (λ post abl, post (psepl abl)).
  Proof.
    split; [by intros ????|].
    move=> ??? abπl ??. move: (papp_ex abπl)=> [aπl[?->]].
    iIntros "_ _ _ _ $ [T _] ? $ !>". iExists aπl. iFrame "T".
    iApply proph_obs_eq; [|done]=> ?. by rewrite/= papp_sepl.
  Qed.

  Definition tctx_equiv {𝔄l} (T T': tctx 𝔄l) : Prop :=
    ∀E L, tctx_incl E L T T' id ∧ tctx_incl E L T' T id.

  Lemma get_tctx_equiv {𝔄l} (T T': tctx 𝔄l) :
    (∀tid vπl, tctx_interp tid T vπl ⊣⊢ tctx_interp tid T' vπl) → tctx_equiv T T'.
  Proof.
    move=> Eq ??; split; (split; [apply _|]);
      iIntros (??????) "_ _ _ _ $ T Obs $ !>"; iExists _; rewrite Eq; iFrame.
  Qed.

  Lemma copy_tctx_incl {𝔄 𝔄l} (ty: type 𝔄) `{!Copy ty} (T: tctx 𝔄l) p E L :
    tctx_incl E L (p ◁ ty +:: T) (p ◁ ty +:: p ◁ ty +:: T)
      (λ post '(a -:: al), post (a -:: a -:: al)).
  Proof.
    split; [by intros ??? [??]|].
    iIntros (???[vπ wπl]??) "_ _ _ _ $ /=[#? T] Obs $ !>".
    iExists (vπ -:: vπ -:: wπl). iFrame "Obs T". by iSplit.
  Qed.

  Lemma tctx_to_shift_loc_0 {𝔄 𝔅l} (ty: type 𝔄) p (T: tctx 𝔅l) E L :
    JustLoc ty → tctx_incl E L (p ◁ ty +:: T) (p +ₗ #0 ◁ ty +:: T) id.
  Proof.
    intros JLoc. split; [apply _|].
    - iIntros (???[??]??) "_ _ _ _ $ /=[(%&%& %Ev & A) T] Obs $ !>".
      iDestruct "A" as "[ty %phys1]".
      iExists (_-::_). iDestruct (JLoc with "ty") as (l) "%phys2".
      iFrame "T Obs". iExists v, _. iFrame "ty". iSplit.
      { iPureIntro. rewrite/= Ev.
        assert (v = #l) as Hvl. { rewrite phys1 in phys2. inversion phys2. trivial. }
        subst v. by rewrite/= shift_loc_0.
      } { iPureIntro. trivial. }
  Qed.

  Lemma tctx_of_shift_loc_0 {𝔄 𝔅l} (ty: type 𝔄) p (T: tctx 𝔅l) E L :
    tctx_incl E L (p +ₗ #0 ◁ ty +:: T) (p ◁ ty +:: T) id.
  Proof.
    split; [apply _|].
    iIntros (???[??]??) "_ _ _ _ $ /=[(%&%& %Ev & ty) T] Obs $ !>".
    iExists (_-::_). iFrame "T Obs". iExists _, _. iFrame "ty". iPureIntro.
    move: Ev=>/=. case (eval_path p)=>//. (do 2 case=>//)=> ?. by rewrite shift_loc_0.
  Qed.

  Lemma tctx_shift_loc_assoc {𝔄 𝔅l} (ty: type 𝔄) p (T: tctx 𝔅l) (z z': Z) :
    tctx_equiv (p +ₗ #z +ₗ #z' ◁ ty +:: T) (p +ₗ #(z + z') ◁ ty +:: T).
  Proof.
    apply get_tctx_equiv=>/= ?[??]. f_equiv.
    rewrite tctx_elt_interp_hasty_path; [done|]=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc.
  Qed.

  Lemma subtype_tctx_incl {𝔄 𝔅 𝔄l} ty ty' (f: 𝔄 →ₛ 𝔅) (T: tctx 𝔄l) p E L :
    subtype E L ty ty' f →
    tctx_incl E L (p ◁ ty +:: T) (p ◁ ty' +:: T)
      (λ post '(a -:: al), post (f ~~$ₛ a -:: al)).
  Proof.
    intros Sub. split; [by intros ??? [??]|].
    iIntros (???[x wπl]??) "#LFT _ _ E tok /=[(%v & %d &%& A) T] Obs W /=".
    iDestruct "A" as "[ty %phys]".
    iDestruct (Ltok_acc with "tok W") as "[L1 back]".
    iDestruct (Sub with "L1 E") as "#(_ & _ & #InOwn & #InOwnPers & %InPhys)".
    iDestruct ("back" with "L1") as "[$ tok]".
    iModIntro.
    iExists (f ~~$ₛ x -:: wπl). iFrame "tok T".
    iSplitR "Obs".
    - iExists v, d. iSplit; [done|].
      iDestruct ("InOwn" $! _ alt_here with "ty") as "[ty1 _]".
      iFrame.
      iPureIntro. rewrite <- InPhys. trivial.
    - iApply (proph_obs_impl with "Obs"). intros. done.
  Qed.

  (* Extracting from a type context. *)

  Definition tctx_extract_elt {𝔄 𝔄l 𝔅l} E L (t: tctx_elt 𝔄)
    (T: tctx 𝔄l) (T': tctx 𝔅l) (tr: predl_trans 𝔄l (𝔄 :: 𝔅l)) : Prop :=
    tctx_incl E L T (t +:: T') tr.

  Lemma tctx_extract_elt_further {𝔄 𝔅 𝔄l 𝔅l}
    (t: tctx_elt 𝔄) (t': tctx_elt 𝔅) (T: tctx 𝔄l) (T': tctx 𝔅l) tr E L :
    tctx_extract_elt E L t T T' tr →
    tctx_extract_elt E L t (t' +:: T) (t' +:: T')
      (λ post '(b -:: al), tr (λ '(a -:: bl), post (a -:: b -:: bl)) al).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; by [eapply tctx_incl_tail|apply tctx_incl_swap]. }
    move=> ?[??]/=. f_equal.
  Qed.

  Lemma tctx_extract_elt_here_copy {𝔄 𝔅 𝔄l} ty ty' (f: 𝔅 →ₛ 𝔄) (T: tctx 𝔄l) p p' E L :
    p = p' → Copy ty' → subtype E L ty' ty f →
    tctx_extract_elt E L (p ◁ ty) (p' ◁ ty' +:: T) (p' ◁ ty' +:: T)
      (λ post '(b -:: al), post (f ~~$ₛ b -:: b -:: al)).
  Proof.
    move=> ->??. eapply tctx_incl_ext.
    { by eapply tctx_incl_trans; [apply copy_tctx_incl|apply subtype_tctx_incl]. }
    by move=> ?[??].
  Qed.

  Lemma tctx_extract_elt_here_exact {𝔄 𝔄l} (t: tctx_elt 𝔄) (T: tctx 𝔄l) E L :
    tctx_extract_elt E L t (t +:: T) T id.
  Proof. apply tctx_incl_refl. Qed.

  Lemma tctx_extract_elt_here {𝔄 𝔅 𝔄l} ty ty' (f: 𝔅 →ₛ 𝔄) (T: tctx 𝔄l) p E L :
    subtype E L ty' ty f →
    tctx_extract_elt E L (p ◁ ty) (p ◁ ty' +:: T) T
      (λ post '(b -:: al), post (f ~~$ₛ b -:: al)).
  Proof.
    move=> ?. eapply tctx_incl_ext; [by apply subtype_tctx_incl|]. by move=> ?[??].
  Qed.

  Definition tctx_extract_ctx {𝔄l 𝔅l ℭl} E L (T: tctx 𝔄l)
    (T1: tctx 𝔅l) (T2: tctx ℭl) (tr: predl_trans 𝔅l (𝔄l ++ ℭl)) : Prop :=
    tctx_incl E L T1 (T h++ T2) tr.

  Lemma tctx_extract_ctx_eq {𝔄l 𝔅l ℭl} tr tr' E L
                            (T: tctx 𝔄l) (T1: tctx 𝔅l) (T2: tctx ℭl) :
    tctx_extract_ctx E L T T1 T2 tr' → tr = tr' → tctx_extract_ctx E L T T1 T2 tr.
  Proof. by move=> ?->. Qed.

  Lemma tctx_extract_ctx_nil {𝔄l} (T: tctx 𝔄l) E L :
    tctx_extract_ctx E L +[] T T id.
  Proof. apply tctx_incl_refl. Qed.

  Lemma tctx_extract_ctx_elt {𝔄 𝔄l 𝔅l ℭl 𝔇l}
      (t: tctx_elt 𝔄) (T: tctx 𝔄l) (T1: tctx 𝔅l) (T2: tctx ℭl) (T3: tctx 𝔇l)
      tr tr' E L :
    tctx_extract_elt E L t T1 T2 tr → tctx_extract_ctx E L T T2 T3 tr' →
    tctx_extract_ctx E L (t +:: T) T1 T3 (tr ∘ trans_tail tr').
  Proof. move=> ??. eapply tctx_incl_trans; by [|apply tctx_incl_tail]. Qed.

  Lemma tctx_extract_ctx_incl {𝔄l 𝔅l ℭl} (T: tctx 𝔄l) (T': tctx 𝔅l) (Tx: tctx ℭl) tr E L :
    tctx_extract_ctx E L T' T Tx tr →
    tctx_incl E L T T' (λ post, tr (λ bcl, post (psepl bcl))).
  Proof.
    move=> Ex. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [apply Ex|apply tctx_incl_resolve_lower]. }
    done.
  Qed.

  (** resolveing for Unblocking *)

  (* [κ] is a dummy parameter for automation *)
  Definition resolve_unblock_tctx {𝔄l 𝔅l} (E: elctx) (L: llctx) (κ: lft)
      (T: tctx 𝔄l) (T': tctx 𝔅l) (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    ∀γ q tid xl post mask,
      llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗ Ltok γ L q -∗
      tctx_interp tid T xl -∗ ⟨π, tr post xl mask π⟩ =[verus_halt_wsat]{⊤}=∗
        ∃xl', Ltok γ L q ∗ tctx_interp tid T' xl' ∗ ⟨π, post xl' mask π⟩.

  Lemma resolve_unblock_tctx_impl {𝔄l 𝔅l} (tr tr': predl_trans 𝔄l 𝔅l) T T' E L κ :
    resolve_unblock_tctx E L κ T T' tr' → (∀post al mask π, tr post al mask π → tr' post al mask π) →
    resolve_unblock_tctx E L κ T T' tr.
  Proof.
    iIntros (RslvU Imp ??????) "LFT PROPH UNIQ E tok T Obs".
    iApply (RslvU with "LFT PROPH UNIQ E tok T [Obs]").
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  Lemma resolve_unblock_tctx_nil κ E L : resolve_unblock_tctx E L κ +[] +[] id.
  Proof.
    iIntros (???[]??) "/= _ _ _ _ tok _ Obs $ !>". iExists -[]. by iFrame.
  Qed.

  Lemma resolve_unblock_tctx_cons_resolve {𝔄 𝔅l ℭl} (ty: type 𝔄) p Φ
      (T: tctx 𝔅l) (T': tctx ℭl) tr κ E L :
    κ ∈ ty_lfts ty → resolve' E L ty Φ → resolve_unblock_tctx E L κ T T' tr →
    resolve_unblock_tctx E L κ (p ◁ ty +:: T) T'
      (λ post '(a -:: bl), tr (λ cl mask π, Φ a π (post cl mask π)) bl).
  Proof.
    iIntros (_ Rslv RslvU ???[vπ ?]??)
      "#LFT #PROPH #UNIQ #E tok /=[(%& %d &_& A) T] Obs W".
    iDestruct "A" as "[ty %phys]". iDestruct (Ltok_split_1 with "tok") as "[t1 t2]".
    iMod (Rslv with "LFT PROPH UNIQ E t1 ty W") as "(W & #Obs1 & t1)"; [done|].
    iMod (RslvU with "LFT PROPH UNIQ E t2 T Obs W")
      as "($ & %vπl' & t2 & T' & #Obs')".
    iModIntro. iExists vπl'. iDestruct (Ltok_split_2 with "t1 t2") as "$".
    iFrame "T'". iCombine "Obs1 Obs'" as "?".
    iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. apply Imp. trivial.
  Qed.

  Lemma resolve_unblock_tctx_cons_keep {𝔄 𝔅l ℭl} (t: tctx_elt 𝔄)
      (T: tctx 𝔅l) (T': tctx ℭl) tr κ E L :
    resolve_unblock_tctx E L κ T T' tr →
    resolve_unblock_tctx E L κ (t +:: T) (t +:: T') (trans_tail tr).
  Proof.
    iIntros (RslvU ???[vπ ?]??) "LFT PROPH UNIQ E tok /=[t T] Obs W".
    iMod (RslvU with "LFT PROPH UNIQ E tok T Obs W")
      as "($ & %vπl' & tok & T' & Obs')". iModIntro.
    iExists (vπ -:: vπl'). iFrame.
  Qed.

  (** Unblocking a Type Context *)
  
  Definition unblock_tctx {𝔄l 𝔄l'} (E: elctx) (L: llctx) (κ: lft) (T: tctx 𝔄l) (T': tctx 𝔄l')
    (f: proph_asn → plist indep_interp_of_syn_type 𝔄l → plist indep_interp_of_syn_type 𝔄l' → Prop) : Prop :=
    ∀γ q tid xl, llft_ctx -∗ proph_ctx -∗ elctx_interp E -∗ Ltok γ L q -∗
      [†κ] -∗ tctx_interp tid T xl =[verus_halt_wsat]{⊤}=∗ ∃xl',
        Ltok γ L q ∗ tctx_interp tid T' xl' ∗ ⟨π, f π xl xl'⟩.

  Lemma unblock_tctx_nil κ E L : unblock_tctx E L κ +[] +[] (λ _ _ _, True).
  Proof.
    iIntros (???[]) "_ _ _ $ _ _ $ !>". iExists -[]. iSplit; [done|].
    by iApply proph_obs_true.
  Qed.

  Lemma unblock_tctx_cons_unblock {𝔄 𝔄l 𝔄l'} p (ty: type 𝔄) (T: tctx 𝔄l) (T': tctx 𝔄l') κ E L f :
    lctx_lft_alive E L (ty_lft ty) → unblock_tctx E L κ T T' f →
    unblock_tctx E L κ (p ◁{κ} blocked_type_ctor _ ty +:: T) (p ◁ ty +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'), blockedπ x π = vπ x' π ∧ f π xl xl').
  Proof.
    iIntros (Alv Un ???[??]) "#LFT #PROPH #E [#ktok f] #†κ /=[(%v &%& Upd) T] W".
    iAssert (Ltok γ L q) with "[$ktok $f]" as "tok".
    iMod ("Upd" with "†κ W") as "[W (%x' & %d & Eqz & ty)]".
    iDestruct (Ltok_acc with "tok W") as "[L1 back]".
    iDestruct (Alv with "L1 E") as "#Lkg".
    iDestruct ("back" with "L1") as "[W tok]".
    iDestruct (Ltok_split_1 with "tok") as "[t1 t2]".
    iMod (Un with "LFT PROPH E t1 †κ T W") as "(W & %xl' & t1 & T & #Obs2)".
    iDestruct "ty" as "[gho phys]".
    iDestruct (ty_gho_pers_impl with "gho") as "#ghoPers".
    (* The original builds this under [▷^(d*(d+1))] and then strips the
      laters with the credits [⧗1] bought; here the guards compose
      directly. *)
    (* The law hands the whole family out under [Wguard], so it is opened
      once here rather than per prophecy variable. *)
    iAssert (|->[Wguard] (∀ ζ, ⌜ζ ∈ ξl x'⌝ -∗
      ((Ltok γ L (q/2) ∗ ty_gho ty x' d d tid) &&{Wguard}&&> 1:[ζ])))%I
      as "Hall0".
    { iApply (ty_guard_proph _ ty (foldr meet static (ty_lfts ty))%I x' d d
        tid (Ltok γ L (q/2) ∗ ty_gho ty x' d d tid) with "LFT [] ghoPers").
      - iApply fguard_refl.
      - iApply guard_lhs_sep_l. iApply (guard_trans with "[] Lkg").
        iApply (Ltok_guard with "ktok").
      - iApply guard_sep_r. }
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct ("Hall0" with "Wg") as "[Wg #Hallζ]".
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    iMod (proph_eqz_to_obs_with_guard (W:=verus_halt_wsat) (WG:=Wguard)
      with "Hallζ [$t2 $gho] Eqz W") as "[W [#Obs [t2 gho]]]";
      [solve_ndisj|apply syn_indep|].
    iModIntro. iFrame "W". iExists (x' -:: xl').
    iDestruct (Ltok_split_2 with "t1 t2") as "$". iFrame "T". iSplitL "gho phys". { iExists v, d. by iFrame. }
    iCombine "Obs Obs2" as "Obs3". iApply "Obs3".
  Qed.

  Lemma unblock_tctx_cons_just {𝔄 𝔄l 𝔄l'} (t: tctx_elt 𝔄) (T: tctx 𝔄l) (T': tctx 𝔄l') κ E L f :
    unblock_tctx E L κ T T' f →
    unblock_tctx E L κ (t +:: T) (t +:: T')
        (λ π '(x -:: xl), λ '(x' -:: xl'), x = x' ∧ f π xl xl').
  Proof.
    iIntros (Un ??? [x xl]) "LFT PROPH E tok †κ /=[t T] W".
    iMod (Un with "LFT PROPH E tok †κ T W") as "($ & %xl' & tok & T' & Obs)".
    iModIntro. iExists (x -:: xl'). iFrame "tok T' t".
    iApply (proph_obs_impl with "Obs"); split; trivial.
  Qed.

  Lemma unblock_tctx_cons_just_hasty {𝔄 𝔄l} p (ty: type 𝔄) (T: tctx 𝔄l) (T': tctx 𝔄l) κ E L f :
    unblock_tctx E L κ T T' f →
    unblock_tctx E L κ (p ◁ ty +:: T) (p ◁ ty +:: T')
        (λ π '(x -:: xl), λ '(x' -:: xl'), x = x' ∧ f π xl xl').
  Proof. apply unblock_tctx_cons_just. Qed.

  Lemma unblock_tctx_cons_just_blocked {𝔄 𝔄l} p (ty: type 𝔄) (T: tctx 𝔄l) (T': tctx 𝔄l) κ κ' E L f :
    κ ≠ κ' → unblock_tctx E L κ T T' f →
    unblock_tctx E L κ (p ◁{κ'} (blocked_type_ctor _ ty) +:: T) (p ◁{κ'} (blocked_type_ctor _ ty) +:: T')
        (λ π '(x -:: xl), λ '(x' -:: xl'), x = x' ∧ f π xl xl').
  Proof. move=> ?. apply unblock_tctx_cons_just. Qed.
End lemmas.

Ltac solve_extract :=
  eapply tctx_extract_ctx_eq; [solve_typing|];
  rewrite /trans_tail /compose /=; by reflexivity.

Ltac solve_resolve_unblock :=
  eapply resolve_unblock_tctx_impl; [solve_typing|]=> ??;
  rewrite /trans_tail /=; by exact id.

Global Hint Resolve resolve_tctx_nil : lrust_typing.
(* Mysteriously, registering [resolve_tctx_cons_*] with [Global Hint Resolve]
  does not help automation in some situations,
  but the following hints let automation work *)
Global Hint Extern 10 (resolve_tctx _ _ _ _) =>
  simple apply resolve_tctx_cons_hasty : lrust_typing.
Global Hint Extern 0 (resolve_tctx _ _ _ _) =>
  simple apply resolve_tctx_cons_just_hasty : lrust_typing.
Global Hint Extern 0 (resolve_tctx _ _ _ _) =>
  simple apply resolve_tctx_cons_just_blocked : lrust_typing.

Global Hint Resolve tctx_extract_elt_here_copy | 1 : lrust_typing.
Global Hint Resolve tctx_extract_elt_here_exact | 2 : lrust_typing.
Global Hint Resolve tctx_extract_elt_here | 20 : lrust_typing.
(* We need [eapply] to use [tctx_extract_elt_further] *)
Global Hint Extern 50 (tctx_extract_elt _ _ _ _ _ _) =>
  eapply tctx_extract_elt_further : lrust_typing.

Global Hint Resolve tctx_extract_ctx_nil tctx_extract_ctx_elt
  tctx_extract_ctx_incl : lrust_typing.

Global Hint Resolve resolve_unblock_tctx_nil resolve_unblock_tctx_cons_resolve
  : lrust_typing.
Global Hint Resolve resolve_unblock_tctx_cons_keep | 20 : lrust_typing.

Global Hint Resolve unblock_tctx_nil unblock_tctx_cons_unblock
  unblock_tctx_cons_just_hasty unblock_tctx_cons_just_blocked : lrust_typing.

Global Hint Opaque resolve_tctx tctx_incl tctx_extract_elt tctx_extract_ctx
  resolve_unblock_tctx unblock_tctx : lrust_typing.
