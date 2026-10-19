(** * Lifetime contexts

  Ported from VerusBelt ([typing/lft_contexts.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  The types [elctx], [llctx] and the interpretation [llctx_interp] live in
  [nola.alerus.typing.ctx], since the global world satisfaction has to mention
  them.  What is left here changes in two places.

  - Every [&&{↑NllftG}&&>] becomes [&&{Wguard}&&>], the guard over
    [alerus_WGuard].  The guard combinators are nola's: [guards_refl] is
    [guard_refl], [guards_transitive] is [guard_trans], [guards_and_point] is
    [guard_and], and [leaf_by_sep] is [guard_intro].
  - [llctx_interp_make_guarded] used Leaf's [frac_split_guard_in_half], i.e. a
    storage protocol over an arbitrary proposition.  Here it is
    [frac_key_split_in_half]: [llctx_interp L] is determined by the Coq value
    [L], so a world satisfaction keyed by ghost names can hold it directly.
    The result carries no later, so the [Timeless] side condition Leaf needed
    is gone too. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.util Require Import basic.
From nola.alerus.typing Require Export base ctx lifetime.
From nola.bi Require Import guard modw.
From nola.iris Require Import point.
Import GuardNotation ModwNotation.

(* External lifetime context. *)
(** An external lifetime-context entry is a *stored* inclusion: it ends up
  inside [&uniq{κ}]'s ghost assertion, which is a formula.  See [AltSem] in
  [typing/ctx.v]. *)
Definition elctx_elt_interp `{!alerusGS FML Σ, !AlerusSem FML Σ, !GsrcSem FML Σ, !TypeFml FML Σ,
  !AltSem FML Σ} (x : elctx_elt) : iProp Σ := dincl x.1 x.2.
Notation elctx_interp := (big_sepL (λ _, elctx_elt_interp)).

Section lft_contexts.
  Context `{!alerusGS FML Σ, !AlerusSem FML Σ, !GsrcSem FML Σ, !TypeFml FML Σ, !AltSem FML Σ}.
  Implicit Type (κ: lft).

  Global Instance elctx_interp_permut :
    Proper ((≡ₚ) ==> (⊣⊢)) elctx_interp.
  Proof. intros ???. by apply big_opL_permutation. Qed.
  Global Instance elctx_interp_persistent E : Persistent (elctx_interp E).
  Proof. apply _. Qed.
  Lemma elctx_interp_app (E1 E2 : elctx) :
    elctx_interp (E1 ++ E2) ⊣⊢ elctx_interp E1 ∗ elctx_interp E2.
  Proof. apply big_sepL_app. Qed.

  Global Instance llctx_elt_interp_timeless (x: llctx_elt) :
    Timeless (llctx_elt_interp x).
  Proof. typeclasses eauto. Qed.

  Global Instance llctx_interp_timeless (L: llctx) : Timeless (llctx_interp L).
  Proof. typeclasses eauto. Qed.

  Global Instance llctx_interp_permut :
    Proper ((≡ₚ) ==> (⊣⊢)) llctx_interp.
  Proof. intros x y Hequiv. apply big_opL_permutation. trivial. Qed.

  Lemma lctx_equalize_lft κ1 κ2 :
    llctx_elt_interp (κ1 ⊑ₗ [κ2]%list) =[alerus_wsat]=∗
      elctx_elt_interp (κ1 ⊑ₑ κ2) ∗ elctx_elt_interp (κ2 ⊑ₑ κ1).
  Proof.
    iDestruct 1 as (κ) "(% & Hκ & _)"; simplify_eq/=.
    iIntros "W". iMod (dincl_eternalize with "Hκ W") as "[$ #Hincl]".
    iModIntro. iSplit.
    - iApply (dincl_trans with "[] []"); iApply dincl_intersect_l.
    - iApply (dincl_glb with "[]"); first iApply (dincl_glb with "[]").
      + iApply dincl_refl.
      + iApply dincl_static.
      + iApply (dincl_trans with "[] Hincl"). iApply dincl_static.
  Qed.

  (** Shared access to a local lifetime context.

    The original goes through Leaf's [frac_split_guard_in_half] with
    [guards_refl], storing [llctx_interp L] in a storage protocol; here it is
    deposited into [frac_key_wsat] and the share is [Ltok] (see
    [nola.alerus.typing.ctx]). *)
  Lemma llctx_interp_make_guarded (L : llctx) :
    llctx_interp L =[alerus_wsat]=∗ ∃ (γ: gname),
      Ltok γ L (1/2) ∗ Ltok γ L (1/2) ∗
      □ (Ltok γ L (1/2) -∗ Ltok γ L (1/2) =[alerus_wsat]=∗ llctx_interp L).
  Proof.
    iIntros "L W". iMod (Ltok_alloc with "L W") as "[$ [%γ tok]]".
    iModIntro. iExists γ. rewrite {1}Ltok_split. iDestruct "tok" as "[$$]".
    iIntros "!> t t' W". iApply (Ltok_withdraw with "[t t'] W").
    rewrite (Ltok_split (q:=1)). iFrame.
  Qed.

  Context (E : elctx) (L : llctx).

  (* Lifetime inclusion *)
  Definition lctx_lft_incl κ κ' : Prop :=
    llctx_interp L -∗ □ (elctx_interp E -∗ dincl κ κ').

  Definition lctx_lft_eq κ κ' : Prop :=
    lctx_lft_incl κ κ' ∧ lctx_lft_incl κ' κ.

  Lemma lctx_lft_incl_incl κ κ' : lctx_lft_incl κ κ' → lctx_lft_incl κ κ'.
  Proof. done. Qed.

  Lemma lctx_lft_incl_refl κ : lctx_lft_incl κ κ.
  Proof. iIntros "A". iModIntro. iIntros "B". iApply dincl_refl. Qed.

  Global Instance lctx_lft_incl_preorder : PreOrder lctx_lft_incl.
  Proof.
    split; first by intros ?; apply lctx_lft_incl_refl.
    - iIntros (??? H1 H2) "HL".
      iDestruct (H1 with "HL") as "#H1".
      iDestruct (H2 with "HL") as "#H2".
      iClear "∗". iIntros "!> #HE". iApply dincl_trans.
      { by iApply "H1". } by iApply "H2".
  Qed.

  Global Instance lctx_lft_incl_proper :
    Proper (lctx_lft_eq ==> lctx_lft_eq ==> iff) lctx_lft_incl.
  Proof. intros ??[] ??[]. split; intros; by etrans; [|etrans]. Qed.

  Global Instance lctx_lft_eq_equivalence : Equivalence lctx_lft_eq.
  Proof.
    split.
    - by split.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; etrans; (apply H1 || apply H2).
  Qed.

  Lemma lctx_lft_incl_static κ : lctx_lft_incl κ static.
  Proof. iIntros "_ !> _". iApply dincl_static. Qed.

  Lemma lctx_lft_incl_local κ κ' κs :
    κ ⊑ₗ κs ∈ L → κ' ∈ κs → lctx_lft_incl κ κ'.
  Proof.
    iIntros (? Hκ'κs) "H".
    iDestruct (big_sepL_elem_of with "H") as "H"; first done.
    iDestruct "H" as (κ'') "[EQ _]". iDestruct "EQ" as %EQ.
    simpl in EQ; subst. iIntros "!> #HE".
    iApply dincl_trans; first by iApply dincl_intersect_l.
    by iApply dincl_intersect_list_elem_of.
  Qed.

  Lemma lctx_lft_incl_local' κ κ' κ'' κs :
    κ ⊑ₗ κs ∈ L → κ' ∈ κs → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; last done. by eapply lctx_lft_incl_local. Qed.

  Lemma lctx_lft_incl_external κ κ' : κ ⊑ₑ κ' ∈ E → lctx_lft_incl κ κ'.
  Proof.
    iIntros (?) "_!>?". by rewrite /elctx_elt_interp big_sepL_elem_of //.
  Qed.

  Lemma lctx_lft_incl_external' κ κ' κ'' :
    κ ⊑ₑ κ' ∈ E → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; [|done]. by eapply lctx_lft_incl_external. Qed.

  Lemma lctx_lft_incl_intersect κ κ' κ'' :
    lctx_lft_incl κ κ' → lctx_lft_incl κ κ'' →
    lctx_lft_incl κ (κ' ⊓ κ'').
  Proof.
    iIntros (Hκ' Hκ'') "HL".
    iDestruct (Hκ' with "HL") as "#Hκ'".
    iDestruct (Hκ'' with "HL") as "#Hκ''".
    iIntros "!> #HE". iApply dincl_glb. by iApply "Hκ'". by iApply "Hκ''".
  Qed.

  Lemma lctx_lft_incl_intersect_l κ κ' κ'' :
    lctx_lft_incl κ κ' → lctx_lft_incl (κ ⊓ κ'') κ'.
  Proof.
    iIntros (Hκ') "HL". iDestruct (Hκ' with "HL") as "#Hκ'".
    iIntros "!> #HE". iApply dincl_trans.
      by iApply dincl_intersect_l. by iApply "Hκ'".
  Qed.

  Lemma lctx_lft_incl_intersect_r κ κ' κ'' :
    lctx_lft_incl κ κ' → lctx_lft_incl (κ'' ⊓ κ) κ'.
  Proof.
    iIntros (Hκ') "HL". iDestruct (Hκ' with "HL") as "#Hκ'".
    iIntros "!> #HE". iApply dincl_trans.
      by iApply dincl_intersect_r. by iApply "Hκ'".
  Qed.

  (* Lifetime aliveness *)

  Definition lctx_lft_alive (κ : lft) : Prop :=
    llctx_interp L ⊢ elctx_interp E -∗ (llctx_interp L &&{Wguard}&&> @[κ]).

  (** The same at *every* candidate interpretation.

    A function call stores the inclusions of [fp_E], and it builds them out of
    this guard; a stored guard can only come from a source that holds at
    every candidate, so [type_call] asks for this stronger form.  See
    [AltSem] in [typing/ctx.v]. *)
  Definition lctx_lft_alive_all (κ : lft) : Prop :=
    ∀ sem, alt_sem sem → alt_into bor_sem sem →
      llctx_interp L ⊢ elctx_interp E -∗
        (llctx_interp L &&{alt_WGuard sem}&&> @[κ]).

  Lemma lctx_lft_alive_all_now κ : lctx_lft_alive_all κ → lctx_lft_alive κ.
  Proof.
    move=> Alv. rewrite /lctx_lft_alive -alt_WGuard_here.
    exact: (Alv _ alt_here (alt_into_refl alt_here)).
  Qed.

  Lemma lctx_lft_alive_static : lctx_lft_alive static.
  Proof. iIntros "**". rewrite -llftl_tok_unit_equiv. iApply guard_true. Qed.

  Lemma lctx_lft_alive_intersect α β :
    lctx_lft_alive α → lctx_lft_alive β → lctx_lft_alive (α ⊓ β).
  Proof.
    iIntros (alα alβ) "L E". iDestruct (alα with "L E") as "#gα".
    iDestruct (alβ with "L E") as "#gβ".
    iApply (guard_and (point_prop0 := point_prop_llft_alive _) with "gα gβ").
    by rewrite llftl_tok_inter_and.
  Qed.

  Lemma lctx_lft_alive_tok_list κs :
    Forall lctx_lft_alive κs → lctx_lft_alive (lft_intersect_list κs).
  Proof.
    elim; [exact: lctx_lft_alive_static|]=>/= ????.
    by apply lctx_lft_alive_intersect.
  Qed.

  Lemma lctx_lft_alive_local κ κs:
    κ ⊑ₗ κs ∈ L → Forall lctx_lft_alive κs → lctx_lft_alive κ.
  Proof.
    unfold lctx_lft_alive. intros Hin Hf.
    have H2 := lctx_lft_alive_tok_list _ Hf.
    iIntros "HL #HE".
    iDestruct (H2 with "HL HE") as "#Alv".
    iAssert (llctx_interp L &&{Wguard}&&> llctx_elt_interp (κ ⊑ₗ κs))%I
      with "[HL]" as "#HL1".
    { iApply guard_intro. iIntros "!> A".
      destruct (list_elem_of_lookup_1 _ _ Hin) as [i Hso].
      by iApply (big_sepL_lookup_acc with "A"). }
    iApply (guard_and (point_prop0 := point_prop_llft_alive _)
      with "Alv HL1").
    iIntros "AB".
    unfold llctx_elt_interp. rewrite bi.and_exist_l. iDestruct "AB" as (κ') "AB".
    simpl.
    iAssert (⌜κ = foldr meet static κs ⊓ κ'⌝)%I with "[AB]" as "%Hk".
      { iDestruct "AB" as "[_ [$ _]]". } subst κ.
    rewrite llftl_tok_inter_and. iSplit.
     - iDestruct "AB" as "[$ _]".
     - iDestruct "AB" as "[_ (_ & $ & _)]".
  Qed.

  Lemma lctx_lft_alive_all_static : lctx_lft_alive_all static.
  Proof.
    move=> sem ??. iIntros "**". rewrite -llftl_tok_unit_equiv.
    iApply guard_true.
  Qed.

  Lemma lctx_lft_alive_all_intersect α β :
    lctx_lft_alive_all α → lctx_lft_alive_all β → lctx_lft_alive_all (α ⊓ β).
  Proof.
    move=> alα alβ sem Hs Hi. iIntros "L #E".
    iDestruct (alα sem Hs Hi with "L E") as "#gα".
    iDestruct (alβ sem Hs Hi with "L E") as "#gβ".
    iApply (guard_and (point_prop0 := point_prop_llft_alive _) with "gα gβ").
    by rewrite llftl_tok_inter_and.
  Qed.

  Lemma lctx_lft_alive_all_tok_list κs :
    Forall lctx_lft_alive_all κs →
    lctx_lft_alive_all (lft_intersect_list κs).
  Proof.
    elim; [exact: lctx_lft_alive_all_static|]=>/= ????.
    by apply lctx_lft_alive_all_intersect.
  Qed.

  Lemma lctx_lft_alive_all_local κ κs :
    κ ⊑ₗ κs ∈ L → Forall lctx_lft_alive_all κs → lctx_lft_alive_all κ.
  Proof.
    move=> Hin Hf sem Hs Hi.
    have H2 := lctx_lft_alive_all_tok_list _ Hf sem Hs Hi.
    iIntros "HL #HE". iDestruct (H2 with "HL HE") as "#Alv".
    iAssert (llctx_interp L &&{alt_WGuard sem}&&>
      llctx_elt_interp (κ ⊑ₗ κs))%I with "[HL]" as "#HL1".
    { iApply guard_intro. iIntros "!> A".
      destruct (list_elem_of_lookup_1 _ _ Hin) as [i Hso].
      by iApply (big_sepL_lookup_acc with "A"). }
    iApply (guard_and (point_prop0 := point_prop_llft_alive _)
      with "Alv HL1").
    iIntros "AB".
    unfold llctx_elt_interp. rewrite bi.and_exist_l. iDestruct "AB" as (κ') "AB".
    simpl.
    iAssert (⌜κ = foldr meet static κs ⊓ κ'⌝)%I with "[AB]" as "%Hk".
      { iDestruct "AB" as "[_ [$ _]]". } subst κ.
    rewrite llftl_tok_inter_and. iSplit.
     - iDestruct "AB" as "[$ _]".
     - iDestruct "AB" as "[_ (_ & $ & _)]".
  Qed.

  (** The guard of [lctx_lft_alive_all], packaged so that it can be read off
    before the local lifetime context is consumed *)
  Lemma lctx_lft_alive_all_guards κ : lctx_lft_alive_all κ →
    llctx_interp L -∗ elctx_interp E -∗
      ∀ sem, ⌜alt_sem sem⌝ → ⌜alt_into bor_sem sem⌝ →
        llctx_interp L &&{alt_WGuard sem}&&> @[κ].
  Proof.
    move=> Alv. iIntros "L #E" (sem Hs Hi). iApply (Alv sem Hs Hi with "L E").
  Qed.

  Lemma lctx_lft_alive_incl κ κ':
    lctx_lft_alive κ → lctx_lft_incl κ κ' → lctx_lft_alive κ'.
  Proof.
    unfold lctx_lft_alive, lctx_lft_incl.
    intros Ha Hb. iIntros "HL #HE".
    iDestruct (Hb with "HL HE") as "#Hb".
    iDestruct (dincl_sem with "Hb") as "#Hb'".
    iDestruct (Ha with "HL HE") as "Ha".
    iApply (guard_trans with "Ha Hb'").
  Qed.

  Lemma lctx_lft_alive_external κ κ':
    κ ⊑ₑ κ' ∈ E → lctx_lft_alive κ → lctx_lft_alive κ'.
  Proof. intros. by eapply lctx_lft_alive_incl, lctx_lft_incl_external. Qed.

  (* External lifetime context satisfiability *)

  Definition elctx_sat E' : Prop :=
    llctx_interp L -∗ □ (elctx_interp E -∗ elctx_interp E').

  Lemma elctx_sat_nil : elctx_sat [].
  Proof. by iIntros "_!>_". Qed.

  Lemma elctx_sat_lft_incl E' κ κ' :
    lctx_lft_incl κ κ' → elctx_sat E' → elctx_sat (κ ⊑ₑ κ' :: E').
  Proof.
    iIntros (Hκκ' HE') "HL".
    iDestruct (Hκκ' with "HL") as "#Hincl".
    iDestruct (HE' with "HL") as "#HE'".
    iClear "∗". iIntros "!> #HE". iSplit; by [iApply "Hincl"|iApply "HE'"].
  Qed.

  Lemma elctx_sat_app E1 E2 :
    elctx_sat E1 → elctx_sat E2 → elctx_sat (E1 ++ E2).
  Proof.
    iIntros (HE1 HE2) "HL".
    iDestruct (HE1 with "HL") as "#HE1".
    iDestruct (HE2 with "HL") as "#HE2".
    iClear "∗". iIntros "!> #HE".
    iDestruct ("HE1" with "HE") as "#$".
    iApply ("HE2" with "HE").
  Qed.

  Lemma elctx_sat_refl : elctx_sat E.
  Proof. iIntros "_ !> ?". done. Qed.

  Lemma elctx_sat_head E' κ κ' :
    elctx_sat (κ ⊑ₑ κ' :: E') → lctx_lft_incl κ κ'.
  Proof.
    iIntros (InE') "L". iDestruct (InE' with "L") as "#InE'"=>/=.
    iIntros "!> #E". iDestruct ("InE'" with "E") as "[$ _]".
  Qed.
  Lemma elctx_sat_tail E' e :
    elctx_sat (e :: E') → elctx_sat E'.
  Proof.
    iIntros (eE') "L". iDestruct (eE' with "L") as "#eE'"=>/=.
    iIntros "!> #E". iDestruct ("eE'" with "E") as "[_ $]".
  Qed.

  Lemma elctx_sat_app_l E₀ E₁ : elctx_sat (E₀ ++ E₁) → elctx_sat E₀.
  Proof.
    iIntros (E₀E₁) "L". iDestruct (E₀E₁ with "L") as "#E₀E₁".
    iIntros "!> #E". rewrite elctx_interp_app.
    iDestruct ("E₀E₁" with "E") as "[$ _]".
  Qed.
  Lemma elctx_sat_app_r E₀ E₁ : elctx_sat (E₀ ++ E₁) → elctx_sat E₁.
  Proof.
    iIntros (E₀E₁) "L". iDestruct (E₀E₁ with "L") as "#E₀E₁".
    iIntros "!> #E". rewrite elctx_interp_app.
    iDestruct ("E₀E₁" with "E") as "[_ $]".
  Qed.
End lft_contexts.

Arguments lctx_lft_incl {_ _ _ _ _ _ _} _ _ _ _.
Arguments lctx_lft_eq {_ _ _ _ _ _ _} _ _ _ _.
Arguments lctx_lft_alive {_ _ _ _ _ _ _} _ _ _.
Arguments lctx_lft_alive_all {_ _ _ _ _ _ _} _ _ _.
Arguments elctx_sat {_ _ _ _ _ _ _} _ _ _.
Arguments lctx_lft_incl_incl {_ _ _ _ _ _ _ _ _} _ _.

Lemma elctx_sat_submseteq `{!alerusGS FML Σ, !AlerusSem FML Σ, !GsrcSem FML Σ,
  !TypeFml FML Σ, !AltSem FML Σ} E E' L :
  E' ⊆+ E → elctx_sat E L E'.
Proof. iIntros (HE') "_ !> H". by iApply big_sepL_submseteq. Qed.

(** The original takes a fancy update at [↑NllftG ⊆ F]; here the guard is
  simply opened against the world satisfaction. *)
Lemma lctx_lft_alive_get_guards `{!alerusGS FML Σ, !AlerusSem FML Σ, !GsrcSem FML Σ,
    !TypeFml FML Σ, !AltSem FML Σ, !WsatIncl W Wguard Wr}
    γ q E L κ :
  lctx_lft_alive E L κ →
  ([∗ list] x ∈ E, elctx_elt_interp x) -∗ Ltok γ L q -∗ W -∗
    Ltok γ L q ∗ W ∗ (llctx_interp L &&{Wguard}&&> @[κ]).
Proof.
  intros Halive. iIntros "E tok W".
  iDestruct (Ltok_acc with "tok W") as "[L back]".
  iDestruct (Halive with "L E") as "#X".
  iDestruct ("back" with "L") as "[$ $]". iFrame "X".
Qed.

Global Hint Resolve
     lctx_lft_incl_refl lctx_lft_incl_static lctx_lft_alive_intersect
     lctx_lft_incl_local' lctx_lft_incl_external' lctx_lft_incl_intersect
     lctx_lft_incl_intersect_l lctx_lft_incl_intersect_r
     lctx_lft_alive_static lctx_lft_alive_external lctx_lft_alive_local
     elctx_sat_nil elctx_sat_lft_incl elctx_sat_app elctx_sat_refl
  : lrust_typing.

Global Hint Resolve elctx_sat_submseteq | 100 : lrust_typing.

Global Hint Opaque elctx_sat lctx_lft_alive lctx_lft_incl : lrust_typing.
