(** * Recursive types, by [profix]

  [typing/fixpoint.v] builds a recursive type as a COFE limit, which costs it
  an assumption the model cannot discharge: [cif] is complete as a [prost],
  not as an OFE ([nola/util/cit.v] gives it an [OfeMixin] and no [Cofe]).
  Nola's own answer is [profix] over a [Productive] map
  ([nola/util/productive.v], [nola/examples/rust_halt/rec.v]), and that is
  what this file uses.

  Two things have to be arranged for it.

  *** The data has to be separated from the laws

  [profix] takes a fixed point of a map on a [prost], so the carrier must be
  plain data.  [tyd 𝔄] below is a type's data; [Ty] is the laws that a
  *guarded* former satisfies without appealing to its argument's, and
  [TyProphAt] is the one law that does appeal - the prophecy law, which
  upstream likewise keeps out of [Ty] (it is [TyOp] there) so that
  [ty_shrref]'s instance can be unconditional.

  *** The lifetimes cannot be part of it

  [tyd] deliberately omits [ty_lfts] and [ty_E].  They are not fixpointable:
  [&shr{κ}]'s lifetime list is [κ :: ty_lfts ty], and [≡[0]≡] relates *any*
  two arguments, so a productive map would have to produce the same list for
  all of them.  [rust_halt] does not have this problem because its [ty] is
  [natPR * (ownty * shrty)] and carries no lifetime list at all - lifetime
  inclusion is a [LftIncl] side condition there.  Here they are supplied
  separately, as [typing/fixpoint.v] already supplies them, through
  [TypeLftMorphism].

  This file is specialised to [cif], as [nola/examples/rust_halt/rec.v] is:
  the development's [FML] is an abstract [oFunctor] and carries no [prost]. *)

From nola.alerus.typing Require Export model_inst.
From nola.alerus.typing Require Import type shr_bor.
From nola.alerus.util Require Import basic.
From nola.util Require Import productive cit.
Import FunPRNotation ProeqvNotation GuardNotation ModwNotation.

Implicit Type 𝔄 : syn_type.

(** ** A type's data, and the laws, abstractly

  This section is in the same context as [typing/shr_bor.v] - an abstract
  [typeG] - so the formula constructors stay folded and the development's
  own lemmas apply.  The [prost] structure comes later, where the model is
  concrete. *)
Section tyd.
  Context `{!typeG FML Σ}.

  Definition ghostdata 𝔄 : Type :=
    (~~𝔄) → nat → nat → thread_id → FML $oi Σ.
  Definition tydata 𝔄 : Type :=
    (nat * (ghostdata 𝔄 * (ghostdata 𝔄 *
      ((~~𝔄) → thread_id → list fancy_val))))%type.

  Notation tyd_size T := (T.1) (only parsing).
  Notation tyd_ghox T := (T.2.1) (only parsing).
  Notation tyd_persx T := (T.2.2.1) (only parsing).
  Notation tyd_phys T := (T.2.2.2) (only parsing).

  (** The laws a *guarded* former satisfies without appealing to its
    argument's.  [rust_halt]'s [Ty] is the same split: the semantic laws
    ([TyOp], [Resol], [Real]) are separate classes, which is what lets
    [sty_shrref_sty] be unconditional. *)
  (** Only the *unconditional* instances - [ty_d_Ty] and [shr_tyd_Ty] - are
    registered below.  A structural former's [Ty] has a [Ty] premise, and
    registering those makes resolution diverge as soon as the goal carries
    an evar: [prod_tyd_Ty] would ask for two more [Ty]s, each of which could
    be a [prod_tyd_Ty] again.  They are applied by name instead. *)
  Class Ty {𝔄} (T : tydata 𝔄) : Prop := TY {
    tyd_size_eq x tid : length (tyd_phys T x tid) = tyd_size T;
    tyd_size_eq2 : size_of 𝔄 = tyd_size T;
    tyd_phys_eq2 x tid : syn_phys x = tyd_phys T x tid;
    tyd_gho_mono_at sem : alt_sem sem → ∀ d g d' g' x tid,
      (d ≤ d')%nat → (g ≤ g')%nat →
      sem (tyd_ghox T x d g tid) -∗ sem (tyd_ghox T x d' g' tid);
    tyd_pers_mono_at sem : alt_sem sem → ∀ d g d' g' x tid,
      (d ≤ d')%nat → (g ≤ g')%nat →
      sem (tyd_persx T x d g tid) -∗ sem (tyd_persx T x d' g' tid);
    tyd_pers_pers_at sem : alt_sem sem → ∀ x d g tid,
      Persistent (sem (tyd_persx T x d g tid));
    tyd_pers_impl x d g tid :
      bor_sem (tyd_ghox T x d g tid) -∗ bor_sem (tyd_persx T x d g tid);
  }.

  (** The law that *does* appeal to the argument, indexed by the depth -
    which is how it survives the fixpoint, by induction. *)
  Definition TyProphAt {𝔄} (lfts : list lft) (T : tydata 𝔄) (d : nat)
    : Prop := ∀ κ x g tid R,
      ⊢ llft_ctx -∗ κ ⊑ lft_intersect_list lfts -∗
        bor_sem (tyd_persx T x d g tid) -∗
        (R &&{Wguard}&&> @[κ]) -∗
        (R &&{Wguard}&&> bor_sem (tyd_ghox T x d g tid)) -∗
        |->[Wguard] (∀ ξ, ⌜ξ ∈ ξl x⌝ -∗ (R &&{Wguard}&&> 1:[ξ])).
  Definition TyProphLt {𝔄} lfts (T : tydata 𝔄) (d : nat) : Prop :=
    ∀ d', (d' < d)%nat → TyProphAt lfts T d'.

  (** Both transport along a pointwise equivalence of the data, because the
    only thing they do to it is take a non-expansive semantics. *)
  Lemma Ty_mono {𝔄} (T T' : tydata 𝔄) :
    tyd_size T = tyd_size T' →
    (∀ x tid, tyd_phys T x tid = tyd_phys T' x tid) →
    (∀ x d g tid, tyd_ghox T x d g tid ≡ tyd_ghox T' x d g tid) →
    (∀ x d g tid, tyd_persx T x d g tid ≡ tyd_persx T' x d g tid) →
    Ty T → Ty T'.
  Proof.
    move=> Hn Hs Hg Hp [Hsz Hsz2 Hph2 Hmono Hpmono Hpers Himpl]. split.
    - move=> x tid. by rewrite -Hs -Hn.
    - by rewrite -Hn.
    - move=> x tid. by rewrite -Hs.
    - move=> sem Hsem *. have ? := alt_sem_ne Hsem.
      rewrite -!Hg. by apply Hmono.
    - move=> sem Hsem *. have ? := alt_sem_ne Hsem.
      rewrite -!Hp. by apply Hpmono.
    - move=> sem Hsem *. have ? := alt_sem_ne Hsem.
      rewrite -Hp. by apply Hpers.
    - move=> *. rewrite -Hg -Hp. apply Himpl.
  Qed.

  Lemma TyProphAt_mono {𝔄} lfts (T T' : tydata 𝔄) d :
    (∀ x d g tid, tyd_ghox T x d g tid ≡ tyd_ghox T' x d g tid) →
    (∀ x d g tid, tyd_persx T x d g tid ≡ tyd_persx T' x d g tid) →
    TyProphAt lfts T d → TyProphAt lfts T' d.
  Proof. move=> Hg Hp HT κ x g tid R. rewrite -Hg -Hp. apply HT. Qed.

  (** ** A type's data, and back *)
  Definition ty_d {𝔄} (ty : type 𝔄) : tydata 𝔄 :=
    (ty.(ty_size), (ty.(ty_ghox), (ty.(ty_gho_persx), ty.(ty_phys)))).

  #[export] Instance ty_d_Ty {𝔄} (ty : type 𝔄) : Ty (ty_d ty).
  Proof.
    split=>/=.
    - exact: ty_size_eq.
    - exact: ty_size_eq2.
    - exact: ty_phys_eq2.
    - move=> sem Hs *. by apply (ty_gho_depth_mono_at ty sem Hs).
    - move=> sem Hs *. by apply (ty_gho_pers_depth_mono_at ty sem Hs).
    - move=> sem Hs *. exact: ty_gho_pers_pers_at.
    - move=> *. exact: ty_gho_pers_impl.
  Qed.

  Lemma ty_d_TyProphAt {𝔄} (ty : type 𝔄) d :
    TyProphAt ty.(ty_lfts) (ty_d ty) d.
  Proof.
    move=> κ x g tid R. iIntros "LFT Incl Pers Rk Rg".
    by iApply (ty_guard_proph _ ty κ x d g tid R with "LFT Incl Pers Rk Rg").
  Qed.

  (** The lifetime list and the external context are supplied from outside -
    see the note at the top of the file. *)
  Program Definition type_of_tyd {𝔄} (lfts : list lft) (E : elctx)
    (T : tydata 𝔄) (HT : Ty T) (HP : ∀ d, TyProphAt lfts T d) : type 𝔄 := {|
    ty_size := tyd_size T; ty_lfts := lfts; ty_E := E;
    ty_ghox := tyd_ghox T; ty_gho_persx := tyd_persx T; ty_phys := tyd_phys T;
  |}.
  Next Obligation. move=> *. exact: tyd_size_eq. Qed.
  Next Obligation. move=> *. exact: tyd_size_eq2. Qed.
  Next Obligation. move=> *. exact: tyd_phys_eq2. Qed.
  Next Obligation.
    move=> ?????? sem Hs *. by apply (tyd_gho_mono_at sem Hs).
  Qed.
  Next Obligation.
    move=> ?????? sem Hs *. by apply (tyd_pers_mono_at sem Hs).
  Qed.
  Next Obligation. move=> ????? HP *. by apply HP. Qed.
  Next Obligation.
    move=> ?????? sem Hs *. exact: (tyd_pers_pers_at sem Hs).
  Qed.
  Next Obligation. move=> *. exact: tyd_pers_impl. Qed.

  (** ** The shared borrow, at the level of data

    Literally [typing/shr_bor.v]'s body with the type replaced by its data.
    Its [Ty] instance is *unconditional*, which is what a guarded former has
    to be for the fixpoint to inherit the laws. *)
  Definition shr_ghod {𝔄} (κ : lft) (T : tydata 𝔄) : ghostdata (at_clocₛ 𝔄) :=
    λ x d g tid,
      ([Ltx(d') := d] [Lex(gg) := g] pers_fml
        (guard_fml (alive_fml κ) ((x.1).1 ↦[^ (x.1).2 ]!∗ syn_phys (snd x)) ∗
         guard_fml (alive_fml κ) (tyd_ghox T (snd x) d' gg tid) ∗
         store_fml (tyd_persx T (snd x) d' gg tid)))%FML.

  Definition shr_tyd {𝔄} (κ : lft) (T : tydata 𝔄) : tydata (at_clocₛ 𝔄) :=
    (1, (shr_ghod κ T, (shr_ghod κ T,
      (λ (x : ~~(at_clocₛ 𝔄)) (_ : thread_id), [FVal (LitV (x.1).1)])))).

  #[export] Instance shr_tyd_Ty {𝔄} κ (T : tydata 𝔄) : Ty (shr_tyd κ T).
  Proof.
    split; simpl.
    - done.
    - done.
    - done.
    - (* both indices are bounded, so weakening is widening a bound - the
         argument's own laws are never touched *)
      move=> sem H d g d' g' x tid ??.
      rewrite !(by_ltx_sem_at (alt_sem_any H)).
      iIntros "(%dd & %Hdd & A)". iExists dd. iSplit; [iPureIntro; lia|].
      rewrite !(by_lex_sem_at (alt_sem_any H)).
      iDestruct "A" as (gg Hgg) "A". iExists gg.
      iSplit; [iPureIntro; lia|done].
    - move=> sem H d g d' g' x tid ??.
      rewrite !(by_ltx_sem_at (alt_sem_any H)).
      iIntros "(%dd & %Hdd & A)". iExists dd. iSplit; [iPureIntro; lia|].
      rewrite !(by_lex_sem_at (alt_sem_any H)).
      iDestruct "A" as (gg Hgg) "A". iExists gg.
      iSplit; [iPureIntro; lia|done].
    - (* persistence is structural *)
      move=> sem H x d g tid.
      apply (by_ltx_persistent_at H)=> d'.
      apply (by_lex_persistent_at H)=> gg.
      rewrite (pers_sem_at_any (alt_sem_any H)). exact _.
    - (* the persistent part *is* the ghost assertion *)
      move=> *. by iIntros "$".
  Qed.

  (** Its prophecy law needs the borrowed data's at every *lower* depth,
    which is what makes the fixpoint's depth induction go through. *)
  Lemma shr_tyd_TyProphAt {𝔄} κ lfts (T : tydata 𝔄) d :
    TyProphLt lfts T d → TyProphAt (κ :: lfts) (shr_tyd κ T) d.
  Proof.
    move=> HT κ0 x g tid R. rewrite /shr_tyd/shr_ghod/= by_ltx_sem /by_lt.
    iIntros "#LFT #Incl A". iDestruct "A" as (d0 Hd0) "A".
    rewrite by_lex_sem /by_le. iDestruct "A" as (gg Hgg) "A".
    rewrite pers_fml_sem !bor_sep_sem.
    iDestruct "A" as "#(_ & Gho & St)". iIntros "#Rk _ W".
    iDestruct (store_fml_acc with "St") as "#Acc".
    iDestruct ("Acc" with "W") as "[W Pers]".
    iApply (HT d0 Hd0 κ0 (snd x) gg tid R with "LFT [] Pers Rk [] W").
    { iApply (llftl_incl_trans with "Incl []"). iApply llftl_intersect_incl_r. }
    iDestruct (dguard_alive_sem with "Gho") as "#Gho0".
    iDestruct (fguard_here with "Incl") as "#Inclh".
    iApply (guard_trans with "Rk"). iApply (guard_trans with "Inclh").
    iApply (guard_trans with "[] Gho0"). iApply llftl_intersect_incl_l_at.
  Qed.
  (** ** A structural former, at the level of data

    [prod_ty]'s body with the records replaced by their data.  Unlike
    [shr_tyd] its laws are *conditional* on its arguments', which is all a
    structural former ever needs: in [μ X. G (&shr{κ} X)] the hole is
    already behind the guarded former, so [ty_rec_shr_Ty] only asks [G] to
    preserve [Ty].  [ty_prod_ty] upstream is conditional for the same
    reason. *)
  Definition prod_tyd {𝔄 𝔅} (T : tydata 𝔄) (U : tydata 𝔅)
    : tydata (𝔄 * 𝔅) :=
    (tyd_size T + tyd_size U,
     ((λ x d g tid,
        (tyd_ghox T (fst x) d g tid ∗ tyd_ghox U (snd x) d g tid)%FML),
      ((λ x d g tid,
        (tyd_persx T (fst x) d g tid ∗ tyd_persx U (snd x) d g tid)%FML),
       (λ x tid, tyd_phys T (fst x) tid ++ tyd_phys U (snd x) tid)))).

  Lemma prod_tyd_Ty {𝔄 𝔅} (T : tydata 𝔄) (U : tydata 𝔅)
    `{!Ty T, !Ty U} : Ty (prod_tyd T U).
  Proof.
    split; simpl.
    - move=> x tid. by rewrite length_app !tyd_size_eq.
    - by do 2 (rewrite -tyd_size_eq2).
    - move=> [??] tid. by do 2 (rewrite -tyd_phys_eq2).
    - move=> sem H d g d' g' x tid ??. rewrite !(sep_sem_at H).
      iIntros "[A B]".
      iDestruct (tyd_gho_mono_at sem H d g d' g' with "A") as "A"; [done..|].
      iDestruct (tyd_gho_mono_at sem H d g d' g' with "B") as "B"; [done..|].
      iFrame.
    - move=> sem H d g d' g' x tid ??. rewrite !(sep_sem_at H).
      iIntros "[A B]".
      iDestruct (tyd_pers_mono_at sem H d g d' g' with "A") as "A"; [done..|].
      iDestruct (tyd_pers_mono_at sem H d g d' g' with "B") as "B"; [done..|].
      iFrame.
    - move=> sem H x d g tid.
      have ? := tyd_pers_pers_at (T:=T) sem H.
      have ? := tyd_pers_pers_at (T:=U) sem H.
      rewrite (sep_sem_at H). exact _.
    - move=> x d g tid. rewrite !bor_sep_sem. iIntros "[A B]".
      iSplitL "A"; by iApply tyd_pers_impl.
  Qed.

  Lemma prod_tyd_TyProphAt {𝔄 𝔅} lfts lfts' (T : tydata 𝔄) (U : tydata 𝔅) d :
    TyProphAt lfts T d → TyProphAt lfts' U d →
    TyProphAt (lfts ++ lfts') (prod_tyd T U) d.
  Proof.
    move=> HT HU κ x g tid R. rewrite /prod_tyd/=. fml_simpl.
    iIntros "#LFT #Incl [Gho1 Gho2] #Rk #Rgho".
    iMod (HT κ (fst x) g tid R with "LFT [] Gho1 Rk []") as "H1".
    { rewrite lft_intersect_list_app. iApply (fguard_trans with "Incl []").
      iApply llftl_intersect_incl_l. }
    { iApply guard_rhs_sep_l. iFrame "Rgho". }
    iMod (HU κ (snd x) g tid R with "LFT [] Gho2 Rk []") as "H2".
    { rewrite lft_intersect_list_app. iApply (fguard_trans with "Incl []").
      iApply llftl_intersect_incl_r. }
    { iApply guard_rhs_sep_r. iFrame "Rgho". }
    iModIntro. iIntros (ξ Hin). rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]; [iApply "H1"|iApply "H2"]; by iPureIntro.
  Qed.

  (** The owning pointer, likewise.  It matches on the depth with
    [by_succ]'s exact match, as [typing/own.v] does - only the *guarded*
    formers need the bounded form. *)
  Definition own_tyd {𝔄} (n : nat) (T : tydata 𝔄) : tydata (at_locₛ 𝔄) :=
    (1,
     ((λ x d g tid, [Sx(d') := d]
        ((fst x) ↦!∗ tyd_phys T (snd x) tid ∗
         freeable_fml n (tyd_size T) (fst x) ∗
         tyd_ghox T (snd x) d' g tid)%FML),
      ((λ x d g tid, [Sx(d') := d] (tyd_persx T (snd x) d' g tid)),
       (λ (x : ~~(at_locₛ 𝔄)) (_ : thread_id), [FVal (LitV (fst x))])))).

  Lemma own_tyd_Ty {𝔄} n (T : tydata 𝔄) `{!Ty T} :
    Ty (own_tyd n T).
  Proof.
    split; simpl.
    - done.
    - done.
    - done.
    - move=> sem H [|d] g d' g' x tid ??.
      { rewrite /= (false_sem_at H). by iIntros "[]". }
      destruct d' as [|d']; first lia. rewrite /= !(sep_sem_at H).
      iIntros "($ & $ & Hgho)".
      iApply (tyd_gho_mono_at sem H with "Hgho"); lia.
    - move=> sem H [|d] g d' g' x tid ??.
      { rewrite /= (false_sem_at H). by iIntros "[]". }
      destruct d' as [|d']; first lia. simpl. iIntros "Hp".
      iApply (tyd_pers_mono_at sem H with "Hp"); lia.
    - move=> sem H x d g tid. apply (by_succx_persistent_at H)=> d'.
      apply (tyd_pers_pers_at sem H).
    - move=> x d g tid. destruct d as [|d'].
      { rewrite /= !false_fml_sem. by iIntros "[]". }
      fml_simpl'. iIntros "A". iDestruct "A" as "[_ [_ gho]]".
      by iApply tyd_pers_impl.
  Qed.

  Lemma own_tyd_TyProphAt {𝔄} n lfts (T : tydata 𝔄) d :
    (∀ d', TyProphAt lfts T d') → TyProphAt lfts (own_tyd n T) d.
  Proof.
    move=> HT κ x g tid R. iIntros "#LFT #Incl Pers".
    destruct d as [|d'].
    { iIntros "_ _". by iDestruct (false_fml_sem_1 with "Pers") as "[]". }
    fml_simpl'. iIntros "#Rk #Rg".
    iApply (HT d' κ (snd x) g tid R with "LFT Incl Pers Rk").
    iApply (guard_trans with "Rg"). iApply (guard_trans with "[]").
    { iApply (guard_sep_r (P:=((fst x) ↦!∗ tyd_phys T (snd x) tid)%I)). }
    iApply guard_sep_r.
  Qed.

  (** ** The owning pointer, made *productive*

    [own_tyd] above holds the pointee's ghost assertion as a visible child,
    so it is [Preserv] and not [Productive] and cannot be the guarded
    former of a recursion.  This one puts it behind a *stored guard*,
    [guard_fml empty_fml Px], whose children are [cdom] children.

    Four things change, and each is forced.

    A guard rather than [store_fml], because the pointee's ghost assertion
    is *owned*: [store_fml_acc] hands its content out for good, which is
    sound only for persistent content, while a guard returns it -
    [guard_acc] is [Q ∗ (Q -∗ W ∗ T)].  [nola/iris/store.v]'s [store_tok],
    the one [ty_box] uses upstream, cannot do that.

    A guard rather than [dinv_fml], which is where this started and where
    it could not stay: a token *names the formula it stores*, so nothing
    turns [dinv_tok Px] into [dinv_tok Qx] and a former holding one admits
    no subtyping rule.  A guard composes, so this one does
    ([sown_tyd_incl]).  Nothing is lost by the trade, because [ctx.v]'s
    [eguard_fml_alloc] allocates the token and stores the guard it yields -
    the token is still how one is built.  This is the thesis's (5.5) in the
    port's terms.

    Both indices are *bounded* ([Ltx], [Lex]) rather than matched exactly,
    as in [shr_tyd].  An invariant holds a formula at one fixed depth and
    guard index, so weakening cannot push them up; widening a bound is the
    only weakening left.  [rust_halt]'s [sty_shrref] carries [⌜d' < d⌝] for
    the same reason.

    The argument's *size* and *physical contents* are gone, replaced by
    [size_of] and [syn_phys].  [proeqv 0] relates nothing in a discrete
    component, so a [Productive] former may not mention [tyd_size T] or
    [tyd_phys T] at all - the same constraint [shr_tyd] is under, and the
    reason it writes [syn_phys].  A [Ty T] bridges the two.

    And the whole stored part sits in the *persistent* component as well as
    the ghost one, because [ty_guard_proph] is handed the persistent
    component directly while the guard it is handed cannot be opened -
    [guard_acc] wants the left-hand side, which the law does not supply. *)
  Definition sown_persd {𝔄} (T : tydata 𝔄) : ghostdata (at_locₛ 𝔄) :=
    λ x d g tid,
      ([Ltx(d') := d] [Lex(gg) := g]
        (guard_fml empty_fml (tyd_ghox T (snd x) d' gg tid) ∗
         store_fml (tyd_persx T (snd x) d' gg tid)))%FML.

  Definition sown_tyd {𝔄} (n : nat) (T : tydata 𝔄) : tydata (at_locₛ 𝔄) :=
    (1,
     ((λ x d g tid,
        ((fst x) ↦!∗ syn_phys (snd x) ∗
         freeable_fml n (size_of 𝔄) (fst x) ∗
         sown_persd T x d g tid)%FML),
      (sown_persd T,
       (λ (x : ~~(at_locₛ 𝔄)) (_ : thread_id), [FVal (LitV (fst x))])))).

  (** Unconditional, like [shr_tyd_Ty] and for the same reason: a properly
    guarded former never appeals to its argument's laws. *)
  #[export] Instance sown_tyd_Ty {𝔄} n (T : tydata 𝔄) : Ty (sown_tyd n T).
  Proof.
    have Hmono : ∀ sem, alt_sem sem → ∀ d g d' g' x tid, (d ≤ d')%nat →
      (g ≤ g')%nat → sem (sown_persd T x d g tid) -∗
      sem (sown_persd T x d' g' tid).
    { move=> sem H d g d' g' x tid ??.
      rewrite /sown_persd !(by_ltx_sem_at (alt_sem_any H)).
      iIntros "(%dd & %Hdd & A)". iExists dd. iSplit; [iPureIntro; lia|].
      rewrite !(by_lex_sem_at (alt_sem_any H)).
      iDestruct "A" as (gg Hgg) "A". iExists gg.
      iSplit; [iPureIntro; lia|done]. }
    have Hpers : ∀ sem, alt_sem sem → ∀ x d g tid,
      Persistent (sem (sown_persd T x d g tid)).
    { move=> sem H ????. rewrite /sown_persd.
      apply (by_ltx_persistent_at H)=> d'. apply (by_lex_persistent_at H)=> gg.
      rewrite (sep_sem_at H).
      have ? := guard_fml_pers_at_any (alt_sem_any H)
        empty_fml (tyd_ghox T _ d' gg _).
      have ? := store_fml_pers_at_any (alt_sem_any H) (tyd_persx T _ d' gg _).
      exact _. }
    split; simpl.
    - done.
    - done.
    - done.
    - move=> sem H d g d' g' x tid ??. rewrite !(sep_sem_at H).
      iIntros "($ & $ & A)". by iApply (Hmono sem H with "A").
    - move=> sem H d g d' g' x tid ??. by apply Hmono.
    - move=> sem H *. by apply Hpers.
    - move=> x d g tid. rewrite !bor_sep_sem. by iIntros "(_ & _ & $)".
  Qed.

  (** Its prophecy law needs the pointee's at every *lower* depth, as
    [shr_tyd]'s does - which is what the fixpoint's depth induction
    supplies.  It reaches the pointee through [eguard_fml_guard_any]: a
    stored guard with [empty_fml] on the left is a guard against any
    left-hand side. *)
  Lemma sown_tyd_TyProphAt {𝔄} n lfts (T : tydata 𝔄) d :
    TyProphLt lfts T d → TyProphAt lfts (sown_tyd n T) d.
  Proof.
    move=> HT κ x g tid R. rewrite /sown_tyd/sown_persd/= by_ltx_sem /by_lt.
    iIntros "#LFT #Incl A". iDestruct "A" as (d0 Hd0) "A".
    rewrite by_lex_sem /by_le. iDestruct "A" as (gg Hgg) "A".
    rewrite !bor_sep_sem. iDestruct "A" as "#[Inv St]".
    iIntros "#Rk _ W".
    iDestruct (store_fml_acc with "St") as "#Acc".
    iDestruct ("Acc" with "W") as "[W Pers]".
    iApply (HT d0 Hd0 κ (snd x) gg tid R with "LFT Incl Pers Rk [] W").
    by iApply eguard_fml_guard_any.
  Qed.

  (** Relabelling along an isomorphism of refinement types - [mod_ty.v]'s
    body at the data level.  This is [rust_halt]'s [ty_mod], which is how
    [verify/list.v] and [verify/mutlist.v] make their generator's refinement
    type match its argument's. *)
  Definition mod_tyd {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) (fⁱ : 𝔅 →ₛ 𝔄) `{!Isoₛ f fⁱ}
    (T : tydata 𝔄) : tydata 𝔅 :=
    (tyd_size T,
     ((λ x d g tid, tyd_ghox T (fⁱ ~~$ₛ x) d g tid),
      ((λ x d g tid, tyd_persx T (fⁱ ~~$ₛ x) d g tid),
       (λ x tid, tyd_phys T (fⁱ ~~$ₛ x) tid)))).

  Lemma mod_tyd_Ty {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) (fⁱ : 𝔅 →ₛ 𝔄)
    `{!Isoₛ f fⁱ} (T : tydata 𝔄) `{!Ty T} : Ty (mod_tyd f fⁱ T).
  Proof.
    split; simpl.
    - move=> *. exact: tyd_size_eq.
    - rewrite -tyd_size_eq2. inversion Isoₛ0. done.
    - move=> x tid. rewrite -tyd_phys_eq2. inversion Isoₛ0.
      rewrite (syn_iso_phys_eq ((~~!ₛ) fⁱ x)). by rewrite semi_iso'.
    - move=> sem H *. by apply (tyd_gho_mono_at sem H).
    - move=> sem H *. by apply (tyd_pers_mono_at sem H).
    - move=> sem H *. exact: (tyd_pers_pers_at sem H).
    - move=> *. exact: tyd_pers_impl.
  Qed.

  Lemma mod_tyd_TyProphAt {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) (fⁱ : 𝔅 →ₛ 𝔄) `{!Isoₛ f fⁱ}
    lfts (T : tydata 𝔄) d :
    TyProphAt lfts T d → TyProphAt lfts (mod_tyd f fⁱ T) d.
  Proof.
    move=> HT κ x g tid R. iIntros "LFT Incl Pers Rk Rg".
    iMod (HT κ (fⁱ ~~$ₛ x) g tid R with "LFT Incl Pers Rk Rg") as "H".
    iModIntro. iIntros (ξ Hin). iApply "H". iPureIntro.
    by rewrite -syn_type_morphism_ξl.
  Qed.

  (** [TyProphAt] is antitone in the lifetime list: a longer list is a
    stronger premise.  Composing formers needs it, because the hole's law
    comes with the guarded former's lifetime prepended. *)
  (** [typing/sum.v] proves this too, inside its own section; [rec.v] does
    not import it. *)
  Local Lemma pad_len l n : length (pad l n) = n.
  Proof.
    rewrite /pad. case_decide; [rewrite length_take; lia|].
    rewrite length_app repeat_length. lia.
  Qed.

  (** ** The two formers a list needs beside [prod_tyd] and [mod_tyd]

    The unit, which is the nil branch's payload: no memory, no prophecies,
    and a formula that is [True] at every candidate interpretation. *)
  Definition unit_tyd : tydata unitₛ :=
    (0, ((λ _ _ _ _, pure_fml True), ((λ _ _ _ _, pure_fml True),
      (λ _ _, [])))).

  Lemma unit_tyd_Ty : Ty unit_tyd.
  Proof.
    split; simpl.
    - done.
    - done.
    - done.
    - move=> ??*. by iIntros "$".
    - move=> ??*. by iIntros "$".
    - move=> sem H *. rewrite (pure_sem_at H). exact _.
    - move=> *. by iIntros "$".
  Qed.

  Lemma unit_tyd_TyProphAt lfts d : TyProphAt lfts unit_tyd d.
  Proof.
    move=> κ[]g tid R. iIntros "_ _ _ _ _ !>" (ξ Hξ). exfalso.
    move: Hξ=>/=. by rewrite elem_of_nil.
  Qed.

  (** The binary tagged sum.  [typing/sum.v]'s [xsum_ty] is the general one,
    over a heterogeneous list; two branches is all a list needs, and taking
    them one at a time means the [psum] is a plain [+] and every obligation
    is a case split rather than an induction over [𝔄l].

    The physical layout is [xsumₛ]'s, tag and padding included, which is
    what lets [tyd_phys_eq2] hold: [syn_phys] on [xsumₛ [𝔄; 𝔅]] computes to
    exactly this. *)
  Definition xsum2_tyd {𝔄 𝔅} (T : tydata 𝔄) (U : tydata 𝔅)
    : tydata (xsumₛ [𝔄; 𝔅]) :=
    (size_of (xsumₛ [𝔄; 𝔅]),
     ((λ x d g tid, match x.1 with
                    | inl a => tyd_ghox T a d g tid
                    | inr (inl b) => tyd_ghox U b d g tid
                    | inr (inr e) => absurd e
                    end),
      ((λ x d g tid, match x.1 with
                     | inl a => tyd_persx T a d g tid
                     | inr (inl b) => tyd_persx U b d g tid
                     | inr (inr e) => absurd e
                     end),
       (λ x tid, match x.1 with
                 | inl a => pad (FVal (LitV (LitInt 0)) ::
                     tyd_phys T a tid ++ fmap FVal x.2) (size_of (xsumₛ [𝔄; 𝔅]))
                 | inr (inl b) => pad (FVal (LitV (LitInt 1)) ::
                     tyd_phys U b tid ++ fmap FVal x.2) (size_of (xsumₛ [𝔄; 𝔅]))
                 | inr (inr e) => absurd e
                 end)))).

  Lemma xsum2_tyd_Ty {𝔄 𝔅} (T : tydata 𝔄) (U : tydata 𝔅) `{!Ty T, !Ty U} :
    Ty (xsum2_tyd T U).
  Proof.
    split; simpl.
    - move=> [[a|[b|e]]?]?/=;
        [apply pad_len|apply pad_len|by apply absurd].
    - done.
    - move=> [[a|[b|e]]?]?/=;
        [by rewrite -tyd_phys_eq2|by rewrite -tyd_phys_eq2|by apply absurd].
    - move=> sem H d g d' g' [[a|[b|e]]?] tid ??/=;
        [by apply (tyd_gho_mono_at sem H)|by apply (tyd_gho_mono_at sem H)|
         by apply absurd].
    - move=> sem H d g d' g' [[a|[b|e]]?] tid ??/=;
        [by apply (tyd_pers_mono_at sem H)|by apply (tyd_pers_mono_at sem H)|
         by apply absurd].
    - move=> sem H [[a|[b|e]]?] d g tid/=;
        [by apply (tyd_pers_pers_at sem H)|by apply (tyd_pers_pers_at sem H)|
         by apply absurd].
    - move=> [[a|[b|e]]?] d g tid/=;
        [by apply tyd_pers_impl|by apply tyd_pers_impl|by apply absurd].
  Qed.

  Lemma xsum2_tyd_TyProphAt {𝔄 𝔅} lfts (T : tydata 𝔄) (U : tydata 𝔅) d :
    TyProphAt lfts T d → TyProphAt lfts U d →
    TyProphAt lfts (xsum2_tyd T U) d.
  Proof.
    move=> HT HU κ [[a|[b|e]]?] g tid R/=; [exact: HT|exact: HU|by apply absurd].
  Qed.

  Lemma TyProphAt_lfts {𝔄} lfts lfts' (T : tydata 𝔄) d :
    (⊢ lft_intersect_list lfts' ⊑ lft_intersect_list lfts) →
    TyProphAt lfts T d → TyProphAt lfts' T d.
  Proof.
    move=> Hin HT κ x g tid R. iIntros "LFT #Incl".
    iApply (HT κ x g tid R with "LFT []").
    iApply (llftl_incl_trans with "Incl"). iApply Hin.
  Qed.
  (** ** Inclusion of a type's data, depth by depth

    [typing/type.v]'s [type_incl] has two ghost components, both quantified
    over the depth *inside* the [□].  This is the same pair with the depth
    pulled out, and pulling it out is the whole point.

    The thesis derives [listᵢ T ≤ listⱼ U] from [T ≤ U], [U ≤ T] and
    [i ≤ j] by using [≤-ref] *coinductively* (§ 5.1 fn. 1), and its device
    for that is Definition 4.5's [Deriv_φ] - derivability parameterised by
    an induction hypothesis.  It needs one because its [rec] carries no
    index at all: [⟦rec X. T⟧ᵢ ≜ ⟦T[rec X.T/X]⟧ᵢ] is plain substitution.
    The port's guarded formers *do* carry an index - [&shr{κ}]'s body is
    [[Ltx(d') := d] …], i.e. [∃ d' < d] - so the same rule is an ordinary
    well-founded induction on the depth here, which is also how [rust_halt]
    proves [ty_rec_ty_op] and how [ty_rec_TyProphAt] above is proved.  What
    the induction needs is a statement indexed by [d], and [type_incl] is
    not one; [tyd_incl_at] is. *)
  Definition tyd_incl_at {𝔄 𝔅} (T : tydata 𝔄) (U : tydata 𝔅)
      (f : 𝔄 →ₛ 𝔅) (d : nat) : iProp Σ :=
    (□ ∀ sem (_ : alt_sem sem) x g tid,
       sem (tyd_ghox T x d g tid) -∗ sem (tyd_ghox U (f ~~$ₛ x) d g tid) ∗
         (sem (tyd_ghox U (f ~~$ₛ x) d g tid) -∗
          sem (tyd_ghox T x d g tid))) ∗
    (□ ∀ sem (_ : alt_sem sem) x g tid,
       sem (tyd_persx T x d g tid) -∗ sem (tyd_persx U (f ~~$ₛ x) d g tid)).

  #[export] Instance tyd_incl_at_persistent {𝔄 𝔅} T U f d :
    Persistent (@tyd_incl_at 𝔄 𝔅 T U f d) := _.

  (** The inclusion at every *lower* depth: what a guarded former consumes,
    and what the fixpoint's induction hypothesis supplies. *)
  Definition tyd_incl_lt {𝔄 𝔅} (T : tydata 𝔄) (U : tydata 𝔅)
      (f : 𝔄 →ₛ 𝔅) (d : nat) : iProp Σ :=
    □ ∀ d', ⌜(d' < d)%nat⌝ → tyd_incl_at T U f d'.

  (** It transports along a pointwise equivalence of the data, as [Ty] and
    [TyProphAt] do, because the only thing it does to the data is take a
    non-expansive semantics of it.  [ty_rec_unfold] is why. *)
  Lemma tyd_incl_at_mono {𝔄 𝔅} (T T' : tydata 𝔄) (U U' : tydata 𝔅) f d :
    (∀ x dd g tid, tyd_ghox T x dd g tid ≡ tyd_ghox T' x dd g tid) →
    (∀ x dd g tid, tyd_persx T x dd g tid ≡ tyd_persx T' x dd g tid) →
    (∀ x dd g tid, tyd_ghox U x dd g tid ≡ tyd_ghox U' x dd g tid) →
    (∀ x dd g tid, tyd_persx U x dd g tid ≡ tyd_persx U' x dd g tid) →
    tyd_incl_at T U f d ⊢ tyd_incl_at T' U' f d.
  Proof.
    move=> HgT HpT HgU HpU. iIntros "#[A B]". iSplit.
    - iIntros "!>" (sem Hsem x g tid). have ? := alt_sem_ne Hsem.
      rewrite -HgT -HgU. iApply ("A" $! sem Hsem).
    - iIntros "!>" (sem Hsem x g tid). have ? := alt_sem_ne Hsem.
      rewrite -HpT -HpU. iApply ("B" $! sem Hsem).
  Qed.

  (** ...and the bridge back to [type_incl].  The size and the physical
    layout are pure side conditions, and they are conditions on the
    *refinement types* alone: [tyd_size_eq2] and [tyd_phys_eq2] tie a type
    to its refinement, so a subtyping map has to preserve both.  That is
    the same demand [Isoₛ] makes, and [prophecy/syn_type.v]'s
    [shr_list_size_eq]/[shr_list_phys_eq] discharge it for the list. *)
  Lemma type_incl_of_tyd_incl {𝔄 𝔅} (ty : type 𝔄) (ty' : type 𝔅) f :
    size_of 𝔄 = size_of 𝔅 →
    (∀ x, @syn_phys 𝔄 x = @syn_phys 𝔅 (f ~~$ₛ x)) →
    dincl (ty_lft ty') (ty_lft ty) -∗
    (∀ d, tyd_incl_at (ty_d ty) (ty_d ty') f d) -∗
    type_incl ty ty' f.
  Proof.
    move=> Hsz Hph. iIntros "#Lft #Sub". iSplit.
    { iPureIntro. by rewrite -(ty_size_eq2 _ ty) -(ty_size_eq2 _ ty'). }
    iSplit; [done|]. iSplit.
    - iIntros "!>" (sem Hsem x d g tid).
      iDestruct ("Sub" $! d) as "[A _]". iApply ("A" $! sem Hsem).
    - iSplit.
      + iIntros "!>" (sem Hsem x d g tid).
        iDestruct ("Sub" $! d) as "[_ B]". iApply ("B" $! sem Hsem).
      + iPureIntro=> x tid.
        by rewrite -(ty_phys_eq2 _ ty) -(ty_phys_eq2 _ ty') Hph.
  Qed.

  (** ** The congruences, former by former

    Each is [typing/*.v]'s own subtyping rule with the record replaced by
    its data and the depth exposed.  Only [shr_tyd_incl] is interesting:
    it is the one that takes its argument's inclusion at a *lower* depth
    and so lets the induction turn. *)
  Lemma unit_tyd_incl d : ⊢ tyd_incl_at unit_tyd unit_tyd idₛ d.
  Proof.
    iSplit; iIntros "!>" (sem Hsem x g tid).
    - iIntros "$". by iIntros "$".
    - by iIntros "$".
  Qed.

  Lemma prod_tyd_incl {𝔄 𝔄' 𝔅 𝔅'} (T : tydata 𝔄) (T' : tydata 𝔄')
      (U : tydata 𝔅) (U' : tydata 𝔅') f g d :
    tyd_incl_at T T' f d -∗ tyd_incl_at U U' g d -∗
    tyd_incl_at (prod_tyd T U) (prod_tyd T' U') (prod_mapₛ f g) d.
  Proof.
    iIntros "#[A1 B1] #[A2 B2]". iSplit.
    - iIntros "!>" (sem Hsem x g0 tid). rewrite !(sep_sem_at Hsem).
      iIntros "[P Q]".
      iDestruct ("A1" $! sem Hsem with "P") as "[P' Pb]".
      iDestruct ("A2" $! sem Hsem with "Q") as "[Q' Qb]".
      iSplitL "P' Q'"; [by iFrame|]. iIntros "[P' Q']".
      iSplitL "P' Pb"; by [iApply "Pb"|iApply "Qb"].
    - iIntros "!>" (sem Hsem x g0 tid). rewrite !(sep_sem_at Hsem).
      iIntros "[P Q]". iSplitL "P"; by [iApply "B1"|iApply "B2"].
  Qed.

  Lemma xsum2_tyd_incl {𝔄 𝔄' 𝔅 𝔅'} (T : tydata 𝔄) (T' : tydata 𝔄')
      (U : tydata 𝔅) (U' : tydata 𝔅') f g d :
    tyd_incl_at T T' f d -∗ tyd_incl_at U U' g d -∗
    tyd_incl_at (xsum2_tyd T U) (xsum2_tyd T' U')
      (psum_mapₛ (𝔄l := [𝔄; 𝔅]) (𝔅l := [𝔄'; 𝔅']) (f -:: g -:: -[])) d.
  Proof.
    iIntros "#[A1 B1] #[A2 B2]". iSplit;
      iIntros "!>" (sem Hsem [[a|[b|e]] p] g0 tid); simpl.
    - iApply ("A1" $! sem Hsem).
    - iApply ("A2" $! sem Hsem).
    - by apply absurd.
    - iApply ("B1" $! sem Hsem).
    - iApply ("B2" $! sem Hsem).
    - by apply absurd.
  Qed.

  (** Relabelling: the two maps have to commute with the two unfoldings,
    which for the list is [prophecy/syn_type.v]'s [unfoldshr_mapₛ]. *)
  Lemma mod_tyd_incl {𝔄 𝔅 𝔄' 𝔅'} (f : 𝔄 →ₛ 𝔅) (fⁱ : 𝔅 →ₛ 𝔄) `{!Isoₛ f fⁱ}
      (f' : 𝔄' →ₛ 𝔅') (f'ⁱ : 𝔅' →ₛ 𝔄') `{!Isoₛ f' f'ⁱ}
      (T : tydata 𝔄) (U : tydata 𝔄') (h : 𝔄 →ₛ 𝔄') (k : 𝔅 →ₛ 𝔅') d :
    (∀ x, h ~~$ₛ (fⁱ ~~$ₛ x) = f'ⁱ ~~$ₛ (k ~~$ₛ x)) →
    tyd_incl_at T U h d -∗
    tyd_incl_at (mod_tyd f fⁱ T) (mod_tyd f' f'ⁱ U) k d.
  Proof.
    move=> Hsq. iIntros "#[A B]". iSplit; iIntros "!>" (sem Hsem x g tid);
      simpl; rewrite -Hsq; [iApply ("A" $! sem Hsem)|iApply ("B" $! sem Hsem)].
  Qed.

  (** The guarded former.  Everything the body mentions of the argument
    sits at a depth strictly below [d] - that is what [by_ltx] says - so
    this consumes [tyd_incl_lt] and produces [tyd_incl_at].  The proof is
    [typing/shr_bor.v]'s [shr_type_incl] with the depth exposed; the
    backward direction of the ghost component is free because a shared
    borrow's ghost assertion is persistent, exactly as
    [type_incl_simple_type] has it. *)
  Lemma shr_ghod_incl {𝔄 𝔅} κ κ' (T : tydata 𝔄) (U : tydata 𝔅) f d :
    (∀ x, @syn_phys 𝔄 x = @syn_phys 𝔅 (f ~~$ₛ x)) →
    dincl κ' κ -∗ tyd_incl_lt T U f d -∗
    □ ∀ sem (_ : alt_sem sem) x g tid,
        sem (shr_ghod κ T x d g tid) -∗
        sem (shr_ghod κ' U (at_cloc_mapₛ f ~~$ₛ x) d g tid).
  Proof.
    move=> Hph. iIntros "#Incl #Sub !>" (sem Hsem x g tid).
    destruct x as [lx x]; simpl.
    have ? := guard_fml_pers_at Hsem.
    rewrite /shr_ghod !(by_ltx_sem_at (alt_sem_any Hsem)).
    iIntros "(%dd & %Hdd & A)". iExists dd. iSplit; [done|].
    rewrite !(by_lex_sem_at (alt_sem_any Hsem)).
    iDestruct "A" as (gg Hgg) "A". iExists gg. iSplit; [done|].
    rewrite !(pers_sem_at_any (alt_sem_any Hsem)) !(sep_sem_at Hsem).
    iDestruct "A" as "#(Hphys & Hgho & Hpers)".
    iAssert (sem (guard_fml (alive_fml κ') (alive_fml κ))) as "#Incl0".
    { iApply (dincl_at Hsem with "Incl"). }
    iDestruct ("Sub" $! dd with "[%]") as "[Sg Sp]"; [done|].
    iModIntro. iSplit.
    { rewrite -(Hph x).
      iApply (dguard_trans_at Hsem with "Incl0 Hphys"). }
    iSplit.
    - iApply (dguard_trans_at Hsem with "Incl0 []").
      iApply (dguard_trans_at Hsem with "Hgho []").
      iApply (dguard_intro_at Hsem). iIntros (sem' Hs) "!> gho".
      iDestruct ("Sg" $! sem' Hs with "gho") as "[$ $]".
    - iApply (store_fml_map_at Hsem with "[] Hpers").
      iIntros "!>" (sem' Hs _) "pers". by iApply ("Sp" $! sem' Hs).
  Qed.

  Lemma shr_tyd_incl {𝔄 𝔅} κ κ' (T : tydata 𝔄) (U : tydata 𝔅) f d :
    (∀ x, @syn_phys 𝔄 x = @syn_phys 𝔅 (f ~~$ₛ x)) →
    dincl κ' κ -∗ tyd_incl_lt T U f d -∗
    tyd_incl_at (shr_tyd κ T) (shr_tyd κ' U) (at_cloc_mapₛ f) d.
  Proof.
    move=> Hph. iIntros "#Incl #Sub".
    iDestruct (shr_ghod_incl κ κ' T U f d Hph with "Incl Sub") as "#H".
    iSplit; [|done]. iIntros "!>" (sem Hsem x g tid).
    have ? : Persistent (sem (shr_ghod κ T x d g tid)).
    { rewrite /shr_ghod. apply (by_ltx_persistent_at Hsem)=> d'.
      apply (by_lex_persistent_at Hsem)=> gg.
      rewrite (pers_sem_at_any (alt_sem_any Hsem)). exact _. }
    iIntros "#A". iSplitR; [by iApply ("H" $! sem Hsem)|by iIntros "_"].
  Qed.

  (** The other guarded former, now that its pointee sits behind a *stored
    guard* rather than a bare invariant token.  [ctx.v]'s
    [eguard_fml_alloc] is what makes that an even trade: the token is still
    how one is built, but a guard composes and a token does not, so this is
    the former that has a subtyping rule.  It is the thesis's (5.5) - the
    indirection is the whole reason [≤-ref] is provable. *)
  Lemma sown_persd_pers_at {𝔄} (T : tydata 𝔄) {sem} (H : alt_sem sem)
      x d g tid : Persistent (sem (sown_persd T x d g tid)).
  Proof.
    rewrite /sown_persd. apply (by_ltx_persistent_at H)=> d'.
    apply (by_lex_persistent_at H)=> gg. rewrite (sep_sem_at H).
    have ? := guard_fml_pers_at_any (alt_sem_any H) empty_fml
      (tyd_ghox T _ d' gg _).
    have ? := store_fml_pers_at_any (alt_sem_any H) (tyd_persx T _ d' gg _).
    exact _.
  Qed.

  Lemma sown_persd_incl {𝔄 𝔅} (T : tydata 𝔄) (U : tydata 𝔅) f d :
    tyd_incl_lt T U f d -∗
    □ ∀ sem (_ : alt_sem sem) x g tid,
        sem (sown_persd T x d g tid) -∗
        sem (sown_persd U (at_loc_mapₛ f ~~$ₛ x) d g tid).
  Proof.
    iIntros "#Sub !>" (sem Hsem x g tid). destruct x as [lx x]; simpl.
    have ? := guard_fml_pers_at Hsem.
    have ? := store_fml_pers_at_any (alt_sem_any Hsem).
    rewrite /sown_persd !(by_ltx_sem_at (alt_sem_any Hsem)).
    iIntros "(%dd & %Hdd & A)". iExists dd. iSplit; [done|].
    rewrite !(by_lex_sem_at (alt_sem_any Hsem)).
    iDestruct "A" as (gg Hgg) "A". iExists gg. iSplit; [done|].
    rewrite !(sep_sem_at Hsem). iDestruct "A" as "#[Hgho Hpers]".
    iDestruct ("Sub" $! dd with "[%]") as "[Sg Sp]"; [done|]. iSplit.
    - iApply (dguard_trans_at Hsem with "Hgho []").
      iApply (dguard_intro_at Hsem). iIntros (sem' Hs) "!> gho".
      iDestruct ("Sg" $! sem' Hs with "gho") as "[$ $]".
    - iApply (store_fml_map_at Hsem with "[] Hpers").
      iIntros "!>" (sem' Hs _) "pers". by iApply ("Sp" $! sem' Hs).
  Qed.

  (** Unlike [shr_tyd_incl] this one has a *non*-persistent ghost component
    - the pointer and its deallocation permission - so the backward
    direction is not free; it is free of the argument's laws all the same,
    because those two pieces are literally the same formula on both sides
    once the two layout equations are used. *)
  Lemma sown_tyd_incl {𝔄 𝔅} n (T : tydata 𝔄) (U : tydata 𝔅) f d :
    size_of 𝔄 = size_of 𝔅 →
    (∀ x, @syn_phys 𝔄 x = @syn_phys 𝔅 (f ~~$ₛ x)) →
    tyd_incl_lt T U f d -∗
    tyd_incl_at (sown_tyd n T) (sown_tyd n U) (at_loc_mapₛ f) d.
  Proof.
    move=> Hsz Hph. iIntros "#Sub".
    iDestruct (sown_persd_incl T U f d with "Sub") as "#H".
    iSplit; last first.
    { iIntros "!>" (sem Hsem x g tid). iApply ("H" $! sem Hsem). }
    iIntros "!>" (sem Hsem x g tid). destruct x as [lx x]; simpl.
    have ? := sown_persd_pers_at T Hsem (lx, x) d g tid.
    have ? := sown_persd_pers_at U Hsem (lx, (~~!ₛ) f x) d g tid.
    rewrite !(sep_sem_at Hsem) -Hsz -(Hph x).
    iIntros "(Hm & Hf & #Hp)".
    iAssert (sem (sown_persd U (lx, (~~!ₛ) f x) d g tid)) as "#Hp'".
    { by iApply ("H" $! sem Hsem (lx, x)). }
    iSplitL; [by iFrame "Hm Hf Hp'"|].
    iIntros "(Hm & Hf & _)". by iFrame "Hm Hf Hp".
  Qed.

End tyd.

(** ** The [prost], and the fixpoint

  Here the model is concrete, because [cif] is where the [prost] lives. *)
Section rec.
  Context `{!typingC CON} {JUDG Σ} `{!alerusGS (cifOF CON) Σ,
    !typingJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !typingCS CON JUDG Σ, !typingJS CON JUDG Σ}.

  Definition ghostd 𝔄 : prost :=
    (~~𝔄) -pr> nat -pr> nat -pr> thread_id -pr> cifPR CON Σ.
  Definition physd 𝔄 : prost :=
    discretePR ((~~𝔄) -d> thread_id -d> leibnizO (list fancy_val)).
  (** Its carrier is [tydata 𝔄] at this model *)
  Definition tyd 𝔄 : prost :=
    (discretePR natO * (ghostd 𝔄 * (ghostd 𝔄 * physd 𝔄)))%type.

  Notation tyd_size T := (T.1) (only parsing).
  Notation tyd_ghox T := (T.2.1) (only parsing).
  Notation tyd_persx T := (T.2.2.1) (only parsing).
  Notation tyd_phys T := (T.2.2.2) (only parsing).

  (** The [prost]'s carrier *is* [tydata] at this model; Coq needs it
    spelled out. *)
  Local Definition tod {𝔄} (T : tyd 𝔄) : tydata (FML:=cifOF CON) (Σ:=Σ) 𝔄 := T.

  (** Projecting [proeqv_later] through the data *)
  Local Lemma tyd_later_ghox {𝔄} k (T T' : tyd 𝔄) :
    proeqv_later k T T' →
    ∀ x d g tid, proeqv_later k (tyd_ghox T x d g tid) (tyd_ghox T' x d g tid).
  Proof. destruct k as [|k]; [done|]. move=> [_ [Hg _]] ????. apply Hg. Qed.
  Local Lemma tyd_later_persx {𝔄} k (T T' : tyd 𝔄) :
    proeqv_later k T T' →
    ∀ x d g tid, proeqv_later k (tyd_persx T x d g tid) (tyd_persx T' x d g tid).
  Proof. destruct k as [|k]; [done|]. move=> [_ [_ [Hp _]]] ????. apply Hp. Qed.

  Local Lemma proeqv_later_refl {PR : prost} k (a : PR) : proeqv_later k a a.
  Proof. destruct k as [|k]=>//=. Qed.
  Local Ltac citg_ind :=
    apply Citg_preserv_productive; [|apply proeqv_later_refl|done].

  (** The point of the whole rebuild: the borrowed data is needed only at
    [≡[<k]≡], which is exactly what [profix] supplies. *)
  #[export] Instance shr_tyd_productive {𝔄} κ :
    Productive' (tyd 𝔄) (tyd (at_clocₛ 𝔄))
      (shr_tyd (𝔄:=𝔄) (FML:=cifOF CON) (Σ:=Σ) κ).
  Proof.
    move=> k T T' Hlt. split; [done|]. split; [|split]=>/=; [| |done].
    all: move=> x d g tid; rewrite /shr_ghod /= /by_ltx /by_lex.
    all: citg_ind; move=> dd /=;
      citg_ind; (move=> b; destruct b=>/=; [reflexivity|]);
      citg_ind; move=> gg /=;
      citg_ind; (move=> b; destruct b=>/=; [reflexivity|]);
      citg_ind; move=> ? /=;
      citg_ind; move=> b; destruct b=>/=; [reflexivity|].
    all: citg_ind; move=> b; destruct b=>/=.
    all: [> apply cif_guard_productive;
            [apply proeqv_later_refl|by apply tyd_later_ghox]
        | apply cif_pstore_productive; by apply tyd_later_persx
        | apply cif_guard_productive;
            [apply proeqv_later_refl|by apply tyd_later_ghox]
        | apply cif_pstore_productive; by apply tyd_later_persx ].
  Qed.

  (** And so is the owning pointer, now that its pointee sits behind
    [guard_fml] and its persistent part behind [store_fml] - both [cdom]
    children.  This is the one thing PLAN.md listed as still missing. *)
  #[export] Instance sown_tyd_productive {𝔄} n :
    Productive' (tyd 𝔄) (tyd (at_locₛ 𝔄))
      (sown_tyd (𝔄:=𝔄) (FML:=cifOF CON) (Σ:=Σ) n).
  Proof.
    move=> k T T' Hlt. split; [done|]. split; [|split]=>/=; [| |done].
    - move=> x d g tid. rewrite /sown_persd /= /by_ltx /by_lex.
      citg_ind; (move=> b; destruct b=>/=; [reflexivity|]);
      citg_ind; (move=> b; destruct b=>/=; [reflexivity|]);
      citg_ind; move=> dd /=;
      citg_ind; (move=> b; destruct b=>/=; [reflexivity|]);
      citg_ind; move=> gg /=;
      citg_ind; (move=> b; destruct b=>/=; [reflexivity|]);
      citg_ind; move=> b; destruct b=>/=.
      + apply cif_guard_productive;
          [apply proeqv_later_refl|by apply tyd_later_ghox].
      + apply cif_pstore_productive. by apply tyd_later_persx.
    - move=> x d g tid. rewrite /sown_persd /= /by_ltx /by_lex.
      citg_ind; move=> dd /=;
      citg_ind; (move=> b; destruct b=>/=; [reflexivity|]);
      citg_ind; move=> gg /=;
      citg_ind; (move=> b; destruct b=>/=; [reflexivity|]);
      citg_ind; move=> b; destruct b=>/=.
      + apply cif_guard_productive;
          [apply proeqv_later_refl|by apply tyd_later_ghox].
      + apply cif_pstore_productive. by apply tyd_later_persx.
  Qed.

  (** The structural formers are *size-preserving*, which is all
    [shr_rec_productive] asks of them.  They may mention their argument's
    physical contents and size - those sit in a constructor's selector and
    data, which [proeqv k] compares by equality at every level, and the
    discrete components supply exactly that.  Only the *guarded* former has
    to keep its argument out of those positions. *)
  #[export] Instance prod_tyd_preserv_r {𝔄 𝔅} (T : tyd 𝔄) :
    Preserv' (tyd 𝔅) (tyd (𝔄 * 𝔅)) (λ U : tyd 𝔅, prod_tyd (tod T) (tod U)).
  Proof.
    move=> k U U' [/=Hn [/=Hg [/=Hp Hph]]]. split.
    { have Hn' : tyd_size (tod _) = tyd_size (tod _) := Hn. simpl.
      by rewrite Hn'. }
    split; [|split]=>/=.
    - move=> x d g tid. citg_ind. move=> b. destruct b=>/=; [reflexivity|].
      apply Hg.
    - move=> x d g tid. citg_ind. move=> b. destruct b=>/=; [reflexivity|].
      apply Hp.
    - move=> x tid /=.
      have Hph' : tyd_phys (tod U) (snd x) tid = tyd_phys (tod U') (snd x) tid
        := Hph (snd x) tid.
      by rewrite Hph'.
  Qed.
  #[export] Instance prod_tyd_preserv_l {𝔄 𝔅} (U : tyd 𝔅) :
    Preserv' (tyd 𝔄) (tyd (𝔄 * 𝔅)) (λ T : tyd 𝔄, prod_tyd (tod T) (tod U)).
  Proof.
    move=> k T T' [/=Hn [/=Hg [/=Hp Hph]]]. split.
    { have Hn' : tyd_size (tod _) = tyd_size (tod _) := Hn. simpl.
      by rewrite Hn'. }
    split; [|split]=>/=.
    - move=> x d g tid. citg_ind. move=> b. destruct b=>/=; [|reflexivity].
      apply Hg.
    - move=> x d g tid. citg_ind. move=> b. destruct b=>/=; [|reflexivity].
      apply Hp.
    - move=> x tid /=.
      have Hph' : tyd_phys (tod T) (fst x) tid = tyd_phys (tod T') (fst x) tid
        := Hph (fst x) tid.
      by rewrite Hph'.
  Qed.

  #[export] Instance xsum2_tyd_preserv_r {𝔄 𝔅} (T : tydata 𝔄) :
    Preserv' (tyd 𝔅) (tyd (xsumₛ [𝔄; 𝔅]))
      (λ U : tyd 𝔅, xsum2_tyd T (tod U)).
  Proof.
    move=> k U U' [/=_ [/=Hg [/=Hp Hph]]]. split; [done|].
    split; [|split]=>/=.
    - move=> [[?|[b|?]]?] d g tid /=; by [|apply Hg|].
    - move=> [[?|[b|?]]?] d g tid /=; by [|apply Hp|].
    - move=> [[?|[b|?]]?] tid /=; [done| |done].
      have Hph' : tyd_phys (tod U) b tid = tyd_phys (tod U') b tid
        := Hph b tid.
      by rewrite Hph'.
  Qed.

  #[export] Instance mod_tyd_preserv {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) (fⁱ : 𝔅 →ₛ 𝔄)
    `{!Isoₛ f fⁱ} :
    Preserv' (tyd 𝔄) (tyd 𝔅) (λ T : tyd 𝔄, mod_tyd f fⁱ (tod T)).
  Proof.
    move=> k T T' [/=Hn [/=Hg [/=Hp Hph]]]. split; [exact Hn|].
    split; [|split].
    - move=> x d g tid /=. apply Hg.
    - move=> x d g tid /=. apply Hp.
    - move=> x tid /=.
      have Hph' : tyd_phys (tod T) ((~~!ₛ) fⁱ x) tid
                = tyd_phys (tod T') ((~~!ₛ) fⁱ x) tid := Hph _ _.
      by rewrite Hph'.
  Qed.

  #[export] Instance own_tyd_preserv {𝔄} n :
    Preserv' (tyd 𝔄) (tyd (at_locₛ 𝔄)) (λ T : tyd 𝔄, own_tyd n (tod T)).
  Proof.
    move=> k T T' [/=Hn [/=Hg [/=Hp Hph]]].
    have Hn' : tyd_size (tod T) = tyd_size (tod T') := Hn.
    have Hph' : ∀ x tid, tyd_phys (tod T) x tid = tyd_phys (tod T') x tid
      := Hph.
    split; [done|]. split; [|split]=>/=; [| |done].
    - move=> x d g tid. rewrite /by_succx. destruct d as [|d']; [done|].
      simpl. rewrite Hn' Hph'.
      citg_ind. move=> b. destruct b=>/=; [reflexivity|].
      citg_ind. move=> b. destruct b=>/=; [reflexivity|].
      apply Hg.
    - move=> x d g tid. rewrite /by_succx. destruct d as [|d']; [done|].
      apply Hp.
  Qed.

  (** ** The fixpoint *)
  Definition ty_rec {𝔄} (F : tyd 𝔄 → tyd 𝔄) `{!Productive F} : tyd 𝔄 :=
    profix F.

  Lemma ty_rec_unfold {𝔄} (F : tyd 𝔄 → tyd 𝔄) `{!Productive F} :
    ty_rec F ≡ F (ty_rec F).
  Proof. apply profix_unfold. Qed.

  (** The unconditional laws survive it by unfolding once - which is
    [nola/examples/rust_halt/rec.v]'s [ty_rec_ty], proved
    [by rewrite ty_rec_unfold]. *)
  Lemma ty_rec_Ty {𝔄} (F : tyd 𝔄 → tyd 𝔄) `{!Productive F} :
    (∀ T, Ty (tod (F T))) → Ty (tod (ty_rec F)).
  Proof.
    move=> HF. have [/=Hn [/=Hg [/=Hp Hph]]] := ty_rec_unfold F.
    apply (Ty_mono (tod (F (ty_rec F))) (tod (ty_rec F))).
    - by rewrite Hn.
    - move=> x tid. by rewrite (Hph x tid).
    - move=> x d g tid. by rewrite (Hg x d g tid).
    - move=> x d g tid. by rewrite (Hp x d g tid).
    - apply HF.
  Qed.

  (** The prophecy law survives it by induction on the depth, because a
    guarded former uses its argument strictly below the depth it is asked
    about.  [ty_rec_ty_op] is proved the same way upstream. *)
  Lemma ty_rec_TyProphAt {𝔄} lfts (F : tyd 𝔄 → tyd 𝔄) `{!Productive F} :
    (∀ T d, TyProphLt lfts (tod T) d → TyProphAt lfts (tod (F T)) d) →
    ∀ d, TyProphAt lfts (tod (ty_rec F)) d.
  Proof.
    move=> HF d. induction (lt_wf d) as [d _ IH].
    have [/=_ [/=Hg [/=Hp _]]] := ty_rec_unfold F.
    apply (TyProphAt_mono lfts (tod (F (ty_rec F))) (tod (ty_rec F))).
    - move=> x dd g tid. by rewrite (Hg x dd g tid).
    - move=> x dd g tid. by rewrite (Hp x dd g tid).
    - apply HF=> d' Hlt. by apply IH.
  Qed.

  (** The inclusion survives the fixpoint by induction on the depth, for
    the same reason [ty_rec_TyProphAt] does: a guarded former uses its
    argument strictly below the depth it is asked about.

    This is the thesis's § 5.1 fn. 1 - [≤-ref] used *coinductively*, so
    that [listᵢ T ≤ listⱼ U] follows from [T ≤ U], [U ≤ T] and [i ≤ j].
    The thesis needs coinduction, and Definition 4.5's [Deriv_φ] to carry
    the coinductive hypothesis, because its [rec] is plain substitution
    with no index to descend on.  The port's guarded formers carry
    [⌜d' < d⌝], so the same rule is a well-founded induction, and [Deriv]
    is not needed for it: the quantification over candidate interpretations
    that [Deriv] would provide is already inside [tyd_incl_at], which is
    stated at every [alt_sem].

    [P] is whatever persistent side condition the body needs - for the
    lists below, the lifetime inclusion and the element's own inclusion. *)
  Lemma ty_rec_incl {𝔄 𝔅} (F : tyd 𝔄 → tyd 𝔄) `{!Productive F}
      (G : tyd 𝔅 → tyd 𝔅) `{!Productive G} (f : 𝔄 →ₛ 𝔅)
      (P : iProp Σ) `{!Persistent P} :
    (∀ d, P -∗ tyd_incl_lt (tod (ty_rec F)) (tod (ty_rec G)) f d -∗
          tyd_incl_at (tod (F (ty_rec F))) (tod (G (ty_rec G))) f d) →
    ∀ d, P ⊢ tyd_incl_at (tod (ty_rec F)) (tod (ty_rec G)) f d.
  Proof.
    move=> HFG d. induction (lt_wf d) as [d _ IH].
    have [/=_ [/=HgF [/=HpF _]]] := ty_rec_unfold F.
    have [/=_ [/=HgG [/=HpG _]]] := ty_rec_unfold G.
    iIntros "#P".
    iApply (tyd_incl_at_mono (tod (F (ty_rec F))) (tod (ty_rec F))
                             (tod (G (ty_rec G))) (tod (ty_rec G)) f d).
    { move=> x dd g tid. by rewrite (HgF x dd g tid). }
    { move=> x dd g tid. by rewrite (HpF x dd g tid). }
    { move=> x dd g tid. by rewrite (HgG x dd g tid). }
    { move=> x dd g tid. by rewrite (HpG x dd g tid). }
    iApply (HFG with "P"). iIntros "!>" (d' Hd'). by iApply (IH d' Hd').
  Qed.

  (** ** Putting it together

    A recursive type is [μ X. G (&shr{κ} X)] for a *structural* [G]: the
    shared borrow contributes the productivity, so [G] need only be
    size-preserving, and it need only preserve [Ty] and the prophecy law,
    which is what every structural former does.  This is the thesis's
    guardedness condition (§ 5.1) and [rust_halt]'s three-layer pattern:
    guarded formers unconditional, unguarded ones conditional, and
    [ty_rec] asking for [∀ T, Ty (F T)]. *)
  Lemma shr_rec_productive {𝔄 𝔅} κ (G : tyd (at_clocₛ 𝔅) → tyd 𝔄) :
    Preserv' (tyd (at_clocₛ 𝔅)) (tyd 𝔄) G →
    Productive' (tyd 𝔅) (tyd 𝔄) (λ T, G (shr_tyd κ T)).
  Proof.
    move=> HG k T T' Hlt. apply HG.
    by apply (shr_tyd_productive (𝔄:=𝔅) κ k T T').
  Qed.

  Section shr_rec.
    Context {𝔄} (κ : lft) (G : tyd (at_clocₛ 𝔄) → tyd 𝔄)
      (HG : Preserv' (tyd (at_clocₛ 𝔄)) (tyd 𝔄) G).

    #[local] Instance shr_rec_prod :
      Productive' (tyd 𝔄) (tyd 𝔄) (λ T : tyd 𝔄, G (shr_tyd κ T)) :=
      shr_rec_productive κ G HG.

    Definition ty_rec_shr : tyd 𝔄 := ty_rec (λ T : tyd 𝔄, G (shr_tyd κ T)).

    (** Unconditional, because [Ty (shr_tyd κ T)] is *)
    Lemma ty_rec_shr_Ty :
      (∀ U, Ty (tod U) → Ty (tod (G U))) → Ty (tod ty_rec_shr).
    Proof. move=> HTy. apply ty_rec_Ty=> T. apply HTy, shr_tyd_Ty. Qed.

    (** Conditional, and discharged by the depth induction.

      The lifetime list has to contain [κ]: the guarded former's law comes
      out at [κ :: lfts], and the structural [G] takes it at [lfts], so the
      two are reconciled by [TyProphAt_lfts] - which needs
      [⋀lfts ⊑ κ ⊓ ⋀lfts], i.e. [⋀lfts ⊑ κ]. *)
    Lemma ty_rec_shr_TyProphAt lfts :
      (⊢ lft_intersect_list lfts ⊑ κ) →
      (∀ U d, TyProphAt lfts (tod U) d → TyProphAt lfts (tod (G U)) d) →
      ∀ d, TyProphAt lfts (tod ty_rec_shr) d.
    Proof.
      move=> Hκ HG' d. apply ty_rec_TyProphAt=> T d' Hlt.
      apply HG', (TyProphAt_lfts (κ :: lfts) lfts).
      { iApply llftl_incl_glb; [iApply Hκ|iApply llftl_incl_sub; set_solver]. }
      by apply shr_tyd_TyProphAt.
    Qed.
    (** And the end of the road: an actual [type].

      The lifetime list and the external context are *supplied*, not
      derived.  `typing/fixpoint.v` derives them with [TypeLftMorphism]
      because its carrier is the whole record; here they were never in the
      carrier, so the only thing that constrains them is the prophecy law,
      and [HP] is exactly that obligation. *)
    Definition type_of_rec_shr lfts E
      (Hκ : ⊢ lft_intersect_list lfts ⊑ κ)
      (HTy : ∀ U, Ty (tod U) → Ty (tod (G U)))
      (HP : ∀ U d, TyProphAt lfts (tod U) d → TyProphAt lfts (tod (G U)) d)
      : type 𝔄 :=
      type_of_tyd lfts E (tod ty_rec_shr) (ty_rec_shr_Ty HTy)
        (ty_rec_shr_TyProphAt lfts Hκ HP).

    Lemma type_of_rec_shr_ghox lfts E Hκ HTy HP x d g tid :
      (type_of_rec_shr lfts E Hκ HTy HP).(ty_ghox) x d g tid =
        tyd_ghox (tod ty_rec_shr) x d g tid.
    Proof. done. Qed.
  End shr_rec.

  (** ** The same, with the owning pointer as the guarded former *)
  Lemma own_rec_productive {𝔄 𝔅} n (G : tyd (at_locₛ 𝔅) → tyd 𝔄) :
    Preserv' (tyd (at_locₛ 𝔅)) (tyd 𝔄) G →
    Productive' (tyd 𝔅) (tyd 𝔄) (λ T, G (sown_tyd n T)).
  Proof.
    move=> HG k T T' Hlt. apply HG.
    by apply (sown_tyd_productive (𝔄:=𝔅) n k T T').
  Qed.

  Section own_rec.
    Context {𝔄} (n : nat) (G : tyd (at_locₛ 𝔄) → tyd 𝔄)
      (HG : Preserv' (tyd (at_locₛ 𝔄)) (tyd 𝔄) G).

    #[local] Instance own_rec_prod :
      Productive' (tyd 𝔄) (tyd 𝔄) (λ T : tyd 𝔄, G (sown_tyd n T)) :=
      own_rec_productive n G HG.

    Definition ty_rec_own : tyd 𝔄 := ty_rec (λ T : tyd 𝔄, G (sown_tyd n T)).

    Lemma ty_rec_own_Ty :
      (∀ U, Ty (tod U) → Ty (tod (G U))) → Ty (tod ty_rec_own).
    Proof. move=> HTy. apply ty_rec_Ty=> T. apply HTy, sown_tyd_Ty. Qed.

    (** No lifetime to reconcile, unlike [ty_rec_shr_TyProphAt]: an owning
      pointer adds none. *)
    Lemma ty_rec_own_TyProphAt lfts :
      (∀ U d, TyProphAt lfts (tod U) d → TyProphAt lfts (tod (G U)) d) →
      ∀ d, TyProphAt lfts (tod ty_rec_own) d.
    Proof.
      move=> HG' d. apply ty_rec_TyProphAt=> T d' Hlt.
      by apply HG', sown_tyd_TyProphAt.
    Qed.

    Definition type_of_rec_own lfts E
      (HTy : ∀ U, Ty (tod U) → Ty (tod (G U)))
      (HP : ∀ U d, TyProphAt lfts (tod U) d → TyProphAt lfts (tod (G U)) d)
      : type 𝔄 :=
      type_of_tyd lfts E (tod ty_rec_own) (ty_rec_own_Ty HTy)
        (ty_rec_own_TyProphAt lfts HP).
  End own_rec.

(** The whole chain rests on [Eq_rect_eq] and nothing else. *)
Print Assumptions ty_rec_Ty.
Print Assumptions ty_rec_TyProphAt.

  (** ** A list behind shared references

    [nola/examples/rust_halt/verify/list.v] builds its list as

    >  ty_list T := ty_rec (λ Self, ty_mod list_unwrap
    >                        (ty_sum ty_unit (ty_prod T (ty_box Self))))

    - choose a refinement type whose unfolding matches the body's, extending
    the grammar if need be, and bridge with [ty_mod] along an injective
    unwrap.  This is that, with the one substitution this port forces:

    >  μ X. Σ! [(); 𝔄 * &shr{κ} X]

    [ty_box] is productive upstream because [ty'_box_def] puts the pointee's
    [ty_own] behind [cif_store]; our [own_ptr] holds it as a visible child,
    so it is [Preserv] and not [Productive], and [&shr{κ}] is the guarded
    former we have.  So this is a list of *shared references* rather than of
    owning pointers; making [own_ptr] productive is the one thing between
    the two, and it is the arc [&shr] already went through.

    The refinement type is [shr_listₛ 𝔄], added to [prophecy/syn_type.v] for
    this.  [listₛ] could not serve: [Isoₛ] here demands equal [size_of] *and*
    equal [syn_phys], because [ty_size_eq2]/[ty_phys_eq2] tie a type to its
    refinement, and [size_of (listₛ _)] is [0] while the body is
    [xsumₛ]-shaped.  [shr_listₛ]'s clauses *are* the body's, written so that
    the two are convertible rather than merely equal - which is why
    [shrlist_isoₛ] over there is three [done]s and a case split. *)
  Section shr_list.
    Context {𝔄} (κ : lft) (T : tyd 𝔄).

    Definition shr_list_gen (U : tyd (at_clocₛ (shr_listₛ 𝔄)))
      : tyd (shr_listₛ 𝔄) :=
      mod_tyd foldshrₛ unfoldshrₛ
        (xsum2_tyd unit_tyd (prod_tyd (tod T) (tod U))).

    #[local] Instance shr_list_gen_preserv :
      Preserv' (tyd (at_clocₛ (shr_listₛ 𝔄))) (tyd (shr_listₛ 𝔄))
        shr_list_gen.
    Proof.
      move=> k U U' E. rewrite /shr_list_gen.
      apply (mod_tyd_preserv foldshrₛ unfoldshrₛ k).
      apply (xsum2_tyd_preserv_r unit_tyd k).
      by apply (prod_tyd_preserv_r T k).
    Qed.

    Lemma shr_list_gen_Ty (HT : Ty (tod T)) U :
      Ty (tod U) → Ty (tod (shr_list_gen U)).
    Proof.
      move=> HU. rewrite /shr_list_gen.
      have ? : Ty unit_tyd := unit_tyd_Ty.
      have ? : Ty (prod_tyd (tod T) (tod U)) by apply prod_tyd_Ty.
      have ? : Ty (xsum2_tyd unit_tyd (prod_tyd (tod T) (tod U)))
        by apply xsum2_tyd_Ty.
      by apply mod_tyd_Ty.
    Qed.

    Lemma shr_list_gen_TyProphAt lfts
      (HT : ∀ d, TyProphAt lfts (tod T) d) U d :
      TyProphAt lfts (tod U) d → TyProphAt lfts (tod (shr_list_gen U)) d.
    Proof.
      move=> HU. rewrite /shr_list_gen. apply mod_tyd_TyProphAt.
      apply xsum2_tyd_TyProphAt; [apply unit_tyd_TyProphAt|].
      apply (TyProphAt_lfts (lfts ++ lfts) lfts).
      { rewrite lft_intersect_list_app. apply llftl_incl_sub.
        unfold meet, llft_intersect. set_solver. }
      by apply prod_tyd_TyProphAt.
    Qed.

    (** The data, as a fixed point *)
    Definition shr_list_tyd : tyd (shr_listₛ 𝔄) :=
      ty_rec_shr κ shr_list_gen shr_list_gen_preserv.

    Lemma shr_list_tyd_Ty (HT : Ty (tod T)) : Ty (tod shr_list_tyd).
    Proof.
      rewrite /shr_list_tyd. apply ty_rec_shr_Ty=> U HU.
      by apply shr_list_gen_Ty.
    Qed.

    Lemma shr_list_tyd_TyProphAt lfts
      (Hκ : ⊢ lft_intersect_list lfts ⊑ κ)
      (HT : ∀ d, TyProphAt lfts (tod T) d) d :
      TyProphAt lfts (tod shr_list_tyd) d.
    Proof.
      rewrite /shr_list_tyd. apply ty_rec_shr_TyProphAt; [done|].
      move=> U d' HU. by apply shr_list_gen_TyProphAt.
    Qed.

    (** ...and as a [type] *)
    Definition ty_shr_list lfts E
      (Hκ : ⊢ lft_intersect_list lfts ⊑ κ)
      (HT : Ty (tod T)) (HP : ∀ d, TyProphAt lfts (tod T) d)
      : type (shr_listₛ 𝔄) :=
      type_of_rec_shr κ shr_list_gen shr_list_gen_preserv lfts E Hκ
        (λ U HU, shr_list_gen_Ty HT U HU)
        (λ U d HU, shr_list_gen_TyProphAt lfts HP U d HU).
  End shr_list.

  (** ** A list of owning pointers

    The same recipe again, with the guarded former that PLAN.md said could
    not be one:

    >  μ X. Σ! [(); 𝔄 * own n X]

    This is [rust_halt]'s [ty_list] with nothing substituted.  [sown_tyd]
    differs from [typing/own.v]'s [own_ptr] in exactly one way - the
    pointee's ghost assertion is reached through a stored guard rather than
    held in hand - which is what buys the productivity, and which means the
    pointee can be *borrowed* but not moved out.

    Moving it out cannot be added by storing [Px ∨ token γ] the way
    [nola/iris/store.v] does: narrowing the guard back to [Px] needs
    [guard_or_false] or [guard_cancel_or], and both ask for a *persistent*
    side condition - [guard] is [□ ∀ T, …] - which an owned token is not.
    PLAN.md has the argument and the ways out. *)
  Section own_list.
    Context {𝔄} (n : nat) (T : tyd 𝔄).

    Definition own_list_gen (U : tyd (at_locₛ (own_listₛ 𝔄)))
      : tyd (own_listₛ 𝔄) :=
      mod_tyd foldownₛ unfoldownₛ
        (xsum2_tyd unit_tyd (prod_tyd (tod T) (tod U))).

    #[local] Instance own_list_gen_preserv :
      Preserv' (tyd (at_locₛ (own_listₛ 𝔄))) (tyd (own_listₛ 𝔄))
        own_list_gen.
    Proof.
      move=> k U U' E. rewrite /own_list_gen.
      apply (mod_tyd_preserv foldownₛ unfoldownₛ k).
      apply (xsum2_tyd_preserv_r unit_tyd k).
      by apply (prod_tyd_preserv_r T k).
    Qed.

    Lemma own_list_gen_Ty (HT : Ty (tod T)) U :
      Ty (tod U) → Ty (tod (own_list_gen U)).
    Proof.
      move=> HU. rewrite /own_list_gen.
      have ? : Ty unit_tyd := unit_tyd_Ty.
      have ? : Ty (prod_tyd (tod T) (tod U)) by apply prod_tyd_Ty.
      have ? : Ty (xsum2_tyd unit_tyd (prod_tyd (tod T) (tod U)))
        by apply xsum2_tyd_Ty.
      by apply mod_tyd_Ty.
    Qed.

    Lemma own_list_gen_TyProphAt lfts
      (HT : ∀ d, TyProphAt lfts (tod T) d) U d :
      TyProphAt lfts (tod U) d → TyProphAt lfts (tod (own_list_gen U)) d.
    Proof.
      move=> HU. rewrite /own_list_gen. apply mod_tyd_TyProphAt.
      apply xsum2_tyd_TyProphAt; [apply unit_tyd_TyProphAt|].
      apply (TyProphAt_lfts (lfts ++ lfts) lfts).
      { rewrite lft_intersect_list_app. apply llftl_incl_sub.
        unfold meet, llft_intersect. set_solver. }
      by apply prod_tyd_TyProphAt.
    Qed.

    Definition own_list_tyd : tyd (own_listₛ 𝔄) :=
      ty_rec_own n own_list_gen own_list_gen_preserv.

    Lemma own_list_tyd_Ty (HT : Ty (tod T)) : Ty (tod own_list_tyd).
    Proof.
      rewrite /own_list_tyd. apply ty_rec_own_Ty=> U HU.
      by apply own_list_gen_Ty.
    Qed.

    Lemma own_list_tyd_TyProphAt lfts
      (HT : ∀ d, TyProphAt lfts (tod T) d) d :
      TyProphAt lfts (tod own_list_tyd) d.
    Proof.
      rewrite /own_list_tyd. apply ty_rec_own_TyProphAt=> U d' HU.
      by apply own_list_gen_TyProphAt.
    Qed.

    (** ...and as a [type] *)
    Definition ty_own_list lfts E
      (HT : Ty (tod T)) (HP : ∀ d, TyProphAt lfts (tod T) d)
      : type (own_listₛ 𝔄) :=
      type_of_rec_own n own_list_gen own_list_gen_preserv lfts E
        (λ U HU, own_list_gen_Ty HT U HU)
        (λ U d HU, own_list_gen_TyProphAt lfts HP U d HU).
  End own_list.

  (** ** Subtyping of a recursive type

    The thesis's § 5.1 fn. 1 at the shared-reference list: from the
    element's inclusion and [κ' ⊑ κ], the list's.  Its [i ≤ j] is the
    lifetime inequality here, a shared reference's lifetime standing in for
    the level; and its two premises [T ≤ U] and [U ≤ T] are one hypothesis,
    because [type_incl]'s ghost component is two-way in this port anyway -
    a borrow has to be given back.

    What is *not* needed is the coinduction.  [ty_rec_incl] turns the loop
    with an induction on the depth, and the quantification over candidate
    interpretations that Definition 4.5's [Deriv_φ] would supply is already
    inside [tyd_incl_at]. *)
  Section shr_list_incl.
    Context {𝔄 𝔅} (κ κ' : lft) (T : tyd 𝔄) (U : tyd 𝔅) (f : 𝔄 →ₛ 𝔅)
      (Hsz : size_of 𝔄 = size_of 𝔅)
      (Hph : ∀ x, @syn_phys 𝔄 x = @syn_phys 𝔅 ((~~!ₛ) f x)).

    (** The body is a congruence, former by former *)
    Lemma shr_list_gen_incl V W d :
      tyd_incl_at (tod T) (tod U) f d -∗
      tyd_incl_at (tod V) (tod W) (at_cloc_mapₛ (shr_list_mapₛ f)) d -∗
      tyd_incl_at (tod (shr_list_gen T V)) (tod (shr_list_gen U W))
        (shr_list_mapₛ f) d.
    Proof.
      iIntros "#A #B". rewrite /shr_list_gen.
      iApply (mod_tyd_incl foldshrₛ unfoldshrₛ foldshrₛ unfoldshrₛ _ _
        (shr_list_body_mapₛ f) (shr_list_mapₛ f) d).
      { move=> x. by rewrite unfoldshr_mapₛ. }
      rewrite /shr_list_body_mapₛ.
      iApply (xsum2_tyd_incl unit_tyd unit_tyd _ _ idₛ _ d).
      { iApply unit_tyd_incl. }
      by iApply (prod_tyd_incl with "A B").
    Qed.

    (** The side condition the fixpoint carries: persistent, as
      [ty_rec_incl] asks, because both halves are. *)
    Definition shr_list_inclP : iProp Σ :=
      (dincl κ' κ ∗ ∀ d, tyd_incl_at (tod T) (tod U) f d)%I.

    Lemma shr_list_tyd_incl d :
      shr_list_inclP ⊢
      tyd_incl_at (tod (shr_list_tyd κ T)) (tod (shr_list_tyd κ' U))
        (shr_list_mapₛ f) d.
    Proof.
      rewrite /shr_list_tyd /ty_rec_shr.
      apply (ty_rec_incl _ _ (shr_list_mapₛ f) shr_list_inclP).
      move=> d'. iIntros "#[Inκ Sub] #Lt".
      iApply (shr_list_gen_incl with "Sub").
      iApply (shr_tyd_incl κ κ' _ _ (shr_list_mapₛ f) d'
        (shr_list_phys_eq f Hsz Hph) with "Inκ Lt").
    Qed.

    (** ...and at the level of [type]s *)
    Lemma ty_shr_list_type_incl lfts E Hκ HT HP lfts' E' Hκ' HU HP' :
      dincl (lft_intersect_list lfts') (lft_intersect_list lfts) -∗
      shr_list_inclP -∗
      type_incl (ty_shr_list κ T lfts E Hκ HT HP)
                (ty_shr_list κ' U lfts' E' Hκ' HU HP') (shr_list_mapₛ f).
    Proof.
      iIntros "#Lft #P".
      iApply (type_incl_of_tyd_incl (ty_shr_list κ T lfts E Hκ HT HP)
        (ty_shr_list κ' U lfts' E' Hκ' HU HP') (shr_list_mapₛ f)
        (shr_list_size_eq Hsz) (shr_list_phys_eq f Hsz Hph) with "Lft").
      iIntros (d). by iApply shr_list_tyd_incl.
    Qed.

    Lemma ty_shr_list_subtype E0 L lfts E Hκ HT HP lfts' E' Hκ' HU HP' :
      lctx_lft_incl E0 L κ' κ →
      lctx_lft_incl E0 L (lft_intersect_list lfts')
        (lft_intersect_list lfts) →
      (llctx_interp L -∗ □ (elctx_interp E0 -∗
        ∀ d, tyd_incl_at (tod T) (tod U) f d)) →
      subtype E0 L (ty_shr_list κ T lfts E Hκ HT HP)
                   (ty_shr_list κ' U lfts' E' Hκ' HU HP') (shr_list_mapₛ f).
    Proof.
      move=> Inκ Inl Sub. iIntros "L".
      iDestruct (Inκ with "L") as "#Inκ". iDestruct (Inl with "L") as "#Inl".
      iDestruct (Sub with "L") as "#Sub". iIntros "!> #E".
      iApply (ty_shr_list_type_incl with "[] [Sub]").
      - by iApply "Inl".
      - rewrite /shr_list_inclP. iSplit; [by iApply "Inκ"|by iApply "Sub"].
    Qed.
  End shr_list_incl.

(** The subtyping rule rests on the same two axioms the rest of the chain
  does - no [Deriv], no coinduction, no [Cofe]. *)
Print Assumptions ty_shr_list_subtype.

  (** ** ...and of the owning-pointer list

    The same rule again, and getting it took one change of model rather
    than any new proof technique.  [sown_tyd] used to hold its pointee
    behind [dinv_fml], a bare invariant token - and a token *names the
    formula it stores*, so nothing turns [dinv_tok Px] into [dinv_tok Qx]
    and the former admitted no subtyping rule at all.

    That is exactly the obstruction the thesis's (5.5) exists to remove:

    >  `⟦ref°ₖ T⟧ᵢᵟ v ≜ ∃U, k' ≤ k. □ δ(T ≤̇ U) ∗ □ δ(U ≤̇ T) ∗ invₖ'ᴺ((ℓ+o) ↦ U)`

    - the invariant holds a *different* type tied to [T] by two stored
    implications, and § 5.1 says in so many words that the indirection is
    the only reason [≤-ref] is provable.  [&shr{κ}] had the indirection
    already, in the Leaf guard its body is wrapped in; [sown_tyd] now has
    it too, holding [guard_fml empty_fml Px] instead of [dinv_fml Px].
    [ctx.v]'s [eguard_fml_alloc] is what makes the trade free: the token is
    still how one is allocated, and [guard_fml_sem_2] stores the guard it
    yields.  A guard composes ([guard_trans]); a token does not. *)
  Section own_list_incl.
    Context {𝔄 𝔅} (n : nat) (T : tyd 𝔄) (U : tyd 𝔅) (f : 𝔄 →ₛ 𝔅)
      (Hsz : size_of 𝔄 = size_of 𝔅)
      (Hph : ∀ x, @syn_phys 𝔄 x = @syn_phys 𝔅 ((~~!ₛ) f x)).

    Lemma own_list_gen_incl V W d :
      tyd_incl_at (tod T) (tod U) f d -∗
      tyd_incl_at (tod V) (tod W) (at_loc_mapₛ (own_list_mapₛ f)) d -∗
      tyd_incl_at (tod (own_list_gen T V)) (tod (own_list_gen U W))
        (own_list_mapₛ f) d.
    Proof.
      iIntros "#A #B". rewrite /own_list_gen.
      iApply (mod_tyd_incl foldownₛ unfoldownₛ foldownₛ unfoldownₛ _ _
        (own_list_body_mapₛ f) (own_list_mapₛ f) d).
      { move=> x. by rewrite unfoldown_mapₛ. }
      rewrite /own_list_body_mapₛ.
      iApply (xsum2_tyd_incl unit_tyd unit_tyd _ _ idₛ _ d).
      { iApply unit_tyd_incl. }
      by iApply (prod_tyd_incl with "A B").
    Qed.

    (** No lifetime to carry, unlike the shared-reference list *)
    Definition own_list_inclP : iProp Σ :=
      (∀ d, tyd_incl_at (tod T) (tod U) f d)%I.

    Lemma own_list_tyd_incl d :
      own_list_inclP ⊢
      tyd_incl_at (tod (own_list_tyd n T)) (tod (own_list_tyd n U))
        (own_list_mapₛ f) d.
    Proof.
      rewrite /own_list_tyd /ty_rec_own.
      apply (ty_rec_incl _ _ (own_list_mapₛ f) own_list_inclP).
      move=> d'. iIntros "#Sub #Lt".
      iApply (own_list_gen_incl with "Sub").
      iApply (sown_tyd_incl n _ _ (own_list_mapₛ f) d'
        (own_list_size_eq Hsz) (own_list_phys_eq f Hsz Hph) with "Lt").
    Qed.

    Lemma ty_own_list_type_incl lfts E HT HP lfts' E' HU HP' :
      dincl (lft_intersect_list lfts') (lft_intersect_list lfts) -∗
      own_list_inclP -∗
      type_incl (ty_own_list n T lfts E HT HP)
                (ty_own_list n U lfts' E' HU HP') (own_list_mapₛ f).
    Proof.
      iIntros "#Lft #P".
      iApply (type_incl_of_tyd_incl (ty_own_list n T lfts E HT HP)
        (ty_own_list n U lfts' E' HU HP') (own_list_mapₛ f)
        (own_list_size_eq Hsz) (own_list_phys_eq f Hsz Hph) with "Lft").
      iIntros (d). by iApply own_list_tyd_incl.
    Qed.

    Lemma ty_own_list_subtype E0 L lfts E HT HP lfts' E' HU HP' :
      lctx_lft_incl E0 L (lft_intersect_list lfts')
        (lft_intersect_list lfts) →
      (llctx_interp L -∗ □ (elctx_interp E0 -∗
        ∀ d, tyd_incl_at (tod T) (tod U) f d)) →
      subtype E0 L (ty_own_list n T lfts E HT HP)
                   (ty_own_list n U lfts' E' HU HP') (own_list_mapₛ f).
    Proof.
      move=> Inl Sub. iIntros "L". iDestruct (Inl with "L") as "#Inl".
      iDestruct (Sub with "L") as "#Sub". iIntros "!> #E".
      iApply (ty_own_list_type_incl with "[] [Sub]").
      - by iApply "Inl".
      - rewrite /own_list_inclP. by iApply "Sub".
    Qed.
  End own_list_incl.

(** Both rules rest on the same two axioms the rest of the chain does -
  no [Deriv], no coinduction, no [Cofe]. *)
Print Assumptions ty_own_list_subtype.

(** ** The degenerate recursive type, at a closed refinement type

  [ty_shr_list] above is parametric in [𝔄], so it never asks Coq to compute
  with a *concrete* refinement type.  This does: [~~(at_clocₛ (xsumₛ []))]
  is empty, hence isomorphic to [~~(at_clocₛ (at_clocₛ (xsumₛ [])))], with
  the sizes and [syn_phys] agreeing vacuously, so [μ X. &shr{κ} X] exists at
  it.  The type is uninhabited and says nothing about lists; what it checks
  is that the chain still goes through once [𝔄] is closed and every [size_of]
  and [syn_phys] in sight reduces.

  One tactical note, because it cost a day.  Each application below unfolds
  its abbreviation first ([rewrite /chain]).  Left folded, [apply
  ty_rec_shr_Ty] fails to match [chain κ] against [ty_rec_shr ?κ ?G ?HG]
  first-order and falls back on conversion, which unfolds [ty_rec] through
  [profix]'s seal and does not come back - the goal is still *provable*, by
  a fully explicit term, but the tactic will not find it.  Unfolded, the
  whole section below elaborates in about a second.  Anything built on
  [profix] will want the same discipline. *)
  Local Notation Eₛ := (at_clocₛ (xsumₛ [])).

  (** Both interpretations of [xsumₛ []] are [∅ * list val], so one [Void]
    instance per shape covers [~~ Eₛ] and [Eₛ] alike. *)
  Local Instance E_void : Void (~~ Eₛ).
  Proof. by move=> ? [? [[] ?]]. Qed.
  Local Instance acE_void : Void (~~ (at_clocₛ Eₛ)).
  Proof. move=> ? [? y]. by apply absurd. Qed.

  Definition foldEₛ : at_clocₛ Eₛ →ₛ Eₛ := {|
    syn_type_morphism_fn := absurd; syn_type_morphism_proph_fn := absurd;
    syn_type_morphism_commutes := λ x _, absurd x;
    syn_type_morphism_ξl := λ x, absurd x;
  |}.
  Definition unfoldEₛ : Eₛ →ₛ at_clocₛ Eₛ := {|
    syn_type_morphism_fn := absurd; syn_type_morphism_proph_fn := absurd;
    syn_type_morphism_commutes := λ x _, absurd x;
    syn_type_morphism_ξl := λ x, absurd x;
  |}.

  (** Any two maps between void types are mutually inverse.  [void_iso] in
    [nola/alerus/util/basic.v] says this for [absurd] itself; stating it for
    arbitrary maps avoids having to match the [Void] instance the record
    literal happened to pick. *)
  Local Lemma iso_of_void {A B} `{!Void A, !Void B} (f : A → B) (g : B → A) :
    Iso f g.
  Proof. split; fun_ext=> x; exact (absurd x). Qed.

  #[local] Instance isoEₛ : Isoₛ foldEₛ unfoldEₛ.
  Proof.
    split; simpl.
    - apply iso_of_void.
    - apply iso_of_void.
    - done.
    - move=> x. exact (absurd x).
  Qed.

  (** The generator: the body's refinement type brought back to the
    recursion's, exactly as [ty_mod list_unwrap] does upstream *)
  Definition chain_gen (U : tyd (at_clocₛ Eₛ)) : tyd Eₛ :=
    mod_tyd foldEₛ unfoldEₛ (tod U).

  #[local] Instance chain_gen_preserv :
    Preserv' (tyd (at_clocₛ Eₛ)) (tyd Eₛ) chain_gen.
  Proof. apply mod_tyd_preserv. Qed.

  (** [μ X. &shr{κ} X], as data *)
  Definition chain (κ : lft) : tyd Eₛ :=
    ty_rec_shr κ chain_gen chain_gen_preserv.

  Lemma chain_Ty κ : Ty (tod (chain κ)).
  Proof. rewrite /chain. apply ty_rec_shr_Ty=> U HU. by apply mod_tyd_Ty. Qed.

  Lemma chain_TyProphAt κ d : TyProphAt [κ] (tod (chain κ)) d.
  Proof.
    rewrite /chain. apply ty_rec_shr_TyProphAt.
    { iApply llftl_intersect_incl_l. }
    move=> U d' HU. by apply mod_tyd_TyProphAt.
  Qed.

  (** ...and as a [type] *)
  Definition ty_chain (κ : lft) : type Eₛ :=
    type_of_tyd [κ] [] (tod (chain κ)) (chain_Ty κ) (chain_TyProphAt κ).
End rec.

(** Both rest on [Eq_rect_eq] and [functional_extensionality], the latter
  only through the [Iso] proofs - [SemiIso] is stated as [g ∘ f = id], an
  equality of functions, so any [Isoₛ] instance needs it.  The soundness
  theorems use neither. *)
Print Assumptions ty_shr_list.
Print Assumptions ty_own_list.
Print Assumptions ty_chain.
