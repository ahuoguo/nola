(** * VerusBelt's [syn_type] as a Nola syntactic type

  Nola's prophecy library ([nola.util.proph], [nola.iris.proph]) and
  everything built on it - [proph_ag], [pborrow], [pborrow_deriv] - is
  parameterised by a syntactic type universe [synty].  [rust_halt]
  instantiates it with [nola.examples.xty]'s [xty].  VerusBelt already has
  such a universe, [syn_type] ([alerus/prophecy/syn_type.v]), so Nola's
  machinery applies to it unchanged once the structure is registered.

  This is the first file of the Nola-native rewrite described in
  [alerus/typing/README.md]: the type system is rebuilt on Nola's own
  lifetime, borrow and prophetic-borrow libraries rather than on the Leaf
  reimplementation in [alerus/lifetime/].

  Note which interpretation of [syn_type] is used.  Nola's prophecy
  variables range over *semantic* values, and a clairvoyant value is a
  function [clair TY 𝔄 = prasn TY → 𝔄].  VerusBelt instead carries a
  syntactic representation [~~𝔄] together with [vπ : ~~𝔄 → proph_asn → 𝔄].
  So [synty_ty] is the prophecy interpretation [𝔄], and [vπ] is the map
  from VerusBelt's representation into Nola's [clair]. *)

From nola.util Require Export proph.
From nola.alerus.prophecy Require Export syn_type.

(** [syn_type] as a syntactic pre-type.

  The inhabitance predicate is [inh_syn_type], which decides inhabitance of
  the prophecy interpretation; [inh_syn_type'] - inhabitance of the
  independent interpretation [~~𝔄] - is *not* what [synpty] wants. *)
Canonical syn_pty : synpty :=
  {| synpty_car := syn_type; synpty_inhab := λ 𝔄, inh_syn_type 𝔄; |}.

Notation aprvars := (aprvar syn_pty).

(** [syn_type] as a syntactic type *)
Program Canonical syn_ty : synty :=
  {| synty_pty := syn_pty; synty_ty := λ 𝔄 : syn_type, proph_interp_of_syn_type 𝔄; |}.
Next Obligation. by move=> ? /of_inh_syn_type. Qed.
Next Obligation. by move=> ? /to_inh_syn_type. Qed.

(** ** Bridging the two packagings of a prophecy variable

  VerusBelt's [proph_var] is [PrVar { pv_ty : syn_typei; pv_id : positive }]
  and Nola's is [Aprvar { aprvar_ty : syn_type; aprvar_var : prvar _ }] with
  [prvar 𝔄 = Prvar { prvar_inhab; prvar_id }].  The same data, associated
  differently, so the two are isomorphic. *)
Definition pv_to_aprvar (ξ : proph_var) : aprvars :=
  Aprvar (`ξ.(pv_ty)) (@Prvar syn_pty (`ξ.(pv_ty)) (proj2_sig ξ.(pv_ty)) ξ.(pv_id)).
Definition aprvar_to_pv (ξ : aprvars) : proph_var :=
  PrVar (ξ.(aprvar_ty) ↾ ξ.(aprvar_var).(prvar_inhab))
    ξ.(aprvar_var).(prvar_id).

Lemma pv_to_aprvar_to_pv ξ : aprvar_to_pv (pv_to_aprvar ξ) = ξ.
Proof. by case ξ=> [[??]?]. Qed.
Lemma aprvar_to_pv_to_aprvar ξ : pv_to_aprvar (aprvar_to_pv ξ) = ξ.
Proof. by case ξ=> ?[??]. Qed.

(** Hence the two notions of prophecy assignment agree *)
Definition prasn_to_proph_asn (π : prasn syn_ty) : proph_asn :=
  λ ξ, π (pv_to_aprvar ξ).
Definition proph_asn_to_prasn (π : proph_asn) : prasn syn_ty :=
  λ ξ, π (aprvar_to_pv ξ).

(** And VerusBelt's representation of a clairvoyant value maps into Nola's.
  This is the bridge the rest of the rewrite uses: a refinement value is
  Nola's [clair], and [vπ] composed with [prasn_to_proph_asn] turns
  VerusBelt's [~~𝔄] into one. *)
Definition clair_of {𝔄 : syn_type} (x : ~~𝔄) : clair syn_ty 𝔄 :=
  λ π, vπ x (prasn_to_proph_asn π).
