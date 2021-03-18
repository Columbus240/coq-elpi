From Coq Require Ltac Bool.
Declare ML Module "elpi_plugin".

(* We load once and forall these files in this .vo, to ease redistribution *)
Elpi Document Builtins.
Elpi Checker "etc/coq-elpi-checker.elpi".
Elpi Printer "elpi2html.elpi".
Elpi Template Command "elpi-command.elpi".
Elpi Template Tactic "elpi-tactic.elpi".

(* TO BE MOVED AWAY: For discriminate *)
Lemma bool_discr : true = false -> forall T : Type, T.
Proof.
exact (fun h T =>
  eq_rect true (fun x => match x with false => T | _ => True end) I false h).
Qed.

(* Special constant used for HOAS of match over unknown inductive type
   in terms like "let (a,b...) := t in ..." *)
Inductive unknown_inductive : Prop := unknown_constructor.
Register unknown_inductive as elpi.unknown_inductive.

Register bool_discr as elpi.bool_discr.
Register Coq.Init.Logic.eq as elpi.eq.
Register Coq.Init.Logic.eq_refl as elpi.erefl.
Register Coq.Bool.Bool.reflect as elpi.reflect.
Register Coq.Bool.Bool.ReflectF as elpi.ReflectF.
Register Coq.Bool.Bool.ReflectT as elpi.ReflectT.
Register Coq.Init.Logic.False as elpi.False.

Definition eq_axiom T eqb :=
  forall (x y : T), Bool.Bool.reflect (x = y) (eqb x y).

Definition eq_axiom_at T eqb (x : T) :=
  forall y, Bool.Bool.reflect (x = y) (eqb x y).

Definition eq_axiom_on T eqb (x y : T) :=
  Bool.Bool.reflect (x = y) (eqb x y).

Register eq_axiom as elpi.eq_axiom.
Register eq_axiom_at as elpi.eq_axiom_at.
Register eq_axiom_on as elpi.eq_axiom_on.

Register Coq.Init.Datatypes.bool as elpi.bool.
Register Coq.Init.Datatypes.andb as elpi.andb.
Register Coq.Init.Datatypes.true as elpi.true.
Register Coq.Init.Datatypes.false as elpi.false.

Lemma hole : True. Proof. exact I. Qed.
Register hole as elpi.hole.

Lemma eq_f (T1 : Type) (T2 : Type) (f : T1 -> T2) a b : a = b -> f a = f b.
Proof.
exact (fun h =>
  eq_rect a (fun x => f a = f x) (eq_refl (f a)) b h).
Defined.

Register eq_f as elpi.eq_f.

Definition contractible T := { x : T & forall y, @eq T x y }.

Register contractible as elpi.contractible.

Definition contracts T P (x : T) w u := (@existT (P x) (fun u : P x => forall v : P x,@eq (P x) u v) w u).

Register contracts as elpi.contracts.

Definition full T P := forall x : T, P x.

Register full as elpi.full.

Definition trivial T P := forall x : T, contractible (P x).

Register trivial as elpi.trivial.

Definition trivial_full T P (e : trivial T P) (x : T) : P x := projT1 (e x).

Register trivial_full as elpi.trivial_full.

Definition trivial_uniq T P (e : trivial T P) (x : T) (p : P x) :
  trivial_full T P e x = p := projT2 (e x) p.

Register trivial_uniq as elpi.trivial_uniq.
