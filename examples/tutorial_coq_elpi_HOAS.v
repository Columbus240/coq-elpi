From elpi Require Import elpi.
(**
   Elpi is an extension language that comes as a library
   to be embedded into host applications such as Coq.

   Elpi is a variant of λProlog enriched with constraints.
   λProlog is a programming language designed to make it easy
   to manipulate abstract syntax trees containing binders.
   Elpi extends λProlog with programming constructs that are
   designed to make it easy to manipulate abstract syntax trees
   containing metavariables (also called unification variables, or
   evars in the Coq jargon).

   This software, "coq-elpi", is a Coq plugin embedding Elpi and
   exposing to the extension language Coq spefic data types (e.g. terms)
   and API (e.g. to declare a new inductive type).

   In order to get proper syntax highlighting using VSCode please install the
   "gares.coq-elpi-lang" extension. In CoqIDE please chose "coq-elpi" in
   Edit -> Preferences -> Colors.
*)

(** ----------------------- ----------------------- -----------------------

   This tutorial focuses on the integration of Elpi within Coq, in particular
   it describes how Coq terms are exposed to Elpi programs and how Coq APIs can
   be called.

   This tutorial assumes the reader is familiar with Elpi and HOAS; if it is not
   the case, please take a look at this other tutorial first:
     https://github.com/LPCIC/coq-elpi/blob/master/examples/tutorial_elpi_lang.v

   Contents:
   - HOAS for Gallina
   - Quotations and Antiquotations
   - The context
   - Holes (implicit arguments)

*)

Elpi Command tutorial_HOAS. (* ignore this *)


(** ----------------------- HOAS for Gallina ----------------------------- *)

(**
     The full syntax of Coq terms can be found here

        https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi

     We defer to later quotations and antiquotations: syntactic features that
     let one write terms in Coq's native syntax. Here we focus on the abstract
     syntax tree.

     Let's start with the "gref" data type and the "global" term
     constructor.

     The "coq.locate" builtin resolves a name to a global rerence ("gref").

      type const constant -> gref.
      type indt inductive -> gref.
      type indc constructor -> gref.

     "constant", "inductive" and "constructor" are Coq specific data
     types that are opaque to Elpi. Still the "gref" data type lets you
     see what these names point to (a constant, and inductive type or a
     constructor).
*)

Elpi Query lp:{{

  coq.locate "nat" GRnat,   coq.say "nat is:" GRnat,
  coq.locate "S" GRs,       coq.say "S is:" GRs,
  coq.locate "plus" GRplus, coq.say "plus is:" GRplus.

}}.

(**
   The "coq.env.*" family of built-in predicates lets one access the
   environment of well typed Coq terms that have a global name.
   *)

Definition x := 2.

Elpi Query lp:{{

  coq.locate "x" GR,
  coq.env.typeof GR Ty, % all global references have a type
  coq.say "The type of x is:" Ty,

  GR = const C, % destruct GR to obtain its constant part C
  coq.env.const C (some Bo) TyC, % constans may have a body, do have a type
  coq.say "The body of x is:" Bo

}}.

(**
    Remark: "indt «nat»" is not a term (or better a type).
    The "global" term constructor turns a "gref" into an actual term.

    type global gref -> term.

    Remark: the "app" term constructor is taking a list of terms and building
    the application. "app [global (indc «S»), global (indc «O»)]" is
    the representation of 1.

    type app   list term -> term.

    Let's move to binders!
*)

Definition f := fun x : nat => x.

Elpi Query lp:{{

  coq.locate "f" (const C),
  coq.env.const C (some Bo) _,
  coq.say "The body of f is:" Bo

}}.

(**
   The "fun" constructor carries a pretty printing hint "`x`", the type
   of the bound variable "nat" and a function describing the body:

     type fun  name -> term -> (term -> term) -> term.

   Remark: name is just for pretty printing, in spite of carrying
   a value in the Coq world, it has no content in Elpi (like the unit type).
   Elpi terms of type name are just identifiers written between "`" (backticks).
   
   Remark: API such as coq.name-suffix lets one craft a family of names starting
   from one, eg "coq.name-suffix `H` 1 N" sets N to `H1`
*)

Elpi Query lp:{{
  
  fun `foo` T B = fun `bar` T B
  
}}.

(**
   The other binders "prod" (Coq's "forall", AKA "Π") and "let" are similar,
   so let's rather focus on "fix" here.
*)

Elpi Query lp:{{

  coq.locate "plus" (const C),
  coq.env.const C (some Bo) _,
  coq.say "The body of plus is:" Bo

}}.

Check match 3 as w in nat return bool with 0 => true | S _ => false end.

(**
   The "fix" constructor carries a pretty printing hint, the number of the
   recursive argument (starting at 0), the type and finally the body where the
   recursive call is represented via a bound variable

     type fix   name -> int -> term -> (term -> term) -> term.

   A "match" constructor carries the term being inspected, the return clause
   and a list of branches. Each branch is a Coq function expecting in input
   the arguments of the corresponding constructor. The order follows the
   order of the constructors in the inductive type declaration.

     type match term -> term -> list term -> term.

   The return clause is represented as a Coq function expecting in input
   the indexes of the inductive type, the inspected term and generating the
   type of the branches.
*)

Definition m (h : 0 = 1 ) P : P 0 -> P 1 :=
  match h as e in eq _ x return P 0 -> P x
  with eq_refl => fun (p : P 0) => p end.

Elpi Query lp:{{

    coq.locate "m" (const C),
    coq.env.const C (some (fun _ _ h\ fun _ _ p\ match _ (RT h p) _)) _,
    coq.say "The return type of m is:" RT

}}.


(**
   The last term constructor worth discussing is "sort".

   type sort  universe -> term.

   type prop universe.
   type typ univ -> universe.

   The opaque "univ" is a universe level variable. Elpi holds a store of
   constraints among these variables and provides built-in predicates
   named "coq.univ.*" to impose constraints.
*)

Elpi Query lp:{{

  coq.univ.sup U U1,
  coq.say U "<" U1,
  not(coq.univ.leq U1 U) % This constraint can't be allowed in the store!

}}.

(**
    Note that the user is not required to declare universe constraints by hand,
    since the type checking primitives update the store of constraints
    automatically and put Coq universe variables in place of Elpi's unification
    variables (U and V below).
*)

Elpi Query lp:{{

  ID = (fun `x` (sort (typ U)) x\ x),
  A = (sort (typ U)), % the same U as before
  B = (sort (typ V)),
  coq.say "(id b) is:" (app [ID, B]),
  coq.typecheck (app [ID, A]) T (error ErrMsg), % since U : U is not valid
  coq.say ErrMsg,
  coq.typecheck (app [ID, B]) T ok,        % since V : U is possible
  coq.say "(id b) is now:" (app [ID, B]) ":" T, % remark: U and V are now Coq's
  coq.univ.print                                % univ with constraints

}}.

(** --------------- Quotations and Antiquotations ------------------------- *)

(**
   Writing Gallina terms as we did so far is surely possible but very verbose
   and unhandy. Elpi provides a system of quotations and antiquotations to
   let one take advantage of the Coq parser to write terms.

   The antiquotation, from Coq to Elpi, is written lp:{{ .. }} and we have
   been using it since the beginning of the tutorial. The quotation from
   Elpi to Coq is written {{:coq .. }} or also just {{ .. }} since the ":coq" is
   the default quotation. (Coq has no default quotation, hence you always need
   to write "lp:" there).
*)

Elpi Query lp:{{

  coq.say {{:coq 1 + 2 }} "=" {{ 1 + 2 }}

}}.

(** Of course quotations can nest. *)

Elpi Query lp:{{

  coq.locate "S" S,
  coq.say {{ 1 + lp:{{ app[global S, {{ 0 }} ]  }}   }}
% elpi....  coq..     epi............  coq  elpi  coq
}}.

(**
   One rule governs bound variables:

     if a variable is bound in a language, Coq or Elpi,
     then the variable is only visible in that language (not in the other one).

   The following example is horrible but proves this point. In real code
   you are encouraged to pick appropriate names for your variables, avoiding
   gratuitous (visual) clashes.
*)

Elpi Query lp:{{

  coq.say (fun `x` {{nat}} x\ {{ fun x : nat => x + lp:{{ x }} }})
%                          e         c          c         e
}}.

(**
   A commodity quotation without parentheses let's one quote identifiers
   omitting the curly braces.
   That is "lp:{{ <ident> }}" can be written just "lp:<ident>".
*)


Elpi Query lp:{{

  coq.say (fun `x` {{nat}} x\ {{ fun x : nat => x + lp:x }})
%                          e         c          c      e
}}.

(**
   It is quite frequent to put Coq variables in the scope of an Elpi
   unification variable, and this can be done by sinmply writing
   "lp:(X a b)" which is a shorhand for "lp:{{ X {{ a }} {{ b }} }}".

   Note that writing "lp:X a b" (without parentheses) would result in a
   Coq application, not an Elpi one. *)

Elpi Query lp:{{

  X = (x\y\ {{ lp:y + lp:x }}),
  coq.say {{ fun a b : nat => lp:(X a b) }}

}}.

(**
    Another commodity quotation lets one access the "coqlib"
    feature introduced in Coq 8.10.

    Coqlib gives you an indirection between your code and the actual name
    of constants.

    Remark: the optional "@" to disable implicits. *)

Register Coq.Init.Datatypes.nat as my.N.
Register Coq.Init.Logic.eq as my.eq.

Elpi Query lp:{{

  coq.say {{ fun a b : lib:my.N => lib:@my.eq lib:my.N a b }}

}}.


(**
    The "{{:gref .. }}" quotation lets one the gref data type, instead of the
    term one. It supports "lib:" as well. *)

Elpi Query lp:{{
 
  coq.say {{:gref  nat  }},
  coq.say {{:gref  lib:my.N  }}.

}}.

(**
    The last thing to keep in mind when using quotations is that implicit
    arguments are inserted (according to the Arguments setting in Coq)
    but not synthesized automatically.
    
    It is the job of the type checker or elaborator to synthesize them.
    We shall see more on this in the section on Holes.
*)

Elpi Query lp:{{

  T = (fun `ax` {{nat}} a\ {{ fun b : nat => lp:a = b }}),
  coq.say "before:" T,
  % this is the standard Coq typechecker (but you may write your own ;-)
  coq.typecheck T _ ok,
  coq.say "after:" T.

}}.

(** ----------------------- HOAS for Gallina ----------------------------- *)


(**
    The context of Elpi (the hypothetical program made of clauses loaded
    via "=>") is taken into account by the Coq APIs. In particular every time
    a bound variable is crossed, the programmer must load in the context a
    clause attaching to that variable a type. There are a few facilities to
    do that, but let's first see what happens if one forgets it.
*)

Fail Elpi Query lp:{{

  T = {{ fun x : nat => x + 1 }},
  coq.typecheck T _ ok,
  T = fun _ _ Bo,
  pi x\
    coq.typecheck (Bo x) _ _.

}}. (* Error:

Bound variable c0 not found in the Coq context:
Mapping from DBL:
  

Named:
  
Rel:
  
Did you forget to load some hypotheses with => ?

*)

(** 
    This fatal error says that "x" in "(Bo x)" is unknown to Coq. It is
    a variable postulated in Elpi, but it's type, "nat", was lost. There
    is nothing wrong per se in using "pi x\" as we did if we don't call Coq
    APIs under it. But if we do, we have to record the type of "x" somewhere.

    In some sense Elpi's way of traversing a binder is similar to a Zipper.
    The context of Elpi must record the part of the Zipper context that is
    relevant for binders.

    The following two predicates are used for that purpose:

    pred decl i:term, o:name, o:term. % Var Name Ty
    pred def  i:term, o:name, o:term, o:term. % Var Name Ty Bo
       
    where "def" is used to cross "let-in"
*)

Elpi Query lp:{{

  T = {{ fun x : nat => x + 1 }},
  coq.typecheck T _ ok,
  T = fun N Ty Bo,
  pi x\
    decl x N Ty =>
      coq.typecheck (Bo x) _ ok.

}}.

(**
     In order to ease this task, Coq-Elpi provides a few commodity macros in:

       https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi

     For example:

       macro @pi-decl N T F :- pi x\ decl x N T => F x.
*)

Elpi Query lp:{{

  T = {{ fun x : nat => x + 1 }},
  coq.typecheck T _ ok,
  T = fun N Ty Bo,
  @pi-decl N Ty x\
      coq.typecheck (Bo x) _ ok.

}}.

(** -------------------- Holes (implicit arguments) ----------------------- *)
