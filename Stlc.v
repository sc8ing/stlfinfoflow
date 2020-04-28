
(** * Abstract *)

(** Safely securing data is always a priority for systems that work
with sensitive information. There are numerous ways to protect the
integrity of data and manage the permissions as to how it can be
accessed, but most rely on the programmer to correctly implement
- a task which can become exceedingly difficult to ensure is met
satisfactorily as a project grows. Information flow analysis provides
a means to formally guarantee that certain constraints are met. By
using a type-based approach, these assertions can be embedded in
a programming language's type system directly, thus removing the need
for external analysis and providing compile-time checking. The
various techniques for proving these assertions are sound and well
documented. The goal of this thesis is to formally verify the
integrity of one of these proofs using the proof management system
Coq.  *)


(** * Background *)

(** ** Information Flow *)

(** When a program is executed, bits of data are stored in various
regions of the computer's memory. Some of this information may be of
greater importance, such as in a voting system where it must be
ensured that the development of publicly-available aggregate data of
candidate totals cannot be used to recover information about who
voted. (TODO better example?). In such cases it's not only critical
to ensure that the program does not accidentally leak sensitive
information to low-security areas, but also that implicit information
regarding the structure or content of sensitive data remains solely
in high-security areas as well.

For example, a simple imperative program with high-security data in
some variable [x] and low-security data in [y] of the following form
may not explicitly copy sensitive data to a low-security area, but it
does reveal information about the contents of this data, which an
attacker may or may not eventually accumulate enough of in
a real-world scenario to deduce significant details about the
contents of [x].
  
<<
  x := getSecretNumber()
  y := 2
  if x > 5
    y := y - 1
  else
    y := y + 1
>>
*)

(** Various conceptions and degrees of information flow have been
explored in the literature. For the purposes of this paper, all
expressions in a language can be assigned a security level of either
[High] or [Low]. The assertion that the flow of information in
a program is secure can then be stated as follows: for any two sets
of high-security inputs [H1], [H2] and low-security input [L], the
low-security result of executing a program with [H1] and [L] as its
initial states is identical to executing it with [H2] and [L] as its
initial states. This proposition is referred to as
non-interference. TODO: how to state this property for the way this
language is set up? *)


(** ** The Proof Assistant Coq *)

(** Coq is an interactive theorem prover used to assist in formal
proofs in a logical framework. It includes both a custom programming
language Gallina with advanced implementations of type theory as well
as a language for constructing machine-checked proofs. Coq is often
used to prove properties of programs and languages, but is also used
for intricate mathematical proofs and other related domains.

Part of what makes a system like Coq so powerful is the guarantees it
can provide for correctness. Not only does the specification of the
language itself have the weak normalization property (meaning
programs cannot diverge), but it also allows for complicated
arguments to be constructed with many parts. As such, it lends itself
naturally to areas of computer science where extreme rigor is
necessary, such as encryption or compiler verification. Areas related
to the effectiveness of security techniques, such as information
flow, are also strong candidates for machine-checked proofs in order
to increase confidence in the program.

The reader should keep in mind that, while the proofs given in this
paper are written out in a conventional style, every step given is
backed by the formal guarantees of the Coq theorem assistant in
a machine-checked proof, which is ultimately what this paper is about
and not merely the results of the proofs themselves, which were
already believed to probably be true. *)
 

(** ** About the Proof *)

(** The formal proof for type-based information flow presented here
is largely based off the work of François Pottier and his
presentation at The National Institute for Research in Computer
Science and Automation (INRIA). Some modifications have been made for
practical reasons – such as the decision not to use evaluation
contexts and the inclusion of different types in the language – but
these are unimportant to the overall goal and the essence of the
conclusion is the same. *)


(** * The Language *)

(** We begin by specifying a simple programming language about which
to construct the proof. For the purposes of clarity, it is rather
bare bones. More involved languages for practical use in the real
world would nevertheless follow the same fundamental structure,
simply with more nuances. The critical detail of whatever language is
used is that it must be typed. (TODO: is this true?). *)

(* begin hide *)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From STLCIF Require Import Maps.
From STLCIF Require Import Smallstep.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.

Module STLC.
(* end hide *)

(** ** Syntax *)

(** The language contains only booleans as a primitive data type,
along with single-argument functions. Expressions are vaguely similar
to simply-typed lambda calculus, with two notable additions: [hole]
and [marked]. The latter is the purely-syntactical way for
a programmer to mark an expression as belonging to one of two
security classes, either [High] or [Low]. Types, security classes,
and expressions are defined straightforwardly in Coq as the inductive
data structures shown below. *)

  Inductive data_type : Type :=
    | Bool  : data_type
    | Arrow : data_type -> data_type -> data_type.

(* begin hide *)
  Definition data_type_eq_dec :
    forall (x y : data_type), { x = y } + { x <> y }.
  Proof. decide equality. Defined.
(* end hide *)

  Inductive sec_class : Type :=
    | High : sec_class
    | Low : sec_class.

(* begin hide *)
  Definition sec_class_eq_dec :
    forall (x y : sec_class), { x = y } + { x <> y }.
  Proof. decide equality. Defined.
(* end hide *)

  Inductive exp : Type :=
    | var : string -> exp
    | app : exp -> exp -> exp
    | abs : string -> data_type -> exp -> exp
    | tru : exp
    | fls : exp
    | test : exp -> exp -> exp -> exp
    | marked : sec_class -> exp -> exp
    | hole.

(* begin hide *)
  Open Scope string_scope.
  Definition x := "x".
  Definition y := "y".
  Definition z := "z".
  Hint Unfold x.
  Hint Unfold y.
  Hint Unfold z.
(* end hide *)

(** ** Semantics *)

(** *** Values *)

(** In order to differentiate between a program that "gets stuck" and
one that has terminated successfully, a [value] proposition is
introduced. Values are expressions that are well-typed but cannot
take a step. *)

  Inductive value : exp -> Prop :=
    | v_abs :
        forall x T t,
        value (abs x T t)
    | v_tru :
        value tru
    | v_fls :
        value fls
    | v_markedval :
        forall class val,
        value val -> value (marked class val).

(* begin hide *) 
  Hint Constructors value.
(* end hide *)

(** *** Substitutions *)

(** Syntax for substitution semantics is introduced in the form [[v
// x] e is e'] where [v], [e] and [e'] are expressions and [x] is
a variable that may or may not exist in [e]. The statement can be
read as "the result of substituting [v] for [x] in [e] yields
[e']". The formal rules are detailed below. *)

  Reserved Notation "'[' v '//' x ']' e 'is' r" (at level 40).
  Inductive substi (x : string) (s : exp) : exp -> exp -> Prop :=
    | s_var_eq :
        substi x s (var x) s
    | s_var_neq :
        forall y,
        y <> x ->
        substi x s (var y) (var y)
    | s_abs_eq :
        forall t1 T, substi x s (abs x T t1) (abs x T t1)
    | s_abs_neq :
        forall t1 t1' T,
        x <> y ->
        substi x s t1 t1' ->
        substi x s (abs y T t1) (abs y T t1')
    | s_app :
        forall t1 t1' t2 t2',
        substi x s t1 t1' ->
        substi x s t2 t2' ->
        substi x s (app t1 t2) (app t1' t2')
    | s_tru :
        substi x s tru tru
    | s_fls :
        substi x s fls fls
    | s_test :
        forall t1 t1' t2 t2' t3 t3',
        substi x s t1 t1' ->
        substi x s t2 t2' ->
        substi x s t3 t3' ->
        substi x s (test t1 t2 t3) (test t1' t2' t3')
    | s_marked :
        forall class e e',
        substi x s e e' ->
        substi x s (marked class e) (marked class e')
    | s_hole :
        substi x s hole hole
      where "'[' v '//' x ']' e 'is' r" := (substi x v e r)
  .

  (* begin hide *)
  Hint Constructors substi.
  (* end hide *)

(* *** Smallstep *)

(** The reduction of expressions in the language is given in
small-step semantics. All well-typed expressions can either take
a step or are values. The notation [e --> e'] is introduced to mean
that the expression [e] steps to [e'] in exactly one step. [e -->*
e'] is then used to denote a multi-step relation between [e] and [e']
or zero or more steps. The stepping rules are as follows: *)

  Reserved Notation "t1 '-->' t2" (at level 40).
  Inductive step : exp -> exp -> Prop :=
    | ST_AppAbs :
        forall x T t12 v2 subres,
        [v2//x] t12 is subres ->
        (app (abs x T t12) v2) --> subres

    | ST_App1 :
        forall t1 t1' t2,
        t1 --> t1' ->
        app t1 t2 --> app t1' t2

    | ST_TestTru :
        forall t1 t2,
        (test tru t1 t2) --> t1

    | ST_TestFls :
        forall t1 t2,
        (test fls t1 t2) --> t2

    | ST_Test :
        forall t1 t1' t2 t3,
        t1 --> t1' ->
        (test t1 t2 t3) --> (test t1' t2 t3)

    | ST_LiftApp :
        forall class func e,
        (app (marked class func) e) --> (marked class (app func e))

    | ST_LiftTestCond :
        forall class cond b1 b2,
        (test (marked class cond) b1 b2) --> (marked class (test cond b1 b2))

    | ST_MarkReduce :
        forall class body body',
        body --> body' ->
        (marked class body) --> (marked class body')

    where "t1 '-->' t2" := (step t1 t2).

(* begin hide *)
  Hint Constructors step.

  Notation multistep := (multi step).
  Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


  Definition context := partial_map data_type.

  Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
(* end hide *)

(** ** Typing *)

(** The following relation is defined to type an expression and
guarantee type safety. Any expression not satisfying the requirements
of one of the constructors is ill-typed and therefore
illegal. Constraining the amount of types in the language keeps this
specification relatively short. Following convention as closely as
possible within the limitations of Coq's syntactical restraints, the
notation [Gamma |- e \in T] is used to signify that expression [e] is
        has type [T] under a typing context [Gamma]. *)

  Inductive has_dtype : context -> exp -> data_type -> Prop :=
    | T_Var : forall Gamma x T,
        Gamma x = Some T ->
        Gamma |- var x \in T

    | T_Abs : forall Gamma x T11 T12 t12,
        (x |-> T11 ; Gamma) |- t12 \in T12 ->
        Gamma |- abs x T11 t12 \in Arrow T11 T12

    | T_App : forall T11 T12 Gamma t1 t2,
        Gamma |- t1 \in Arrow T11 T12 ->
        Gamma |- t2 \in T11 ->
        Gamma |- app t1 t2 \in T12

    | T_Tru : forall Gamma,
        Gamma |- tru \in Bool
    | T_Fls : forall Gamma,
        Gamma |- fls \in Bool

    | T_Test : forall t1 t2 t3 T Gamma,
        Gamma |- t1 \in Bool ->
        Gamma |- t2 \in T ->
        Gamma |- t3 \in T ->
        Gamma |- test t1 t2 t3 \in T

    | T_Marked : forall Gamma class e T,
        Gamma |- e \in T ->
        Gamma |- marked class e \in T
    where "Gamma '|-' t '\in' T" := (has_dtype Gamma t T).

(* begin hide *)
  Hint Constructors has_dtype.

  Reserved Notation "a << b" (at level 40).
(* end hide *)

(** * The Proofs *)

(** The given definitions of the language used here's syntax, typing
rules, and small-step execution semantics is sufficient to prove the
soundness of its information flow typing with marked
expressions. A variety of propositions and lemmas used to construct
the proof are first introduced, along with two larger theorems that,
together, form the majority of the proof for non-interference, which
is the ultimate goal. *)

(** ** Lemmas and Definitions For Monotonicity *)

(** *** Hole Definitions and the Holier Relation ([<<]) *)

(** Holes are of expressions that, in essence, do not exist or
have been removed for some reason. In the context of this paper,
holes are introduced into expressions when they are stripped of all
data consisting of a given security class (what's been termed
"pruning" and is detailed further on). The notion of an incomplete or
holey" expression and the relationship between expressions with
    different numbers of holes provide a means of redaction of terms
    that would otherwise violate the safety information flow typing
    seeks to provide.

An expression [e] is holier than an expression [e'] (written [e <<
e']) if the ASTs of each expression are congruent (i.e. both are
variables, abstractions, or some other possible expression) and all
sub-expressions of [e] are holier than the corresponding ones of
[e']. The requirement for expressions to have congruent ASTs is
removed for holes – a hole is by definition holier than any other
expression. Note that the [<<] relation is reflexive as well.

Also given is the proposition [noholes] (not shown here). As would be
expected, an expression [e] satisfies [noholes] if it is not a hole
and none of its sub-expressions are holes. *)

  Inductive holier : exp -> exp -> Prop :=
    | H_refl :
        forall e,
        e << e

    | H_hole :
        forall e,
        hole << e

    | H_app :
        forall func arg func' arg',
        func << func' ->
        arg << arg' ->
        (app func arg) << (app func' arg')

    | H_abs :
        forall x T body body',
        body << body' ->
        (abs x T body) << (abs x T body')

    | H_test :
        forall cond b1 b2 cond' b1' b2',
        cond << cond' ->
        b1 << b1' ->
        b2 << b2' ->
        (test cond b1 b2) << (test cond' b1' b2')

    | H_marked :
        forall class body body',
        body << body' ->
        (marked class body) << (marked class body')

    where "a << b" := (holier a b).

(* begin hide *)
  Hint Constructors holier.

  Inductive noholes : exp -> Prop :=
    | NH_var : forall s,
        noholes (var s)

    | NH_app : forall func arg,
        noholes func -> noholes arg ->
        noholes (app func arg)

    | NH_abs : forall x T func,
        noholes func ->
        noholes (abs x T func)

    | NH_tru : noholes tru
    | NH_fls : noholes fls

    | NH_test : forall cond b1 b2,
        noholes cond -> noholes b1 -> noholes b2 ->
        noholes (test cond b1 b2)

    | NH_marked : forall class body,
        noholes body ->
        noholes (marked class body).
(* end hide *)

(** *** holyval_meansval *)

  Lemma holyval_meansval : forall v1 v2,
    value v1 ->
    v1 << v2 ->
    value v2.
  Proof.
    intros. generalize dependent v2.
    induction H; intros; inversion H0; try constructor.
    - assumption.
    - subst. apply IHvalue. assumption.
  Qed.

(** Since the [<<] relation requires the congruence of both
arguments' ASTs, any proposition of the form [v << v'] where [v] is
a value entails that [v'] is also a value. The proof proceeds by
induction on the [value] proposition. Most cases follow directly from
constructors for the [holier] relation. The inductive hypothesis is
used for expressions of the form [marked class body] to show that the
bodies of both marks must be the same. *)

(** *** holier_abs_inv *)

  Lemma holier_abs_inv : forall x T body e',
    (abs x T body) << e' ->
    exists body', body << body' /\ e' = (abs x T body').
  Proof.
    intros. inversion H; subst.
    - induction body; eexists; eauto.
    - exists body'. auto.
  Qed.

(** For any abstraction [abs x T body] holier than an another
expression [e'], there must exist some [body'] such that [body <<
body'] and [abs x T body << abs x' T' body']. This lemma and its
proof may seem rather trivial. Most of the merit behind it comes from
the simplification it provides later on in the proof of
monotonicity.

As a side note, this proof is a rather good example of the degree to
which tactics can automate the more tedious aspects of proofs. For
a more complex language with a wide variety of expressions, doing
induction on an expression would be exceedingly tedious to check
manually since the number of cases corresponds to the number of forms
for expressions. In the machine proof, <<"; eauto">> is used and
amounts to saying "most of the cases follow directly from the
assumption", thus removing the need to explicitly iterate through
them. *)

(** *** subst_noholes *)

  Lemma subst_noholes : forall x body arg result,
    [ arg // x ] body is result ->
    noholes result ->
    noholes body.
  Proof.
    intros. induction H; try constructor; auto.
    - inversion H0; subst. auto.
    - inversion H0; subst.
      apply IHsubsti in H3. auto.
    - inversion H0; subst.
      apply IHsubsti1 in H4. auto.
    - inversion H0; subst.
      apply IHsubsti2 in H5. auto.
    - inversion H0; subst.
      apply IHsubsti1 in H6. auto.
    - inversion H0; subst.
      apply IHsubsti2 in H7. auto.
    - inversion H0; subst.
      apply IHsubsti3 in H8. auto.
    - inversion H0; subst.
      apply IHsubsti in H2. auto.
  Qed.

(** If the result of a substitution has no holes, then the expression
into which the substitution was done ([body]) must not have had any
holes to begin with. Note that it's not necessarily true that the
term substituted in ([arg]) has no holes, since the substitution
relation as defined does not require the substitution variable ([x])
to exists in [body] - in other words, a hole could be "subbed in" but
never used.

The proof proceeds by induction on the substitution relation. The
majority of cases proceed by using the [noholes] assumption to derive
that sub-expressions in the result must also not have holes and
therefore the inductive hypothesis applies. More detail is given in
the proof for [noholes_app_arg_orunused] to avoid redundancy since
they proofs are quite similar. *)

(** *** noholes_app_arg_orunused *)

  Lemma noholes_app_arg_orunused : forall x body arg f,
  noholes f ->
  [arg // x] body is f ->
  noholes arg \/ forall xsub, [xsub // x] body is f.
  Proof.
    intros. induction H0.
    - left. assumption.
    - right. intros. econstructor. auto.
    - right. intros. constructor.
    - inversion H; subst.
      specialize H3 as H3'. apply IHsubsti in H3.
      destruct H3 as [argnoholes | argunused].
      * left. assumption.
      * right. intros. constructor.
        eauto. eauto.
    - inversion H; subst.
      specialize H2 as H2'.
      specialize H3 as H3'.
      apply IHsubsti1 in H2.
      apply IHsubsti2 in H3.
      destruct H2 as [nh1 | unused1].
      + left. assumption.
      + destruct H3 as [nh2 | unused2].
        * left. assumption.
        * right. intros. constructor.
          auto. auto.
    - right. constructor.
    - right. constructor.
    - inversion H; subst.
      specialize H3 as H3'.
      specialize H4 as H4'.
      specialize H5 as H5'.
      apply IHsubsti1 in H3.
      apply IHsubsti2 in H4.
      apply IHsubsti3 in H5.
      destruct H3 as [nht1 | t1unused]. auto.
      destruct H4 as [nht2 | t2unused]. auto.
      destruct H5 as [nht3 | t3unused]. auto.
      auto.
    - inversion H; subst.
      specialize H2 as H2'.
      apply IHsubsti in H2.
      destruct H2 as [nh | unused]; auto.
    - inversion H.
  Qed.

(** As mentioned in the above clarification for [subst_noholes],
similar judgments can be made about the substituted value in
a substitution if the result has no holes. The only difference is the
additional possibility of this value being unused in the body of the
substitution, which makes this lemma slightly weaker as
a consequence. The proof proceeds similarly by induction over the
substitution. *)

(** Consider the case where a substitution is made into an expression
like [app body arg] to yield one like [app body' arg']. Since the
latter has no holes, neither do [body'] or [arg']. This allows for
the inductive hypotheses to give that either [arg] has no holes or
[body = body']. If [arg] has no holes, we're done.

Now use the induction hypothesis to get from [noholes arg'] that
either (redundantly) [noholes arg] or [arg = arg']. The first case is
the same. We're still in the case where [body = body'], though, so
showing that [app body arg = app body' arg'] is already done.

The rest of the cases are similar. *)

(** *** noholes_holier_means_eq *)

  Lemma noholes_holier_means_eq : forall e e',
    noholes e ->
    e << e' ->
    e = e'.
  Proof.
    intros. generalize dependent e'. induction H; intros; subst.
    - inversion H0. auto.
    - inversion H1; subst; auto.
      apply IHnoholes1 in H4.
      apply IHnoholes2 in H6.
      subst. auto.
    - inversion H0; subst; auto.
      apply IHnoholes in H5; subst; auto.
    - inversion H0; subst; auto.
    - inversion H0; subst; auto.
    - inversion H2; subst; auto.
      apply IHnoholes1 in H6.
      apply IHnoholes2 in H8.
      apply IHnoholes3 in H9.
      subst. auto.
    - inversion H0; subst; auto.
      apply IHnoholes in H4; subst; auto.
  Qed.

(** The way relativity is defined for the holier relation means that
any expression without holes [e] that's holier than another
expression [e'] must be equivalent to [e']. The proof proceeds by
induction on the assertion that [e] has no holes. The congruence of
the [<<] relation then gives the equivalence of [e] to [e'] for
expressions that are values. The inductive hypothesis serves to show
equivalence for expressions with sub-expressions. *)

(** As an example, the [e = test cond b1 b2] case is given. From the
assumption that [test cond b1 b2 << e'], we know [e'] is of the form
[test cond' b1' b2'], [cond << cond'], [b1 << b1'], and [b2 <<
b2']. By the inductive hypotheses, all of these sub-expressions must
therefore be equivalent. Consequently, the [test] expressions are
equivalent. The rest of the cases proceed similarly. *)
  
(** *** bodystepsappsteps *)

  Lemma bodystepsappsteps : forall body arg body',
    body -->* body' ->
    (app body arg) -->* (app body' arg).
  Proof.
    intros. induction H; subst.
    - constructor.
    - apply multi_step with (app y0 arg); auto.
  Qed.

(** According to the smallstep rules for this language, several
expressions with sub-expressions step their sub-expressions until they
become values. While the expression as a whole has not completely
changed shape, it has nevertheless made a step. The following few
lemmas cover the cases for applications, conditionals ([test]s), and
marked expressions. In a richer language, evaluation contexts could
be used to avoid an explosion of similar lemmas for each possible
expression with sub-expressions. *)

(** Bodies of applications (essentially function bodies) are reduced
as much as possible before the substitution of the argument is
made. Hence, if the body can take a step, the entire term can take
a step. The proof is straightforward induction on the stepping
relation between the body of the application and the expression is
steps to. Conditionals in [test] expressions and bodies of [marked] ones follow a nearly identical pattern. *)

(** *** condstepsteststeps *)

  Lemma condstepsteststeps : forall cond cond' b1 b2,
    cond -->* cond' ->
    (test cond b1 b2) -->* (test cond' b1 b2).
  Proof.
    intros. induction H; subst.
    - constructor.
    - apply multi_step with (test y0 b1 b2); auto.
  Qed.

(** *** markedbodstepstermsteps *)

  Lemma markedbodstepstermsteps : forall class body body',
    body -->* body' ->
    (marked class body) -->* (marked class body').
  Proof.
    intros. induction H; subst.
    - constructor.
    - apply multi_step with (marked class y0); auto.
  Qed.
  
(** ** Monotonicity *)

(** The above set of lemmas are sufficient to prove
monotonicity, which is the property that any time an expression [e]
that's holier than an expression [e'] steps to an expression [f]
containing no holes, [e'] must also eventually step to [f]. *)

(** *** Single-step Version *)

  Lemma monotonicity_single_step : forall e e' f,
    noholes f ->
    e << e' ->
    e --> f ->
    e' -->* f.
  Proof.
    intros. generalize dependent f. induction H0; intros.
    - apply multi_R. assumption.
    - inversion H1; subst.
    - inversion H1; subst.
      + apply holier_abs_inv in H0_.
        destruct H0_ as [body' [bodyprop funcprop]].
        subst. specialize H0_0 as H'.
        eapply multi_R.
        specialize H4 as H4'.
        apply noholes_app_arg_orunused in H4; eauto.
        destruct H4 as [nh | unused].
        * apply noholes_holier_means_eq in H'.
          subst.
          apply subst_noholes in H4'; eauto.
          apply noholes_holier_means_eq in bodyprop; eauto.
          subst. eauto. assumption.
        * apply subst_noholes in H4'; eauto.
          apply noholes_holier_means_eq in bodyprop; eauto.
          subst.
          constructor; eauto.
      + inversion H; subst.
        apply noholes_holier_means_eq in H0_0; eauto.
        subst.
        eapply bodystepsappsteps.
        apply IHholier1; eauto.
      + apply noholes_holier_means_eq in H0_; subst; eauto.
        inversion H; subst. inversion H2; subst.
        apply noholes_holier_means_eq in H0_0; subst; eauto.
        apply multi_R. eauto.
        inversion H; subst. inversion H2; subst.
        constructor. auto.
    - inversion H1.
    - inversion H1; subst.
      + apply noholes_holier_means_eq in H0_; subst; eauto.
        apply noholes_holier_means_eq in H0_0; subst; eauto.
        apply multi_R.
        constructor.
        constructor.
      + apply noholes_holier_means_eq in H0_; subst; eauto.
        apply noholes_holier_means_eq in H0_1; subst; eauto.
        apply multi_R.
        constructor.
        constructor.
      + inversion H; subst.
        apply noholes_holier_means_eq in H0_0; subst; auto.
        apply noholes_holier_means_eq in H0_1; subst; auto.
        apply IHholier1 in H5; auto.
        apply condstepsteststeps. auto.
      + inversion H; subst.
        apply noholes_holier_means_eq in H0_; subst; auto.
        apply noholes_holier_means_eq in H0_0; subst; auto.
        apply noholes_holier_means_eq in H0_1; subst; auto.
        apply multi_R. apply ST_LiftTestCond.
        inversion H2; subst; auto.
        inversion H2; subst; auto.
        constructor. inversion H2; subst; auto.
    - inversion H1; subst.
      inversion H; subst.
      apply IHholier in H3; auto.
      apply markedbodstepstermsteps. assumption.
  Qed.

(** The proof begins with induction on the holier relation [e <<
e']. Some of the cases are rather straightforward. *)

(**

- The reflexive case of [e << e'] is immediate; the expressions are
  equivalent and obviously step to the same thing.

- In the event that [e << e'] because [e] is a hole, an implicit
  contradiction is assumed in the premises since holes don't step to
  any expression under the [step] relation. The conclusion is
  therefore vacuously true.

- Abstractions are similar; since they're values, there's also
  nothing for them to step to.

- Marked expressions are only slightly more complex. Given the
  stepping relation and the assumption that [marked class body -->
  f], a few facts can be derived. First, it must be the case that
  [body] steps to some other expression [body']. [f] must also be
  a marked expression, so it is of the form [marked classf
  bodyf]. Since the stepping relation gives no way for a security
  class to be altered from the stepping of a sub-expression, we can
  further derive that [class = classf].

  Showing that [e' -->* f] can now be rewritten as showing [marked
  class body' -->* marked class bodyf']. Since [bodyf] can't have
  holes, there's enough information to apply the inductive hypothesis
  and get that [body' -->* bodyf]. The simple lemma
  [markedbodstepstermsteps] then completes this section of the
  proof. *)

(** The proofs for cases where [e] and [e'] are [test] or [app]
expressions are more involved, since the multiple step rules for
these kinds of expressions give more possibilities as to how [e -->
f]. While the proof may be rather long, most of the cases proceed
fairly similarly to proof of the marked expression component. The
more interesting case of applications stepping to the substitution
result will be given in more detail, while the rest of the proofs are
omitted for brevity. The application case proceeds by considering the
possible ways that [e], of the form [app bodye arge], can step to
[f].

  - Let us first examine the case where the body of the application
    [e = app bodye arge] takes a step. Under this scenario, [f] must
    be of the form [app bodyf argf] and, since only the body of [e]
    took a step and not the argument, [argf = arge]. Since [e = app
    bodye arge << app bodye' arge' = e'], it's necessary from the
    definition of [holier] that [bodye << bodye'] and [arge <<
    arge']. [noholes f] implies [noholes argf] and therefore [noholes
    arge] by equivalence. [noholes_holier_means_eq] then yields [arge
    = arge'].

    At this stage we are left to show that [app bodye' arge' -->* app
    bodyf arge']. We use [bodystepsappsteps] to reduce this to
    showing that [bodye' -->* bodyf], which is given by the first
    inductive hypothesis ([forall x, noholes x -> bodye --> x ->
    bodye' --> x]).

  - Now assume the step from [e] to [f] was done by lifting the
    security class marking the application body up to the top
    level. Then [f] is of the form [marked class (app bodyf argf)],
    [bodyf = bodye], and [argf = arge]. Similar to the proof section
    immediately above, it can be derived from [noholes f], these
    equivalences, and the [e << e'] assumption that [argf = arge']
    and [bodyf = bodye']. [app (marked class bodye') arge' -->*
    marked class (app bodye' arge')] then becomes an instance of the
    [step] lifting rule for applications.

  - The final case to be considered for the event that [e] is an
    application is if [f] is the result of [e] stepping by
    substitution of its argument.  Since the [step] relation
    implements call-by-name semantics, it's possible that neither the
    body of the application nor its argument are fully reduced - they
    can be any expression at all, and therefore so can the result of
    the substitution, [f]. By [holier_abs_inv] and the [e << e']
    assumption, we know that [bodye << bodye'] and [e'] is an
    abstraction of the form [abs x T bodye'].

    Since the result of the substitution, [f], has no holes, either
    [arge] has no holes, or [bodye] doesn't use the variable to
    substitute in for. This argument is captured in the
    [noholes_app_arg_orunused] lemma from earlier. 

    - First, the case of [noholes arge]. [noholes_holier_means_eq]
      immediately gives [arge = arge']. We can also derive [noholes
      bodye] by [subst_noholes]. Another use of
      [noholes_holier_means_eq] and the assumption that [bodye <<
      bodye'] finishes this case.

    - Now the case where the argument to the substitution is
      unused. We proceed similarly with applications of
      [subst_noholes] and [noholes_holier_means_eq] to get that
      [bodye] must not have holes and is equal to [bodye']. Under the
      current set of assumptions, [e'] can only step to [f] via the
      substitution rule. Since any substitution into [bodye'] is
      going unused, [arge'] is irrelevant and [bodye = bodye'
      = f]. This case reduces to showing that the step from [e'] to
      [f] amounts to a discarding of the application's argument and
      retaining of the body. 
*)

(** *** Full Version *)

  Lemma monotonicity : forall e e' f,
    noholes f ->
    e << e' ->
    e -->* f ->
    e' -->* f.
  Proof.
    intros. generalize dependent e'.
    induction H1.
    - intros. apply noholes_holier_means_eq in H0; subst; auto.
      apply multi_refl.
    - intros. eapply monotonicity_single_step in H0.
      + apply IHmulti; auto.
  Admitted.

(** It should be mentioned at this point that a mistake was
discovered in the approach to proving this theorem late along the
process. An unfortunate problem arises when trying to use the
[monotonicity_single_step] proven above to prove the full
[monotonicity] lemma below: as it turns out, the assertion is simply
too weak. When induction is done on the multi-step relation from [e]
to [f], it becomes necessary to prove that there exists a middle
expression [m] such that [e --> m] and [m -->* f]. However, there is
no guarantee that this middle expression satisfies the [noholes]
proposition and therefore the [monotonicity_single_step] lemma no
longer applies. *)

(** One approach that was considered for remedying this problem is
to reverse the induction principle. Concretely speaking, we could
take the same approach as outlined above with the middle expression
[m], but instead formulate logically equivalent goals of the form [e
-->* m] and [m --> f]. This would solve the problem of ensuring that
[m] steps to something satisfying [noholes], but ends up losing other
information necessary to complete the proof, namely that the
expression [m] that [e] steps to is still holier than the expression
[m'] that [e'] steps to, since [monotonicity_single_step] requires in
its premises that [e << f]. The correct way to fix these issues
involves restating [monotonicity_single_step] to remove the
requirement that both [e] and [e'] step to the same
expression. Additionally, it shouldn't yet be required that [f] not
have holes. Such a lemma looks like this: *)

(* begin hide *)
  Lemma multi_ind_rev :
    forall (X : Type) (R : relation X) (P : X -> X -> Prop),
    (forall x : X, P x x) ->
    (forall x y z : X, R y z -> multi R x y -> P x y -> P x z) ->
    forall y y0 : X, multi R y y0 -> P y y0.
  Proof.
  Admitted.

  Lemma monotonicity_rev_ind : forall e e' f,
    noholes f ->
    e << e' ->
    e -->* f ->
    e' -->* f.
  Proof.
    intros. generalize dependent e'.
    induction H1.
    - intros. apply noholes_holier_means_eq in H0; subst; auto.
      apply multi_refl.
    - intros. eapply monotonicity_single_step in H0.
      + apply IHmulti; auto.
  Admitted.
(* end hide *)
  
  Lemma monotonicity_single_step' : forall e e' f,
    e << e' ->
    e --> f ->
    exists f', e' -->* f' /\ f << f'.
  Proof.
  Admitted.

(** The conclusion is now slightly weaker, but contains the still
useful addition that [f << f'] and compensates by relaxing the
antecedents. A second intermediary lemma is then used to simplify the
proof of the final [monotonicity] theorem where an [f'] term is
introduced corresponding to its role in the above lemma. *)
  
  Lemma monotonicity' : forall e e' f,
    e << e' ->
    e -->* f ->
    exists f', e' -->* f' /\ f << f'.
  Proof.
  Admitted.

(** [monotonicity] now follows from the above two lemmas with the
requirement of [f] not having holes reinstated. Since [monotonicity']
gives as a result that [f << f'], the only way this could be possible
is if [f = f'] by [noholes_holier_means_eq], which is equivalent to
the original statement of [monotonicity]. *)
  
(** Unfortunately, the problems related to the weakness of
[monotonicity_single_step] as originally stated were encountered too
late in the semester to allow for time to reconstruct the corrected
proofs in Coq, so this section is missing a corresponding machine-checked proof, which is disappointing. *)

(** ** Lemmas and Definitions for Stability *)

(** The second (and last) component leading to non-interference is
what's referred to as stability. First, some terminology is
introduced and several stepping-stone lemmas are proven. *)

(** *** Pruning *)

(** The notation [\\ e //_ labs] is used to symbolize the result of
_pruning_ a list of labels (security classes) from an expression
[e]. To prune an expression of a labeled security class [lab] is to
replace all marked expressions [marked class body] where [class
= lab] with holes. The replacement descends into sub-expressions
recursively. *)

  Fixpoint prune_single (l : sec_class) (e : exp) : exp :=
    match e with
    | app func arg =>
        let func' := prune_single l func in
        let arg' := prune_single l arg in
        app func' arg'

    | abs x T body => abs x T (prune_single l body)

    | test cond b1 b2 =>
        let cond' := prune_single l cond in
        let b1' := prune_single l b1 in
        let b2' := prune_single l b2 in
        test cond' b1' b2'

    | (marked lab body) as e =>
        if sec_class_eq_dec lab l then hole else (marked lab (prune_single l body))

    | other => other
    end.

  Definition prune (allowed : list sec_class) (e : exp) : exp :=
    List.fold_left (fun e' lab => prune_single lab e') allowed e.

(* begin hide *)
  Notation "\\ e //_ labs" := (prune labs e) (at level 40).
(* end hide *)

(** *** subprunenoorder *)

  Lemma subprunenoorder : forall v x body result lab,
    [v // x] body is result ->
    \\result//_(lab::nil) = result ->
    [\\v//_(lab::nil) // x] \\body//_(lab::nil) is result.
  Proof.
    intros. induction H; subst; try (simpl in *; auto).
    - rewrite H0. constructor.
    - inversion H0. repeat (rewrite H1). constructor.
    - constructor; try assumption. apply IHsubsti. 
      inversion H0. congruence.
    - constructor.
      + apply IHsubsti1. inversion H0; congruence.
      + apply IHsubsti2. inversion H0; congruence.
    - constructor.
      + apply IHsubsti1. inversion H0; congruence.
      + apply IHsubsti2. inversion H0; congruence.
      + apply IHsubsti3. inversion H0; congruence.
    - destruct (sec_class_eq_dec class lab) as [eq | neq].
      + discriminate H0.
      + constructor. apply IHsubsti.
        inversion H0; congruence.
     Qed.

(** If the result of a substitution has none of a label, then pruning
the body for that label beforehand doesn't affect the result. *)

(** *** prunesubst_commute *)

 Lemma prunesubst_commute : forall lab v x body result,
    [v // x] body is result ->
    [(prune_single lab v) // x] (prune_single lab body) is (prune_single lab result).
  Proof.
    intros. induction H; subst; try (simpl; auto).
    destruct (sec_class_eq_dec class lab); auto.
  Qed.

(** Pruning the result of a substitution is the same as pruning the
argument and body before making the substitution. *)
 
(** ** Stability *)

(** *** Single-step Version *)

(** Fortunately, while monotonicity was not able to be fully
machine-verified to due to time constraints, stability was, despite
a similar issue in originally stating the sub-lemmas
inadequately. Originally, the same flawed approach was taken by
stating the single-step lemma as so: *)

(* Stability single step incorrectly stated & proven *)
  Lemma stabilitysinglestep_tooweak : forall e f lab,
    noholes f ->
    e --> f ->
    (\\ f //_ (lab::nil)) = f ->
    \\ e //_ (lab::nil) -->* f.
  Proof.
    intros. induction H0; subst.
    - simpl. apply multi_R. constructor.
      apply subprunenoorder. auto. auto.
    - simpl in *. inversion H1. rewrite H4. rewrite H4.
      apply bodystepsappsteps.
      rewrite H3. apply IHstep.
      + inversion H; subst; auto.
      + auto.
    - simpl in *. apply multi_R. rewrite H1; auto.
    - simpl in *. apply multi_R. rewrite H1; auto.
    - simpl in *. inversion H1; subst.
      repeat (rewrite H4).
      repeat (rewrite H5).
      repeat (rewrite H3).
      apply condstepsteststeps.
      apply IHstep; auto. inversion H; subst; auto.
    - simpl in *. destruct (sec_class_eq_dec class lab).
      + apply multi_R. inversion H1.
      + apply multi_R. inversion H1.
        repeat (rewrite H2).
        repeat (rewrite H3).
        constructor.
    - simpl in *. destruct (sec_class_eq_dec class lab).
      + inversion H1.
      + inversion H1.
        repeat (rewrite H2).
        repeat (rewrite H3).
        repeat (rewrite H4).
        apply multi_R. auto.
    - simpl in *. destruct (sec_class_eq_dec class lab).
      + inversion H1.
      + apply markedbodstepstermsteps. 
        apply IHstep. inversion H; subst; auto.
        inversion H1; subst. congruence.
  Qed.

(** The following single-step version is slightly different than
this, for reasons similar to the problems encountered with
    monotonicity. This single-step lemma shows that whenever an
    expression [e] steps to another expression [f] in a single step,
    either the prune of [e] steps to the prune of [f] or the prune of
    [f] is holier than the prune of the term it came from, [e]. For
    the purposes of clarity, the proofs for stability and its related
    lemmas are restricted to the pruning of a single label rather
    than a list; the full proof would be significantly longer and add
    little value. *)

  Lemma stabilitysinglestep : forall e f lab,
    e --> f ->
    \\ e //_ (lab :: nil) -->* (\\ f //_ (lab :: nil))
    \/
    \\ f //_ (lab :: nil) << \\ e //_ (lab :: nil).
  Proof.
    intros. induction H.
    - left. simpl. apply multi_R. constructor.
      apply prunesubst_commute; auto.
    - destruct IHstep as [L | R].
      + left. simpl in *. apply bodystepsappsteps. auto.
      + right. simpl in *. constructor; auto.
    - left. simpl. apply multi_R. constructor.
    - left. simpl. apply multi_R. constructor.
    - destruct IHstep as [L | R].
      + left. simpl in *. apply condstepsteststeps. auto.
      + right. simpl in *. constructor; auto.
    - simpl. destruct (sec_class_eq_dec class lab) as [eq | neq].
      + right. constructor.
      + left. apply multi_R. constructor.
    - simpl. destruct (sec_class_eq_dec class lab) as [eq | neq].
      + right. constructor.
      + left. apply multi_R. constructor.
    - simpl.
      destruct (sec_class_eq_dec class lab) as [eq | neq].
      left. constructor.
      destruct IHstep.
      + simpl in H0. left.
        apply markedbodstepstermsteps. auto.
      + right. simpl in *.
        constructor; auto.
  Qed.

(** The proof is by induction on the step from [e] to [f]. Many of
the cases are fairly similar. A few have been picked out to
demonstrate the process. Since the value of the security class
identified by the label is irrelevant here and the same in all cases,
the "[_[lab]]" for prune notation is omitted. *)

(**

- Consider the case where [e --> f] because [e] is of the form [app
  (abs x T body) arg] and [f] is the result of substituting [arg]
  into the abstraction. Since the structure of the result is
  necessarily different than that of an application and the holier
  relation requires congruent expressions, the possibility of [\\
  f // << \\ e //] can be eliminated.

  Partially applying the [prune] rules to these expressions means we
  must show that [app (abs x T \\body//) \\arg// -->* \\subres//]
  where [[arg // x] body is subres]. This amounts to showing that
  [[\\arg// // x] \\body// is \\subres//] as defined in the [step]
  relation. The [prunesubst_commute] lemma given above takes care of
  the rest.

- The case where [e --> f] by reducing a marked body ([marked class
  body --> marked class body']) is more interesting. Nothing can be
  said yet as to which disjunct will apply, because it depends on
  whether the marked expression is of the security class to be
  pruned. Consider first that it is. Then [\\marked class bodye//
  -->* \\marked class bodyf//] is trivial; we're showing that [hole
  -->* hole] (or that [hole << hole], which is also true). So now
     assume it's not. The inductive hypothesis gives us the
     relationship between [bodye] and [bodyf], so the two cases are
     examined separately.

  - First consider that [\\bodye// -->* \\bodyf//]. In this case,
    [markedbodystepstermsteps] makes it easy to show the left
    disjunct in the conclusion is true: [marked class \\bodye// -->*
    marked class \\bodyf//].

  - Now assume [\\bodyf// << \\bodye//]. The [<<] relation between
    marked terms requires exactly this, so the right disjunct is
    true: [marked class \\bodyf// << marked class \\bodye//].

The rest of the cases follow in a similar fashion by case-splitting
on the inductive hypothesis and whether [class = lab] if needed.

*)

(** *** Full Version *)

(** Stability is the property where, when any expression [e] that
steps to an expression [f] without holes or labels to be pruned, the
prune of [e] will also step to [f]. *)

  Lemma stability : forall e f lab,
    noholes f ->
    e -->* f ->
    (\\ f //_(lab :: nil)) = f ->
    \\ e //_(lab :: nil) -->* f.
  Proof.
    intros. induction H0.
    - rewrite H1; constructor.
    - apply stabilitysinglestep with
      (e := x0) (f := y0) (lab := lab) in H0.
      destruct H0 as [L | R].
      + eapply multi_trans.
        * apply L.
        * apply IHmulti; auto.
      + eapply monotonicity; eauto.
  Qed.

(** Proof for the stability theorem is done here by induction on the
    [e -->* f] assumption. Most of the legwork is already
    accomplished by [monotonicity]. Note that [e -->* f] is
    a multistep relation, not a single step, and so the base case is
    that zero steps are taken. If zero steps are taken from [e] to
    [f], then [e = f] and the conclusion is trivial. If at least one
    step is taken, [e --> m] for some term [m] and we can assume         [m -->* f]. We must show that [\\e// -->* f].  Since we have that    [e --> m], [stabilitysinglestep] gives us that either                [\\e// -->* \\m//] or [\\m// << \\e//].

    - If [\\e// -->* \\m//], then the transitivity of [-->*] and the
      inductive hypothesis give that [\\e// -->* \\m// -->* \\f//
      = f].

    - Now presume [\\m// << \\e//]. It's already given that [f] has
      no holes and [m -->* f]. All that's needed to apply the
      [monotonicity] theorem and complete the proof is to show that
      [\\m// -->* f], but this is exactly what the inductive
      hypothesis provides and so we are done.

*)

(** ** Non-interference *)

(** Together, stability and monotonicity (along with the guarantees
of the type system) form the majority of the proof for
non-interference. To restate the theorem, it's the property that
TODO: unsure how to state this from the slides *)

(** * References and Related Work *)

(** 

- The idea for using stability and monotonicity to complete
  a syntactic proof of non-interference was inspired by François
  Pottier's 2004 presentation at INRIA. The slides of his
  presentation can be found at
  http://gallium.inria.fr/~fpottier/slides/eugene.pdf.

- TODO: any other things I should add?

*)

(* begin hide *)
End STLC.
(* end hide *)
