
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From STLCIF Require Import Maps.
From STLCIF Require Import Smallstep.

Module STLC.
  Inductive data_type : Type :=
    | Bool  : data_type
    | Arrow : data_type -> data_type -> data_type.

  Inductive sec_class : Type :=
    | High : sec_class
    | Low : sec_class.

  Inductive exp : Type :=
    | var : string -> exp
    | app : exp -> exp -> exp
    | abs : string -> data_type -> exp -> exp
    | tru : exp
    | fls : exp
    | test : exp -> exp -> exp -> exp
    | marked : sec_class -> exp -> exp.

  Open Scope string_scope.
  Definition x := "x".
  Definition y := "y".
  Definition z := "z".
  Hint Unfold x.
  Hint Unfold y.
  Hint Unfold z.

  Notation idB :=
    (abs x Bool (var x)).

  Notation idBB :=
    (abs x (Arrow Bool Bool) (var x)).

  Notation idBBBB :=
    (abs x (Arrow (Arrow Bool Bool)
    (Arrow Bool Bool))
    (var x)).

  Notation k := (abs x Bool (abs y Bool (var x))).

  Notation notB := (abs x Bool (test (var x) fls tru)).

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

  Hint Constructors value.

  Reserved Notation "'[' x '//' v ']' e 'is' r" (at level 40).
  Inductive substi (x : string) (s : exp) : exp -> exp -> Prop :=
    | s_var_eq :
        substi x s (var x) s
    | s_var_neq :
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
      where "'[' v '//' x ']' e 'is' r" := (substi x v e r)
  .

  Hint Constructors substi.

  Reserved Notation "t1 '-->' t2" (at level 40).
  Inductive step : exp -> exp -> Prop :=
    | ST_AppAbs :
        forall x T t12 v2 subres,
        value v2 ->
        [v2//x] t12 is subres ->
        (app (abs x T t12) v2) --> subres

    | ST_App1 :
        forall t1 t1' t2,
        t1 --> t1' ->
        app t1 t2 --> app t1' t2

    | ST_App2 :
        forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        app v1 t2 --> app v1  t2'

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

    | ST_LiftTestB1 :
        forall class cond b1 b2,
        (test cond (marked class b1) b2) --> (marked class (test cond b1 b2))

    | ST_LiftTestB2 :
        forall class cond b1 b2,
        (test cond b1 (marked class b2)) --> (marked class (test cond b1 b2))

    where "t1 '-->' t2" := (step t1 t2).

  Hint Constructors step.

  Notation multistep := (multi step).
  Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


  Definition context := partial_map data_type.

  Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

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

  Hint Constructors has_dtype.

  (* Reserved Notation "a << b" (at level 40). *)
  Definition holier (a : exp) (b : exp) : Prop :=
    True.
  Notation "a << b" := (holier a b) (at level 40).

  Lemma monotonicity : forall e e' f,
    e << e' ->
    e -->* f ->
    e' -->* f.
  Proof.
  Admitted.

  Definition prune (e : exp) (allowed : exp) (res : exp) : Prop :=
    True.
  Notation "\\ e // L >> r" := (prune e L r) (at level 40).

  Lemma stability : forall e f L,
    e -->* f ->
    \\f//L >> f ->
    \\e//L >> f.
  Proof.
  Admitted.
End STLC.
