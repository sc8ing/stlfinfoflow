
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From STLCIF Require Import Maps.
From STLCIF Require Import Smallstep.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.

Module STLC.
  Inductive data_type : Type :=
    | Bool  : data_type
    | Arrow : data_type -> data_type -> data_type.
  Definition data_type_eq_dec :
    forall (x y : data_type), { x = y } + { x <> y }.
  Proof. decide equality. Defined.

  Inductive sec_class : Type :=
    | High : sec_class
    | Low : sec_class.
  Definition sec_class_eq_dec :
    forall (x y : sec_class), { x = y } + { x <> y }.
  Proof. decide equality. Defined.

  Inductive exp : Type :=
    | var : string -> exp
    | app : exp -> exp -> exp
    | abs : string -> data_type -> exp -> exp
    | tru : exp
    | fls : exp
    | test : exp -> exp -> exp -> exp
    | marked : sec_class -> exp -> exp
    | hole.
  
  Definition exp_eq_dec :
    forall (x y : exp), { x = y } + { x <> y }.
  Proof.
    decide equality.
    - destruct (string_dec s s0) eqn:E.
      + left. auto.
      + right. auto.
    - Admitted.
(*  Defined. *)

  Inductive protected (l : sec_class) : data_type -> Prop :=
    | P_bool :
        protected l Bool
    | P_arrow :
        forall t1 t2,
        protected l t2 ->
        protected l (Arrow t1 t2).

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

  Reserved Notation "'[' v '//' x ']' e 'is' r" (at level 40).
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

    | ST_MarkReduce :
        forall class body body',
        body --> body' ->
        (marked class body) --> (marked class body')

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
(*        (protected class dtype) -> *)
        Gamma |- marked class e \in T

    where "Gamma '|-' t '\in' T" := (has_dtype Gamma t T).

  Hint Constructors has_dtype.

  Reserved Notation "a << b" (at level 40).
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


  Lemma holyval_meansval : forall v1 v2,
    value v1 ->
    v1 << v2 ->
    value v2.
  Proof.
    intros. generalize dependent v2.
    induction H; intros; inversion H0; constructor.
    - subst. assumption.
    - subst. apply IHvalue. assumption.
  Qed.


  Lemma holier_abs_inv : forall x T body e',
    (abs x T body) << e' ->
    exists body', body << body' /\ e' = (abs x T body').
  Proof.
    intros. inversion H; subst. induction body.
    - exists (var s). auto.
    - exists (app body1 body2). auto.
    - exists (abs s d body). auto.
    - exists tru. auto.
    - exists fls. auto.
    - exists (test body1 body2 body3). auto.
    - exists (marked s body). auto.
    - exists hole. auto.
    - exists body'. auto.
  Qed.


  Lemma noholes_app_body : forall x body arg f,
  noholes f ->
  [arg // x] body is f ->
  noholes body.
  Proof.
    intros. induction H0.
    - econstructor.
    - assumption.
    - assumption.
    - inversion H; subst. apply IHsubsti in H3.
      apply NH_abs. assumption.
    - inversion H; subst.
      apply IHsubsti1 in H2.
      apply IHsubsti2 in H3.
      apply NH_app; assumption.
    - assumption.
    - assumption.
    - inversion H; subst.
      apply IHsubsti1 in H3.
      apply IHsubsti2 in H4.
      apply IHsubsti3 in H5.
      apply NH_test; assumption.
    - inversion H; subst.
      apply IHsubsti in H2.
      apply NH_marked. assumption.
  Qed.

  Lemma noholes_app_arg_orunused : forall x body arg f,
  noholes f ->
  [arg // x] body is f ->
  noholes arg \/ forall xsub, [xsub // x] body is f.
  Proof.
    intros. induction H0.
    - left. assumption.
    - right. intros. econstructor. auto.
    - right. intros. constructor.
    - right. intros. constructor.
      + assumption.
      + inversion H; subst.
        specialize H3 as H3'. apply IHsubsti in H3.
        destruct H3 as [argnoholes | argunused].
        * admit.
        * apply argunused.
    - inversion H; subst.
      specialize H2 as H2'.
      specialize H3 as H3'.
      apply IHsubsti1 in H2.
      apply IHsubsti2 in H3.
      (* destruct on yes/no whether arg has holes? *)
      (*
      induction H2. induction H3.
      + left. assumption.
      + left. assumption.
      + right. intros. constructor.

      destruct H2 as [argnoholes | argunused].
      destruct H3 as [argnoholes2 | argunused2].
      + left. assumption.
      + left. assumption.
      + right. intros. constructor.
        * apply IHsubsti1 in H2'.
      *)
        admit.
    - right. constructor.
    - right. constructor.
    - (* same issue *) admit.
    - (* same *)
      inversion H; subst.
      specialize H2 as H2'.
      apply IHsubsti in H2.
      admit.
  Admitted.


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
        apply holyval_meansval in H0_0.
        eapply multi_step.
        apply ST_AppAbs.
        assumption.
  Admitted.

  
  Lemma monotonicity : forall e e' f,
    noholes f ->
    e << e' ->
    e -->* f ->
    e' -->* f.
  Proof.
    intros. generalize dependent f. induction H0; intros.
    - assumption.
    - inversion H1; subst.
      + inversion H.
      + inversion H0.
    - inversion H1; subst.
      + 
  Admitted.


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
        if sec_class_eq_dec lab l then hole else e

    | other => other
    end.

  Definition prune (allowed : list sec_class) (e : exp) : exp :=
    List.fold_left (fun e' lab => prune_single lab e') allowed e.

  Notation "\\ e //_ labs" := (prune labs e) (at level 40).


  (* induction on stepping relation num steps *)
  Lemma stability : forall e f labs,
    noholes f ->
    e -->* f ->
    (\\ f //_labs) = f ->
    \\ e //_labs -->* f.
  Proof.
  Admitted.
End STLC.
