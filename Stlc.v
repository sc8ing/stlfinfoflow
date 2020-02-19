
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From STLCIF Require Import Maps.
From STLCIF Require Import Smallstep.

Module STLC.
  (** ** Types *)
  Inductive dtype : Type := (* data type *)
    | Bool  : dtype
    | Arrow : dtype -> dtype -> dtype.
  Inductive stype : Type := (* security type/class *)
    | High : stype
    | Low : stype.
  Inductive stype_orderi : stype -> stype -> Prop :=
    | stype_eq : forall styp1 styp2,
        stype_orderi styp1 styp2
    | stype_low_less : forall styp,
        stype_orderi Low styp.
  Definition stype_order (s1 : stype) (s2 : stype) : bool :=
    match s1, s2 with
    | Low, _ => true
    | High, High => true
    | _, _ => false
    end.

  (** Terms *)
  Inductive term : Type :=
    | read : string -> stype -> term
    | var : string -> term
    | app : term -> term -> term (* application of a term to a an abstraction *)
    | abs : string -> dtype -> term -> term (* abstraction ~= function *)
    | tru : term
    | fls : term
    | test : term -> term -> term -> term.

  Inductive cmd : Type :=
    | C_write : term -> string -> stype -> cmd
    | C_seq : cmd -> cmd -> cmd
    | C_if : term -> cmd -> cmd -> cmd
    | C_skip : cmd.

  Infix ";;" := C_seq (at level 80, right associativity).


  Open Scope string_scope.
  Definition x := "x".
  Definition y := "y".
  Definition z := "z".
  Hint Unfold x.
  Hint Unfold y.
  Hint Unfold z.


  (** We write these as [Notation]s rather than [Definition]s to
    make things easier for [auto]. *)
    (** [idB = \x:Bool. x] *)
    Notation idB :=
      (abs x Bool (var x)).

    (** [idBB = \x:Bool->Bool. x] *)
    Notation idBB :=
      (abs x (Arrow Bool Bool) (var x)).

    (** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)
    Notation idBBBB :=
      (abs x (Arrow (Arrow Bool Bool)
      (Arrow Bool Bool))
      (var x)).

    (** [k = \x:Bool. \y:Bool. x] *)
    Notation k := (abs x Bool (abs y Bool (var x))).

    (** [notB = \x:Bool. test x then fls else tru] *)
    Notation notB := (abs x Bool (test (var x) fls tru)).


    (** * Operational Semantics *)
    (** ** Values *)
    Inductive value : term -> Prop :=
      | val_abs : forall x T t,
          value (abs x T t)
      | val_tru :
          value tru
      | val_fls :
          value fls.

    Hint Constructors value.

    Definition Hstate := partial_map term.
    Definition Lstate := partial_map term.

    (*
    (** ** Substitution *)
    Reserved Notation "'[' x ':=' s ']' t" (at level 20).

    Fixpoint subst (Lst : Lstate) (Hst : Hstate) (x : string)
                   (s : term) (t : term) : term :=
      match t with
      | read loc High => 
          (match Hst loc with
          | None =>  (* what? make it an optional? *)
          | Some ter => subst Lst Hst x s ter
          end)
      | read loc Low => 
          subst Lst Hst x s (Lst loc)
      | var x' =>
          if eqb_string x x' then s else t
      | abs x' dtyp t1 =>
          abs x' dtyp (if eqb_string x x' then t1 else ([x:=s] t1))
      | app t1 t2 =>
          app ([x:=s] t1) ([x:=s] t2)
      | tru =>
          tru
      | fls =>
          fls
      | test t1 t2 t3 =>
          test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
      end

      where "'[' x ':=' s ']' t" := (subst x s t).
      *)

    Inductive substi (Lst : Lstate) (Hst : Hstate) (x : string)
      (s : term) : term -> term -> Prop :=
      | s_read_H :
          forall loc readterm readtermsub,
          Hst loc = Some readterm ->
          substi Lst Hst x s readterm readtermsub ->
          substi Lst Hst x s (read loc High) readtermsub
      | s_read_L :
          forall loc readterm readtermsub,
          Lst loc = Some readterm ->
          substi Lst Hst x s readterm readtermsub ->
          substi Lst Hst x s (read loc Low) readtermsub
      | s_var_eq :
          substi Lst Hst x s (var x) s
      | s_var_neq :
          y <> x ->
          substi Lst Hst x s (var y) (var y)
      | s_abs_eq :
          forall t1 T, substi Lst Hst x s (abs x T t1) (abs x T t1)
      | s_abs_neq :
          forall t1 t1' T,
          x <> y ->
          substi Lst Hst x s t1 t1' ->
          substi Lst Hst x s (abs y T t1) (abs y T t1')
      | s_app :
          forall t1 t1' t2 t2',
          substi Lst Hst x s t1 t1' ->
          substi Lst Hst x s t2 t2' ->
          substi Lst Hst x s (app t1 t2) (app t1' t2')
      | s_tru :
          substi Lst Hst x s tru tru
      | s_fls :
          substi Lst Hst x s fls fls
      | s_test :
          forall t1 t1' t2 t2' t3 t3',
          substi Lst Hst x s t1 t1' ->
          substi Lst Hst x s t2 t2' ->
          substi Lst Hst x s t3 t3' ->
          substi Lst Hst x s (test t1 t2 t3) (test t1' t2' t3')
    .

    Hint Constructors substi.

    (*
    Theorem subst_substi_eq : forall x s t t',
      [x:=s]t = t' <-> substi x s t t'.
    Proof.
      intros. split; intros H.
      - induction t.
        + simpl in H.
    Admitted.
    *)


    (* Smallstep Semantics *)
    Reserved Notation "L H '::' t1 '-->' t2" (at level 40).

    Inductive step_term (Lst : state) (Hst :state ) :
      term -> term -> Prop :=
      | ST_Read_H : forall loc readterm,
          Hst loc = Some readterm ->
          step_term Lst Hst (read loc High) readterm
      | ST_Read_H : forall loc readterm,
          Hst loc = Some readterm ->
          step_term Lst Hst (read loc High) readterm
      | ST_AppAbs : forall x T t12 v2 t12',
          value v2 ->
          substi Lst Hst x v2 t12 t12' ->
          Lst Hst :: (app (abs x T t12) v2) --> t12'
      | ST_App1 : forall t1 t1' t2,
          Lst Hst :: t1 --> t1' ->
          Lst Hst :: app t1 t2 --> app t1' t2
      | ST_App2 : forall v1 t2 t2',
          value v1 ->
          Lst Hst :: t2 --> t2' ->
          Lst Hst :: app v1 t2 --> app v1  t2'
      | ST_TestTru : forall t1 t2,
          Lst Hst :: (test tru t1 t2) --> t1
      | ST_TestFls : forall t1 t2,
          Lst Hst :: (test fls t1 t2) --> t2
      | ST_Test : forall t1 t1' t2 t3,
          Lst Hst :: t1 --> t1' ->
          Lst Hst :: (test t1 t2 t3) --> (test t1' t2 t3)

          where "L H '::' t1 '-->' t2" := (step_term Lst Hst t1 t2).

    Hint Constructors step_term.

    Notation multistepterm := (multi step_term).
    Notation "t1 '-->*' t2" := (multistepterm t1 t2) (at level 40).

    
    Inductive step_cmd : state * cmd -> state * cmd -> Prop :=
      | ST_C_write : forall st vstr loc dt st,
          step_cmd (C_write loc dt st)
                   ((loc |-> dt ; st), C_skip)

      | ST_C_seq_step : forall st st' c1 c1' c2,
          step_cmd (st, c1) (st', c1') ->
          step_cmd (st, (c1 ;; c2)) (st', (c1' ;; c2))

      | ST_C_seq_skip : forall state c2,
          step_cmd (state, (C_skip ;; c2))
                   (state, c2)
(*
      | ST_C_seq_2 : forall c1 c2,
          (~exists c1' step_cmd c1 c1') ->
          step_cmd (c1 ;; c2) c2 *)

      | ST_C_if_tru : forall state b1 b2,
          step_cmd (state, (C_if tru b1 b2))
                   (state, b1)

      | ST_C_if_fls : forall state b1 b2,
          step_cmd (state, (C_if fls b1 b2))
                   (state, b2)

      | ST_C_if_cond : forall state cond cond' b1 b2,
          step_term cond cond' ->
          step_cmd (state, (C_if cond b1 b2))
                   (state, (C_if cond' b1 b2))
    .


    (** * Typing *)
    Definition context := partial_map ty.

    (** ** Typing Relation *)

    Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

    Inductive has_type : context -> tm -> ty -> Prop :=
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
                          where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

    Hint Constructors has_type.
End STLC.
