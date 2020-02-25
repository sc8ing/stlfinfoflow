
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From STLCIF Require Import Maps.
From STLCIF Require Import Smallstep.

Module STLC.
  Inductive dtype : Type := (* data type *)
    | Bool  : dtype
    | Arrow : dtype -> dtype -> dtype
    | Unit : dtype.


  Inductive stype : Type := (* security type/class *)
    | High : stype
    | Low : stype.


  Reserved Notation "s '_<=' S" (at level 100).
  Inductive stype_orderi : stype -> stype -> Prop :=
    | stype_eq : forall s,
        s _<= s
    | stype_low_less : forall s,
        Low _<= s
    where "s '_<=' S" := (stype_orderi s S).


  Definition stype_order (s1 : stype) (s2 : stype) : bool :=
    match s1, s2 with
    | Low, _ => true
    | High, High => true
    | _, _ => false
    end.


  Inductive exp : Type :=
    (* read [location] from [security class] *)
    | read : string -> stype -> exp

    (* write [val] to [location] in [security class] *)
    | write : exp -> string -> stype -> exp

    (* a lambda calculus binding *)
    | var : string -> exp 

    (* [abstraction] [arg] *)
    | app : exp -> exp -> exp 

    (* abstraction ~= function *)
    | abs : string -> dtype -> exp -> exp 

    | tru : exp
    | fls : exp

    | seq : exp -> exp -> exp
    | test : exp -> exp -> exp -> exp
    | skip : exp.

  Infix ";;" := seq (at level 80, right associativity).


  Open Scope string_scope.
  Definition x := "x".
  Definition y := "y".
  Definition z := "z".
  Hint Unfold x.
  Hint Unfold y.
  Hint Unfold z.


  (* To help do things with auto. *)
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


  Inductive value : exp -> Prop :=
    | val_abs : forall x T t,
        value (abs x T t)
    | val_tru :
        value tru
    | val_fls :
        value fls.

  Hint Constructors value.

  Definition Hstate := partial_map exp.
  Definition Lstate := partial_map exp.


  (* x = s in [exp] *)
  Inductive substi (x : string) (s : exp) : exp -> exp -> Prop :=
(*    | s_read :
        forall loc sclass,
        substi x s loc loc' ->
        substi x s (read loc sclass) (read loc' sclass)*)

    | s_write :
        forall d d' loc sc,
        substi x s d d' ->
        substi x s (write d loc sc) (write d' loc sc)

    | s_var_eq :
        substi x s (var x) s

    | s_var_neq :
        y <> x ->
        substi x s (var y) (var y)

    | s_app :
        forall t1 t1' t2 t2',
        substi x s t1 t1' ->
        substi x s t2 t2' ->
        substi x s (app t1 t2) (app t1' t2')

    | s_abs_eq :
        forall t1 T,
        substi x s (abs x T t1) (abs x T t1)

    | s_abs_neq :
        forall t1 t1' T,
        x <> y ->
        substi x s t1 t1' ->
        substi x s (abs y T t1) (abs y T t1')

    | s_tru :
        substi x s tru tru
    | s_fls :
        substi x s fls fls

    | s_seq :
        forall c1 c1' c2 c2',
        substi x s c1 c1' ->
        substi x s c2 c2' ->
        substi x s (c1;;c2) (c1';;c2')

    | s_test :
        forall t1 t1' t2 t2' t3 t3',
        substi x s t1 t1' ->
        substi x s t2 t2' ->
        substi x s t3 t3' ->
        substi x s (test t1 t2 t3) (test t1' t2' t3')

    | s_skip :
        substi x s skip skip
    .

    Hint Constructors substi.


    Reserved Notation "'[[' L '|' H ']]' e1 '-->' e2 '[[' L2 '|' H2 ']]'" (at level 40).
    Inductive step : (Lstate * Hstate * exp)
                  -> (Lstate * Hstate * exp) -> Prop :=
    | ST_read_L :
        forall loc (L : Lstate) (H : Hstate) v,
        L loc = Some v ->
        [[L|H]] (read loc Low) --> v [[L|H]]

    | ST_read_H :
        forall loc L H v,
        H loc = Some v ->
        [[L|H]] (read loc High) --> v [[L|H]]

    | ST_write_L :
        forall loc L H data,
        [[L|H]] (write data loc Low) --> skip [[(loc |-> data ; L) | H]]

    | ST_write_H :
        forall loc L H data,
        [[L|H]] (write data loc High) --> skip [[L | (loc |-> data ; H)]]

    | ST_appAbs :
        forall L H x T t12 v2 t12',
        value v2 ->
        substi x v2 t12 t12' ->
        [[L|H]] (app (abs x T t12) v2) --> t12' [[L|H]]

    | ST_app1 :
        forall L L' H H' t1 (t1' : exp) t2,
        [[L|H]] t1 --> t1' [[L'|H']] ->
        [[L|H]] (app t1 t2) --> (app t1' t2) [[L'|H']]

    | ST_app2 :
        forall L L' H H' v1 t2 (t2':exp),
        value v1 ->
        [[L|H]] t2 --> t2' [[L'|H']] ->
        [[L|H]] (app v1 t2) --> (app v1 t2') [[L'|H']]

    | ST_TestTru :
        forall L H b1 b2,
        [[L|H]] (test tru b1 b2) --> b1 [[L|H]]

    | ST_TestFls :
        forall L H b1 b2,
        [[L|H]] (test fls b1 b2) --> b2 [[L|H]]

    | ST_Test :
        forall L L' H H' cond (cond':exp) b1 b2,
        [[L|H]] cond --> cond' [[L'|H']] ->
        [[L|H]] (test cond b1 b2) --> (test cond' b1 b2) [[L'|H']]
    where "'[[' L '|' H ']]' e1 '-->' e2 '[[' L2 '|' H2 ']]'" := (step (L, H, e1) (L2, H2, e1)).

    Hint Constructors step.

    Notation multistep:= (multi step).
    Notation "'[[' L '|' H ']]' e1 '-->*' e2 '[[' L2 '|' H2 ']]'" := (multistep (L, H, e1) (L2, H2, e2)) (at level 40).


      (* no H that affects L' *)
      (* i.e. no 2 Hs that result in different L' L2' *)
      (* i.e. H|L->H'|L' /\ H2|L->H2'|L2' -> L'=L2' *)
      Definition non_interference :=
        forall L H L' H' H2 H2' L2' p p' p'',
        value p' ->
        value p'' ->
        [[ H | L ]] p -->*  p' [[ H' | L' ]] /\
            [[ H2 | L ]] p -->* p'' [[ H2' | L2' ]] ->
        L' = L2'.



      (** * Typing *)
      Definition dtype_context := partial_map dtype.

      (** ** Typing Relation *)

      Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

      Inductive has_dtype : dtype_context -> exp -> dtype -> Prop :=
(*        | T_read :
            forall Gamma loc styp e T,
            env loc = Some e ->
            Gamma |- e \in T ->
            Gamma |- (read loc styp) \in T *)
                (* pass in states, make separate copy without *)

        | T_write :
            forall e loc styp,
            Gamma |- (write e loc styp) \in Unit

        | T_var : forall Gamma x T,
            Gamma x = Some T ->
            Gamma |- var x \in T

        | T_app :
            forall T11 T12 Gamma t1 t2,
            Gamma |- t1 \in Arrow T11 T12 ->
            Gamma |- t2 \in T11 ->
            Gamma |- app t1 t2 \in T12

        | T_abs :
            forall Gamma x T11 T12 t12,
            (x |-> T11 ; Gamma) |- t12 \in T12 ->
            Gamma |- abs x T11 t12 \in Arrow T11 T12

        | T_tru :
            forall Gamma,
            Gamma |- tru \in Bool

        | T_fls :
            forall Gamma,
            Gamma |- fls \in Bool

        | T_seq :
            forall e1 e2,
            Gamma |- (e1 ;; e2) \in Unit

        | T_test :
            forall cond b1 b2 T Gamma,
            Gamma |- cond \in Bool ->
            Gamma |- b1 \in T ->
            Gamma |- b2 \in T ->
            Gamma |- test cond b1 b2 \in T

        | T_skip :
            Gamma |- skip \in Unit

        where "Gamma '|-' t '\in' T" := (has_dtype Gamma t T).

      Hint Constructors has_dtype.


      Definition stype_context := partial_map stype.

      Reserved Notation "gam '|-' p '\:' ST" (at level 40).
      Inductive has_stype : stype_context -> cmd -> stype -> Prop :=
        | S_skip : forall gam st,
            gam |- C_skip \: st

        | S_write : forall gam data dataSC loc writeSC propSC,
            dataSC _<= writeSC ->
            writeSC _<= propSC ->
            gam |- (C_write data loc writeSC) \: propSC

        | S_seq : forall gam c1 c2 c1SC c2SC propSC,
            propSC _<= c1SC /\ propSC _<= c2SC ->
            gam |- (c1 ;; c2) \: propSC

                (*
        | S_if : forall gam cond b1 b2 condSC b1SC b2SC propSC,
            b1SC _<= condSC /\ b2SC _<= condSC,
    *)

      where "gam '|-' p '\:' ST" := (has_stype gam p ST).

    End STLC.
