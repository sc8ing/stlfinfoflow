
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From STLCIF Require Import Maps.
From STLCIF Require Import Smallstep.

Module STLC.
  Inductive dtype : Type := (* data type *)
    | Bool  : dtype
    | Arrow : dtype -> dtype -> dtype.


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

    | seq : cmd -> cmd -> cmd
    | if : exp -> cmd -> cmd -> cmd
    | skip : cmd.

  Infix ";;" := seq (at level 80, right associativity).


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
      (* sub in for the arguments of the read command (except High low) *)
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
    Inductive step_term (Lst : Lstate) (Hst : Hstate) :
      term -> term -> Prop :=
      | ST_Read_H : forall loc readterm,
          Hst loc = Some readterm ->
          step_term Lst Hst (read loc High) readterm
      | ST_Read_L : forall loc readterm,
          Lst loc = Some readterm ->
          step_term Lst Hst (read loc Low) readterm
      | ST_AppAbs : forall x T t12 v2 t12',
          value v2 ->
          substi Lst Hst x v2 t12 t12' ->
          step_term Lst Hst (app (abs x T t12) v2) t12'
      | ST_App1 : forall t1 t1' t2,
          step_term Lst Hst t1 t1' ->
          step_term Lst Hst (app t1 t2) (app t1' t2)
      | ST_App2 : forall v1 t2 t2',
          value v1 ->
          step_term Lst Hst t2 t2' ->
          step_term Lst Hst (app v1 t2) (app v1  t2')
      | ST_TestTru : forall t1 t2,
          step_term Lst Hst (test tru t1 t2) t1
      | ST_TestFls : forall t1 t2,
          step_term Lst Hst (test fls t1 t2) t2
      | ST_Test : forall t1 t1' t2 t3,
          step_term Lst Hst t1 t1' ->
          step_term Lst Hst (test t1 t2 t3) (test t1' t2 t3).

    Hint Constructors step_term.

    Notation multistepterm := (multi step_term).
    Notation "L H t1 '-->*' t2" := (multistepterm L H t1 t2) (at level 40).

    
    Reserved Notation "'[[' L '|' H ']]' t1 '-->' '[[' L2 '|' H2 ']]' t2" (at level 40).
    Inductive step_cmd : Lstate * Hstate * cmd ->
                         Lstate * Hstate * cmd -> Prop :=
      | ST_C_write_L : forall L H data loc,
          [[ L | H ]] (C_write data loc Low)
          --> [[ (loc |-> data ; L) | H ]] C_skip

      | ST_C_write_H : forall L H data loc,
          [[ L | H ]] (C_write data loc High)
             --> [[ L | (loc |-> data ; H) ]] C_skip

      | ST_C_seq_step : forall L H L2 H2 c1 c1' c2,
          [[ L | H ]] c1 --> [[ L2 | H2 ]] c1' ->
          [[ L | H ]] (c1 ;; c2) --> [[ L2 | H2 ]] (c1' ;; c2)

      | ST_C_seq_skip : forall L H c2,
          [[ L | H ]] (C_skip ;; c2) --> [[ L | H ]] c2

      | ST_C_if_tru : forall L H b1 b2,
          [[ L | H ]] (C_if tru b1 b2) --> [[ L | H ]]b1

      | ST_C_if_fls : forall L H b1 b2,
          [[ L | H ]] (C_if fls b1 b2) --> [[ L | H ]] b2

      | ST_C_if_cond : forall L H cond cond' b1 b2,
          step_term L H cond cond' ->
          [[ L | H ]] (C_if cond b1 b2)
              --> [[ L | H ]] (C_if cond' b1 b2)
    
      where "'[[' L '|' H ']]' c1 '-->' '[[' L2 '|' H2 ']]' c2" := (step_cmd (L, H, c1) (L2, H2, c2)). 

    Notation multistepcmd := (multi step_cmd).
    Notation "'[[' L '|' H ']]' c1 '-->*' '[[' L2 '|' H2 ']]' c2" :=
        (multistepcmd (L, H, c1) (L2, H2, c2)) (at level 40).
    
    

    (* no H that affects L' *)
    (* i.e. no 2 Hs that result in different L' L2' *)
    (* i.e. H|L->H'|L' /\ H2|L->H2'|L2' -> L'=L2' *)
    Definition non_interference :=
      forall L H L' H' H2 H2' L2' p p' p'',
      [[ H | L ]] p -->* [[ H' | L' ]] p' /\
          [[ H2 | L ]] p -->* [[ H2' | L2' ]] p'' ->
      L' = L2'.



    (** * Typing *)
    Definition dtype_context := partial_map dtype.

    (** ** Typing Relation *)

    Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

    Inductive has_dtype : dtype_context -> term -> dtype -> Prop :=
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
