(* Since the variable names are now strings, we need to import the required libraries *)
Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.

(* ErrorNat encapsulates the constructor error_nat,
   which is useful in the case of arithmetic operations like division by 0*)
Inductive ErrorNat :=
  | error_nat: ErrorNat
  | num: nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool: ErrorBool
  | boolean: bool -> ErrorBool.

Inductive ErrorStr :=
  | error_str: ErrorStr
  | str: string -> ErrorStr.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.
Coercion str: string >-> ErrorStr.

(* A general type which includes all kind of types *)
Inductive Result :=
  | err_undecl: Result
  | err_assign: Result
  | default: Result
  | res_nat: ErrorNat -> Result
  | res_bool: ErrorBool -> Result
  | res_str: ErrorStr -> Result.

Scheme Equality for Result.

(* An environment which maps variable names (strings) to the Result type *)
Definition Env := string -> Result.

(* Initial environment *)
Definition env : Env := fun x => err_undecl.

(* Initially each variable is undeclared *)
Compute (env "x").

Definition check_eq_over_types (t1 : Result) (t2 : Result) : bool :=
  match t1 with
    | err_undecl => match t2 with
                      | err_undecl => true
                      | _ => false
                    end
    | err_assign => match t2 with 
                     | err_assign => true
                     | _ => false
                     end
    | default => match t2 with
                   | default => true
                   | _ => false
                 end
    | res_nat x => match t2 with
                   | res_nat y => true
                   | _ => false
                 end
    | res_bool x => match t2 with
                    | res_bool y => true
                    | _ => false
                  end
    | res_str x => match t2 with
                   | res_str y => true
                   | _ => false
                 end
  end.

Compute (check_eq_over_types (res_bool true) (res_bool false)).
Compute (check_eq_over_types (res_nat 0) err_undecl).

Definition update (env : Env) (x : string) (v : Result) : Env :=
  fun y =>
    if (eqb y x)
    then
      if (andb (check_eq_over_types err_undecl (env y)) (negb (check_eq_over_types default v)))
      then err_undecl
      else
        if (andb (check_eq_over_types err_undecl (env y)) (check_eq_over_types default v))
        then default
        else
          if (orb (check_eq_over_types default (env y)) (check_eq_over_types v (env y)))
          then v
          else err_assign
    else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).

Compute (env "y").
Compute (update (update env "y" (default)) "y" (res_bool true) "y").
Compute (update (update env "y" (default)) "y" (res_str "test") "y").
Compute ((update (update (update env "y" default) "y" (res_nat 10)) "y" (res_bool true)) "y").
Compute ((update (update (update env "y" default) "y" (res_nat 10)) "y" (res_str "test")) "y").

Inductive AExp :=
  | avar: string -> AExp
  | anum: ErrorNat -> AExp
  | aplus: AExp -> AExp -> AExp
  | aminus: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp
  | adiv: AExp -> AExp -> AExp
  | amod: AExp -> AExp -> AExp.

Coercion anum: ErrorNat >-> AExp.
Coercion avar: string >-> AExp.

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (aminus A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).

(* Notations used for the Big-Step semantics *)
Reserved Notation "A =[ S ]=> N" (at level 60).
Reserved Notation "B ={ S }=> B'" (at level 70).

Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.

Definition minus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else num (n1 - n2)
    end.

Definition mul_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition mod_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.

Fixpoint aeval_fun (a : AExp) (env : Env) : ErrorNat :=
  match a with
  | avar v => match (env v) with
                | res_nat n => n
                | _ => error_nat
              end
  | anum v => v
  | aplus a1 a2 => (plus_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | aminus a1 a2 => (minus_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amul a1 a2 => (mul_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | adiv a1 a2 => (div_ErrorNat  (aeval_fun a1 env) (aeval_fun a2 env))
  | amod a1 a2 => (mod_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  end.

(* Big-Step semantics for arithmetic operations *)
Inductive aeval : AExp -> Env -> ErrorNat -> Prop :=
  | const: forall n sigma, anum n =[ sigma ]=> n
  | var: forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                                 | res_nat x => x
                                                 | _ => error_nat
                                               end
  | add: forall a1 a2 i1 i2 sigma n,
          a1 =[ sigma ]=> i1 ->
          a2 =[ sigma ]=> i2 ->
          n = (plus_ErrorNat i1 i2) ->
          a1 +' a2 =[sigma]=> n
  | substract: forall a1 a2 i1 i2 sigma n,
                a1 =[ sigma ]=> i1 ->
                a2 =[ sigma ]=> i2 ->
                n = (minus_ErrorNat i1 i2) ->
                a1 -' a2 =[sigma]=> n
  | times: forall a1 a2 i1 i2 sigma n,
            a1 =[ sigma ]=> i1 ->
            a2 =[ sigma ]=> i2 ->
            n = (mul_ErrorNat i1 i2) ->
            a1 *' a2 =[sigma]=> n
  | division: forall a1 a2 i1 i2 sigma n,
               a1 =[ sigma ]=> i1 ->
               a2 =[ sigma ]=> i2 ->
               n = (div_ErrorNat  i1 i2) ->
               a1 /' a2 =[sigma]=> n
  | modulo: forall a1 a2 i1 i2 sigma n,
             a1 =[ sigma ]=> i1 ->
             a2 =[ sigma ]=> i2 ->
             n = (mod_ErrorNat i1 i2) ->
             a1 %' a2 =[sigma]=> n
  where "a =[ sigma ]=> n" := (aeval a sigma n).

Example substract_error : 1 -' 2 =[ env ]=> error_nat.
Proof.
  eapply substract.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example division_error : 10 /' 0 =[ env ]=> error_nat.
Proof.
  eapply division.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example modulo_error : 10 %' 0 =[ env ]=> error_nat.
Proof.
  eapply modulo.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Inductive BExp :=
  | berror
  | btrue
  | bfalse
  | bvar: string -> BExp
  | blt: AExp -> AExp -> BExp
  | bgt: AExp -> AExp -> BExp
  | bequal: AExp -> AExp -> BExp
  | bnot: BExp -> BExp
  | band: BExp -> BExp -> BExp
  | bor: BExp -> BExp -> BExp.

Notation "A <' B" := (blt A B) (at level 70).
Notation "A >' B" := (bgt A B) (at level 70).
Notation "A =' B" := (bequal A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

Definition lt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
  end.

Definition gt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v2 v1)
  end.

Definition equal_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.eqb v1 v2)
  end.

Definition not_ErrorBool (n :ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
  end.

Definition and_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
  end.

Definition or_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
  end.

Fixpoint beval_fun (a : BExp) (envnat : Env) : ErrorBool :=
  match a with
    | btrue => true
    | bfalse => false
    | berror => error_bool
    | bvar v => match (env v) with
                  | res_bool n => n
                  | _ => error_bool
                end
    | blt a1 a2 => (lt_ErrorBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
    | bgt a1 a2 => (gt_ErrorBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
    | bequal a1 a2 => (equal_ErrorBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
    | bnot b1 => (not_ErrorBool (beval_fun b1 envnat))
    | band b1 b2 => (and_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
    | bor b1 b2 => (or_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  end.

Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
  | b_error: forall sigma, berror  ={ sigma }=> error_bool
  | b_true: forall sigma, btrue ={ sigma }=> true
  | b_false: forall sigma, bfalse ={ sigma }=> false
  | b_var: forall v sigma, bvar v ={ sigma }=>  match (sigma v) with
                                                   | res_bool x => x
                                                   | _ => error_bool
                                                 end
  | b_lessthan: forall a1 a2 i1 i2 sigma b,
                 a1 =[ sigma ]=> i1 ->
                 a2 =[ sigma ]=> i2 ->
                 b = (lt_ErrorBool i1 i2) ->
                 a1 <' a2 ={ sigma }=> b
  | b_greaterthan: forall a1 a2 i1 i2 sigma b,
                 a1 =[ sigma ]=> i1 ->
                 a2 =[ sigma ]=> i2 ->
                 b = (gt_ErrorBool i1 i2) ->
                 a1 >' a2 ={ sigma }=> b
  | b_equal: forall a1 a2 i1 i2 sigma b,
                 a1 =[ sigma ]=> i1 ->
                 a2 =[ sigma ]=> i2 ->
                 b = (equal_ErrorBool i1 i2) ->
                 a1 =' a2 ={ sigma }=> b
  | b_not: forall a1 i1 sigma b,
            a1 ={ sigma }=> i1 ->
            b = (not_ErrorBool i1) ->
            !'a1 ={ sigma }=> b
  | b_and: forall a1 a2 i1 i2 sigma b,
            a1 ={ sigma }=> i1 ->
            a2 ={ sigma }=> i2 ->
            b = (and_ErrorBool i1 i2) ->
            (a1 &&' a2) ={ sigma }=> b 
  | b_or: forall a1 a2 i1 i2 sigma b,
           a1 ={ sigma }=> i1 ->
           a2 ={ sigma }=> i2 ->
           b = (or_ErrorBool i1 i2) ->
           (a1 ||' a2) ={ sigma }=> b 
where "B ={ S }=> B'" := (beval B S B').

Example boolean_operation : bnot (100 <' "n") ={ env }=> error_bool.
Proof.
  eapply b_not.
  eapply b_lessthan.
  - eapply const.
  - eapply var.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Inductive SExp :=
  | serror
  | svar: string -> SExp
  | sconst: ErrorStr -> SExp
  | strstr: SExp -> SExp -> SExp
  | strcmp: SExp -> SExp -> SExp.

Coercion svar: string >-> SExp.
Coercion sconst: ErrorStr >-> SExp.

Notation "'strstr(' A ',' B ')'" := (strstr A B)(at level 50, left associativity).
Notation "'strcmp(' A ',' B ')'" := (strcmp A B)(at level 50, left associativity).

(* It doesn't work from here *)
Definition strstr_error (s1 s2 : SExp) : ErrorStr :=
  match s1, s2 with
    | error_str, _ => error_str
    | _, error_str => error_str
    | sconst str1, sconst str2 => strstr(str1,str2)
  end.

Definition strcmp_error (s1 s2 : SExp) : ErrorStr :=
  match s1, s2 with
    | error_str, _ => error_str
    | _, error_str => error_str
    | sconst str1, sconst str2 => strcmp(str1,str2)
  end.

Fixpoint seval_fun (a : SExp) (env : Env) : ErrorStr :=
  match a with
    | serror => error_str
    | svar v => match (env v) with
                  | res_str s => s
                  | _ => error_str
                end
    | sconst v => v
    | strstr a1 a2 => (strstr_error (seval_fun a1 env) (seval_fun a2 env))
    | strcmp a1 a2 => (strcmp_error (seval_fun a1 env) (seval_fun a2 env))
  end.

Inductive seval : SExp -> Env -> ErrorStr -> Prop :=
  | s_error: forall sigma, serror  ={ sigma }=> error_str
  | s_var: forall v sigma, svar v ={ sigma }=>  match (sigma v) with
                                                   | res_str x => x
                                                   | _ => error_str
                                                 end
  | s_const: forall s sigma, sconst ={ sigma }=> s
  | s_strstr: forall s1 s2 i1 i2 sigma s,
               s1 =[ sigma ]=> i1 ->
               s2 =[ sigma ]=> i2 ->
               s = (strstr_error i1 i2) ->
               strstr(s1,s2) ={ sigma }=> s
  | s_strstr: forall s1 s2 i1 i2 sigma s,
               s1 =[ sigma ]=> i1 ->
               s2 =[ sigma ]=> i2 ->
               s = (strcmp_error i1 i2) ->
               strcmp(s1,s2) ={ sigma }=> s
  where "B ={ S }=> B'" := (seval B S B').

Inductive Stmt :=
  | nat_decl: string -> AExp -> Stmt
  | bool_decl: string -> BExp -> Stmt
  | str_decl: string -> SExp -> Stmt
  | nat_assign: string -> AExp -> Stmt
  | bool_assign: string -> BExp -> Stmt
  | str_assign: string -> SExp -> Stmt
  | sequence: Stmt -> Stmt -> Stmt
  | ifthenelse: BExp -> Stmt -> Stmt -> Stmt
  | ifthen: BExp -> Stmt -> Stmt
  | while: BExp -> Stmt -> Stmt
  | switch: AExp -> list Cases -> Stmt
  with Cases := | default: Stmt -> Cases
                | case: nat -> Stmt -> Cases.

Notation "X n= A" := (nat_assign X A)(at level 90).
Notation "X b= A" := (bool_assign X A)(at level 90).
Notation "X s= A" := (str_assign X A)(at level 90).
Notation "'Nat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'Bool' X ::= A" := (bool_decl X A)(at level 90).
Notation "'String' X ::= A" := (str_decl X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'fordo' ( A -- B -- C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).
Notation "'default' : { A }" := (default A) (at level 96).
Notation "'case' ( A ) : { B }" := (case A B) (at level 96).
Notation "'switch' ( A ) : { B } " := (switch A (cons B nil)) (at level 97).
Notation "'switch' ( A ) : { B1 ; B2 ; ... ; Bn }" := (switch A (cons B1 (cons B2 .. (cons Bn nil) ..))) (at level 97).

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Inductive eval : Stmt -> Env -> Env -> Prop :=
  | e_nat_decl: forall a i x sigma sigma',
                a =[ sigma ]=> i ->
                sigma' = (update sigma x (res_nat i)) ->
                (x :n= a) -{ sigma }-> sigma'
  | e_nat_assign: forall a i x sigma sigma',
                  a =[ sigma ]=> i ->
                  sigma' = (update sigma x (res_nat i)) ->
                  (x :n= a) -{ sigma }-> sigma'
  | e_bool_decl: forall a i x sigma sigma',
                 a ={ sigma }=> i ->
                 sigma' = (update sigma x (res_bool i)) ->
                 (x :b= a) -{ sigma }-> sigma'
  | e_bool_assign: forall a i x sigma sigma',
                   a ={ sigma }=> i ->
                   sigma' = (update sigma x (res_bool i)) ->
                   (x :b= a) -{ sigma }-> sigma'
  | e_str_decl: forall a i x sigma sigma',
                a ={ sigma }=> i ->
                sigma' = (update sigma x (res_str i)) ->
                (x :s= a) -{ sigma }-> sigma'
  | e_str_assign: forall a i x sigma sigma',
                  a ={ sigma }=> i ->
                  sigma' = (update sigma x (res_str i)) ->
                  (x :s= a) -{ sigma }-> sigma'
  | e_seq: forall s1 s2 sigma sigma1 sigma2,
           s1 -{ sigma }-> sigma1 ->
           s2 -{ sigma1 }-> sigma2 ->
           (s1 ;; s2) -{ sigma }-> sigma2
  | e_if_then: forall b s sigma,
               ifthen b s -{ sigma }-> sigma
  | e_if_then_elsetrue: forall b s1 s2 sigma sigma',
                        b ={ sigma }=> true ->
                        s1 -{ sigma }-> sigma' ->
                        ifthenelse b s1 s2 -{ sigma }-> sigma' 
  | e_if_then_elsefalse: forall b s1 s2 sigma sigma',
                         b ={ sigma }=> false ->
                         s2 -{ sigma }-> sigma' ->
                         ifthenelse b s1 s2 -{ sigma }-> sigma' 
  | e_whilefalse: forall b s sigma,
                  b ={ sigma }=> false ->
                  while b s -{ sigma }-> sigma
  | e_whiletrue: forall b s sigma sigma',
                 b ={ sigma }=> true ->
                 (s ;; while b s) -{ sigma }-> sigma' ->
                 while b s -{ sigma }-> sigma'
  | e_switch: forall a i c b s sigma sigma', (* I don't know if this is correct *)
              a ={ sigma }=> i ->
              b = (Nat.eqb i c) ->
              switch b s -{ sigma }-> sigma'
  where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

Fixpoint eval_fun (s : Stmt) (env : Env) (gas: nat) : Env :=
    match gas with
      | 0 => env
      | S gas' => match s with
                    | sequence S1 S2 => eval_fun S2 (eval_fun S1 env gas') gas'
                    | nat_decl a aexp => update (update env a default) a (res_nat (aeval_fun aexp env))
                    | bool_decl b bexp => update (update env b default) b (res_bool (beval_fun bexp env))
                    | str_decl s sexp => update (update env s default) s (res_str (seval_fun sexp env))
                    | nat_assign a aexp => update env a (res_nat (aeval_fun aexp env))
                    | bool_assign b bexp => update env b (res_bool (beval_fun bexp env))
                    | str_assign s aexp => update env s (res_str (seval_fun sexp env))
                    | ifthen cond s' => match (beval_fun cond env) with
                                          | error_bool => env
                                          | boolean v => match v with
                                                           | true => eval_fun s' env gas'
                                                           | false => env
                                                         end
                                        end
                    | ifthenelse cond S1 S2 => match (beval_fun cond env) with
                                                 | error_bool => env
                                                 | boolean v  => match v with
                                                                   | true => eval_fun S1 env gas'
                                                                   | false => eval_fun S2 env gas'
                                                                 end
                                               end
                    | while cond s' => match (beval_fun cond env) with
                                         | error_bool => env
                                         | boolean v => match v with
                                                          | true => eval_fun (s' ;; (while cond s')) env gas'
                                                          | false => env
                                                        end
                                       end
                    | switch cond s' => match (beval_fun cond env with
                                          | (* I am stuck *)
                  end
    end.

Definition while_stmt :=
    Nat "i" ::= 0 ;;
    Nat "sum" ::= 0 ;;
    while 
        ("i" <' 6) 
        (
           "sum" n= "sum" +' "i" ;;
           "i" n= "i" +' 1
        ).

Compute (eval_fun while_stmt env 100) "sum".

Definition for_stmt :=
    Nat "sum" ::= 0 ;;
    fordo ( Nat "i" ::= 0 -- "i" <' 6 -- "i" n= "i" +' 1 ) {
      "sum" n= "sum" +' "i"
    }.

Compute (eval_fun for_stmt env 100) "sum".