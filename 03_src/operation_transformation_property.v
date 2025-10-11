Require Import Arith.
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.

Check (1 ::2:: 3 :: []).

Class Eq A :=
  {
    eqb : A -> A -> bool
  }.

Notation "x =? y" := (eqb x y).

Instance eqNat : Eq nat :=
 {
  eqb := Nat.eqb
 }.

Instance eqBool : Eq bool :=
 {
  eqb := Bool.eqb
 }.

Context {A: Type} `{Eq A}.


(* 任意の型Aに対して関数Ins を定義*)
Fixpoint insert [A : Type] (p : nat) (x : A) (l : list A) : option (list A) :=
  match p, l with
  | 0, _ => Some (x :: l)
  | S p', [] => None
  | S p', h :: t =>
      match insert p' x t with
      | None => None
      | Some l' => Some ( h :: l')
      end
  end.
  
Compute insert 0 9 [1].
Compute insert 2 true [false;false;false].

Fixpoint delete [A : Type] (p : nat) (x : A) (l : list A) `{Eq A} : option (list A) :=
  match p, l with
  | 0, h :: t => if eqb h x then Some t else None
  | 0, [] => None
  | S p', h :: t =>
      match delete p' x t with
      | Some t'  => Some (h :: t')
      | None  => None
      end
  | S p', [] => None
  end.

Compute delete 0 1 [1;2;3].
Compute delete 5 3 [1;2;3]. (* リストの長さ以上の要素に対する操作に対して、"None"を返す*)
Compute delete 0 true [true;false;true].
Compute delete 0 true [false;false;false]. 

(* 操作の型 (Op) を定義。各コンストラクタは、操作に必要な情報（位置と値）を保持する *)
Inductive Op (A : Type) :=
 | OpIns : nat -> A ->  Op A
 | OpDel : nat -> A -> Op A.

About OpIns.

Arguments OpIns [A%_type_scope] _%_nat_scope _.
Arguments OpDel [A%_type_scope] _%_nat_scope _.

(* 操作opをリストlを適用する関数 *)
Definition interp_op [A : Type] `{Eq A}  (op : Op A) (l : list A) : option (list A) :=
  match op with
  | OpIns p x => insert p x l
  | OpDel p x => delete p x l
  end.

(* ある操作に対して、その逆の操作を行う関数 *)
Definition inv_op [A : Type] `{Eq A} (op : Op A) : Op A :=
  match op with
  | OpIns p x  => OpDel p x
  | OpDel p x => OpIns p x
  end.

Definition list_ex := (1 :: 2 :: 3 :: []).
Compute (interp_op (OpIns 0 0) list_ex). (* => [0; 1; 2; 3] *)
Compute (inv_op (OpIns 0 0)).  
Compute (inv_op (OpDel 0 1)).

Definition it_op_sc {A : Type} `{Eq A} (op1 op2 : Op A) (f : bool) : list(Op A) :=
  if f then [] (* f=trueの時、空リストを返す *)
  else [inv_op op2 ; op1]. (* f=falseの時、サーバの操作を優先する為、クライアントの操作op2を戻して、op1を行うという操作のリストを返す *) 

(* 全ての操作をリストに適用する関数 ins->insなど *)
(** リストlに対して、操作のリストから操作を一つずつ適用する **)
Fixpoint exec_all [A : Type] `{Eq A} (ops : list(Op A)) (l : list A): option (list A) :=
  match ops with
   | [] => Some l
   | op :: t => match interp_op op l with
                        | Some l' =>  exec_all t l'
                        | None => None
                        end
  end. 

Class OTBase (X cmd : Type) := 
{
 interp_op : cmd -> X -> option X;
 it_op    : cmd -> cmd -> bool -> list cmd;
 it_c1 : forall (op1 op2 : cmd) (f : bool) (m m1 m2 : X),
  interp_op op1 m = Some m1 -> interp_op op2 m = Some m2 -> 
  let m21 := (exec_all interp_op) (Some m2) (it_op op1 op2 f) in
   let m12 := (exec_all interp_op) (Some m1) (it_op op2 op1 (~~f)) in
    m21 = m12 /\ exists node, m21 = Some node
}.

Instance OTBaseListSC [A : Type] : OTBase (list A) (Op A) :=
{
  interp_op : Op A -> list A -> option(list A);
  it_op : Op A -> Op A -> bool -> list(Op A);
  it_c1 : forall (op1 op2 : Op A) (f : bool) (m m1 m2 : list A),
  interp_op op1 m = Some m1 -> interp_op op2 m = Some m2 -> 
  let m21 := (exec_all interp_op) (Some m2) (it_op op1 op2 f) in
   let m12 := (exec_all interp_op) (Some m1) (it_op op2 op1 (~~f)) in
    m21 = m12 /\ exists node, m21 = Some node
}


Class OTInv (A : Type) (op : Op A) (l : list A) :=
 {
  inv_op : Op A -> Op A
  ip1 : forall (l1 : list A) (op l l1), 
    interp_op op s = Some l1 -> interp_op (inv_op op) l1 = Some l
 }.