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
Fixpoint insert (A : Type) (p : nat) (x : A) (l : list A) : option (list A) :=
  match p, l with
  | 0, _ => Some (x :: l)
  | S p', [] => None
  | S p', h :: t =>
      match insert A p' x t with
      | None => None
      | Some l' => Some ( h :: l')
      end
  end.
  
Compute insert nat 0 9 [1].
Compute insert bool 2 true [false;false;false].

Fixpoint delete (A : Type) (p : nat) (x : A) (l : list A) `{Eq A} : option (list A) :=
  match p, l with
  | 0, h :: t => if eqb h x then Some t else None
  | 0, [] => None
  | S p', h :: t =>
      match delete A p' x t with
      | Some t'  => Some (h :: t')
      | None  => None
      end
  | S p', [] => None
  end.

Compute delete nat 0 1 [1;2;3].
Compute delete nat 5 3 [1;2;3]. (* リストの長さ以上の要素に対する操作に対して、"None"を返す*)
Compute delete bool 0 true [true;false;true].
Compute delete bool 0 true [false;false;false]. 

(* 操作の型 (Op) を定義。各コンストラクタは、操作に必要な情報（位置と値）を保持する *)
Inductive Op (A : Type) :=
 | OpIns : nat -> A ->  Op A
 | OpDel : nat -> A -> Op A.

(* 操作opをリストlを適用する関数 *)
Definition interp_op (A : Type) `{Eq A}  (op : Op A) (l : list A) : option (list A) :=
  match op with
  | OpIns _ p x => insert _ p x l
  | OpDel _ p x => delete _ p x l
  end.

(* ある操作に対して、その逆の操作を行う関数 *)
Definition inv_op (A : Type) (op : Op A) `{Eq A}  (l : list A) : option (list A) :=
  match op with
  | OpIns _ p x  => delete _ p x l
  | OpDel _ p x => insert _ p x l
  end.

Definition list_ex := (1 :: 2 :: 3 :: []).
Compute (interp_op nat (OpIns nat 0 0) list_ex). (* => [0; 1; 2; 3] *)
Compute (inv nat (OpIns nat 0 0) list_ex). (* => 対象のリストに対して、"p番目の要素=文字x"でないと"None"を返す *)
Compute (inv nat (OpIns nat 0 1) list_ex). (* => [2; 3] *)


TODO:操作間の変換関数it_op を定義
Definition it_op (A : Type) (op1 op2 : Op A) (l : list A) : option (list A) :=


(* p365で用いられるunit型 ならその実装が不要。*)

Definition flip {A B C : Type} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

(* 2つの操作が逆に適用された場合に関数interp を適用するための関数 *)
(** ここでは bind を用いずに記述しているが変更可 **)
(** 部分適用の形で型を明示的に記述 **)
Definition exec_all (op : Op A) (f : op -> X -> option X) : list C -> option X -> option X :=
  List.fold_left (flip (fun c acc => 
    match acc with
     | None => None
     | Some x => f c x
    end
  )).

Class OTBase (X cmd : Type) :=
 {
   interp : cmd -> X -> option X;
   it : cmd -> cmd -> bool -> list cmd;
   it_c1 : forall (op1 op2 : cmd) (f : bool) m (m1 m2 : X),
      interp op1 m = Some m1 -> interp op2 m = Some m2 ->
        let m21 := 
 }

Class OTInv (X cmd : Type) :=
 {
  inv : cmd -> com
  ip1 : forall (op s s1), 
      interp op s = Some s1 -> interp (inv op) s1 = Some s
 }.