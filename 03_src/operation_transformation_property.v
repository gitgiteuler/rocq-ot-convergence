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

(* 削除した要素の位置情報xを持つdeleted_elem型を導入 *)
Inductive deleted_elem (A : Type) : Type :=
 | Deleted (x : A) (l : list A)
 | Error.

Fixpoint delete (A : Type) (p : nat) (x : A) (l : list A) `{Eq A} : deleted_elem A :=
  (* TODO: リストの位置pの要素と削除する文字x の等価性判定を実装する *)
  match p, l with
  | 0, h :: t => Deleted A h t
  | 0, [] => Error A
  | S p', h :: t =>
      match delete A p' x t with
      | Deleted _ x l'  => Deleted A x (h :: l')
      | Error _  => Error A
      end
  | S p', [] => Error A
  end.

Compute delete nat 0 1 [1;2;3].
Compute delete nat 5 3 [1;2;3]. (* リストの長さ以上の要素に対する操作に対して、"None"を返す*)
Compute delete bool 0 true [true;false;true].
Compute delete bool 0 true [false;false;false]. 

(* 操作の型を定義する型コンストラクタ *)
Inductive Op (A : Type) :=
 | OpIns : nat -> A -> list A -> Op A
 | OpDel : nat -> A -> list A -> Op A.

Inductive op_handle_dif_type (A : Type) : Type :=
 | OpInsHandle (result : option (list A))
 | OpDelHandle (result : deleted_elem A).

(* 操作に対して、解釈関数interp_op を定義 *)
Definition interp_op (A : Type) (op : Op A) (l : list A) `{Eq A} : op_handle_dif_type A :=
  match op with
  | OpIns _ p x l' => OpInsHandle A (insert _ p x l')
  | OpDel _ p x l' => OpDelHandle A (delete _ p x l')
  end.

(* 操作間の変換関数it_op を定義 *)
(*Definition it_op :=*)

(* delete の引数に削除する文字xを追加することで元のデータに戻れるようにする必要がある*)
(* しかし、そうなるとEq型クラスで要素の等価性を調べることができるような実装が必要*)
(* p365で用いられるunit型 ならその実装が不要。*)

Definition flip {A B C : Type} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

(* 2つの操作が逆に適用された場合に関数interp を適用するための関数 *)
(** ここでは bind を用いずに記述しているが変更可 **)
(** 部分適用の形で型を明示的に記述 **)
Definition exec_all (f : C -> X -> option X) : list C -> option X -> option X :=
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