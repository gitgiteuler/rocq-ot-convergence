Require Import Arith.
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.
From OTRocq Require Import OtDef.

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

(*Context {A: Type} `{Eq A}.*)


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

Compute it_op_sc (OpIns 1 1) (OpIns 2 2) true.
Compute it_op_sc (OpIns 1 1) (OpIns 2 2) false.

Compute Nat.ltb 1 2. (* 1 < 2 と言う命題が”真” *)
Compute S 0.
Compute Nat.eqb (S 0) 1.

(* op1, op2 の操作の優先度（順番）を表す値が必要 => サイトID（sid）を使う？ *)
(*Definition it_op_pair {A : Type} `{Eq A} (op1 op2 : Op A) : list (Op A) :=
  match op1, op2 with
  | Ins p1 x1, Ins p2 x2 => if Nat.ltb p1 p2 then [Ins p1 x1]
                            else if Nat.ltb p2 p1 then [Ins (p1 + 1) x1]
                            else (* p1 == p2 位置の競合が起きる場合 *)
                              if 
*)


(* 全ての操作をリストに適用する関数 *)
Fixpoint exec_all_op [A : Type] `{Eq A} (ops : list(Op A)) (l : list A): option (list A) :=
  match ops with
   | [] => Some l
   | op :: t => match interp_op op l with
                        | Some l' =>  exec_all_op t l'
                        | None => None
                        end
  end.

(* 一時的にOtDevから引用しているコード *) 
(** foldl を fold.left に変更 **)
(*Context {C : Type} {X : Type}.*)
(*Definition exec_all (f : C -> X -> option X) := fold_left (flip (fun c => bind (f c))).*)

Compute exec_all_op [OpIns 0 0 ; OpDel 1 1 ; OpDel 1 2] [1;2;3].

Check OTBase.

Instance OTBaseListSC {A : Type} `{Eq A} : OTBase (list A) (Op A) :=
{
  interp := @interp_op A _;
  it := @it_op_sc A _;
  it_c1 :=
    fun (op1 op2 : Op A) (f : bool) (m m1 m2 : list A)
        (H1 : interp_op op1 m = Some m1)
        (H2 : interp_op op2 m = Some m2) =>

        let m21 := exec_all_op (it_op_sc op1 op2 f) m2 in
        let m12 := exec_all_op (it_op_sc op2 op1 (negb f)) m1 in
        
        (* 証明のスキップ *)
        admit
}.

Class OTInv [A : Type] `{Eq A} :=
{
  inv_op : Op A -> Op A
  ip1 : forall (op : Op A) (l l' : list A), 
    interp_op op l = Some l' -> interp_op (inv_op op) l' = Some l
}.