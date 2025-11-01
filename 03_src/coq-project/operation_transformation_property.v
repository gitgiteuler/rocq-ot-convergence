Require Import Arith.
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.
From OTRocq Require Import OtDef.

Check (1 ::2:: 3 :: []).

Class Eq A := {eqb : A -> A -> bool}.

Notation "x =? y" := (eqb x y).

Instance eqNat : Eq nat := {eqb := Nat.eqb}.

Instance eqBool : Eq bool := {eqb := Bool.eqb}.

Compute (eqb 1 1).
Compute (eqb 1 2).
Compute (eqb true false). 

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
Definition interp_op [A : Type] `{Eq A} (op : Op A) (l : list A) : option (list A) :=
  match op with
  | OpIns p x => insert p x l
  | OpDel p x => delete p x l
  end.

About interp_op.

Arguments interp_op {A} {H} op l.

(* ある操作に対して、その逆の操作を行う関数 *)
Definition inv_op [A : Type] `{Eq A} (op : Op A) : Op A :=
  match op with
  | OpIns p x  => OpDel p x
  | OpDel p x => OpIns p x
  end.

Compute inv_op (OpIns 1 2).

Definition it_sc {A : Type} `{Eq A} (op1 op2 : Op A) (f : bool) : list(Op A) :=
  (* f=true の場合はクライアント優先、f=false の場合はサーバ優先 *)
  if f then []
  (* f=falseの時、サーバの操作を優先するため、まずクライアントの操作op2を逆操作で元に戻し（inv op2）、その後サーバの操作op1を適用する。
     これにより、サーバ側の状態を優先しつつ、クライアントの操作が競合した場合でも一貫性を保つことができる。操作順序は「クライアントの操作を巻き戻してからサーバの操作を適用する」ことを意図している。*)
  else [inv_op op2 ; op1]. 

Compute it_sc (OpIns 1 1) (OpIns 2 2) true.
Compute it_sc (OpIns 1 1) (OpIns 2 2) false.

Compute Nat.ltb 1 2. (* 1 < 2 と言う命題が”真” *)
Compute S 0.
Compute Nat.eqb (S 0) 1.

(* 全ての操作をリストに適用する関数 *)
Fixpoint exec_all_op [A : Type] `{Eq A} (ops : list(Op A)) (l : list A): option (list A) :=
  match ops with
   | [] => Some l
   | op :: t => match interp_op op l with
                        | Some l' =>  exec_all_op t l'
                        | None => None
                        end
  end.

Lemma ot_convergence_property_c1 (A : Type) `{Eq A} :
  forall (op1 op2 : Op A) (f : bool) m (m1 m2 : list A),
    interp_op op1 m = Some m1 ->
    interp_op op2 m = Some m2 ->
    let m21 := (exec_all interp_op) (Some m2) (it_sc op1 op2 f) in
    let m12 := (exec_all interp_op) (Some m1) (it_sc op2 op1 (negb f)) in
      m21 = m12 /\ exists node, m21 = Some node.
Proof.
  intros.
  split.
  unfold m21, m12.
  unfold it_sc.
  unfold inv_op.
  destruct f.
  (* f=true*の時 *)
    simpl.
    rewrite <- H1.
    unfold interp_op.
    unfold Basics.flip.
    unfold Commons.bind.
    destruct op2.
      (* op2 = insertの時 *)
      destruct op1.
        (* op1 = insertの時 *)
        destruct (delete n0 a0 m1).
          (* delete n0 a0 m1について場合分け *)
          assert (H_eqml : m=l).
          admit. 
          rewrite H_eqml.
          reflexivity.
          
        (* op1 = deleteの時 *)
      (* op2 = deleteの時 *)
        (* op1 = insertの時 *)
        
        (* op1 = deleteの時 *)
Admitted.

Instance OTBaseListSC {A : Type} `{Eq A} : OTBase (list A) (Op A) :=
{
  interp := interp_op;
  it := it_sc;
  it_c1 := fun op1 op2 f m m1 m2 =>
          ot_convergence_property_c1 A op1 op2 f m m1 m2;
}.

(* TODO:型クラスOTInv のインスタンスの作成に必要な補題ot_inv_propertyの証明 *)
Class OTInv [A : Type] `{Eq A} :=
{
  inv := @inv_op 
  ip1 : forall op m mr, interp op m = Some mr -> interp (inv op) mr = (Some m)
}.

(* TODO:型クラスOTInv のインスタンスの作成 -> 証明 *)