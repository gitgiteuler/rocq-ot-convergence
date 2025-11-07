Require Import Arith.
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.
From OTRocq Require Import OtDef.

Check (1 ::2:: 3 :: []).

Class Eq A := {
  eqb : A -> A -> bool;
  eqb_refl : forall (x : A), eqb x x = true;
  (*eqP : forall (x y : A), (eqb x y = true) = (x = y)*)
}.

Notation "x =? y" := (eqb x y).

Instance eqNat : Eq nat := 
{
  eqb := Nat.eqb;
  eqb_refl := Nat.eqb_refl;
  (*eqP := fun x y => if eqb x y then (x = y) else (x  y)*)
}.

Instance eqBool : Eq bool := 
{
  eqb := Bool.eqb;
  eqb_refl := fun x => match x with
                       | true => eq_refl
                       | false => eq_refl
                       end
}.

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

Lemma insert_delete_inverse (A : Type) `{Eq A}:
  forall (p : nat) (x : A) (l l' : list A),
    insert p x l = Some l' -> delete p x l' = Some l.
Proof.
  induction p as [ | p'].
  (* p = 0 *)
    intros x l l' H_ins.
    simpl in H_ins.
    inversion H_ins. (* Some (x :: l) = Some l'から中身の等価性を示す*)
    simpl.
    rewrite eqb_refl.
    reflexivity.
  (* p = S p' *)
    intros x l l' H_ins_sp'.
    destruct l.
    (* l = [] *)
    simpl in H_ins_sp'.
    discriminate.
    (* l = a :: l *)
    simpl in H_ins_sp'.
    destruct (insert p' x l) eqn:H_ins_p'.
    rename l0 into l''.
      (* Some l'' *)
      inversion H_ins_sp'.
      simpl.
      specialize (IHp' x l l'' H_ins_p').
      rewrite IHp'.
      reflexivity.
      (* None *)
      simpl.
      discriminate.
Qed.

(* TODO:合流性c1の証明に必要な補題ip1の証明 *)
Lemma ot_inverse_property_ip1 (A : Type) `{Eq A} :
  forall op m mr, interp_op op m = Some mr ->
   interp_op (inv_op op) mr = Some m.
Proof.
  intros op m mr H_op.
  destruct op.
  (* op = OpIns n aの場合 *)
    unfold inv_op.
    unfold interp_op.
    induction n as [| n' IHn'].
    (* n = 0 の場合*)
      simpl in H_op.
      injection H_op as H_eq.
      subst mr.
      simpl.
      destruct (a =? a) eqn:Heq.
      (* a = a *)  
        reflexivity.
      (* a != a *)
        exfalso.
        assert (H_refl : a =? a = true) by apply eqb_refl.  
        rewrite Heq in H_refl.
        discriminate H_refl.
    (* n = S n' の場合*)
      destruct m as [| h t].
      (* m = [] *)
        discriminate H_op.
      (* m = h :: t *)
        destruct mr as [| h' t'].
        (* mr が空リストの場合 *)
          simpl in H_op.
          destruct (insert n' a t).
          inversion H_op.
          (*discriminate H_op.*)
        (* mr = h' :: t' の場合 *)
          simpl in H_op.
          destruct (insert n' a t).
          discriminate H_op.
          discriminate H_op.
          (* Some l' *)
          simpl in *.
          simpl in H_op.
          destruct (insert n' a t).
          injection H_op as Hh' Ht'.
          subst.
          simpl.
          (* 証明で行き詰まっている箇所 *)

    (* op = OpDel n aの場合 *)

Instance otInvProperty {A : Type} `{Eq A} : 

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
    rewrite <- H1.
    simpl.
    unfold Basics.flip.
    unfold Commons.bind.
    destruct op1.
      destruct (interp_op (OpDel n a) m1) as [m' | ].
      (*rewrite ot_inverse_property_ip1.*)


Admitted.

Instance OTBaseListSC {A : Type} `{Eq A} : OTBase (list A) (Op A) :=
{
  interp := interp_op;
  it := it_sc;
  it_c1 := fun op1 op2 f m m1 m2 =>
          ot_convergence_property_c1 A op1 op2 f m m1 m2;
}.

(* TODO:型クラスOTInv のインスタンスの作成 -> 証明 *)