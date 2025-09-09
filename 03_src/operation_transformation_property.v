Require Import Arith.
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.

Check (1 ::2:: 3 :: []).

Context {A B C : Type} {X : Type}.

Definition flip {A B C : Type} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

(* 2つの操作が逆に適用された場合に関数interp を適用するための関数 *)
(** ここでは bind を用いずに記述しているが変更可 **)
Definition exec_all (f : C -> X -> option X) : list C -> option X -> option X :=
  List.fold_left (flip (fun c acc => 
    match acc with
     | None => None
     | Some x => f c x
    end
  )).

(*Definition g x y : nat := 
  Nat.add (x * 3) y.

Definition h x : nat -> nat :=
  Nat.add (x * 3).

Compute g 1 2.
Compute h 1 2.
*)

(* exec_all の型、定義する際には型を一部明示せずともいいってこと？
 exec_all
     : (C -> X -> option X) -> list C -> option X -> option X 
*)

Check exec_all.

Definition test_exec_all_nat (op : nat -> nat) (x : nat) : nat :=
  exec_all (fun op x => Some (op x))

Compute exec_all 

Class OTBase (X cmd : Type) :=
 {
   interp : cmd -> X -> option X;
   it : cmd -> cmd -> bool -> list cmd;
   it_c1 : forall (op1 op2 : cmd) (f : bool) m (m1 m2 : X),
     interp op1 m = Some m1 -> interp op2 m = Some m2 ->
      let m21 := 
 }

(*Inductive op :=
|Int : nat -> nat -> list nat -> list nat
|Del : nat  -> list nat -> list nat.
 *)
Print option.

Fixpoint Ins (p x : nat) (l : list nat) : option (list nat) :=
  match p, l with
  | 0, _ => Some (x :: l)
  | S p', [] => None
  | S p', h :: t =>
      match Ins p' x t with
      | None => None
      | Some l' => Some ( h :: l')
      end
  end.
  
Compute Ins 0 9 [1].
Compute Ins 9 1 [1;2;3].
Compute Ins 2 9 [1;2;3;4].

(* パターンマッチの演習 *)
Definition head (A : Type) (l : list A) : option A :=
  match l with
  | x :: _ => Some x
  | [] => None
  end.

Compute head nat [1;2;3].

Definition rtn_bind_value (x y : nat) : option nat :=
  match y with
  | 0 => None
  | S y' => Some (y') 
  end.

Compute rtn_bind_value 10 2. (* yに2が渡されて、2はS 1にとパターンマッチする。-> y'に1が束縛される *)
Compute rtn_bind_value 10 3.
Compute rtn_bind_value 10 4.

Definition safe_div (x y : nat) : option nat :=
  match y with
  | 0 => None (* unable to divide *)
  | S y' => Some (x / S y')
  end.

Compute safe_div 10 2.
  
Fixpoint Del (p : nat) (l : list nat) : option (list nat) :=
  match p, l with
  | 0, _ :: t => Some t
  | 0, [] => None
  | S p', h :: t =>
      match Del p' t with
      | Some l'  => Some (h :: l')
      | None  => None
      end
  | S p', [] => None
  end.

Compute Del 0 [1;2;3].
Compute Del 0 [].
Compute Del 2 [1;2;3].
Compute Del 5 [1;2;3].






  
