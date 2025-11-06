Class Eq (A : Type) := { eqb : A -> A -> bool }.

Instance eqNat : Eq nat := { eqb := Nat.eqb }.

Compute eqb 1 1.

Class Le (A : Type) := { le : A -> A -> bool}.

Fixpoint le_nat (x y : nat) : bool :=
 match x with
 | 0 => match y with
        | 0 => false
        | S _ => true
        end
 | S x' => match y with
           | 0 => false
           | S y' => le_nat x' y'
           end
end. 

Instance leNat : Le nat := 
  { 
    le := le_nat
  }.

Compute le 1 2.
Compute le 1000 1001.

Fixpoint plus (m n : nat) :=
  match m with
  | 0 => n
  | S m' => S (plus m' n)
  end.

Compute plus 129 457.

Fixpoint mult (m n : nat) :=
  match m with
  | 0 => 0
  | S m' => plus n (mult m' n)
  end.

Compute mult 25 25.
