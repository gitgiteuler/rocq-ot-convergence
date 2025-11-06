(* 新しい型Op Bを定義する *)
Inductive Op_isd (B : Type) :=
 | OpIns : nat -> B -> Op_isd B
 | OpDel : nat -> B -> Op_isd B.

(* op1, op2 の操作の優先度（順番）を表す値が必要 => サイトID（sid）を使う？ *)
Definition it_op_pair {B : Type} `{Eq B} (op1 op2 : Op A) : list (Op A) :=
  match op1, op2 with
  | Ins p1 x1, Ins p2 x2 => if Nat.ltb p1 p2 then [Ins p1 x1]
                            else if Nat.ltb p2 p1 then [Ins (p1 + 1) x1]
                            else (* p1 == p2 位置の競合が起きる場合 *)
                              if 
  | Ins p1 x1, Del p2 x2 => if 
  | Del p1 x1, Ins p2 x2 => if 
  | Del p1 x1, Del p2 x2 => if 
  end.
