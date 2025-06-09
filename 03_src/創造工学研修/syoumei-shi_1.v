Definition x := 1.
Check x.
Print x.

Definition y := 1 + 1.
Print y.
Compute y.

Definition z : nat := 1 + 1.
Check z.

(*入力xに3を足して返す関数*)
Definition plus3(x:nat) : nat := x + 3.
Check plus3.
Compute (plus3 8).

(*Coqには強力な形推論があるので型を省略することもできる*)
(*入力xを3倍して返す関数*)
Definition triple x := x * 3.
Check triple.
Compute (triple 34).

Theorem easy_thm:
  forall (A:Prop), A -> A.
  (*全ての命題Aに対して、AならばAが成り立つ*)
Proof.
  intro B.
  intro G.
  apply G.
Qed.

Theorem easy_app:
  forall (A:Prop)(B:Prop),
    A /\ (A -> B) -> B.
Proof.
  intro A.
  intro B.
  intro H. (* -> の左側を仮定する*)
  destruct H. (*P/\Qを分解する*)
  apply H0.
  apply H.
Qed.

Theorem example_1:
  forall (A:Prop)(B:Prop),
    A -> (A -> B) -> B.
Proof.
  intro A.
  intro B.
  intro H.
  intro H0.
  apply H0.
  apply H.
Qed.

Theorem example_2:
  forall (A:Prop)(B:Prop)(C:Prop),
    (A -> B) -> (B -> C) ->  (A -> C).
Proof.
  intro A.
  intro B.
  intro C.
  intro H.
  intro H0.
  intro H1.
  apply H0.
  apply H.
  apply H1.
Qed.

Theorem example_1':
  forall (A:Prop)(B:Prop),
    A -> (A -> B) -> B.
Proof.
  intro A.
  intro B.
  intro H.
  intro H0.
  apply H0 in H.
  apply H.
Qed.

Theorem example_3:
  forall (A:Prop)(B:Prop),
    A /\ (A -> B) -> B.
Proof.
  intro A.
  intro B.
  intro H.
  destruct H.
  apply H0.
  apply H.
Qed.

Theorem example_4:
  forall (A:Prop)(B:Prop)(C:Prop),
    (A -> B) /\ (B -> C) /\ A -> C.
Proof.
  intro A.
  intro B.
  intro C.
  intro H.
  destruct H.
  destruct H0.
  apply H0.
  apply H.
  apply H1.
Qed.

Theorem example_5:
  forall (A:Prop)(B:Prop),
    A /\ B -> B /\ A.
Proof.
  intro A.
  intro B.
  intro H.
  destruct H.
  split.
  apply H0.
  apply H.
Qed.

Theorem example_6:
  forall (A:Prop),
    (A \/ A) -> A.
Proof.
  intro A.
  intro H.
  destruct H.
  apply H.
  apply H.
Qed.

Theorem example_7:
  forall (A:Prop)(B:Prop),
    A -> (A \/ B).
Proof.
  intro A.
  intro B.
  intro H.
  left.
  apply H.
Qed.

Theorem example_8:
  forall (A:Prop)(B:Prop),
    (A \/ B) -> (B \/ A).
Proof.
  intro A.
  intro B.
  intro H.
  destruct H.
  right.
  apply H.
  left.
  apply H.
Qed.
