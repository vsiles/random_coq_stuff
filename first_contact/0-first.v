(* Noob IDE, not the best one but ok to start:
  CoqIDE:
  https://github.com/coq/coq/releases/tag/V8.10.1
*)

(* Chapter 1: Very basic logical stuff *)
Lemma l1: forall A, A -> A.
Proof.
intro A.
intro a.
exact a.
Qed.

Lemma l1bis: forall A, A -> A.
Proof.
tauto. (* intuition / firstorder *)
Qed.

Lemma l2: forall A B, A /\ B -> A.
Proof.
intros A B ab.
destruct ab as [a b].
exact a.
Qed.

Lemma l3: forall (A B C: Prop), (A -> C) -> (B -> C) -> (A \/ B -> C).
Proof.
intros A B C hac hbc hab.
destruct hab as [ha | hb].
- apply hac.
  assumption.
- now apply hbc.
Qed.

Lemma l3bis: forall (A B C: Prop), (A -> C) /\ (B -> C) -> (A \/ B -> C).
Proof.
intros A B C h; now apply l3.
Qed.

(* Chapter 2: Some user definitions *)
Definition NOT (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Lemma l4: forall b, NOT (NOT b) = b.
Proof.
intros []; simpl.
reflexivity.
reflexivity.
Qed.

Lemma l5: forall n m, (1 + n) + m = 1 + (n + m).
Proof.
intros n m; reflexivity.
Qed.

Require Import Arith.

Lemma l6: forall n m, n + (1 + m) = 1 + (n + m).
Proof.
intros n m.
Fail reflexivity.
auto with arith.
Qed.

(* This is only syntactic sugar for inductive type with single constructor *)
Record some_struct := mk_some_struct {
    x: nat;
    y: bool;
}.

Check x.
Check y.
Check mk_some_struct.

(* Chapte 3: inductive types *)
Inductive same_struct :=
 | mk_some_struct2 : nat -> bool -> same_struct
.

Definition x2 s :=
    match s with
    | mk_some_struct2 n _ => n
    end.

Definition y2 s :=
    match s with
    | mk_some_struct2 _ b => b
    end.

Check mk_some_struct2.
Check x2.
Check y2.

Inductive myList A :=
 | NIL : myList A
 | CONS : A -> myList A -> myList A
.

Fixpoint myLength A (l: myList A) :=
    match l with
    | NIL _ => 0
    | CONS _ _ tl => 1 + myLength _ tl
    end.

Fail Fixpoint myLength_fail A (l: myList A) := 
    match l with
    | NIL _ => 0
    | CONS _ _ _ => 1 + myLength_fail _ l
    end.

Fail Fixpoint myLength_fail A (l: myList A) { struct l } :=
    match l with
    | NIL _ => 0
    | CONS _ _ _ => 1 + myLength_fail _ l
    end.

Fixpoint myMap A B (f : A -> B) (l: myList A) :=
    match l with
    | NIL _ => NIL _
    | CONS _ hd tl => CONS _ (f hd) (myMap _ _ f tl)
    end.

Lemma myLengthMap: forall A B (f: A -> B) (l: myList A),
    myLength _ (myMap _ _ f l) = myLength _ l.
Proof.
intros A B f.
induction l as [ | hd tl hi].
- simpl.
  reflexivity.
- simpl.
  rewrite hi.
  reflexivity.
Qed.
