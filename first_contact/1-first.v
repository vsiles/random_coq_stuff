Require Import Arith.
Require Import Omega.

(* Chapter 4: Primality *)
Definition divides (a b : nat) := 
  exists q, b = a * q.

Notation "x `div y" := (divides x y) (at level 70).

Definition prime (p : nat) :=
  (p <> 1) /\ (forall x, x `div p -> (x = 1) \/ (x = p)).

Remark one_not_prime: ~ prime 1.
Proof.
intros [h1 h2]; now apply h1.
Qed.

Remark two_is_prime: prime 2.
Proof.
split; [now firstorder | ].
intros x [q hq].
destruct x as [ | [ | [ | x ]]]; try now intuition.
destruct q as [ | q]; [ now rewrite mult_0_r in hq | ].
simpl in hq.
injection hq; clear hq; intro hq.
rewrite Nat.add_succ_r in hq.
injection hq; clear hq; intro hq.
now rewrite !Nat.add_succ_r in hq.
Qed.

Lemma divides_refl: forall n, n `div n.
Proof.
intro n; exists 1.
now rewrite mult_1_r.
Qed.

Lemma divides0: forall n, n `div 0.
Proof.
now intro n; eexists; eauto.
Qed.

Remark eq1: forall a b, 1 = a * b -> a = 1 /\ b = 1.
Proof.
intros [ | [ | a]] [ | [ | b]] h; simpl in *;
  try solve [discriminate | firstorder ].
Qed.

Lemma divides1: forall n, n `div 1 <-> n = 1.
Proof.
intro n; split; intro h.
- destruct h as [ q hq ].
  now apply eq1 in hq as [h1 h2].
- subst.
  apply divides_refl.
Qed.

Lemma divides_trans:forall a b c, a `div b -> b `div c -> a `div c.
Proof.
intros a b c [q hq] [p hp].
rewrite hq in hp.
exists (q * p).
rewrite mult_assoc.
exact hp.
Qed.

Lemma divides_add: forall d a b, d `div a -> d `div b -> d `div (a + b).
Proof.
intros d a b [q hq] [p hp].
exists (q + p).
rewrite hq, hp.
SearchAbout mult.
rewrite Nat.mul_add_distr_l.
reflexivity.
Qed.

Lemma divides_sub: forall d a b, d `div a -> d `div b -> d `div (a - b).
Proof.
intros d a b [q hq] [p hp].
exists (q - p).
rewrite hq, hp, Nat.mul_sub_distr_l.
reflexivity.
Qed.

Lemma divides_addl: forall d a b, d `div a -> d `div (a + b) -> d `div b.
Proof.
intros d a b ha hab.
replace b with ((a + b) - a).
- apply divides_sub; assumption.
- auto with arith.
Qed.

Lemma divides_lmul: forall d a x, d `div a -> d `div (x * a).
Proof.
intros d a x [q hq].
exists (q * x).
rewrite hq.
now rewrite mult_comm, mult_assoc.
Qed.

Lemma divides_rmul: forall d a x, d `div a -> d `div (a * x).
Proof.
now intros; rewrite mult_comm; apply divides_lmul.
Qed.

Lemma divides_le: forall m n, m `div n -> (m <= n \/ n = 0).
Proof.
intros m n [q hq]; subst.
destruct q as [ | q].
- now right; auto with arith.
- left.
  rewrite mult_succ_r.
  now auto with arith.
Qed.

Fixpoint factorial (n: nat) : nat :=
  match n with
  | 0 => 1
  | S n => (S n) * (factorial n)
  end.

Lemma factorial_non_zero: forall n, factorial n <> 0.
Proof.
induction n as [ | n hi]; simpl in *; intro h; [ discriminate | ].
apply plus_is_O in h as [h _].
now apply hi.
Qed.

Remark le_lt_eq: forall a b, a <= S b -> a = S b \/ a <= b.
Proof.
intros a b h.
inversion h; subst; clear h.
- now left.
- now right.
Qed.

Lemma divides_fact:forall m n, 0 < m -> m <= n -> 
  m `div (factorial n).
Proof.
intros m; induction n as [ | n hi]; simpl in *; intros hlt hle.
- apply le_n_0_eq in hle; subst.
  apply lt_irrefl in hlt.
  elim hlt.
- apply le_lt_eq in hle as [h | h].
  + subst.
    replace (factorial n + n * factorial n) with
       (S n * factorial n) by (auto with arith).
    apply divides_rmul.
    apply divides_refl.
  + apply divides_add.
    * now apply hi.
    * apply divides_lmul.
      now apply hi.
Qed.

(* I'm going to need to prove that forall n, prime n \/ ~ prime n
   so, without the excluded middle, I need a computational way to
   test if a natural number is prime or not.
   First let's do the "simple" version in classical logic
*)
Require Import Wf.

Lemma prime_factor_with_EM: 
    (forall A: Prop, A \/ ~ A) -> 
    forall n, n <> 1 -> exists p, prime p /\ p `div n.
Proof.
intro EM.
induction n as [ n hi ] using (well_founded_induction lt_wf).
case_eq (n =? 0); intros hn0;
  [ intros _; apply Nat.eqb_eq in hn0; subst;
    exists 2; split; [ apply two_is_prime | apply divides0 ] | ].
apply Nat.eqb_neq in hn0.
intros hn1.
destruct (EM (prime n)) as [hp | hp].
- exists n; split; [ assumption | ].
  now apply divides_refl.
- destruct (EM (exists m, 1 < m /\ m < n /\ m `div n)) as [hd | hd ].
  + destruct hd as [d [h0 [h1 h2]]].
    destruct (hi d h1) as [p [hp1 hp2]]; [now intuition | ].
    exists p; intuition.
    now apply divides_trans with d.
  + elim hp; split; [ assumption | intros x hx].
    case_eq (x =? n); intro hxn; [ now apply Nat.eqb_eq in hxn; right | ].
    case_eq (x =? 0); intro hx0.
    * apply Nat.eqb_eq in hx0; subst.
      destruct hx as [ q hq].
      now rewrite hq; right.
    * case_eq (x =? 1); intro hx1.
      -- apply Nat.eqb_eq in hx1; now left.
      -- apply Nat.eqb_neq in hx0.
         apply Nat.eqb_neq in hx1.
         apply Nat.eqb_neq in hxn.
         elim hd.
         exists x; repeat split; [ now intuition | | assumption ].
         now apply divides_le in hx as [hx | hx]; [ intuition | subst; now elim hn0].
Qed.

Section NoEM.
(*
Now let's avoid EM and build a function to test the primality of natural
numbers. We'll do that by writing a function to perform the division
(there's probably a few in the lib, this is for showing how it's done).
*)

(* Write concrete implementation of division (stollen from ssreflect) *)
Fixpoint divn_rec d m q :=
  match m - d with
  | S x => divn_rec d x (S q)
  | _ => (q, m)
  end.

Lemma divn_rec_unroll : forall d m q, divn_rec d m q =
  match m - d with
  | S x => divn_rec d x (S q)
  | _ => (q, m)
  end.
Proof.
now intros d [] q.
Qed.


(* And its specification *)
Lemma divn_rec_spec: forall d m x,
 let (q, r) := divn_rec d m x in m = (q - x) * (S d) + r /\ x <= q /\ r < S d.
Proof.
intro d; induction m as [m hi] using (well_founded_induction lt_wf); intros x; simpl in *.
rewrite divn_rec_unroll.
case_eq (m - d); [ now intros;  rewrite Nat.sub_diag; firstorder | ].
intros md heq.
assert (hlt: md < m) by omega.
specialize hi with md (S x).
destruct divn_rec as [ q r].
replace m with (d + S md) by now apply Nat.add_sub_eq_nz in heq.
destruct (hi hlt) as [ h [hle hr]].
split; [ | split; [now auto with arith | assumption ]].
rewrite h.
replace ((q - x) * S d) with ((q - S x) * S d + S d).
omega.
replace (q - x) with (S (q - S x)) by omega.
rewrite Nat.mul_succ_l.
reflexivity.
Qed.

(* Main function *)
Definition divn m d := 
 match d with 
 | 0 => (0, m)
 | S d => divn_rec d m 0
end.

Inductive divn_spec m d : nat * nat -> Type :=
  DivnSpec: forall q r, m = q * d + r -> ((d > 0) -> (r < d)) -> divn_spec m d (q, r).

(* And specification *)
Lemma divn_spec_ok m d : divn_spec m d (divn m d).
Proof.
unfold divn.
destruct d as [ | d]; [ now constructor | ].
pose (hrec := divn_rec_spec d m 0).
case_eq (divn_rec d m 0); intros q r heq.
rewrite heq in hrec; destruct hrec as [h1 [h2 h3]].
constructor.
- now rewrite Nat.sub_0_r in h1.
- now intros.
Qed.

(* We now show that divn is equivalent to divides *)
Lemma divn_div: forall m d,
  d `div m <-> (let (q, r) := divn m d in r = 0).
Proof.
intros m d; split; intro h.
- destruct h as [q hq].
  destruct (divn_spec_ok m d) as [k s heq hrem].
  rewrite mult_comm in heq.
  destruct d as [ | d].
  + now simpl in *; subst.
  + rewrite heq in hq.
    apply Nat.add_sub_eq_l in hq.
    rewrite <- Nat.mul_sub_distr_l in hq.
    case_eq (q - k).
    * intro h; rewrite h in hq. 
      now rewrite mult_comm in hq.
    * intros x hx; rewrite hx in hq.
      assert (hn : S d <= s).
      -- replace (S d) with ((S d) * 1) by now rewrite mult_comm, mult_1_l.
         rewrite <- hq.
         apply mult_le_compat_l.
         now auto with arith.
      -- elim (lt_irrefl s).
         apply lt_le_trans with (S d); [ now apply hrem; auto with arith | now apply hn ].
- destruct (divn_spec_ok m d) as [q s heq hrem].
  rewrite heq, h, plus_0_r.
  now exists q; rewrite mult_comm.
Qed.

(* Now let's write an algorithm that tests if a number is prime, by
   testing all of the possible divisors. Remember we prove things so
   we don't care at all if that inefficent
*)
Fixpoint prime_rec p d :=
  match d with
  | 1 => true
  | 0 => true
  | S d => 
    let (q, r) := divn p (S d) in
    if Nat.eqb r 0
    then false
    else prime_rec p d
  end.

(* Spec of the function *)
Lemma prime_rec_spec: forall p d,
  2 <= d ->
  (prime_rec p d = true <-> (forall x, x <= d -> 1 < x -> ~ x `div p)).
Proof.
intro p; induction d as [ | d hi]; intros hd; split; simpl in *.
- now auto with arith.
- intros _; reflexivity.
- apply le_S_n in hd.
  destruct d as [ | d]; [ now auto with arith | ].
  intros h x hle hlt hdiv.
  apply le_lt_eq in hle as [ -> | hle ].
  + apply divn_div in hdiv; unfold divn in hdiv.
    now destruct divn_rec; subst.
  + assert (hd' : 2 <= S d) by
       now destruct d as [ | d];
       [ elim (lt_irrefl 1); apply lt_le_trans with x | auto with arith ].
    apply hi in hd'.
    destruct hd' as [hl hr].
    revert h.
    generalize (divn_rec_spec (S d) p 0).
    destruct divn_rec as [ q r ]; intros [heq [_ hrem]] h.
    rewrite Nat.sub_0_r in heq.
    case_eq (r =? 0); intro h0; rewrite h0 in h; [ discriminate | ].
    now apply hl with x.
- destruct d as [ | d]; [ intros _; reflexivity | ].
  clear hd.
  intro h.
  generalize (divn_rec_spec (S d) p 0).
  destruct divn_rec as [ q r ]; intros [heq [_ hrem]].
  rewrite Nat.sub_0_r in heq.
  case_eq (r =? 0); intro h0.
  + apply Nat.eqb_eq in h0; rewrite h0 in *; clear h0.
    rewrite plus_0_r in heq.
    elim (h (S (S d))).
    * now apply le_refl.
    * now auto with arith.
    * now exists q; rewrite mult_comm.
  + apply Nat.eqb_neq in h0.
    destruct d as [ | d].
    * replace r with 1 in *; [ now idtac | ].
      assert (0 < r) by now destruct r; [elim h0 | auto with arith]. 
      destruct r as [ | ]; [now elim h0 | ].
      destruct r as [ | ]; [ reflexivity | ].
      apply lt_S_n in hrem.
      apply lt_S_n in hrem.
      now apply lt_n_0 in hrem.
   * apply hi; [now auto with arith | ].
     intros x hle ht hdiv.
     apply h with x; now auto with arith.
Qed.

(* We also need the negative case -> if we are not prime, we get a non trivial
   divisor from the function *)
Lemma prime_rec_spec_false: forall p d,
    prime_rec p d = false -> exists x, x <= d /\ 1 < x /\ x `div p.
Proof.
intro p; induction d as [ | d hi]; intros hp; simpl in *; [ discriminate | ].
destruct d as [ | d]; [ discriminate | ].
generalize (divn_rec_spec (S d) p 0).
revert hp.
destruct divn_rec.
destruct n0 as [ | n0].
- intros _.
  rewrite Nat.sub_0_r, plus_0_r.
  intros [-> _].
  exists (S (S d)); intuition.
  apply divides_lmul.
  now apply divides_refl.
- simpl Nat.eqb; intro h.
  apply hi in h as [q [h0 [h1 h2]]].
  rewrite Nat.sub_0_r; intros [hp [_ hlt]].
  now exists q; intuition.
Qed.

(* Main function *)
Definition primen p :=
    match p with
    | 0 => false
    | 1 => false
    | S q => prime_rec p q
    end.

(* and spec *)
Lemma primen_spec: forall p, primen p = true <-> prime p.
Proof.
unfold primen, prime.
intros [ | p]; split; intro h.
- discriminate h.
- destruct h as [_ h].
  destruct (h 2); [ now apply divides0 | discriminate | discriminate ].
- destruct p as [ | p]; [ discriminate | ].
  split; [ now idtac | ].
  intros x hdiv.
  generalize (prime_rec_spec (S (S p)) (S p)); intro hp.
  destruct p as [ | p].
  + now apply two_is_prime in hdiv.
  + assert (hh: 2 <= S ( S p)) by now auto with arith.
    apply hp in hh as [hl hr].
    case_eq (x =? (S (S (S p)))); intro hx; [ now right; apply Nat.eqb_eq |].
    apply Nat.eqb_neq in hx.
    destruct x as [ | x]; [ destruct hdiv as [q hq]; discriminate | ].
    destruct x as [ | x]; [now left | ].
    right.
    apply hl with (S (S x)) in h.
    * now apply h in hdiv.
    * apply divides_le in hdiv.
      destruct hdiv as [hdiv | ]; [ | discriminate ].
      apply le_lt_eq in hdiv as [ h0 | h1]; [now subst | assumption ].
    * now auto with arith.
- destruct h as [hp hf].
  destruct p as [ | p]; [ now elim hp | ].
  clear hp.
  destruct p as [ | p]; [ reflexivity | ].
  apply prime_rec_spec; [now auto with arith | ].
  intros x hle ht hdiv.
  apply hf in hdiv as [ h | h].
  + subst; now apply lt_irrefl in ht.
  + subst.
    repeat apply le_S_n in hle.
    apply (lt_irrefl (S p)).
    apply le_lt_trans with p; [ assumption | ].
    now constructor.
Qed.

(* every number as at least one prime factor *)
Lemma prime_factor: forall n, n <> 1 -> exists p, prime p /\ p `div n.
Proof.
induction n as [ n hi ] using (well_founded_induction lt_wf).
intros hn1.
case_eq (primen n); intro hp.
- exists n; split.
  + now apply primen_spec.
  + now apply divides_refl.
- unfold primen in hp.
  destruct n as [ | n].
  + now exists 2; split; [ apply two_is_prime | apply divides0 ].
  + destruct n as [ | n]; [ now elim hn1 | ].
    apply prime_rec_spec_false in hp as [q [h0 [h1 h2]]].
    destruct (hi q) as [y [hy0 hy1]].
    * now auto with arith.
    * now intro; subst; apply lt_irrefl in h1.
    * exists y; split;[ assumption | ].
      now apply divides_trans with q.
Qed.

End NoEM.

(* Now that we have `prime_factor` we can easily finish the proof *)

(* all prime factors of n! + 1 are > n *)
Lemma prime_div_factor: forall n p, p `div (factorial n + 1) -> prime p -> n < p.
Proof.
intros n p hdiv0 hp.
destruct (lt_dec n p) as [ h | h]; [assumption | ].
assert (hdiv1: p `div factorial n).
- apply divides_fact.
  + destruct p as [ | p].
    * destruct hp as [_ hp].
      now destruct (hp 2 (divides0 2)).
    * now auto with arith.
  + now apply not_lt in h.
- assert (h1: p `div 1) by now apply divides_addl with (factorial n).
  apply divides1 in h1.
  elim one_not_prime. 
  now rewrite <- h1.
Qed.

(* for any natural number, there exists a natural number greater than it *)
Lemma euclid: forall n, exists p, n < p /\ prime p.
Proof.
intros n.
destruct (prime_factor (factorial n + 1)) as [p [hp hd]].
- rewrite plus_comm; intro hf; injection hf; clear hf; intro hf.
  now apply factorial_non_zero in hf.
- exists p; split; [ | assumption ]. 
  now apply prime_div_factor.
Qed.
