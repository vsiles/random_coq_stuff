(** * Term definition for Simply Typed Lambda Calculus and de Bruijn manipulation . *)
(** * Usual Term syntax .*)
Require Import Arith Omega.

(** Var syntax: *)
Definition Vars := nat.

(** Type syntax:*)
Inductive Ty: Set :=
  | Base : Ty
  | Arr  : Ty -> Ty -> Ty
.

(** Term syntax:*)
Inductive Term : Set:=
 | Var : Vars -> Term
 | App : Term -> Term -> Term
 | La  : Ty -> Term -> Term
.

Notation "x · y" := (App x y) (at level 15, left associativity) : STLC_scope.
Notation "# v" := (Var v) (at level 1) : STLC_scope.
Notation "'λ' [ T ] , v " := (La T v) (at level 20, T , v at level 30) : STLC_scope.
Notation "A ⇒ B" := (Arr A B) (at level 17, right associativity): STLC_scope.

Reserved Notation " t ↑ x # n " (at level 5, x at level 0, left associativity).

Delimit Scope STLC_scope with STLC. 

Open Scope STLC_scope.

(** In order to deal with variable bindings and captures, we need a lift
function to deal with free and bounded variables.


   [M ↑ n # m] recursivly add [n] to all variables that are
   above [m] in [M]. *)
Fixpoint lift_rec (n:nat) (k:nat) (T:Term) {struct T} := match T with
   | # x =>  if le_gt_dec k x then Var (n+x) else Var x
   | M · N =>  App (M ↑ n # k) (N ↑ n # k)
   | λ [ A ], M => λ [A ], (M ↑ n # (S k)) 
 end  
   where "t ↑ n # k" := (lift_rec n k t) : STLC_scope.

Notation " t ↑ n " := (lift_rec n 0 t) (at level 5, n at level 0, left associativity) : STLC_scope.

(** Some basic properties of the lift function. That is everything we will
ever need to handle de Bruijn indexes *)

Lemma inv_lift : forall M N n m , M ↑ n # m = N ↑ n # m -> M = N.
Proof.
induction M as [ v | F hiF X hiX | T V hiV]; destruct N as [ w | G Y | T' W]; simpl in *; intros n m.
- destruct (le_gt_dec m v) as [ h | h]; destruct (le_gt_dec m w) as [ h' | h']; intro heq;
  now injection heq; clear heq; intro heq; f_equal; omega.
- destruct (le_gt_dec m v) as [ h | h]; intro heq; now discriminate.
- destruct (le_gt_dec m v) as [ h | h]; intro heq; now discriminate.
- destruct (le_gt_dec m w) as [ h | h]; intro heq; now discriminate.
- intro heq1; injection heq1; clear heq1; intros heq1 heq2.
  now rewrite (hiF _ _ _ heq2), (hiX _ _ _ heq1).
- intro heq; now discriminate.
- destruct (le_gt_dec m w) as [ h | h]; intro heq; now discriminate.
- intro heq; now discriminate.
- intro heq1; injection heq1; clear heq1; intros heq1 heq2.
  now rewrite (hiV _ _ _ heq1), heq2.
Qed.

Lemma lift_rec0 : forall M n, M ↑ 0 # n = M.
Proof.
induction M as [ v | F hiF X hiX | T V hiV]; intros; simpl.
- now destruct (le_gt_dec n v).
- now rewrite hiF, hiX.
- now rewrite hiV.
Qed.

Lemma lift0 : forall M, M ↑ 0 = M.
Proof.
intros; apply lift_rec0.
Qed.

Lemma liftP1 : forall M i j k, (M ↑ j # i) ↑ k # (j+i) = M ↑ (j+k) # i.
Proof.
induction M as [ v | F hiF X hiX | T V hiV]; intros i j k; simpl in *.
- destruct (le_gt_dec i v) as [ h | h]; simpl.
  + destruct (le_gt_dec (j+i) (j+v)) as [ h' | h']; simpl; now apply f_equal; omega.
  + destruct (le_gt_dec (j+i)) as [ h' | h']; [ | reflexivity].
    now apply f_equal; omega.
- now rewrite hiF, hiX.
- rewrite <- hiV.
  now replace (j + S i) with (S(j + i)).
Qed.

Lemma liftP2: forall M i j k n, i <= n ->
  (M ↑ j # i) ↑ k # (j+n) = (M ↑ k # n) ↑ j # i.
Proof.
induction M as [ v | F hiF X hiX | T V hiV]; intros i j k n hle; simpl in *.
- destruct (le_gt_dec i v) as [ h | h]; destruct (le_gt_dec n v) as [ h' | h']; simpl in *;
  destruct le_gt_dec; destruct le_gt_dec; now apply f_equal; omega.
- now rewrite hiF, hiX.
- replace (S (j + n)) with (j + S n) by intuition. 
  rewrite hiV; [ reflexivity | now omega].
Qed.

Lemma liftP3 : forall M i k j n , i <= k -> k <= (i+n) ->
  (M ↑ n # i) ↑ j # k = M ↑ (j+n) # i.
Proof.
induction M as [ v | F hiF X hiX | T V hiV]; intros i k j n h1 h2; simpl in *.
- destruct (le_gt_dec i v) as [ h | h]; simpl in *; destruct le_gt_dec; apply f_equal; omega.
- now rewrite hiF, hiX.
- rewrite hiV; [ reflexivity | now omega | now omega].
Qed.

Lemma lift_lift : forall M n m, (M ↑ m) ↑ n  = M↑ (n+m).
Proof.
intros.
apply liftP3; intuition.
Qed.

(** We will consider the usual implicit substitution without variable capture
(this is where the lift operator comes in handy).
  [ M [ n ← N ] ] replace the variable [n] in [M] by the term [N].
  *)
Reserved Notation "t [ x ← u ]" (at level 5, x at level 0, left associativity).

Fixpoint subst_rec U T n {struct T} :=
 match T with
  | # x => match (lt_eq_lt_dec x n) with
      | inleft (left _) => # x (* v < n *)
      | inleft (right _) => U ↑ n  (* v = n *)
      | inright _ => # (x - 1) (* v > n *)
      end
  | M · N => (M [ n ← U ]) · ( N [ n ← U ]) 
  | λ [ A ], M => λ [ A ], (M [ S n ← U ]) 
end
    where " t [ n ← w ] " := (subst_rec w t n) : STLC_scope.

Notation " t [ ← w ] " := (subst_rec w t 0) (at level 5) : STLC_scope.

(** Some basic properties of the substitution function. Again, we will only need
a few functions to deal with indexes. *)

Lemma substP1: forall M N i j k , 
  ( M [ j ← N] ) ↑ k # (j+i) = (M ↑ k # (S (j+i))) [ j ← (N ↑ k # i ) ].
Proof.
induction M as [ v | F hiF X hiX | T V hiV]; intros N i j k.
- simpl (#v [j ← N] ↑ k # (j+i)).
  change (#v ↑ k # (S (j+i))) with  (if le_gt_dec (S (j+i)) v then #(k+v) else #v).
  destruct (lt_eq_lt_dec v j) as [[ | ] | ].
  + destruct (le_gt_dec (S (j+i)) v); [ now omega| ].
    simpl.
    destruct (le_gt_dec (j+i) v) as [  | ]; [ now omega | ].
    destruct (lt_eq_lt_dec v j) as [[ | ] | ]; [ reflexivity | now omega| now omega].
  + destruct (le_gt_dec (S(j+i)) v) as [ | ]; [ now omega| ].
    simpl.
    destruct (lt_eq_lt_dec v j) as [[] | ]; [now omega | | now omega].
    subst; apply liftP2; now omega.
  + destruct (le_gt_dec (S (j+i)) v).
    * simpl.
      destruct (le_gt_dec (j+i) v) as [  | ].
      -- destruct (lt_eq_lt_dec) as [ [] | ].
         ++ destruct le_gt_dec;now omega.
         ++ destruct le_gt_dec; now omega.
         ++ destruct le_gt_dec; [ f_equal; now omega| now omega].
      -- destruct le_gt_dec; destruct lt_eq_lt_dec as [ [] | ]; now omega.
    * simpl.
      destruct le_gt_dec; destruct lt_eq_lt_dec as [ [] | ]; try now omega.
      reflexivity.
- simpl.
  rewrite hiF.
  replace (S(S(j+i))) with (S((S j)+i)) by intuition.
  now rewrite <- hiX.
- simpl.
  replace (S(S(j+i))) with (S((S j)+i)) by intuition.
  now rewrite <- hiV.
Qed.

Lemma substP2: forall M N i j n, i <= n ->
  (M ↑ j # i ) [ j+n ← N ] = ( M [ n ← N]) ↑ j # i .
Proof.
induction M as [ v | F hiF X hiX | T V hiV]; intros N i j n hle; simpl in *.
- destruct (le_gt_dec i v); destruct (lt_eq_lt_dec v n) as [[] | ]; simpl.
  + destruct lt_eq_lt_dec as [ [] | ]; destruct le_gt_dec; try now omega.
    reflexivity.
  + destruct lt_eq_lt_dec as [ [] | ]; try now omega.
    now rewrite liftP3; [ | omega | omega].
  + destruct lt_eq_lt_dec as [ [] | ]; destruct le_gt_dec; try now omega.
    now f_equal; omega.
  + destruct lt_eq_lt_dec as [ [] | ]; destruct le_gt_dec; try now omega.
    reflexivity.
  + now omega.
  + now omega.
- now rewrite hiF, hiX.
- rewrite <- hiV; [ | now omega].
  now replace (S (j + n)) with (j + S n).
Qed.

Lemma substP3: forall M N i  k n, i <= k -> k <= i+n ->
  (M↑ (S n) # i) [ k← N] = M ↑ n # i.
Proof.
induction M as [ v | F hiF X hiX | T V hiV]; intros N i k n h1 h2; simpl in *.
- destruct (le_gt_dec i v).
  + unfold subst_rec.
   destruct (lt_eq_lt_dec (S(n+v)) k) as [[] | ]; [ now omega | now omega| now f_equal; omega].
  + simpl. destruct (lt_eq_lt_dec v k) as [[] | ]; [ reflexivity | now omega | now omega].
- rewrite hiF, hiX; [ reflexivity | now omega | now omega | now omega | now omega].
- rewrite hiV; [ reflexivity | now omega | now omega].
Qed.

Lemma substP4: forall M N P i j, 
   (M [ i← N]) [i+j ← P] = (M [S(i+j) ← P]) [i← N[j← P]].
Proof.
induction M as [ v | F hiF X hiX | T V hiV]; intros N P i j; simpl in *.
- destruct lt_eq_lt_dec as [ [] | ]; destruct lt_eq_lt_dec as [ [] | ]; simpl.
  + destruct lt_eq_lt_dec as [ [] | ]; destruct lt_eq_lt_dec as [ [] | ]; [ reflexivity | | | | | | | | ]; now omega.
  + now omega.
  + now omega.
  + destruct lt_eq_lt_dec as [ [] | ]; [ now omega | | now omega ].
    now rewrite substP2; [ reflexivity | omega ].
  + now omega.
  + now omega.
  + destruct lt_eq_lt_dec as [ [] | ]; destruct lt_eq_lt_dec as [ [] | ]; [ | | reflexivity | | | | | | ]; now omega.
  + destruct lt_eq_lt_dec as [ [] | ]; [ now omega | | now omega].
    now rewrite substP3; [ reflexivity | omega | omega ].
  + destruct lt_eq_lt_dec as [ [] | ]; destruct lt_eq_lt_dec as [ [] | ]; [ reflexivity | | | | | | | | reflexivity]; now omega.
- now rewrite hiF, hiX.
- replace (S(S(i+j))) with (S((S i)+ j)) by intuition.
  now rewrite <- hiV.
Qed.

Lemma subst_travers : 
 forall  M N P n, (M [← N]) [n ← P] = (M [n+1 ← P])[← N[n← P]].
Proof.
intros.
rewrite plus_comm. change n with (O+n). apply substP4.
Qed.

(** Tool function usefull when eta-conversion is used, but this is not the case
here. *)
Lemma expand_term_with_subst : forall M n, (M ↑ 1 # (S n)) [ n ← #0 ] = M.
Proof.
induction M as [ v | F hiF X hiX | T V hiV]; intros n.
- unfold lift_rec.
  destruct le_gt_dec as [ | ].
  + unfold subst_rec.
    destruct (lt_eq_lt_dec (1+v) n) as [[] | ]; [ now omega | now omega | now f_equal; omega].
  + simpl; destruct (lt_eq_lt_dec v n) as [[] | ]; [ reflexivity |now subst; f_equal; omega| now omega].
- now simpl; rewrite hiF, hiX.
- now simpl; rewrite hiV.
Qed.

Reserved Notation " A  → B " (at level 80).

Inductive Beta : Term -> Term -> Prop :=
 | Beta_head : forall A M  N , (λ[A], M)· N  → M [← N]
 | Beta_red1 : forall M M' N , M  → M' -> M · N   → M'· N
 | Beta_red2 : forall M N  N', N  → N' -> M · N   → M · N'
 | Beta_lam  : forall A M  M', M  → M' -> λ[A],M  → λ[A ],M'
where "M  → N" := (Beta M N) : STLC_scope.

Lemma Beta_lift: forall M N, M → N -> forall n m, M ↑ n # m → N ↑ n # m.
Proof.
induction 1 as [ A M N | M M' N hM hi | M N N' hN hi | A M M' hM hi]; intros n m; simpl in *.
- change m with (0 + m).
  rewrite (substP1 M N m 0 n); simpl.
  now constructor.
- now constructor; apply hi.
- now constructor; apply hi.
- now constructor; apply hi.
Qed.

Lemma Beta_lift_inv : forall M N n m , M ↑ n # m  → N -> exists P, M  → P /\ N = P ↑ n # m .
Proof.
induction M as [ v | u hiU v hiV | A M hi]; intros N n m hred; simpl in *.
- now destruct le_gt_dec as [ h | h]; inversion hred.
- inversion hred; subst; clear hred.
  + destruct u as [ | | B N]; simpl in *; [ destruct le_gt_dec; discriminate | discriminate | ].
    injection H0; intros; subst; clear H0.
    exists (N [ ← v]); split; [ now constructor | ].
    now change m with (0 + m); rewrite <- substP1.
  + apply hiU in H2 as (u' & hu' & ->).
    now exists (u' · v); simpl; split; [ constructor | ].
  + apply hiV in H2 as (v' & hv' & ->).
    now exists (u · v'); simpl; split; [ constructor | ].
- inversion hred; subst; clear hred.
  apply hi in H2 as (Q & hQ & ->).
  now exists (λ [A], Q); split; [ constructor | ].
Qed.

Lemma Beta_subst : forall M N, M  → N -> forall n P, M [ n ← P]  → N [ n ← P].
Proof.
induction 1 as [ A M N | M M' N  hred hi| M N N' hred hi| A M M' hred hi]; intros n P; simpl in *.
- rewrite subst_travers.
  replace (n + 1) with (S n) by intuition.
  now constructor.
- now constructor; apply hi.
- now constructor; apply hi.
- now constructor; apply hi.
Qed.

Require Import List.

(** * Typing Environment for annotated terms .
  As for Terms, we define contexts of "Annotated" terms, with the very 
  safe function and tools as for the usual one.*)

(** Very naive definition of environment : list of term 

 be carefull, the usual written env Γ(x:A) is encoded in 
  A::Γ
**)

Definition Env := list Ty.


(** Some manipulation functions (mostly from Bruno Barras' PTS contrib): 
 - how to find an item in the environment
 - how to truncate an environment 
 - how to insert a new element (with correct de Bruijn update)
 - how to substitute something in the environment
 *)
Set Implicit Arguments.

Inductive item (A:Type) (x:A): list A ->nat->Prop :=
| item_hd: forall Γ :list A, (item x (cons x Γ) O)
| item_tl: forall (Γ:list A)(n:nat)(y:A), item x Γ n -> item x (cons y Γ) (S n).

Hint Constructors item.

(** In the list [Γ], the [n]th item is syntacticaly [x]. *)
Notation " x ↓ n ∈ Γ " := (item x Γ n) (at level 80, no associativity) : STLC_scope.

Lemma fun_item: forall T (A B:T)(Γ:list T)(n:nat), 
  A ↓ n ∈ Γ -> B ↓ n ∈ Γ -> A = B.
Proof.
intros T A B  Γ n;revert T A B Γ. 
induction n as [ | n hi]; intros T A B Γ h1 h2.
- inversion h1; subst; clear h1.
  now inversion h2; subst; clear h2.
- inversion h1; subst; clear h1.
  inversion h2; subst; clear h2.
  now apply (hi _ _ _ _ H1 H0).
Qed.
Inductive trunc (A:Type) : nat->list A ->list A->Prop :=
  | trunc_O: forall (Γ:list A) , (trunc O Γ Γ)
  | trunc_S: forall (k:nat)(Γ Γ':list A)(x:A), trunc k Γ Γ' 
                -> trunc (S k) (cons x Γ) Γ'.

Hint Constructors trunc.

Lemma item_trunc: forall (T:Type) (n:nat) (Γ:list T) (t:T), 
  t ↓ n ∈ Γ -> exists Γ' , trunc (S n) Γ Γ'.
Proof.
intros T; induction n as [ | n hi]; intros Γ t hin.
- inversion hin; subst; clear hin.
  exists Γ0.
  now repeat constructor.
- inversion hin; subst; clear hin.
  destruct (hi Γ0 t H1) as [Γ' hΓ].
  exists Γ'.
  now repeat constructor.
Qed.

(** This type describe how do we add an element in an environment: no type
checking is done, this is just the mecanic way to do it. *)
Inductive ins_in_env (Γ:Env ) (d1:Ty): nat->Env -> Env  ->Prop :=
  | ins_O: ins_in_env Γ d1 O Γ (d1::Γ)
  | ins_S: forall (n:nat)(Δ Δ':Env )(d:Ty), (ins_in_env Γ d1 n Δ Δ')
    -> ins_in_env Γ d1 (S n) (d::Δ) ( d::Δ' ).

Hint Constructors ins_in_env.


(** Some lemmas about inserting a new element. They explain how
 terms in the environment are lifted according to their original position
 and the position of insertion. *)
Lemma ins_item_ge: forall (d':Ty) (n:nat) (Γ Δ Δ':Env), 
  ins_in_env Γ d' n Δ Δ' -> 
  forall (v:nat), n<=v -> 
 forall (d:Ty),  d ↓ v ∈ Δ  -> d ↓ (S v) ∈ Δ'.
Proof.
intros d'; induction n as [ | n hi]; intros Γ Δ Δ' hins v hle d hd.
- inversion hd; subst; clear hd.
  + inversion hins; subst; clear hins.
    now repeat constructor.
  + inversion hins; subst; clear hins.
    now repeat constructor.
- inversion hd; subst; clear hd; [ now omega | ].
  inversion hins; subst; clear hins.
  constructor.
  eapply hi.
  + now apply H4.
  + now omega.
  + assumption.
Qed.

Lemma ins_item_lt: forall (d':Ty)(n:nat)(Γ Δ Δ':Env),
 ins_in_env Γ d' n Δ Δ' ->
 forall (v:nat), n > v ->
 forall (d:Ty), d ↓ v ∈ Δ -> d  ↓ v ∈ Δ' .
Proof.
intros d'; induction n as [ | n hi]; intros Γ Δ Δ' hins v hlt d hd; [ now omega | ].
inversion hins; subst; clear hins.
destruct v as [ | v].
- now inversion hd; subst; constructor.
- inversion hd; subst; clear hd.
  constructor.
  eapply hi.
  + now apply H0.
  + now omega.
  + now assumption.
Qed.


(** This type describe how do we do substitution inside a context.
As previously, no type checking is done at this point.*)

Inductive sub_in_env (Γ : Env) (T:Ty):
  nat -> Env -> Env -> Prop :=
    | sub_O :  sub_in_env Γ T 0 (T :: Γ) Γ
    | sub_S :
        forall Δ Δ' n  B,
        sub_in_env Γ T n Δ Δ' ->
        sub_in_env Γ T (S n) (B :: Δ) ( B :: Δ').

Hint Constructors sub_in_env.


(** Some ins / subst related facts: what happens to term when we do
 a substitution in a context.*)
Lemma nth_sub_sup :
   forall n Γ Δ Δ' T,
   sub_in_env Γ T n Δ Δ' ->
   forall v : nat, n <= v -> 
   forall d , d ↓ (S v) ∈ Δ -> d ↓ v ∈ Δ'.
Proof.
induction 1 as [ | Δ  Δ' n b hΔ hi]; intros v hle d hd.
- now inversion hd; subst; clear hd.
- inversion hd; subst; clear hd.
  destruct v as [ | v]; [ now omega | ].
  constructor.
  now apply hi; [ omega |].
Qed.

Lemma nth_sub_eq :
   forall T n Γ Δ Δ',
   sub_in_env Γ T n Δ Δ' -> 
  forall d , d↓ n ∈ Δ -> T = d.
Proof.
induction 1 as [ | Δ  Δ' n b hΔ hi]; intros d hd.
- now inversion hd; subst; clear hd.
- inversion hd; subst; clear hd.
  now apply hi.
Qed.

Lemma nth_sub_inf :
   forall T n Γ Δ Δ',
   sub_in_env Γ T n Δ Δ' ->
   forall v : nat,
   n > v ->
   forall d , d ↓ v ∈ Δ -> d ↓ v ∈ Δ' .
Proof.
induction 1 as [ | Δ  Δ' n b hΔ hi]; intros v hlt d hd; [ now omega | ].
inversion hd; subst; clear hd; [ now constructor | ].
constructor.
apply hi; [ now omega |assumption].
Qed.

Reserved Notation "Γ ⊢ t : T" (at level 80, t, T at level 30, no associativity) .

Inductive typ : Env -> Term -> Ty -> Prop :=
 | cVar  : forall Γ A v, A ↓ v ∈ Γ -> Γ ⊢ #v : A
 | cLa   : forall Γ A B M, A::Γ ⊢ M : B -> Γ ⊢ λ[A], M : A ⇒ B
 | cApp  : forall Γ M N A B , Γ ⊢ M : A ⇒ B -> Γ ⊢ N : A -> Γ ⊢ M · N : B
where "Γ ⊢ t : T" := (typ Γ t T) : STLC_scope.

Hint Constructors typ.

(** Weakening Property: if a judgement is valid, we can insert a well-typed term
  in the context, it will remain valid. This is where the type checking for
  inserting items in a context is done.*)
Theorem weakening: forall Δ M T, Δ ⊢ M : T -> forall Γ A n Δ', ins_in_env Γ A n Δ Δ' ->
                 Δ' ⊢ M ↑ 1 # n : T.
Proof.
induction 1 as [ Δ V v hin | Δ U V M hM hiM | Δ M N U V hM hiM hN hiN]; intros Γ A n Δ' hins; simpl in *.
- destruct le_gt_dec; constructor.
  + eapply ins_item_ge; [ now apply hins | assumption | assumption].
  + eapply ins_item_lt; [ now apply hins | | ]; assumption.
- constructor.
  eapply hiM.
  constructor.
  now apply hins.
- econstructor.
  + eapply hiM; now apply hins.
  + eapply hiN; now apply hins.
Qed.

Theorem thinning :
   forall Γ M T A, Γ ⊢ M : T -> A::Γ ⊢ M ↑ 1 : T.
Proof.
intros.
eapply weakening.
- now apply H.
- now constructor.
Qed.

Theorem thinning_n : forall n Δ Δ', trunc n Δ Δ' -> forall M T , Δ' ⊢ M : T  -> Δ ⊢ M ↑ n : T.
Proof.
induction n as [ | n hi]; intros Δ Δ' ht M T hM.
- inversion ht; subst; clear ht.
  now rewrite lift0.
- inversion ht; subst; clear ht.
  change (S n) with (1 + n).
  replace (M ↑ (1+n)) with ((M ↑ n )↑ 1) by (apply lift_lift).
  apply thinning; trivial.
  eapply hi.
  + now apply H0.
  + assumption.
Qed.

(** Substitution Property: if a judgment is valid and we replace a variable by a
  well-typed term of the same type, it will remain valid.*)
(* begin hide *)
Lemma sub_trunc : forall Δ A n Γ Γ', sub_in_env Δ A n Γ Γ' -> trunc n Γ' Δ.
Proof.
induction 1; now repeat constructor.
Qed.
(* end hide *)

Theorem substitution : forall Γ M T , Γ  ⊢ M : T  -> forall Δ P A, Δ  ⊢ P : A ->
 forall Γ' n , sub_in_env Δ A n Γ Γ' -> Γ' ⊢ M [ n ←P ]  : T.
Proof.
induction 1 as [ Γ V v hin | Γ U V M hM hiM | Γ M N U V hM hiM hN hiN]; intros Δ P A hP Γ' n hsub; simpl.
- destruct lt_eq_lt_dec as [ [] | ].
  + constructor.
    eapply nth_sub_inf; [ now apply hsub | now omega | assumption].
  + subst.
    eapply thinning_n.
    * eapply sub_trunc.
      now apply hsub.
    * replace V with A; [ assumption | ]. 
      eapply nth_sub_eq; [ now apply hsub | assumption].
  + constructor.
    eapply nth_sub_sup; [ now apply hsub | now omega |].
    replace (S (v - 1)) with v by now omega.
    assumption.
- econstructor.
  eapply hiM; [ now apply hP | ].
  now constructor.
- econstructor.
  + eapply hiM; [ now apply hP | assumption].
  + eapply hiN; [ now apply hP | assumption ].
Qed.

Lemma SR : forall Γ M T, Γ ⊢ M : T -> forall N, M  → N -> Γ ⊢ N : T.
Proof.
induction 1 as [ Γ A v hin | Γ A B M hM hiM | Γ M N A B hM hiM hN hiN]; intros P hred.
- now inversion hred.
- inversion hred; subst; clear hred.
  constructor.
  now apply hiM.
- inversion hred; subst; clear hred.
  + inversion hM; subst; clear hM.
    eapply substitution; [ now apply H1 | now apply hN| now constructor].
  + econstructor.
    * apply hiM; assumption.
    * assumption.
  + econstructor.
    * now apply hM.
    * apply hiN; assumption.
Qed.

Definition is_value (t: Term) : Prop :=
  match t with
  | # v => True
  | λ [ A ], M => True
  | _ => False
  end.

Lemma Progress_: forall Γ M T, Γ ⊢ M : T -> Γ = nil -> (exists N, M  → N) \/ is_value M.
Proof.
induction 1 as [ Γ A v hin | Γ A B M hM hiM | Γ M N A B hM hiM hN hiN]; intros heq; simpl; [ now right | now right | ].
left.
destruct (hiM heq) as [ [M' hM'] | hm].
- exists (M'· N); now constructor.
- destruct (hiN heq) as [ [N' hN'] | hn].
  + exists (M · N'); now constructor.
  + subst; destruct M as [ v | U V | U V].
    * inversion hM; subst; clear hM.
      now inversion H1.
    * simpl in hm; now elim hm.
    * exists (V [← N]); now constructor.
Qed.

Lemma Progress: forall M T, nil ⊢ M : T -> (exists N, M  → N) \/ is_value M.
Proof.
intros M T h; eapply Progress_.
- now apply h.
- reflexivity.
Qed.

Inductive subterm : Term -> Term -> Prop :=
  | sbtrm_abs : forall A M, subterm M (λ [A], M)
  | sbtrm_app_l : forall M N, subterm M (M · N)
  | sbtrm_app_r : forall M N, subterm N (M · N)
.

Fixpoint boccur (n:nat) (t:Term) :=
  match t with
  | # i => if eq_nat_dec n i then true else false
  | u · v => orb (boccur n u) (boccur n v)
  | λ [A], m => boccur (S n) m
  end.


Require Import Relations.

Definition normal t := forall u, ~ (t → u).

Notation SN := (Acc (transp _ Beta)).

Lemma commut_Beta_subterm : commut _ subterm (transp _ Beta).
Proof.
intros M N hsub P hP; unfold transp in *.
inversion hsub; subst; clear hsub.
- now exists (λ [A], P); constructor.
- now exists (P · N0); constructor.
- now exists (M0 · P); constructor.
Qed.

Lemma subterm_SN : forall M , SN M -> forall P, subterm P M -> SN P.
Proof.
induction 1 as [ M hM hi]; intros P hP.
constructor.
intros Q HQ.
destruct (commut_Beta_subterm hP HQ) as [R h1 h2].
now eapply hi; [ now apply h1 | ].
Qed.

Lemma SN_red_SN : forall x y, SN x -> x  → y -> SN y.
Proof.
intros x y h; revert y; induction h as [ x hx hi]; simpl in *.
exact hx.
Qed.

Lemma SN_var : forall n, SN (# n).
Proof.
intros n; constructor; intros x hx.
now inversion hx.
Qed.

Lemma SN_abs : forall M, SN M -> forall A, SN (λ [A], M).
Proof.
induction 1 as [ M hM hi]; intros A; simpl in *.
constructor; intros N hN.
inversion hN; subst; clear hN.
now apply hi.
Qed.

Lemma SN_lift : forall n t k, SN t -> SN (t ↑ n # k).
Proof.
intros n t k h; revert t h n k.
induction 1 as [N hN hi]; intros n k.
constructor; intros P hP.
apply Beta_lift_inv in hP as ( Q & hQ & ->).
now apply hi.
Qed.

Lemma SN_lift_inv : forall M', SN M' -> forall n M k, M' = M ↑ n # k -> SN M.
Proof.
induction 1 as [ M' hM hi]; intros n M k heq; subst; simpl in *.
constructor; intros N hN.
apply hi with (y := N ↑ n # k) (n := n) (k := k); [ | reflexivity].
now apply Beta_lift.
Qed.

Lemma SN_subst_inv_l u m k : SN (subst_rec u m k) -> boccur k m = true -> SN u.
Proof.
revert u k;
induction m as [ v | U hiU V hiV | A U hi]; intros u k hSN hin; simpl in *.
- destruct lt_eq_lt_dec as [ [] | ].
  + destruct Nat.eq_dec; [ now omega | discriminate].
  + destruct Nat.eq_dec; [ | subst; discriminate].
    now apply (SN_lift_inv hSN k _ 0).
  + destruct Nat.eq_dec; [ now omega | discriminate].
- apply Bool.orb_true_iff in hin as [ h | h].
  + apply hiU with (k := k); [ | assumption].
    eapply subterm_SN; [ now apply hSN | ].
    now constructor.
  + apply hiV with (k := k); [ | assumption].
    eapply subterm_SN; [ now apply hSN | ].
    now constructor.
- apply hi with (k := S k); [ | assumption].
  eapply subterm_SN; [ now apply hSN | ].
  now constructor.
Qed.

Lemma SN_subst : forall M T, SN (M [← T]) -> SN M.
Proof.
intros M T hsub.
cut (forall t,  SN t -> forall m, t = m [ ← T] -> SN m).
- intro h; now apply (h _ hsub).
- simple induction 1; intros.
  apply Acc_intro; intros; subst.
  apply H1 with (y [ ← T]); [ | reflexivity].
  now apply Beta_subst.
Qed.

Definition neutral M := match M with La _ _ => False | _ => True end.

Inductive nf : Term -> Prop :=
| Nf_var : forall n, nf (# n)
| Nf_app : forall u v, neutral u -> nf u -> nf v -> nf (u · v)
| Nf_abs : forall t, nf t -> forall A, nf (λ [A], t)
.

Lemma nf_norm : forall t, nf t -> forall u, ~ (t → u).
Proof.
induction 1 as [ v | U V hneutral hU hiU hV hiV | N hN hi A].
- now intros u hu; inversion hu.
- intros u hu; inversion hu; subst; clear hu; [ now elim hneutral | |].
  + now apply (hiU M').
  + now apply (hiV N').
- intros u hu; inversion hu; subst; clear hu.
  now apply (hi M').
Qed.

Lemma nf_sound : forall t, normal t -> nf t.
Proof.
induction t as [ v | U hiU V hiV| A M hi]; intros h; simpl in *.
- now constructor.
- destruct U as [ u | K L | B M].
  + constructor; [ now idtac | |].
    * apply hiU.
      now intros v hv; inversion hv.
    * apply hiV.
      intros W hW.
      now apply (h (#u · W)); constructor.
  + constructor; [ now idtac | |].
    * apply hiU.
      intros W hW.
      now apply (h (W · V)); constructor.
    * apply hiV.
      intros W hW.
      now apply (h (K · L · W)); constructor.
  + now elim (h (M [← V])); constructor.
- constructor.
  apply hi.
  intros W hW.
  now apply (h (λ [A], W)); constructor.
Qed.

Lemma Beta_dec : forall t, {u| t→ u}+{nf t}.
Proof.
induction t as [ u | U hiU V hiV | A M hi]; simpl in *.
- right; now constructor.
- destruct hiU as [[u hu] | hu].
  + now left; exists (u · V); constructor.
  + destruct hiV as [[v hv] | hv].
    * now left; exists (U · v); constructor.
    * destruct U as [ w | K L | A M].
      -- now right; constructor.
      -- now right; constructor.
      -- left; exists (M [← V]); now constructor.
- destruct hi as [[N hN] | h].
  + left; exists (λ [A], N); now constructor.
  + now right; constructor.
Qed.

Inductive Betas: Term -> Term -> Prop :=
  | Betas_refl : forall M, Betas M M
  | Betas_trans: forall M N P, Beta M N -> Betas N P -> Betas M P.

Lemma Betas_Beta: forall M N, Beta M N -> Betas M N.
Proof.
intros M N h; econstructor.
- now apply h.
- now constructor.
Qed.

Lemma Betas_Betas: forall M N, Betas M N -> forall P, Betas N P -> Betas M P.
Proof.
induction 1 as [ M | M N P hMN hi1 hNP hi2]; intros; [ assumption |].
econstructor; [ now apply hMN | ].
now apply hNP.
Qed.

Lemma Betas_App: forall M N, Betas M N -> forall U V, Betas U V -> Betas (M· U) (N · V).
Proof.
induction 1 as [ M | M N P hMN hNP hi]; intros U V h.
- induction h as [ U | U V P hUV hVP hi]; [ now constructor | ].
  eapply Betas_Betas.
  + apply Betas_Beta; apply Beta_red2; exact hUV.
  + assumption.
- eapply Betas_Betas.
  + apply Betas_Beta; apply Beta_red1; exact hMN.
  + now apply hi.
Qed.

Lemma Betas_Lam: forall M N, Betas M N -> forall A, Betas (λ [A], M) (λ [A], N).
Proof.
induction 1 as [ M | M N P hMN hNP hi]; intros A; [ now constructor | ].
eapply Betas_Betas.
+ apply Betas_Beta; apply Beta_lam; now apply hMN.
+ now apply hi.
Qed.

Lemma Betas_lift: forall M N, Betas M N -> forall n m, Betas (M ↑ n # m) (N ↑ n # m).
Proof.
induction 1 as [ M | M N P hMN hNP hi]; intros n m; simpl in *.
- now constructor.
- econstructor.
  + apply Beta_lift.
    now apply hMN.
  + now apply hi.
Qed.

Lemma Beta_subst_l : forall P M N, M → N -> forall n, Betas (P [ n ← M]) (P [ n ← N]).
Proof.
induction P as [ v | U hiU V hiV | A B hi]; intros M N hred n; simpl in *.
- destruct lt_eq_lt_dec as [ [] | ]; [ now constructor | | now constructor ].
  now apply Betas_lift; apply Betas_Beta.
- apply Betas_App; [ now apply hiU | now apply hiV].
- apply Betas_Lam; now apply hi.
Qed.

(* Strong -> Weak *)
Lemma norm : forall t, SN t -> { u | Betas t u /\ nf u}.
Proof.
induction 1 as [ N hN hi].
destruct (Beta_dec N) as [[ P hP] | hnf].
- destruct (hi P hP) as [Q [h1 h2]].
  exists Q; split; [ | assumption].
  now apply Betas_trans with (N := P).
- exists N; split; [ | assumption].
  now constructor.
Qed.

Fixpoint reducible (ty : Ty) (M : Term) : Prop :=
  match ty with
    | Base => SN M
    | T1 ⇒ T2 => forall N, reducible T1 N -> reducible T2 (M · N)
  end.

Lemma CR2: forall T M N,  M  → N -> reducible T M -> reducible T N.
Proof.
induction T as [ | T1 h1 T2 h2]; intros M N hred hcand; simpl in *.
- now apply hcand.
- intros Q hQ; simpl in *.
  eapply h2.
  + constructor.
    now apply hred.
  + now apply hcand.
Qed.

Lemma CR2s: forall T M N,  Betas M  N -> reducible T M -> reducible T N.
Proof.
intro T.
induction 1 as [ M | M N P hMN hNP hi]; intros h; simpl in *; [ assumption | ].
apply hi.
now apply CR2 with (M := M).
Qed.

Lemma acc_preservation_: forall A B (RA : relation A) (RB : relation B) (f : A -> B) a, 
  (forall x y, RA x y -> RB (f x) (f y)) -> forall z, Acc RB z -> z = f a -> Acc RA a.
Proof.
intros A B RA RB f a h z hacc.
revert RA f a h.
induction hacc as [x hx hi]; intros RA f a h heq; subst.
constructor; intros b hb.
eapply hi.
- eapply h.
  now apply hb.
- now apply h. 
- reflexivity.
Qed.

Lemma acc_preservation: forall A B (RA : relation A) (RB : relation B) (f : A -> B) a, 
  (forall x y, RA x y -> RB (f x) (f y)) -> Acc RB (f a) -> Acc RA a.
Proof.
intros; eapply acc_preservation_.
now apply H.
now apply H0.
reflexivity.
Qed.

Lemma Acc_ind':forall (A : Type) (R : relation A) (P : A -> Prop),
  (forall x, (forall y, R y x -> P y) -> P x) -> forall x, Acc R x -> P x.
Proof.
intros A R P h x hacc.
eapply Acc_ind; [ | now apply hacc].
intros y hy h'.
apply h.
exact h'.
Qed.

Lemma CR1_and_CR3: forall T, 
  (forall M, reducible T M -> SN M) /\
  (forall M, neutral M ->
             (forall N, M  → N -> reducible T N) -> reducible T M).
Proof.
induction T as [ | T1 [hi1 hi1'] T2 [hi2 hi2']]; simpl in *; split.
- intros M hM; assumption.
- intros M _ h; constructor; exact h.
- intros M hred.
  assert (h : SN ((fun M => M · #0) M)).
  + apply hi2, hi2'; [ now idtac | ].
    intros N h; apply (CR2 _ h).
    apply hred, hi1'; [ now idtac | ].
    now intros x hh; inversion hh.
  + apply acc_preservation with (f := fun M => M · #0) (RB := transp _ Beta); [ | assumption].
    intros x y hb; now constructor.
- intros M hn h N hred.
  assert (hSN : SN N) by now apply hi1.
  revert hred.
  elim hSN using Acc_ind'; clear N hSN.
  intros N hN hi.
  apply hi2'; [ now idtac | ].
  intros MN hMN; inversion hMN; subst; clear hMN; [ now elim hn | now apply h|].
  apply hN; [ assumption | ].
  now apply CR2 with (M := N).
Qed.

Lemma CR1 : forall T M, reducible T M -> SN M.
Proof.
intros T M; eapply CR1_and_CR3.
Qed.

Lemma CR3: forall T M, neutral M -> (forall N, M  → N -> reducible T N) -> reducible T M.
Proof.
intros T M; eapply CR1_and_CR3.
Qed.

Lemma var_reducibility: forall v T, reducible T # v.
Proof.
intros v T; apply CR3; [ now idtac | ].
now intros u h; inversion h.
Qed.

Lemma red_sat M P : boccur 0 M = true \/ SN P ->
   forall T, reducible T (M [ ← P]) -> forall A, reducible T ((λ[A], M)· P).
Proof.
intros h T hred A.
assert (hP : SN P).
- destruct h as [ h | h]; [ | exact h].
  apply CR1 in hred.
  now apply SN_subst_inv_l in hred.
- clear h; revert M hred.
  induction hP as [ P _ hiP]; unfold transp in *.
  intros M hred.
  generalize hred.
  cut (SN M).
  + simple induction 1.
    clear M hred H; intros M _ hi hred; unfold transp in *.
    apply CR3; [ now idtac | ].
    intros N hbeta.
    inversion hbeta; subst; clear hbeta; [ assumption | | ].
    * inversion H2; subst; clear H2.
      apply hi; [ assumption | ].
      apply CR2 with (M [← P]); [ now apply Beta_subst | assumption].
    * apply hiP; [ assumption | ].
      apply CR2s with (M [ ← P]); [ | assumption].
      now apply Beta_subst_l.
  + apply SN_subst with P.
    now apply CR1 with T.
Qed.

Fixpoint subst_list n l M : Term :=
  match M with
    | #v => if le_gt_dec n v then lift_rec n 0 (nth (v - n) l (# (v - n - length l)))
            else #v
    | M · N => (subst_list n l M) · (subst_list n l N)
    | λ [A], M => λ [A], (subst_list (S n) l M)
  end
.

Lemma subst_list_nil n M : subst_list n nil M = M.
Proof.
revert n; induction M as [ v | U hiU V hiV | A M hi]; intros n; simpl in *.
- destruct le_gt_dec; [ | reflexivity ].
  rewrite <- minus_n_O.
  replace (match v - n with | O | _ => #(v - n) end) with #(v - n) by now destruct (v - n).
  now simpl; f_equal; omega.
- f_equal; [ now rewrite hiU | now rewrite hiV].
- f_equal; now rewrite hi.
Qed.

Lemma subst_shift_cancel n d c l M :
  c <= n -> length l + n <= d + c ->
  subst_list n l (lift_rec d c M) = lift_rec (d - length l) c M.
Proof.
revert n d c l.
induction M as [ v | U hiU V hiV | A M hi]; intros n d c l h1 h2; simpl in *.
- destruct le_gt_dec; simpl in *.
  + destruct le_gt_dec; simpl in *; [ | now omega].
    rewrite nth_overflow; [ | now omega].
    now simpl; f_equal; omega.
  + destruct le_gt_dec; simpl in *; [ now omega | reflexivity ].
- f_equal.
  + now apply hiU.
  + now apply hiV.
- f_equal; apply hi;now omega.
Qed.

Lemma subst_list_app n k l M :
  subst_list n k (subst_list (length k + n) l M) = subst_list n (k ++ l) M.
Proof.
revert M n; induction M as [ v | U hiU V hiV | A M hi]; simpl in *; intros n.
- rewrite app_length.
  destruct (le_gt_dec n v); destruct le_gt_dec; simpl; [ | | now omega| ].
  + rewrite app_nth2; [ | now omega].
    rewrite subst_shift_cancel; [ | now omega | now omega].
    f_equal; [ now omega | ].
    f_equal; [ now omega | ].
    f_equal; now omega.
  + destruct le_gt_dec; [ | now omega].
    f_equal.
    rewrite app_nth1; [ | now omega].
    f_equal; f_equal; now omega.
  + destruct le_gt_dec; [ now omega | reflexivity ].
- f_equal; [ now apply hiU | now apply hiV].
- f_equal.
  replace (S (length k + n)) with (length k + S n) by omega.
  now apply hi.
Qed.

(* just to test it's ok with subst_rec *)
Lemma subst_list_ok: forall M n N, M [ n← N] = subst_list n (N :: nil) M.
Proof.
induction M as [ v | U hiU V hiV | A M hi]; intros n N; simpl in *.
- destruct lt_eq_lt_dec as [ [] | ].
  + destruct le_gt_dec; [ now omega | reflexivity].
  + destruct le_gt_dec; [ | now omega]; subst.
    now rewrite <- minus_n_n.
  + destruct le_gt_dec; [ | now omega ].
    case_eq (v - n); [ now omega | ].
    intros q heq; subst.
    replace (match q with | O | _ => # (S q - 1) end ) with # (S q - 1).
    * simpl; f_equal.
      rewrite <- minus_n_O.
      now omega.
    * now destruct q.
- f_equal.
  + now apply hiU.
  + now apply hiV.
- f_equal; now apply hi.
Qed.

Definition left_list (A B: Type) (l: list (A * B)) := map fst l.
Definition right_list (A B: Type) (l: list (A * B)) := map snd l.

Lemma left_list_length: forall A B (l: list (A * B)), length (left_list l) = length l.
Proof.
intros A B l.
unfold left_list; now rewrite map_length.
Qed.

Lemma reduce_lemma: forall (Δ : list (Term * Ty)) Γ M T,
  (right_list Δ) ++ Γ ⊢ M : T ->
  Forall (fun (x: Term * Ty) => let (tm, ty) := x in reducible ty tm) Δ ->
  reducible T (subst_list 0 (left_list Δ) M).
Proof.
intros Δ Γ M T; revert M T Γ Δ.
induction M as [ v | U hiU V hiV | A M hi]; intros T Γ Δ; simpl in *.
- simpl.
  rewrite <- minus_n_O in *.
  rewrite lift0, left_list_length.
  revert v.
  induction Δ as [ | hd tl hi]; simpl in *; intros v.
  + replace (reducible T match v with
            | 0 | _ => # (v - 0)
            end) with (reducible T #v) by now destruct v.
    intros _ _; now apply var_reducibility.
  + intros hty hf.
    inversion hf; subst; clear hf.
    destruct hd as [hdT hdTy]; simpl in *.
    destruct v.
    * inversion hty; subst; clear hty.
      now inversion H3; subst; clear H3.
    * apply hi; [ | assumption ].
      inversion hty; subst; clear hty.
      inversion H3; subst; clear H3.
      now constructor.
- intros hty hf.
  inversion hty; subst; clear hty.
  generalize (hiU (A ⇒ T) Γ Δ H2 hf); simpl; intros h.
  apply h.
  now apply hiV with Γ.
- intros hty hf.
  inversion hty; subst; clear hty; simpl; intros N hN.
  apply red_sat; [ right; now apply CR1 with A| ].
  rewrite subst_list_ok, subst_list_app; simpl.
  change (N :: left_list Δ) with (left_list ((N, A) :: Δ)).
  apply hi with Γ; [ simpl; assumption | ].
  now constructor.
Qed.

Lemma typ_are_SN: forall Γ M T, Γ ⊢ M : T -> SN M.
Proof.
intros Γ M T hty.
assert (h : reducible T (subst_list 0 (left_list nil) M)) by now apply reduce_lemma with Γ.
simpl in h.
rewrite subst_list_nil in h.
now apply CR1 with T.
Qed.

