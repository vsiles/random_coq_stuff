Require Import Arith List String.

(* Simple functional language *)
Inductive term :=
  | Var: string -> term
  | Nat : nat -> term
  | Plus : term -> term -> term
  | IfZero: term -> term -> term -> term
.

Definition Env := list (string * nat).

Axiom string_eq : string -> string -> bool.
Hypothesis string_eq_spec: forall s t, string_eq s t = true <-> s = t.

Fixpoint mem {T: Type} (env: list (string * T)) (key: string) : option T :=
    match env with
    | nil => None
    | (id, val) :: tl =>
        if string_eq key id then Some val else mem tl key
    end.

Fixpoint eval (env: Env) t : option nat :=
 match t with
 | Var x => mem env x
 | Nat n => Some n
 | Plus a b => 
     match (eval env a, eval env b) with
     | (Some u, Some v) => Some (u + v)
     | _ => None
     end
 | IfZero test then_branch else_branch =>
     match eval env test with
     | Some 0 => eval env then_branch
     | Some _ => eval env else_branch
     | None => None
     end
end.

Inductive ok : Env -> term -> Prop :=
 | okVar: forall env x, mem env x <> None -> ok env (Var x)
 | okNat: forall env n, ok env (Nat n)
 | okPlus: forall env a b, ok env a ->
         ok env b ->
         ok env (Plus a b)
 | okIfZero: forall env test then_branch else_branch,
         ok env test ->
         ok env then_branch ->
         ok env else_branch ->
         ok env (IfZero test then_branch else_branch)
.

Hint Constructors ok.

Lemma wf: forall env t, ok env t ->
    exists v, eval env t = Some v.
Proof.
induction 1 as [ env x hmem | env n | env a b ha [va hia] hb [vb hib] |
        env t l r ht [vt hit] hl [vl hil] hr [vr hir]]; simpl in *.
- now destruct (mem env x) as [ v | ]; [exists v | elim hmem].
- now exists n.
- rewrite hia, hib.
  now exists (va + vb).
- rewrite hit.
  now destruct vt; [rewrite hil; exists vl | rewrite hir; exists vr].
Qed.
