Require Import Arith.
Require Import ZArith.
Require Import Bool.
Require Import List.

Variables P Q R T: Prop.

Parameters 
(binary_word:nat->Set)
(prime_divisor:nat->nat)
(divides: nat->nat->Prop)
(prime: nat->Prop)
(decomp: nat->list nat)
(decomp2:nat->nat*nat)
(iterate: forall A:Set, (A->A)->nat->A->A).

Definition short: Set:=binary_word 32.
Definition long: Set:=binary_word 64.

Section A_declared.
Variables (A:Set)(P Q: A->Prop)(R:A->A->Prop).
Lemma all_perm: (forall a b:A, R a b)-> forall a b :A, R b a.
Proof.
auto.
Qed.


End A_declared.

Definition id (A:Set) (a:A) : A := a.
Definition diag (A B:Set) (f:A -> A -> B) (a:A) : B := f a a.
Definition permute (A B C:Set) (f:A -> B -> C) (b:B) (a:A) : C := f a b.
Definition f_nat_Z (A:Set) (f:nat -> A) (z:Z) : A := f (Zabs_nat z). 
Definition ackermann (n:nat):nat->nat:= iterate (nat->nat)(fun(f:nat->nat)(p:nat)=> iterate nat f (S p) 1) n S.
Definition projekt1:forall A B:Prop, A/\B->A:=fun(A B:Prop)(H:A/\B) => and_ind (fun (H0:A)(_:B)=>H0)H.

Theorem imp_trans: forall P Q R:Prop, (P->Q)->(Q->R)->P->R.
Proof.
intros P Q R H H0 p.
apply H0.
apply H.
assumption.
Qed.

Theorem le_i_SSi: forall i:nat, i<= S(S i).
Proof.
intro i.
apply le_S.
apply le_S.
apply le_n.
Qed.

Theorem all_imp_dist: forall(A:Type)(P Q:A->Prop), (forall x:A, P x->Q x)->(forall y:A, P y)->forall z:A, Q z.
Proof.
intros A P Q H H0 z.
apply H; apply H0; assumption.
Qed.

Theorem le_0_mult: forall n p:nat, 0*n>=0*p.
Proof.
intros n p;apply le_n.
Qed.

Theorem lt_8_9: 8<9.
Proof.
unfold lt; apply le_n.
Qed.

Theorem lt_S: forall n p:nat, n<p->n<S p.
intros n p H.
unfold lt.
apply le_S.
trivial.
Qed.


