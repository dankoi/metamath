(** * Syntactic elements 

  A module defining the natural-deduction-style typing system for
  shift and reset, and a version thereof stratified into a normal-form
  level and a neutral-form level.  
*)
Require Export List.
Require Export Bool.

Set Implicit Arguments.
Unset Strict Implicit.

Parameter atoms : Set.

(** The syntax of formulas including a a distinguished atomic type [Bot] that reset can be set on *)
Inductive formula := 
  Atom : atoms -> formula
| Bot  : formula 
| Func  : formula -> formula -> formula
| Sum : formula -> formula -> formula.

Definition context := list formula.
Hint Unfold context.

(** Church-style proof terms (typing system) *)
Inductive proof : context -> bool -> formula -> Set :=
| Inl   : forall Gamma annot A B, proof Gamma annot A -> 
                                  proof Gamma annot (Sum A B)

| Inr   : forall Gamma annot A B, proof Gamma annot B -> 
                                  proof Gamma annot (Sum A B)

| Lam   : forall Gamma annot A B, proof (A::Gamma) annot B -> 
                                  proof Gamma annot (Func A B)

| Hyp   : forall Gamma annot A, proof (A::Gamma) annot A

| Wkn   : forall Gamma annot A B, proof Gamma annot A -> 
                                  proof (B::Gamma) annot A

| Case  : forall Gamma annot A B C, proof Gamma annot (Sum A B) -> 
                                    proof (A::Gamma) annot C -> 
                                    proof (B::Gamma) annot C -> 
                                    proof Gamma annot C

| App   : forall Gamma annot A B, proof Gamma annot (Func A B) -> 
                                  proof Gamma annot A -> 
                                  proof Gamma annot B

| Reset : forall Gamma annot, proof Gamma true Bot -> 
                              proof Gamma annot Bot

| Shift : forall Gamma A, proof ((Func A Bot)::Gamma) true Bot -> 
                          proof Gamma true A 
.

(** The proof terms stratified into normal-form-terms (which cannot
compute further) and neutral-terms (which could compute if the open
variable(s) they countain would be substituted by a normal-non-neutral
term) *)

Inductive proof_nf : context -> bool -> formula -> Set :=
| nf_Inl  : forall Gamma annot A B,   proof_nf Gamma annot A -> 
                                      proof_nf Gamma annot (Sum A B)
                                               
| nf_Inr  : forall Gamma annot A B,   proof_nf Gamma annot B -> 
                                      proof_nf Gamma annot (Sum A B)
                                               
| nf_Lam    : forall Gamma annot A B, proof_nf (A::Gamma) annot B -> 
                                      proof_nf Gamma annot (Func A B)
                                               
| nf_ne      : forall Gamma annot A,  proof_ne Gamma annot A -> 
                                      proof_nf Gamma annot A
                                               
| nf_Shift  : forall Gamma A,         proof_nf ((Func A Bot)::Gamma) true Bot -> 
                                      proof_nf Gamma true A
                                               
with proof_ne : context -> bool -> formula -> Set :=
| ne_Hyp   : forall Gamma annot A, proof_ne (A::Gamma) annot A

| ne_Case   : forall Gamma annot A B C, proof_ne Gamma annot (Sum A B) -> 
                                        proof_nf (A::Gamma) annot C -> 
                                        proof_nf (B::Gamma) annot C -> 
                                        proof_ne Gamma annot C

| ne_App   : forall Gamma annot A B,    proof_ne Gamma annot (Func A B) -> 
                                        proof_nf Gamma annot A -> 
                                        proof_ne Gamma annot B

| ne_Reset : forall Gamma annot,        proof_ne Gamma true Bot -> 
                                        proof_ne Gamma annot Bot

| ne_Wkn   : forall Gamma annot A B,    proof_nf Gamma annot A -> 
                                        proof_ne (B::Gamma) annot A
.

(** [leb] is the less-than-or-equal order on booleans *)
Lemma leb_refl : forall a, leb a a.
Proof.
  intro a.
  destruct a; simpl; auto.
Defined.

Lemma leb_trans : forall a b c, leb a b -> leb b c -> leb a c.
Proof.
  intros a b c H1 H2.
  destruct a; destruct b; destruct c; simpl in *; auto.
Defined.

(** [prefix] is the prefix relation on two lists *)
Inductive prefix : context -> context -> Set :=
  prefix_refl w : prefix w w
| prefix_cons w w' : forall A, prefix w w' -> prefix w (A::w').

Lemma prefix_trans : forall w w' w'', prefix w w' -> prefix w' w'' -> prefix w w''.
Proof.
  intros.
  induction H0.
  assumption.
  apply prefix_cons.
  apply IHprefix.
  assumption.
Defined.

(** Monotonicity of proof_nf and proof_ne with respect to the order on
contexts and the order on booleans *)

Lemma proof_nf_mon : forall Gamma Gamma', prefix Gamma Gamma' -> forall A annot, proof_nf Gamma annot A -> proof_nf Gamma' annot A.
Proof.
  intros Gamma Gamma' Hle.
  induction Hle.
  
  intros A a r.
  apply r.
  
  intros.
  apply nf_ne.
  apply ne_Wkn.
  auto.
Defined.

Lemma proof_ne_mon : (forall Gamma Gamma', prefix Gamma Gamma' -> forall A annot, proof_ne Gamma annot A -> proof_ne Gamma' annot A).
Proof.
  intros Gamma Gamma' Hle.
  induction Hle.
  
  intros A a r.
  apply r.
  
  intros.
  apply ne_Wkn.
  apply nf_ne.
  auto.
Defined.

Lemma proof_nf_mon2 : (forall A Gamma annot, proof_nf Gamma annot A -> forall annot', leb annot annot' -> proof_nf Gamma annot' A)
with proof_ne_mon2 : (forall A Gamma annot, proof_ne Gamma annot A -> forall annot', leb annot annot' -> proof_ne Gamma annot' A).
Proof.
  intros A Gamma annot p.
  induction p.
  
  intros.
  apply nf_Inl.
  apply IHp.
  assumption.
  
  intros.
  apply nf_Inr.
  apply IHp.
  assumption.
  
  intros.
  apply nf_Lam.
  apply IHp.
  assumption.

  intros.
  apply nf_ne.
  apply proof_ne_mon2 with annot.
  assumption.
  assumption.

  intros.
  inversion H.
  apply nf_Shift.
  apply proof_nf_mon2 with true.
  assumption.
  reflexivity.

  intros A Gamma annot p.
  induction p.
  
  intros.
  apply ne_Hyp.

  intros.
  apply ne_Case with A B.
  apply IHp.
  assumption.
  apply proof_nf_mon2 with annot.
  assumption.
  assumption.
  apply proof_nf_mon2 with annot.
  assumption.
  assumption.
  
  intros.
  apply ne_App with A.
  apply IHp.
  assumption.
  apply proof_nf_mon2 with annot.
  assumption.
  assumption.

  intros.
  apply ne_Reset.
  apply IHp.
  reflexivity.

  intros.
  apply ne_Wkn.
  apply proof_nf_mon2 with annot.
  assumption.
  assumption.
Defined.

(** [forget_nf] forgets the structure NF/NE *)

Theorem forget_nf (Gamma:context)(annot:bool)(A:formula)(r:proof_nf Gamma annot A) : proof Gamma annot A
with forget_ne (Gamma:context)(annot:bool)(A:formula)(e:proof_ne Gamma annot A) : proof Gamma annot A.
Proof.
  induction r.

  apply Inl; assumption.

  apply Inr; assumption.

  apply Lam; assumption.

  apply forget_ne.
  assumption.

  apply Shift; assumption.

  induction e.

  apply Hyp; assumption.

  apply Case with A B.
  assumption.
  apply forget_nf; assumption.
  apply forget_nf; assumption.

  apply App with A.
  assumption.
  apply forget_nf; assumption.

  apply Reset.
  assumption.

  apply Wkn.
  apply forget_nf; assumption.
Defined.


(** For testing purposes we define bare terms *)
Inductive bare : Set :=
| I1 : bare -> bare
| I2 : bare -> bare
| L : bare -> bare
| H : bare
| W : bare -> bare
| C : bare -> bare -> bare -> bare
| A : bare -> bare -> bare
| R : bare -> bare
| S : bare -> bare.

(** [forget_proof] produces a bare structure of a proof term *)
Theorem forget_proof (Gamma:context)(annot:bool)(A:formula)(r:proof Gamma annot A) : bare.
Proof.
  induction r.

  apply I1.
  apply IHr.

  apply I2.
  apply IHr.

  apply L.
  apply IHr.

  apply H.

  apply W.
  apply IHr.

  apply C.
  apply IHr1.
  apply IHr2.
  apply IHr3.

  apply A.
  apply IHr1.
  apply IHr2.

  apply R.
  apply IHr.

  apply S.
  apply IHr.
Defined.

