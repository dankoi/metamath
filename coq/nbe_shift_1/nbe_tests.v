
Require Import syntax.
Require Import nbe_cbv_atomic.
Require Import nbe_cbn_atomic.

Set Implicit Arguments.
Unset Strict Implicit.

Parameter a b:atoms.

Definition nbe_v := nbe_cbv_atomic.Completeness.NbE.
Definition nbe_n := nbe_cbn_atomic.Completeness.NbE.

Definition NbE_v {A} : proof nil false A -> bare := fun p => (forget_proof (forget_nf (nbe_v p))).

Definition NbE_n {A} : proof nil false A -> bare := fun p => (forget_proof (forget_nf (nbe_n p))).

Definition NbE {A} : proof nil false A -> bare * bare := fun p => (NbE_v p, NbE_n p).


(** Some tests of the normalization algorithm *)

(** \x.<(\y.y)(Sk.x)> *)
Definition test_16 : proof nil false (Func Bot Bot).
Proof.
  apply Lam.
  apply Reset.
  apply App with Bot.
  apply Lam.
  apply Hyp.
  apply Shift.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_16). 
Eval compute in (NbE test_16).

(** \x.<<<(\y.y)(Sk.x)>>> *)
Definition test_17 : proof nil false (Func Bot Bot).
Proof.
  apply Lam.
  apply Reset.
  apply Reset.
  apply Reset.
  apply App with Bot.
  apply Lam.
  apply Hyp.
  apply Shift.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_17).
Eval compute in (NbE test_17).

(** \x.<<xy>> *)
Definition test_18 : proof nil false (Func (Func Bot Bot) (Func Bot Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply Reset.
  apply App with Bot.
  apply Wkn.
  apply Hyp.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_18).
Eval compute in (NbE test_18).

(** \xy.<x(Sk.k(ky))> *)
Definition test_19 : proof nil false (Func (Func Bot Bot) (Func Bot Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply App with Bot.
  apply Wkn.
  apply Hyp.
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply App with Bot.
  apply Hyp.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_19).
Eval compute in (NbE test_19).

(** \xy.<(\a.<xa>)<xy>> *)
Definition test_19' : proof nil false (Func (Func Bot Bot) (Func Bot Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply App with Bot.
  apply Lam.
  apply Reset.
  eapply App.
  apply Wkn.
  apply Wkn.
  apply Hyp.
  apply Hyp.
  apply Reset.
  eapply App.
  apply Wkn.
  apply Hyp.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_19').
Eval compute in (NbE_v test_19').

(** \xy.<x<x(Sk.k(ky))>>*)
Definition test_20 : proof nil false (Func (Func Bot Bot) (Func Bot Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply App with Bot.
  apply Wkn.
  apply Hyp.
  apply Reset.
  apply App with Bot.
  apply Wkn.
  apply Hyp.
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply App with Bot.
  apply Hyp.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_20).
Eval compute in (NbE test_20).

(** \xy.<(Sk.ky)x> *)
Definition test_21 : proof nil false (Func Bot (Func (Func Bot Bot) Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply App with Bot.
  apply Shift.
  eapply App.
  apply Hyp.
  apply Wkn.
  apply Hyp.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_21).
Eval compute in (NbE test_21).

(** \xy.<<yx>> *)
Definition test_21' : proof nil false (Func Bot (Func (Func Bot Bot) Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply Reset.
  eapply App.
  apply Hyp.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_21').
Eval compute in (NbE_v test_21').

(** \xy.<yx> *)
Definition test_21'' : proof nil false (Func Bot (Func (Func Bot Bot) Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  eapply App.
  apply Hyp.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_21'').
Eval compute in (NbE_n test_21'').

(** \xyz. <(Sk.y(kz))(Sk'.z(k'x))>*)
Definition test_22 : proof nil false (Func Bot (Func (Func Bot Bot) (Func (Func Bot Bot) Bot))).
Proof.
  apply Lam.
  apply Lam.
  apply Lam.
  apply Reset.
  eapply App.
  apply Shift.
  eapply App.
  apply Wkn.
  apply Wkn.
  apply Hyp.
  eapply App.
  apply Hyp.
  apply Wkn.
  apply Hyp.
  apply Shift.
  eapply App.
  apply Wkn.
  apply Hyp.
  eapply App.
  apply Hyp.
  apply Wkn.
  apply Wkn.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_22).
Eval compute in (NbE test_22).

(** \xyz. <y<z<zx>>> *)
Definition test_22' : proof nil false (Func Bot (Func (Func Bot Bot) (Func (Func Bot Bot) Bot))).
Proof.
  apply Lam.
  apply Lam.
  apply Lam.
  apply Reset.
  eapply App.
  apply Wkn.
  apply Hyp.
  apply Reset.
  eapply App.
  apply Hyp.
  apply Reset.
  eapply App.
  apply Hyp.
  apply Wkn.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_22').
Eval compute in (NbE_v test_22').

(** \xyz. <y<z(Sk'.z(k'x))>> *)
Definition test_22'' : proof nil false (Func Bot (Func (Func Bot Bot) (Func (Func Bot Bot) Bot))).
Proof.
  apply Lam.
  apply Lam.
  apply Lam.
  apply Reset.
  eapply App.
  apply Wkn.
  apply Hyp.
  apply Reset.
  eapply App.
  apply Hyp.
  apply Shift.
  eapply App.
  apply Wkn.
  apply Hyp.
  eapply App.
  apply Hyp.
  apply Wkn.
  apply Wkn.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_22'').
Eval compute in (NbE_n test_22'').

(** \xy.<case x of (z.Sk.kz || z.z) *)
Definition test_23 : proof nil false (Func (Sum Bot Bot) (Func Bot Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply Case with Bot Bot.
  apply Wkn.
  apply Hyp.
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply Wkn.
  apply Hyp.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_23).
Eval vm_compute in (NbE test_23).

(** Implicational version of DNS *)
Definition test_DNS_imp : proof nil false 
  (Func
    (Func (Atom a) (Func (Func (Atom a) Bot) Bot))
    (Func (Func (Func (Atom a) (Atom a)) Bot) Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply App with (Func (Atom a) (Atom a)).
  apply Hyp.
  apply Lam.
  apply Shift.
  apply App with (Func (Atom a) Bot).
  apply App with (Atom a).
  apply Wkn.
  apply Wkn.
  apply Wkn.
  apply Hyp.
  apply Wkn.
  apply Hyp.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_DNS_imp).
Eval vm_compute in (NbE test_DNS_imp).

(** Implicational version of DNS (sums instead of functions) *)
Definition test_DNS_sums : proof nil false 
                            (Func (Func (Sum (Atom a) (Func (Atom a) Bot)) Bot) Bot).
Proof.
  apply Lam.
  apply Reset.
  apply App with (Sum (Atom a) (Func (Atom a) Bot)).
  apply Hyp.
  apply Shift.
  apply App with (Sum (Atom a) (Func (Atom a) Bot)).
  apply Hyp.
  apply Inr.
  apply Lam.
  apply App with (Sum (Atom a) (Func (Atom a) Bot)).
  apply Wkn.
  apply Hyp.
  apply Inl.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_DNS_sums).
Eval vm_compute in (NbE test_DNS_sums).

(** Implicational version of DNS (sums instead of functions) + simulating quantifier *)
Definition test_DNS_sums_quant : proof nil false 
                            (Func (Func (Func (Atom b) (Sum (Atom a) (Func (Atom a) Bot))) Bot) Bot).
Proof.
  apply Lam.
  apply Reset.
  apply App with (Func (Atom b) (Sum (Atom a) (Func (Atom a) Bot))).
  apply Hyp.
  apply Lam.
  apply Shift.
  apply App with (Sum (Atom a) (Func (Atom a) Bot)).
  apply Hyp.
  apply Inr.
  apply Lam.
  apply App with (Sum (Atom a) (Func (Atom a) Bot)).
  apply Wkn.
  apply Hyp.
  apply Inl.
  apply Hyp.
Defined.

Eval compute in (forget_proof test_DNS_sums_quant).
Eval vm_compute in (NbE test_DNS_sums_quant).

