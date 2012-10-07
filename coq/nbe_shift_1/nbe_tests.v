
Require Import syntax.
Require Import nbe_cbv_atomic.
Require Import nbe_cbn_atomic.

Set Implicit Arguments.
Unset Strict Implicit.

Parameter a:atoms.

Definition nbe_v := nbe_cbv_atomic.Completeness.NbE.
Definition nbe_n := nbe_cbn_atomic.Completeness.NbE.

Check nbe_v.

Definition NbE {A} : proof nil false A -> bare * bare := fun p => (forget_proof (forget_nf (nbe_v p)) , forget_proof (forget_nf (nbe_n p))).

(** Some tests of the normalization algorithm *)

Definition id8 : proof nil false  (Func Bot (Func Bot Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply Shift.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof id8).
Eval compute in (NbE id8).

Definition id9 : proof nil false (Func Bot Bot).
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

Eval compute in (forget_proof id9).
Eval compute in (NbE id9).

Definition id10 : proof nil false (Func Bot Bot).
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

Eval compute in (forget_proof id10).
Eval compute in (NbE id10).

Definition id11 : proof nil false (Func (Func Bot Bot) (Func Bot Bot)).
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

Eval compute in (forget_proof id11).
Eval compute in (NbE id11).

Definition id13 : proof nil false (Func (Func Bot Bot) (Func Bot Bot)).
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

Eval compute in (forget_proof id13).
Eval compute in (NbE id13).

Definition id14 : proof nil false (Func (Func Bot Bot) (Func Bot Bot)).
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

Eval compute in (forget_proof id14).
Eval compute in (NbE id14).

Definition id16 : proof nil false (Func (Func Bot Bot) (Func (Func Bot (Func Bot Bot)) (Func Bot Bot))).
Proof.
  apply Lam.
  apply Lam.
  apply Lam.
  apply Reset.
  apply App with Bot.
  apply Wkn.
  apply Wkn.
  apply Hyp.
  apply Reset.
  apply App with Bot.
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
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply App with Bot.
  apply Hyp.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof id16).
Eval compute in (NbE id16).

Definition id19 : proof nil false 
  (Func (Func Bot Bot)
       (Func (Func Bot Bot)
            (Func (Func Bot Bot) (Func Bot Bot)))).
Proof.
  apply Lam.
  apply Lam.
  apply Lam.
  apply Lam.
  apply Reset.
  apply App with Bot.
  apply Wkn.
  apply Hyp.
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply App with Bot.
  apply Hyp.
  apply App with Bot.
  apply Hyp.
  apply Wkn.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (forget_proof id19).
Eval compute in (NbE id19).

Definition id21 : proof nil false (Func (Sum Bot Bot) (Func Bot Bot)).
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

Eval compute in (forget_proof id21).
Eval vm_compute in (NbE id21).

(** Implicational version of DNS *)
Definition test_DNS : proof nil false 
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

Eval compute in (forget_proof test_DNS).
Eval vm_compute in (NbE test_DNS).
