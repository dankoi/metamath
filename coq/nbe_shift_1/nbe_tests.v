
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
Definition id1 : proof nil false (Func (Atom a) (Atom a)).
Proof.
  apply Lam.
  apply Hyp.
Defined.

Eval compute in (NbE id1).

Definition id2 : proof nil false (Func (Func (Atom a) (Atom a)) (Func (Atom a) (Atom a))).
Proof.
  apply Lam.
  apply Hyp.
Defined.

Eval compute in (NbE id2).

Definition id3 : proof nil false (Func (Func (Func (Atom a) (Atom a)) (Func (Atom a) (Atom a))) (Func (Func (Atom a) (Atom a)) (Func (Atom a) (Atom a)))).
Proof.
  apply Lam.
  apply Hyp.
Defined.

Eval compute in (NbE id3).

Definition id4 : proof nil false (Func (Sum (Atom a) (Atom a)) (Sum (Atom a) (Atom a))).
Proof.
  apply Lam.
  apply Hyp.
Defined.

Eval vm_compute in (NbE id4).

Definition id5 : proof nil false (Func (Func (Sum (Atom a) (Atom a)) (Sum (Atom a) (Atom a))) (Func (Sum (Atom a) (Atom a)) (Sum (Atom a) (Atom a)))).
Proof.
  apply Lam.
  apply Hyp.
Defined.

Eval compute in (NbE id5).

Definition id6 : proof nil false (Func (Func (Sum (Atom a) (Atom a)) (Atom a)) (Func (Sum (Atom a) (Atom a)) (Atom a))).
Proof.
  apply Lam.
  apply Hyp.
Defined.

Eval compute in (NbE id6).

(* (Lam 0 (Lam 1 (Match (Var 1) 2 (App (Var 0) (Inl (Var 2))) 2 (App (Var 0) (Inr (Var 2)))))) *)
Definition id7 : proof nil false  (Func (Func (Sum (Atom a) (Atom a)) (Atom a)) (Func (Sum (Atom a) (Atom a)) (Atom a))).
Proof.
  apply Lam.
  apply Lam.
  apply Case with (Atom a) (Atom a).
  apply Hyp.
  apply App with (Sum (Atom a) (Atom a)).
  apply Wkn.
  apply Wkn.
  apply Hyp.
  constructor.
  apply Hyp.
  apply App with (Sum (Atom a) (Atom a)).
  apply Wkn.
  apply Wkn.
  apply Hyp.
  constructor.
  apply Hyp.
Defined.

Eval compute in (NbE id7).

(** The previous were all old examples from intuitionistic logic with disjunction, let's see some examples with shift. *)

(* (Lam 0 (Lam 1 (Reset (Shift 5 (Var 0))))) *)
Definition id8 : proof nil false  (Func Bot (Func Bot Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply Shift.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (NbE id8).

(* (Lam 0 (Reset (App (Lam 1 (Var 1)) (Shift 5 (Var 0))))) *)
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

Eval compute in (NbE id9).

(* (Lam 0 (Reset (Reset (App (Lam 1 (Var 1)) (Shift 5 (Var 0))))))  *)
Definition id10 : proof nil false (Func Bot Bot).
Proof.
  apply Lam.
  apply Reset.
  apply Reset.
  apply App with Bot.
  apply Lam.
  apply Hyp.
  apply Shift.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (NbE id10).

(* (Lam 0 (Lam 1 (Reset (Reset (App (Var 0) (Var 1)))))) *)
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

Eval compute in (NbE id11).

(* (Lam 0 (Lam 1 (Reset (App (Var 0) (Shift 3 (App (Var 3) (Var 1))))))) *) 
Definition id12 : proof nil false (Func (Func Bot Bot) (Func Bot Bot)).
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
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (NbE id12).

(* (Lam 0 (Lam 1 (Reset (App (Var 0) (Shift 3 (App (Var 3) (App (Var 3) (Var 1))))))))  *)
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

Eval compute in (NbE id13).

(* (Lam 0 (Lam 1 (Reset (App (Var 0) (Reset (App (Var 0) (Shift 3 (App (Var 3) (App (Var 3) (Var 1)))))))))) *)
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

Eval compute in (NbE id14).

(* (Lam 4 (Lam 0 (Lam 1 (Reset (App (Var 4) (Reset (App (Var 0) (Shift 3 (App (Var 3) (App (Var 3) (Var 1))))))))))) *)
Definition id15 : proof nil false (Func (Func Bot Bot) (Func (Func Bot Bot) (Func Bot Bot))).
Proof.
  apply Lam.
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

Eval compute in (NbE id15).

(* (Lam 4 (Lam 0 (Lam 1 (Reset (App (Var 4) (Reset (App (App (Var 0) (Shift 3 (App (Var 3) (App (Var 3) (Var 1))))) (Shift 3 (App (Var 3) (App (Var 3) (Var 1)))))))))))  *)
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

Eval compute in (NbE id16).

(* (Lam 0 (Lam 1 (Reset (App (Var 0) (Shift 3 (Shift 5 (App (Var 3) (App (Var 5) (Var 1)))))))))  *)
Definition id17 : proof nil false (Func (Func Bot Bot) (Func Bot Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply App with Bot.
  apply Wkn.
  apply Hyp.
  apply Shift.
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply App with Bot.
  apply Hyp.
  apply Wkn.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (NbE id17).

(* (Lam 0 (Lam 1 (Reset (App (Var 0) (Shift 3 (Shift 5 (App (Var 5) (App (Var 3) (Var 1)))))))))  *)
Definition id18 : proof nil false (Func (Func Bot Bot) (Func Bot Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply App with Bot.
  apply Wkn.
  apply Hyp.
  apply Shift.
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply App with Bot.
  apply Hyp.
  apply Wkn.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (NbE id18).

(* (Lam 9 (Lam 10 (Lam 0 (Lam 1 (Reset (App (Var 0) (Shift 3 (App (Var 9) (Shift 5 (App (Var 10) ((App (Var 5) (App (Var 3) (Var 1)))))))))))))) *)
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

Eval compute in (NbE id19).

(* (Lam 9 (Lam 10 (Lam 0 (Lam 1 (Reset (App (Var 0) (Shift 3 (App (Var 9) (Shift 5 (App (Var 10) ((App (Var 3) (App (Var 5) (Var 1)))))))))))))) *)
Definition id20 : proof nil false 
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

Eval compute in (NbE id20).

(* (Lam 0 (Lam 1 (Reset (Match (Var 0) 2 (Shift 3 (App (Var 3) (Var 1))) 4 (Var 4))))) *)
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

Eval vm_compute in (NbE id21).

(* (Lam 0 (Lam 1 (Reset (Match (Var 0) 2 (Shift 3 (App (Var 3) (Var 2))) 4 (Var 4))))) *)
Definition id22 : proof nil false (Func (Sum Bot Bot) (Func Bot Bot)).
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

Eval vm_compute in (NbE id22).

(* (Lam 0 (Lam 1 (Reset (App (Lam 2 (Shift 3 (App (Var 3) (Var 0)))) (Var 1)))))  *)
Definition id23 : proof nil false (Func Bot (Func Bot Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply App with Bot.
  apply Lam.
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply Wkn.
  apply Hyp.
  apply Hyp.
Defined.

Eval compute in (NbE id23).

(* (Lam 0 (Lam 1 (Reset (App (Lam 2 (Shift 3 (App (Var 3) (Var 2)))) (Var 1))))) *)
Definition id24 : proof nil false (Func Bot (Func Bot Bot)).
Proof.
  apply Lam.
  apply Lam.
  apply Reset.
  apply App with Bot.
  apply Lam.
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply Wkn.
  apply Hyp.
  apply Hyp.
Defined.

Eval compute in (NbE id24).

(* (Lam 1 (Reset (App (Var 1) (Lam 2 (Shift 3 (App (Var 3) (Var 2)))))))  *)
Definition id25 : proof nil false (Func (Func (Func Bot Bot) Bot) Bot).
Proof.
  apply Lam.
  apply Reset.
  apply App with (Func Bot Bot).
  apply Hyp.
  apply Lam.
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (NbE id25).

(** DNS-Func *)
  (* (Lam 0 (Lam 1 (Reset (App (Var 1) (Lam 2 (Shift 3 (App (App (Var 0) (Var 2)) (Var 3))))))))  *)
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

Eval vm_compute in (NbE test_DNS).

(* (Lam 1 (Reset (App (Var 1) (Lam 2 (Shift 3 (App (Var 3) (App (Var 3) (Var 2)))))))) *)
Definition id26 : proof nil false  (Func (Func (Func Bot Bot) Bot) Bot).
Proof.
  apply Lam.
  apply Reset.
  apply App with (Func Bot Bot).
  apply Hyp.
  apply Lam.
  apply Shift.
  apply App with Bot.
  apply Hyp.
  apply App with Bot.
  apply Hyp.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (NbE id26).

(* (Lam 1 (Reset (App (Var 1) (Lam 2 (Shift 3 (Var 2))))))  *)
Definition id27 : proof nil false (Func (Func (Func Bot Bot) Bot) Bot).
Proof.
  apply Lam.
  apply Reset.
  apply App with (Func Bot Bot).
  apply Hyp.
  apply Lam.
  apply Shift.
  apply Wkn.
  apply Hyp.
Defined.

Eval compute in (NbE id27).
