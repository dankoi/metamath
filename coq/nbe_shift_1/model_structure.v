(** * A carrier structure for the models *)

Require Export syntax.

Set Implicit Arguments.
Unset Strict Implicit.

(** A structure that validity will be defined on: 

    - a pre-order [wle] of worlds [K]

    - a monotone "exploding node" predicate [X] on worlds and
      formulas, stratified at two levels (the boolean flag), one
      intuitionistic, the other classical

    - a meta-level reset to go down from the classical to the
      intuitionistic level when the distinguished atomic formula [Bot]
      is being exploded on.  
*)

Module Type Kripke_structure.
    Parameter Inline K : Set.
  
    Parameter wle : K -> K -> Set.
    Axiom wle_refl : forall w, wle w w.
    Axiom wle_trans : forall w w' w'', wle w w' -> wle w' w'' -> wle w w''.

    Parameter X : K -> bool -> formula -> Set.
    Axiom X_mon : forall w annot A, X w annot A -> 
                              forall w', wle w w' -> X w' annot A.
    Axiom X_mon2 : forall w annot A, X w annot A -> 
                               forall annot', leb annot annot' -> X w annot' A.
    Axiom X_reset : forall w annot, X w true Bot -> X w annot Bot.

    Notation "w <= w'" := (wle w w').
End Kripke_structure.

Module Kripke_structure_monad (ks : Kripke_structure).
  Export ks.

  (** [Kont] is the dependently typed continuations "monad" that will
   be used to define "weak forcing" given a more primitive relation
   [F] of "strong forcing" *)

  Definition Kont (F:K->bool->formula->Type)(w:K)(annot:bool)(A:formula) := 
    (** forcing at classical level: *) 
    if annot then 
      (forall w1, w <= w1 -> 
         (forall w2, w1 <= w2 -> F w2 annot A -> X w2 annot Bot) -> X w1 annot Bot)
    (** forcing at intuitionistic level: *) 
    else
      (forall C,
       forall w1, w <= w1 -> 
         (forall w2, w1 <= w2 -> F w2 annot A -> X w2 annot C) -> X w1 annot C).
  
  Hint Unfold Kont.

  (** Monotonicity property for [wle] of [Kont] (that does not depend on
    the one of its parameter [F]) *)
  Lemma Kont_mon {F} : 
    forall w annot A, Kont F w annot A -> forall w', w <= w' ->  Kont F w' annot A.
  Proof.
    intros w annot A H w' ww'.
    destruct annot.
    intros w'' w'w'' k.
    unfold Kont in H.
    apply H.
    eauto using wle_trans.
    assumption.
    intros C w'' w'w'' k.
    unfold Kont in H.
    apply H.
    eauto using wle_trans.
    assumption.
  Defined.
End Kripke_structure_monad.

(** A module type that prescribes what is expected of [sforces], which
    is concretelly defined later vo CBV/CBN, so that generic
    properties (also proved later) can be stated. *)

Module Type sforces_instance (ks : Kripke_structure).
  Export ks.
  Module ks_monad := Kripke_structure_monad ks.
  Export ks_monad.

  Parameter sforces : K->bool->formula->Type.
  Parameter sforces_mon : forall A w annot, sforces w annot A -> 
                          forall w', w <= w' -> sforces w' annot A.
  Parameter sforces_mon2 : forall A w, sforces w false A -> sforces w true A.
  Parameter Kont_sforces_mon2 : forall w annot A, 
      Kont sforces w annot A -> 
      forall annot', leb annot annot' ->  Kont sforces w annot' A.
End sforces_instance.
