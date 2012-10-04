(** * Generic constructions for the models, regardless of CBV/CBN *)

Require Import model_structure.

Set Implicit Arguments.
Unset Strict Implicit.

Module forcing_generic_properties (ks : Kripke_structure)(sforces_implementation : sforces_instance ks).
  Export ks.
  Module ks_monad := Kripke_structure_monad ks.
  Export ks_monad.
  Export sforces_implementation.

  Notation " w ||- A ; annot " := (Kont sforces w annot A) (at level 70).

  (** monadic unit and bind (no monad laws à la functional programming
    are checked, since this is not necessary for our purposes, that
    are just to use them to structure proofs) *)
  Definition ret {w annot A} : sforces w annot A -> Kont sforces w annot A.
  Proof.
    intros H.
    destruct annot.
    
    intros w1 wle1 k1.
    apply k1.
    apply wle_refl.
    apply sforces_mon with w.
    assumption.
    assumption.
    
    intros C w1 ww1 k.
    apply k.
    apply wle_refl.
    apply sforces_mon with w.
    assumption.
    assumption.
  Defined.

  Definition bind {w annot A B} : 
    (forall w', w <= w' -> sforces w' annot A -> Kont sforces w' annot B) -> 
    Kont sforces w annot A -> Kont sforces w annot B.
  Proof.
    intros f a.
    destruct annot.
    
    intros w1 wle1 k1.
    apply a.
    assumption.
    intros w2 wle2 a2.
    simpl in f.
    apply f with w2.
    eauto using wle_trans.
    assumption.
    apply wle_refl.
    intros w3 wle3 b3.
    apply k1.
    eauto using wle_trans.
    assumption.

    intros C1 w1 wle1 k1.
    apply a.
    assumption.
    intros w2 wle2 a2.
    simpl in f.
    apply f with w2.
    eauto using wle_trans.
    assumption.
    apply wle_refl.
    intros w3 wle3 b3.
    apply k1.
    eauto using wle_trans.
    assumption.
  Defined.

  (** The [sforce] and [Kont] defined on *lists* of formulas *)

  Fixpoint sforces_cxt (w:K)(annot:bool)(Gamma:context) : Type :=
    match Gamma with
      | nil => unit
      | cons aA Gamma' => 
        prod (sforces w annot aA) (sforces_cxt w annot Gamma')
    end.

  Notation " w ||++ Gamma ; annot " := (sforces_cxt w annot Gamma) (at level 70).

  Lemma sforces_cxt_mon : forall Gamma w annot, w ||++ Gamma ; annot -> 
                          forall w', w <= w' -> w' ||++ Gamma ; annot.
  Proof.
    induction Gamma.
    simpl.
    auto.
    simpl.
    intros w annot H w' w_w'.
    destruct H.
    split; eauto using wle_trans,sforces_mon.
  Defined.

  Lemma sforces_cxt_mon2 : forall Gamma w annot, w ||++ Gamma ; annot -> 
                           forall annot', leb annot annot' -> w ||++ Gamma ; annot'.
  Proof.
    induction Gamma.
    simpl.
    auto.
    simpl.
    intros w annot H annot' Hleb.
    destruct H.
    split.
    destruct annot';destruct annot.
    assumption.
    eauto using sforces_mon2.
    simpl in Hleb.
    congruence.
    assumption.
    eauto.
  Defined.

  Fixpoint Kont_cxt (w:K)(annot:bool)(Gamma:context) : Type :=
    match Gamma with
      | nil => unit
      | cons aA Gamma' => 
        prod (Kont sforces w annot aA) (Kont_cxt w annot Gamma')
    end.

  Notation " w ||-- Gamma ; annot " := (Kont_cxt w annot Gamma) (at level 70).

  Lemma Kont_cxt_mon : forall Gamma w annot, w ||-- Gamma ; annot -> 
                       forall w', w <= w' -> w' ||-- Gamma ; annot.
  Proof.
    induction Gamma.
    simpl.
    auto.
    simpl.
    intros w annot H w' w_w'.
    destruct H.
    split; eauto using wle_trans,Kont_mon.
  Defined.

  Lemma Kont_sforces_cxt_mon2 : forall Gamma w annot, w ||-- Gamma ; annot -> 
                                forall annot', leb annot annot' -> w ||-- Gamma ; annot'.
  Proof.
    induction Gamma.
    simpl.
    auto.
    simpl.
    intros w annot H annot' Hleb.
    destruct H.
    split.
    destruct annot';destruct annot.
    assumption.
    eauto using Kont_sforces_mon2.
    simpl in Hleb.
    congruence.
    assumption.
    eauto.
  Defined.
End forcing_generic_properties.
