(** * Additional structure for call-by-value models *)

Require Import model_structure.

Set Implicit Arguments.
Unset Strict Implicit.

Module sforces_cbv (ks : Kripke_structure).
  Export ks.
  Module ks_monad := (Kripke_structure_monad ks).
  Export ks_monad.

  (** [sforces] is the strong forcing relation for call-by-value models *)
  Fixpoint sforces (w:K)(annot:bool)(A:formula) {struct A} : Type :=
    match A with
      | Atom a => X w annot (Atom a)
                    
      | Bot => X w annot Bot
                 
      | Func A1 A2 => 
        forall w', w <= w' -> 
                   forall annot', leb annot annot' ->
                                  sforces w' annot' A1 -> Kont sforces w' annot' A2
                                                             
      | Sum A1 A2 => sum (sforces w annot A1) (sforces w annot A2)
    end.
  
  (** Monotonicity properties of [sforces] *)
  
  Lemma sforces_mon : forall A w annot, sforces w annot A -> 
                      forall w', w <= w' -> sforces w' annot A.
  Proof.
    induction A.
    
    simpl.
    eauto using X_mon.
    
    simpl.
    eauto using X_mon.
    
    intros w annot H1 w' ww'.
    simpl in *.
    eauto using wle_trans.
    
    intros w annot H1 w' ww'.
    simpl in *.
    case H1; intro H'.
    eauto using wle_trans.
    eauto using wle_trans.
  Defined.
  
  Lemma sforces_mon2 : forall A w, sforces w false A -> sforces w true A.
  Proof.
    induction A.
    
    simpl.
    intros.
    apply X_mon2 with false.
    assumption.
    reflexivity.
    
    simpl.
    intros.
    apply X_mon2 with false.
    assumption.
    reflexivity.
    
    intros w H.
    simpl in *.
    intros w' ww' annot' Hannot'.
    apply H.
    assumption.
    constructor.
    
    intros w H1.
    simpl in *.
    destruct H1; auto.
  Defined.

  (** This lemma can be proved, but it is not used for CBV *)
  Lemma Kont_sforces_mon2 : forall w annot A, Kont sforces w annot A -> 
        forall annot', leb annot annot' ->  Kont sforces w annot' A.
  Proof.
    intros w annot A H annot' Hleb.
    destruct annot;destruct annot'.
    assumption.
    simpl in Hleb.
    congruence.
    intros w'' w'w'' k.
    unfold Kont in H.
    apply X_mon2 with false.
    apply H.
    eauto using wle_trans.
    intros w2 w''w2 HA.
    apply X_reset.
    apply k.
    assumption.
    apply sforces_mon2.
    assumption.
    reflexivity.
    assumption.
  Defined.
  
  (** The "run" of the continuations monad *)
  Definition run {w annot} :
    Kont sforces w annot Bot -> X w annot Bot.
  Proof.
    intro H.
    destruct annot.
    
    apply H.
    apply wle_refl.
    simpl.
    auto.

    apply H.
    apply wle_refl.
    simpl.
    auto.
  Defined.
End sforces_cbv.
