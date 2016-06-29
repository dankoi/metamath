(** * reify.v

This file defines two reifiers:

- [sreify], mapping the semantics to the lambda calculus [ND]
- [dreify]/[creify], mapping the semantics to the compact calculus [HSb]/[HSc]

 *)
Require Export syntax.
Require Export semantics.

Set Implicit Arguments.

Open Scope type_scope.

Module structureND <: ForcingStructure.
  Export NaturalDeduction.
  
  Definition K := list Formula.
  
  Inductive le_ : list Formula -> list Formula -> Set :=
  | le__refl : forall {w}, le_ w w
  | le__cons : forall {w1 w2 F},
      le_ w1 w2 -> le_ w1 (cons F w2).
  
  Definition le := le_.
  
  Definition le_refl : forall {w}, le w w.
  Proof.
    intro c.
    apply le__refl.
  Defined.
  
  Lemma le_trans : forall {w1 w3},
      forall w2, le w1 w2 -> le w2 w3 -> le w1 w3.
  Proof.
    intros w1 w3 w2 le2 le3.
    induction le3.
    assumption.
    constructor.
    apply IHle3.
    assumption.
  Defined.
  
  Definition pforces := fun w p => ND w (prop p).
  
  Definition Answer := Formula.
  
  Definition X :=  fun w F => ND w F.
  
  Lemma pforces_mon : forall {w' p},
      forall w, le w w' -> pforces w p -> pforces w' p.
  Proof.
    intros w' p w.
    induction 1.
    - intro H.
      apply H.
    - intro H1.
      apply IHle_ in H1.
      apply wkn.
      apply H1.      
  Defined.
End structureND.

Module structureHS <: ForcingStructure.
  Export HighSchool.
  
  Definition K := CNF.
  
  Inductive le_ : CNF -> CNF -> Set :=
    le__refl : forall {w}, le_ w w
  | le__cons : forall {w1 w2 c b},
      le_ w1 w2 -> le_ w1 (con c b w2).
  
  Definition le := le_.
  
  Definition le_refl : forall {w}, le w w.
  Proof.
    intro c.
    apply le__refl.
  Defined.
  
  Lemma le_trans : forall {w1 w3},
      forall w2, le w1 w2 -> le w2 w3 -> le w1 w3.
  Proof.
    intros w1 w3 w2 le2 le3.
    induction le3.
    assumption.
    constructor.
    apply IHle3.
    assumption.
  Defined.
  
  Definition pforces := fun w p => HSb w (prp p).
  
  Definition Answer := Base.
  
  Definition X : K -> Base -> Set
    := fun w b => HSb w b.
  
  Lemma pforces_mon : forall {w' p},
      forall w, le w w' -> pforces w p -> pforces w' p.
  Proof.
    intros w' p w.
    induction 1.
    - intro H.
      apply H.
    - intro H1.
      apply IHle_ in H1.
      unfold pforces.
      replace (con c b w2) with (ntimes (con c b top) w2); [|reflexivity].
      apply wkn.
      apply H1.      
  Defined.
End structureHS.

Module ReifyND.
  Module forcingND := Forcing structureND.
  Export forcingND.

  Lemma ND_mon {Gamma Gamma' A} :
    le Gamma Gamma' -> ND Gamma A -> ND Gamma' A.
  Proof.
    induction 1.
    - intro H.
      apply H.
    - intro HA.
      apply wkn.
      apply IHle_.
      apply HA.
  Defined.

  Theorem preify : forall p w,
      Cont sforces w (prop p) -> ND w (prop p).
  Proof.
    intros.
    apply (H (prop p)).
    apply le_refl.
    intros w1 le1 H1.
    simpl in H1.
    apply H1.
  Defined.

  Theorem sreify : (forall F w, Cont sforces w F -> ND w F)
  with sreflect : (forall F w, ND w F -> Cont sforces w F).
  Proof.
    { induction F.
      - apply preify.
      - intros.
        apply H.
        apply le_refl.      
        intros w1 le1 H1.
        simpl in H1.
        destruct H1.
        apply inl.
        apply IHF1.
        assumption.
        apply inr.
        apply IHF2.
        assumption.
      - intros.
        apply H.
        apply le_refl.
        intros w1 le1 H1.
        apply pair.
        apply IHF1.
        apply H1.
        apply IHF2.
        apply H1.
      - intros.
        apply lam.
        apply IHF2.
        eapply ssbind.
        + eapply Cont_sforces_mon.
          eapply le__cons.
          apply le_refl.
          apply H.
        + intros w1 le1 H1.
          apply H1.
          apply le_refl.
          eapply Cont_sforces_mon.        
          apply le1.                         
          apply sreflect.
          apply hyp. }
    { induction F.
      - intros.
        apply sret.
        apply H.
      - intros.
        intros C w1 le1 k1.
        eapply cas.
        + eapply ND_mon.
          apply le1.
          apply H.
        + apply k1.
          apply le__cons.
          apply le_refl.
          left.
          apply sreflect.
          apply hyp.
        + apply k1.
          apply le__cons.
          apply le_refl.
          right.
          apply sreflect.
          apply hyp.
      - intros.
        apply sret.
        split.
        apply IHF1.
        eapply fst.
        apply H.
        apply IHF2.
        eapply snd.
        apply H.
      - intros.
        apply sret.
        intros w1 le1 H1.
        apply IHF2.
        eapply app.
        eapply ND_mon.
        apply le1.
        apply H.
        apply sreify.
        apply H1. }
  Defined.
End ReifyND.

Module ReifyHS.
  Module forcingHS := Forcing structureHS.
  Export forcingHS.

  Lemma le_ntimes : forall w w' c, le w w' -> le w (ntimes c w').
  Proof.
    intros.
    induction c.
    - simpl.
      assumption.  
    - simpl.
      apply le__cons.
      assumption.
  Defined.

  Lemma le_ntimes' : forall w w1,
      le w w1 -> {c2 : CNF & w1 = ntimes c2 w}.
  Proof.
    intros.
    induction H.
    - exists top.
      reflexivity.    
    - destruct IHle_ as [c2 IH].
      exists (con c b c2).
      simpl.
      rewrite IH.    
      reflexivity.
  Defined.

  Lemma cpbind {w:K}{x:CNF}{y:Proposition} :
    Cont cforces w x ->
    (forall {w'}, le w w' -> cforces w' x -> Cont pforces w' y) ->
    Cont pforces w y.
  Proof.
    intros H f.
    intros x0 w1 le1 k1.
    apply H.
    assumption.    
    intros w2 le2 H2.
    apply (f w2).
    apply le_trans with w1; assumption.
    assumption.
    apply le_refl.    
    intros w3 le3 H3.
    apply k1.
    apply le_trans with w2; assumption.
    assumption.
  Defined.

  Theorem preify : (forall p w, Cont pforces w p -> HSb w (prp p)).
  Proof.
    intros.
    apply (H (prp p)).
    apply le_refl.
    intros w1 le1 H1.
    simpl in H1.
    apply H1.
  Defined.

  Theorem creify : (forall c w, Cont cforces w c -> HSc (explogn c (cnf w)))
  with creflect : (forall c w, Cont cforces (ntimes c w) c)
  with dreify : (forall d w, Cont dforces w d -> HSb w (bd d))
  with dreflect : (forall d c1 c2 c3, 
                      HSc (explogn c1 (cnf (ntimes c3 (con c1 (bd d) c2)))) ->
                      Cont dforces (ntimes c3 (con c1 (bd d) c2)) d).
  Proof.
    { induction c.
      - intros.
        simpl.
        apply tt.
      - clear IHc1.
        simpl.
        intros.
        apply pair.
        + clear IHc2.
          destruct b.
          { apply preify.
            apply (cpbind (x := con c1 (prp p) c2)).
            apply (Cont_cforces_mon (w:=w)).
            apply le_ntimes.
            apply le_refl.
            assumption.
            clear H.
            intros w1 le1 H1.
            simpl in H1.
            apply H1.
            apply le_refl.
            apply (Cont_cforces_mon (w := ntimes c1 w)).
            assumption.
            apply creflect. }
          { apply dreify.
            apply (cdbind (x := con c1 (bd d) c2)).
            apply (Cont_cforces_mon (w:=w)).
            apply le_ntimes.
            apply le_refl.
            assumption.
            clear H.
            intros w1 le1 H1.
            simpl in H1.
            apply H1.
            apply le_refl.
            apply (Cont_cforces_mon (w := ntimes c1 w)).
            assumption.
            apply creflect. }
        + apply (IHc2 w).
          apply (ccbind (x := (con c1 b c2))).
          assumption.
          intros w1 le1 H1.
          simpl in H1.
          apply H1. }
    { induction c.
      - intros.
        apply cret.
        constructor.
      - simpl.
        intro w.
        apply cret.
        split.
        + intros w1 le1 H1.
          apply creify in H1.
          apply le_ntimes' in le1.
          destruct le1 as [c3 H3].
          rewrite H3 in *.
          destruct b.
          * apply bret.
            apply app.
            apply H1.
          * apply dreflect.
            apply H1.
        + apply (Cont_cforces_mon (w := ntimes c2 w)).
          constructor; constructor.
          apply IHc2. }
    { induction d.
      - intros.
        apply (H (bd (two c c0))).
        apply le_refl.
        intros w1 le1 H1.
        clear H.
        destruct H1.
        + apply creify in c1.
          apply inl_two.
          assumption.        
        + apply creify in c1.
          apply inr_two.
          assumption.
      - intros.
        apply (H (bd (dis c d))).
        apply le_refl.
        intros w1 le1 H1.
        clear H.
        destruct H1.
        + apply creify in c0.
          apply inl_dis.
          assumption.        
        + apply inr_dis.
          apply IHd.
          assumption. }
    { intro d.
      intros.
      intros b1 w1 le1 k1.
      apply le_ntimes' in le1.
      destruct le1 as [c4 eq4].
      rewrite eq4 in *.
      { apply (cas (c1:=c1) (d:=d)).
        apply H.    
        clear - k1 creflect.
        generalize dependent k1.
        generalize d at 1 4.
        intros.
        induction d.
        - simpl in *.
          apply pair.
          + apply k1.
            apply le_ntimes.
            apply le_refl.
            left.
            apply creflect.
          + apply pair.
            apply k1.
            apply le_ntimes.
            apply le_refl.
            right.
            apply creflect.
            apply tt.
        - simpl in *.
          apply pair.
          + apply k1.
            apply le_ntimes.
            apply le_refl.
            left.
            apply creflect.
          + apply IHd.
            intros w2 le2 H2.
            apply k1.
            assumption.
            right.
            apply dret.
            assumption. } }
  Defined.
End ReifyHS.
