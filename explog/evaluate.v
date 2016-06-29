(** * evaluate.v

This file defines two evaluators:

- [eval], mapping the lambda calculus [ND] to its semantics
- [evalb]/[evalc], mapping the compact calculus [HSb]/[HSc] to its semantics

 *)
Require Export syntax.
Require Export semantics.

Set Implicit Arguments.

Module EvalND (fs : ForcingStructure).
  Module forcingND := Forcing fs.
  Export forcingND.
  Export NaturalDeduction.

  Fixpoint
    lforces (w:K)(Gamma:list Formula) {struct Gamma} : Set :=
    match Gamma with
    | nil => unit
    | cons A Gamma0 =>
      Cont sforces w A * lforces w Gamma0
    end.

  Lemma lforces_mon : forall {w w' Gamma},
      le w w' -> lforces w Gamma -> lforces w' Gamma.
  Proof.
    intros w w' Gamma.
    generalize dependent w'.
    generalize dependent w.
    induction Gamma.
    - simpl.
      intros.
      constructor.
    - simpl.
      intros.      
      split.
      apply (Cont_sforces_mon (w:=w)).
      assumption.      
      apply H0.
      apply IHGamma with w.
      assumption.
      apply H0.
  Defined.

  Theorem eval {A Gamma} : ND Gamma A -> forall {w},
        lforces w Gamma -> Cont sforces w A.
  Proof.
    induction 1.
    - simpl.
      intros.
      apply H.
    - simpl.
      intros.
      apply IHND.
      apply H0.      
    - simpl.
      intros.
      apply sret.
      simpl.      
      intros w1 le1 H1.
      apply IHND.
      split.
      assumption.      
      apply (lforces_mon (w:=w)); assumption.
    - intros.
      apply (ssbind (x := impl A B)).
      apply IHND1.
      assumption.
      intros.
      apply H3.      
      apply le_refl.
      apply IHND2.
      apply (lforces_mon (w:=w)); assumption.
    - intros.
      apply sret.
      split.
      apply IHND1.
      assumption.
      apply IHND2.
      assumption.
    - intros.
      apply (ssbind (x := conj A B)).
      apply IHND.
      assumption.      
      intros.
      apply H2.      
    - intros.
      apply (ssbind (x := conj A B)).
      apply IHND.
      assumption.      
      intros.
      apply H2.      
    - intros.
      apply sret.
      left.
      apply IHND; assumption.
    - intros.
      apply sret.
      right.
      apply IHND; assumption.
    - intros.
      apply (ssbind (x := disj A B)).
      apply IHND1.      
      assumption.
      intros.
      simpl in *.
      destruct H4.
      + apply IHND2.
        split.
        assumption.
        apply (lforces_mon (w:=w)).
        assumption.
        assumption.
      + apply IHND3.
        split.
        assumption.
        apply (lforces_mon (w:=w)).
        assumption.
        assumption.
  Defined.
End EvalND.

Module EvalHS (fs : ForcingStructure).
  Module forcingHS := Forcing fs.
  Export forcingHS.
  Export HighSchool.

  Theorem evalc {c} : (HSc c -> forall {w}, Cont cforces w c)
  with evalb {b c0} : (HSb c0 b -> forall {w},
                          Cont cforces w c0 -> Cont bforces w b).
  Proof.
    { induction 1.
      - intros.
        apply cret.
        constructor.
      - intros.
        apply cret.
        split.
        + intros w1 le1 H1.
          eapply evalb in h.
          apply h.
          assumption.
        + apply IHHSc. }
    { induction 1.
      - intros.
        eapply evalc in h.
        eapply exp_meta in h.
        Focus 3.
        apply H.        
        apply cforces_ntimes_2 in H.
        destruct H as [_ H].
        eapply cbbind.
        apply H.        
        intros w1 le1 H1.
        apply H1.
        apply le_refl.
        eapply Cont_cforces_mon.
        apply le1.
        assumption.
        apply le_refl.
      - intros.
        eapply evalc in h.
        eapply exp_meta in h.
        Focus 3.
        apply cforces_ntimes_2 in H.
        apply H.        
        eapply evalc in h0.
        eapply exp_meta in h0.
        Focus 3.
        apply H.        
        eapply exp_meta_b in h0.
        apply h0.
        apply le_refl.
        rewrite <- ntimes_assoc in H.
        apply cforces_ntimes_2 in H.
        destruct H as [_ H].    
        eapply cdbind.
        apply H.
        intros w1 le1 H1.
        simpl in H1.
        apply H1.
        apply le_refl.
        eapply Cont_cforces_mon.
        apply le1.
        apply h.
        apply le_refl.
        apply le_refl.
      - intros.
        eapply cbbind.
        apply H0.
        intros w1 le1 H1.
        simpl in H1.
        destruct H1 as [_ H1].
        apply IHHSb.
        assumption.
      - intros.
        eapply evalc in h.
        eapply exp_meta in h.
        Focus 3.
        apply H.
        apply bret.
        left.
        assumption.
        apply le_refl.
      - intros.
        eapply evalc in h.
        eapply exp_meta in h.
        Focus 3.
        apply H.
        apply bret.
        right.
        assumption.
        apply le_refl.
      - intros.
        eapply evalc in h.
        eapply exp_meta in h.
        Focus 3.
        apply H.
        apply bret.
        left.
        assumption.
        apply le_refl.
      - intros.
        apply bret.
        right.
        apply IHHSb.
        assumption. }
  Defined.
End EvalHS.
