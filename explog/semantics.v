(** * semantics.v

This file defines the semantic domains used by the TDPE procedures, a
continuation monad over [sforces], and continuation monads over
[bforces], [cforces], [dforces], and [eforces]. There are also various
utility functions/lemmas defined for working with the semantics, and
that are needed outside this file.

Importantly, the functions [f2f] and [f2f'] are defined that allow to 
switch back and forth between the continuation monads, whenever they 
are instantiated by isomorphis types.

 Danko Ilik, 2016
 
*)
Require Export syntax.

Module Type ForcingStructure.
  Parameter K : Set.
  Parameter le : K -> K -> Set.
  Parameter pforces : K -> Proposition -> Set.
  Parameter Answer : Set.
  Parameter X  : K -> Answer -> Set.
  Parameter le_refl : forall {w}, le w w.
  Parameter le_trans : forall {w1 w3}, forall w2, le w1 w2 -> le w2 w3 -> le w1 w3.
  Parameter pforces_mon : forall {w' b}, forall w, le w w' -> pforces w b -> pforces w' b.
End ForcingStructure.

Module Forcing (fs : ForcingStructure).
  Export fs.
  
  Definition Cont {class:Set}(f:K->class->Set)(w:K)(x:class) :=
    forall (x0:Answer), forall {w'},
        le w w' ->
        (forall {w''}, le w' w'' -> f w'' x -> X w'' x0) ->
        X w' x0.

  Fixpoint bforces (w:K)(b:Base) {struct b} : Set :=
    match b with
    | prp p => pforces w p
    | bd d => dforces w d
    end
  with
  cforces (w:K)(c:CNF) {struct c} : Set :=
    match c with
    | top => unit
    | con c1 b c2 =>
      (forall w', le w w' -> Cont cforces w' c1 -> Cont bforces w' b)
      * (Cont cforces w c2)
    end
  with
  dforces (w:K)(d:DNF) {struct d} : Set :=
    match d with
    | two c1 c2 => (Cont cforces w c1) + (Cont cforces w c2)
    | dis c1 d2 => (Cont cforces w c1) + (Cont dforces w d2)
    end.

  Fixpoint eforces (w:K)(e:ENF) {struct e} : Set :=
    match e with
    | cnf c => cforces w c
    | dnf d => dforces w d
    end.

  Lemma Cont_bforces_mon {w w' b} : le w w' -> Cont bforces w b -> Cont bforces w' b.
  Proof.
    intros le' H.
    intros x0 w'' le'' k''.
    apply H.
    apply le_trans with w'; assumption.
    apply k''.
  Defined.

  Lemma Cont_cforces_mon : forall {w w' x}, le w w' -> Cont cforces w x -> Cont cforces w' x.
  Proof.
    intros w w' x le' H.
    intros x0 w'' le'' k''.
    apply H.
    apply le_trans with w'; assumption.
    apply k''.
  Defined.

  Lemma Cont_dforces_mon : forall {w w' x}, le w w' -> Cont dforces w x -> Cont dforces w' x.
  Proof.
    intros w w' x le' H.
    intros x0 w'' le'' k''.
    apply H.
    apply le_trans with w'; assumption.
    apply k''.
  Defined.

  Lemma Cont_eforces_mon : forall {w w' x}, le w w' -> Cont eforces w x -> Cont eforces w' x.
  Proof.
    intros w w' x le' H.
    intros x0 w'' le'' k''.
    apply H.
    apply le_trans with w'; assumption.
    apply k''.
  Defined.

  Lemma cforces_mon : (forall {w w' c}, le w w' -> cforces w c -> cforces w' c)
  with dforces_mon : (forall {w w' d}, le w w' -> dforces w d -> dforces w' d).
  Proof.
    { destruct c.
      simpl.    
      intros; constructor.
      intros.
      simpl in *.
      split.
      intros.
      apply H0.
      apply le_trans with w'; assumption.
      apply H2.
      apply (Cont_cforces_mon H).
      apply H0. }
    { destruct d.
      - intros le' H'.
        destruct H'.
        left.
        apply (Cont_cforces_mon le').
        assumption.
        right.
        apply (Cont_cforces_mon le').
        assumption.
      - intros le' H'.
        destruct H'.
        left.
        apply (Cont_cforces_mon le').
        assumption.
        right.
        apply (Cont_dforces_mon le').
        assumption. }
  Defined.

  Lemma bforces_mon {w w' b} : (le w w' -> bforces w b -> bforces w' b).
  Proof.
    destruct b.
    apply pforces_mon.
    apply dforces_mon.
  Defined.

  Lemma eforces_mon : forall {w w' e}, le w w' -> eforces w e -> eforces w' e.
  Proof.
    destruct e.
    apply cforces_mon.    
    apply dforces_mon.
  Defined.

  Lemma bret {w:K}{x:Base} : bforces w x -> Cont bforces w x.
  Proof.
    intro H.
    intros x0 w' le' H1.
    apply H1.
    apply le_refl.
    apply (bforces_mon (w:=w)); assumption.
  Defined.

  Lemma cret {w:K}{x:CNF} : cforces w x -> Cont cforces w x.
  Proof.
    intro H.
    intros x0 w' le' H1.
    apply H1.
    apply le_refl.
    apply (cforces_mon (w:=w)); assumption.
  Defined.

  Lemma eret {w:K}{x:ENF} : eforces w x -> Cont eforces w x.
  Proof.
    intro H.
    intros x0 w' le' H1.
    apply H1.
    apply le_refl.
    apply (eforces_mon (w:=w)); assumption.
  Defined.

  Lemma dret {w:K}{x:DNF} : dforces w x -> Cont dforces w x.
  Proof.
    intro H.
    intros x0 w' le' H1.
    apply H1.
    apply le_refl.
    apply (dforces_mon (w:=w)); assumption.
  Defined.

  Fixpoint sforces (w:K)(F:Formula) {struct F} : Set :=
    match F with
    | prop p => pforces w p
    | disj F G => (Cont sforces w F) + (Cont sforces w G)
    | conj F G => (Cont sforces w F) * (Cont sforces w G)
    | impl F G => forall w',
        le w w' -> (Cont sforces w' F) -> (Cont sforces w' G)
    end.

  Lemma Cont_sforces_mon : forall {w w' x}, le w w' -> Cont sforces w x -> Cont sforces w' x.
  Proof.
    intros w w' x le' H.
    intros x0 w'' le'' k''.
    apply H.
    apply le_trans with w'; assumption.
    apply k''.
  Defined.

  Lemma sforces_mon : forall {w w' x}, le w w' -> sforces w x -> sforces w' x.
  Proof.
    intros w w1 F le1 H.
    generalize dependent w1.
    generalize dependent w.
    induction F.
    - intros.
      apply pforces_mon with w.
      assumption.
      assumption.
    - intros.
      destruct H.
      left.
      apply (Cont_sforces_mon (w:=w)); assumption.
      right.
      apply (Cont_sforces_mon (w:=w)); assumption.
    - intros.
      simpl.
      split.
      apply (Cont_sforces_mon (w:=w)); try assumption.
      apply H.
      apply (Cont_sforces_mon (w:=w)); try assumption.
      apply H.
    - intros.
      simpl in *.
      intros w2 le2.
      apply H.
      apply le_trans with w1; assumption.
  Defined.

  Lemma sret {w:K}{x:Formula} : sforces w x -> Cont sforces w x.
  Proof.
    intro H.
    intros x0 w' le' H1.
    apply H1.
    apply le_refl.
    apply (sforces_mon (w:=w)); assumption.
  Defined.

  Lemma ccbind {w:K}{x y:CNF} :
    Cont cforces w x ->
    (forall {w'}, le w w' -> cforces w' x -> Cont cforces w' y) ->
    Cont cforces w y.
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

  Lemma cdbind {w:K}{x:CNF}{y:DNF} :
    Cont cforces w x ->
    (forall {w'}, le w w' -> cforces w' x -> Cont dforces w' y) ->
    Cont dforces w y.
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

  Lemma ddbind {w:K}{x y:DNF} :
    Cont dforces w x ->
    (forall {w'}, le w w' -> dforces w' x -> Cont dforces w' y) ->
    Cont dforces w y.
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

  Lemma edbind {w:K}{x:ENF}{y:DNF} :
    Cont eforces w x ->
    (forall {w'}, le w w' -> eforces w' x -> Cont dforces w' y) ->
    Cont dforces w y.
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

  Lemma debind {w:K}{x:DNF}{y:ENF} :
    Cont dforces w x ->
    (forall {w'}, le w w' -> dforces w' x -> Cont eforces w' y) ->
    Cont eforces w y.
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

  Lemma cbbind {w:K}{x:CNF}{y:Base} :
    Cont cforces w x ->
    (forall {w'}, le w w' -> cforces w' x -> Cont bforces w' y) ->
    Cont bforces w y.
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

  Lemma dbbind {w:K}{x:DNF}{y:Base} :
    Cont dforces w x ->
    (forall {w'}, le w w' -> dforces w' x -> Cont bforces w' y) ->
    Cont bforces w y.
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

  Lemma dcbind {w:K}{x:DNF}{y:CNF} :
    Cont dforces w x ->
    (forall {w'}, le w w' -> dforces w' x -> Cont cforces w' y) ->
    Cont cforces w y.
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

  Lemma dsbind {w:K}{x:DNF}{y:Formula} :
    Cont dforces w x ->
    (forall {w'}, le w w' -> dforces w' x -> Cont sforces w' y) ->
    Cont sforces w y.
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

  Lemma sfbind {w:K}{x:Formula}{y:ENF} :
    Cont sforces w x ->
    (forall {w'}, le w w' -> sforces w' x -> Cont eforces w' y) ->
    Cont eforces w y.
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

  Lemma fsbind {w:K}{x:ENF}{y:Formula} :
    Cont eforces w x ->
    (forall {w'}, le w w' -> eforces w' x -> Cont sforces w' y) ->
    Cont sforces w y.
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
  
  Lemma ssbind {w:K}{x y:Formula} :
    Cont sforces w x ->
    (forall {w'}, le w w' -> sforces w' x -> Cont sforces w' y) ->
    Cont sforces w y.
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

  Lemma lem1 : forall w b,
      Cont cforces w (con top b top) -> Cont bforces w b.
  Proof.
    intros w b H.
    unfold Cont in H.
    simpl in H.
    intros b0 w1 le1 k1.
    apply H.
    assumption.
    intros w2 le2 f2.
    destruct f2 as [f21 f22].
    apply f21 with w2.    
    apply le_refl.
    assumption.
    apply le_refl.
    intros w3 le3 H3.
    apply k1.
    apply le_trans with w2; assumption.
    assumption.
  Defined.

  Lemma lem2 : forall w b,
      Cont bforces w b -> Cont cforces w (con top b top).
  Proof.
    intros w b H.
    apply cret.
    simpl.
    split.
    - intros w' le' _.
      apply (Cont_bforces_mon le').
      assumption.
    - apply cret.
      simpl.
      constructor.
  Defined.

  Lemma cforces_ntimes : forall c1 w c2,
      cforces w c1 -> cforces w c2 -> cforces w (ntimes c1 c2).
  Proof.
    induction c1.
    - simpl in *.
      intros.
      assumption.
    - simpl.
      clear IHc1_1.
      intros.
      split.
      + apply H.
      + destruct H as [_ H].
        apply (ccbind (x := c1_2)).
        assumption.
        intros w1 le1 H1.
        apply cret.
        apply IHc1_2.
        assumption.
        apply (cforces_mon (w:=w)); assumption.
  Defined.

  Lemma cforces_ntimes_1 : forall c1 w c2,
      Cont cforces w c1 -> Cont cforces w c2 -> Cont cforces w (ntimes c1 c2).
  Proof.
    induction c1.
    - simpl in *.
      intros.
      assumption.
    - simpl.
      clear IHc1_1.
      intros.
      apply (ccbind (x := (con c1_1 b c1_2))).
      assumption.
      intros w1 le1 H1.
      simpl in H1.
      apply cret.
      simpl.
      split.
      + apply H1.
      + apply IHc1_2.
        apply H1.
        apply (Cont_cforces_mon (w:=w)); assumption.
  Defined.

  Lemma cforces_ntimes_2 : forall c1 w c2,
      Cont cforces w (ntimes c1 c2) -> Cont cforces w c1 * Cont cforces w c2.
  Proof.
    induction c1.
    - simpl.
      intros.
      split.
      + apply cret; constructor.
      + assumption.
    - simpl.
      intros.
      split.
      + apply (ccbind (x := (con c1_1 b (ntimes c1_2 c2)))).
        assumption.
        clear H.
        intros w1 le1 H1.
        simpl in H1.
        destruct H1 as [H11 H12].
        apply IHc1_2 in H12.      
        destruct H12 as [H121 H122].
        clear IHc1_2.
        apply cret.
        simpl.
        split; assumption.
      + apply (ccbind (x := (con c1_1 b (ntimes c1_2 c2)))).
        assumption.
        clear H.
        intros w1 le1 H1.
        simpl in H1.
        destruct H1 as [H11 H12].
        apply IHc1_2 in H12.      
        destruct H12 as [H121 H122].
        assumption.
  Defined.

  Theorem meta_exp : forall C E, forall w,
        (forall w', le w w' -> Cont eforces w' E -> Cont cforces w' C) ->
        cforces w (explogn C E).
  Proof.
    induction C.
    - simpl.
      intros.
      constructor.
    - simpl.
      intros.
      apply cforces_ntimes.
      + assert (H' : forall w' : K,
                   le w w' -> Cont eforces w' E -> Cont cforces w' (explog1 b (cnf C1))).
        intros w1 le1 H1.
        apply cforces_ntimes_2 with (c2:=C2).
        apply H.
        assumption.
        assumption.
        clear IHC1 IHC2 H.
        { destruct E.
          - simpl in *.
            split; [|apply cret; constructor].
            intros w1 le1 H1.
            apply cforces_ntimes_2 in H1.            
            destruct H1 as [H11 H12].
            apply H' in H12.
            replace (con C1 b top) with (ntimes (explog1 b (cnf C1)) top) in H12.
            apply cforces_ntimes_2 in H12.            
            destruct H12 as [H12 _].
            simpl in H12.
            apply (cbbind (x:=(con C1 b top)) (y:=b) ).
            assumption.
            intros w2 le2 H2.
            simpl in H2.
            apply H2.
            apply le_refl.
            apply (Cont_cforces_mon (w:=w1)); assumption.
            reflexivity.
            assumption.
          - { induction d.
              - simpl in *.
                split.
                + intros w1 le1 H1.
                  apply cforces_ntimes_2 in H1.            
                  destruct H1 as [H11 H12].
                  replace (con C1 b top) with (ntimes (explog1 b (cnf C1)) top) in H'.
                  assert (H12' : Cont cforces w1 (ntimes (explog1 b (cnf C1)) top)).
                  { apply H'.
                    assumption.
                    apply dret.
                    left.
                    assumption.
                  }
                  apply cforces_ntimes_2 in H12'.            
                  destruct H12' as [H12' _].
                  simpl in H12'.
                  apply (cbbind (x:=(con C1 b top)) (y:=b) ).
                  assumption.
                  intros w2 le2 H2.
                  simpl in H2.
                  apply H2.
                  apply le_refl.
                  apply (Cont_cforces_mon (w:=w1)); assumption.
                  reflexivity.
                + apply cret.
                  simpl.
                  split; [|apply cret; constructor].
                  intros w1 le1 H1.
                  apply cforces_ntimes_2 in H1.            
                  destruct H1 as [H11 H12].
                  replace (con C1 b top) with (ntimes (explog1 b (cnf C1)) top) in H'.
                  assert (H12' : Cont cforces w1 (ntimes (explog1 b (cnf C1)) top)).
                  { apply H'.
                    assumption.
                    apply dret.
                    right.
                    assumption.
                  }
                  apply cforces_ntimes_2 in H12'.            
                  destruct H12' as [H12' _].
                  simpl in H12'.
                  apply (cbbind (x:=(con C1 b top)) (y:=b) ).
                  assumption.
                  intros w2 le2 H2.
                  simpl in H2.
                  apply H2.
                  apply le_refl.
                  apply (Cont_cforces_mon (w:=w1)); assumption.
                  reflexivity.
              - unfold distrib1 in *.
                replace (dis c d) with (nplus (cnf c) (dnf d)) ; [|reflexivity].
                rewrite distrib0_nplus.
                unfold explog1.
                rewrite explog0_nplus.
                simpl.
                split.
                + intros w1 le1 H1.
                  apply cforces_ntimes_2 in H1.            
                  destruct H1 as [H11 H12].
                  replace (con C1 b top) with (ntimes (explog1 b (cnf C1)) top) in H'.
                  assert (H12' : Cont cforces w1 (ntimes (explog1 b (cnf C1)) top)).
                  { apply H'.
                    assumption.
                    apply dret.
                    left.
                    assumption.
                  }
                  apply cforces_ntimes_2 in H12'.            
                  destruct H12' as [H12' _].
                  simpl in H12'.
                  apply (cbbind (x:=(con C1 b top)) (y:=b) ).
                  assumption.
                  intros w2 le2 H2.
                  simpl in H2.
                  apply H2.
                  apply le_refl.
                  apply (Cont_cforces_mon (w:=w1)); assumption.
                  reflexivity.
                + apply cret.
                  apply IHd.
                  intros w1 le1 H1.
                  apply H'.
                  assumption.
                  apply dret.
                  right.
                  assumption.
            }                
        }
      + apply IHC2.
        simpl in H.        
        intros w1 le1 H1.
        apply cforces_ntimes_2 with (explog1 b (cnf C1)).
        simpl.
        apply H; assumption.
  Defined.

  Theorem exp_meta : forall C E, forall w,
        Cont cforces w (explogn C E) ->
        (forall w', le w w' -> Cont eforces w' E -> Cont cforces w' C).
  Proof.
    induction C.
    - intros.
      apply cret.
      constructor.
    - intros E w H w1 le1 H1.
      replace (con C1 b C2) with (ntimes (explog1 b (cnf C1)) C2) in *; [|reflexivity].
      rewrite explogn_ntimes in H.
      apply cforces_ntimes_2 in H.
      apply cret.
      split.
      + intros w2 le2 H2.
        destruct H as [H _].
        clear IHC1 IHC2.
        destruct E.
        { simpl in *.
          replace (con (ntimes C1 c) b top) with (ntimes (explog1 b (cnf (ntimes C1 c))) top) in H; [|reflexivity].
          apply cforces_ntimes_2 in H.
          destruct H as [H _].
          simpl in H.
          apply (cbbind (x:= (con (ntimes C1 c) b top))).
          apply (Cont_cforces_mon (w:=w)).
          apply le_trans with w1; assumption.          
          assumption.
          intros w3 le3 H3.
          simpl in H3.
          apply H3.
          apply le_refl.
          clear H3.
          apply cforces_ntimes_1.
          apply (Cont_cforces_mon (w:=w2)); assumption.
          apply (Cont_cforces_mon (w:=w1)).
          apply le_trans with w2; assumption.          
          assumption.
        }
        { simpl in *.
          apply cforces_ntimes_2 in H.
          destruct H as [H _].
          { generalize dependent w2.
            generalize dependent w1.
            generalize dependent w.
            induction d.
            - simpl in *.
              intros.
              apply (cbbind (x := (con (ntimes C1 c) b (con (ntimes C1 c0) b top)))).
              apply (Cont_cforces_mon (w:=w)).
              apply le_trans with w1; assumption.
              assumption.
              intros w3 le3 [H31 H32].
              apply (dbbind (x := two c c0)).              
              apply (Cont_dforces_mon (w:=w1)).
              apply le_trans with w2; assumption.
              assumption.
              intros w4 le4 [H41|H42].
              + apply H31.
                assumption.
                apply cforces_ntimes_1. 
                apply (Cont_cforces_mon (w:=w2)).
                apply le_trans with w3; assumption.
                assumption.
                assumption.
              + apply (cbbind (x := (con (ntimes C1 c0) b top))).
                apply (Cont_cforces_mon (w:=w3)).
                assumption.
                assumption.
                intros w5 le5 H5.
                simpl in H5.
                destruct H5 as [H5 _].
                apply H5.
                apply le_refl.
                apply cforces_ntimes_1. 
                apply (Cont_cforces_mon (w:=w2)).
                apply le_trans with w3; try assumption.
                apply le_trans with w4; try assumption.
                assumption.
                apply (Cont_cforces_mon (w:=w4)); assumption.
            - intros.
              replace (dis c d) with (nplus (cnf c) (dnf d)) in H; [|reflexivity].
              rewrite distrib0_nplus in H.
              unfold explog1 in H.
              rewrite explog0_nplus in H.
              apply cforces_ntimes_2 in H.
              apply (dbbind (x := dis c d)).
              apply (Cont_dforces_mon (w:=w1)); assumption.
              simpl in H.
              intros w3 le3 [H31|H32].
              + destruct H as [H _].
                clear IHd H1.
                apply (cbbind (x := (con (ntimes C1 c) b top))).
                apply (Cont_cforces_mon (w:=w)).
                apply le_trans with w1; try assumption.
                apply le_trans with w2; try assumption.
                assumption.
                clear H.
                intros w4 le4 H4.
                simpl in H4.
                destruct H4 as [H4 _].                
                apply H4.
                apply le_refl.
                apply cforces_ntimes_1.
                apply (Cont_cforces_mon (w:=w2)).
                apply le_trans with w3; assumption.
                assumption.
                apply (Cont_cforces_mon (w:=w3)).
                assumption.
                assumption.
              + destruct H as [_ H].
                apply (IHd w) with w3.
                assumption.
                apply le_trans with w1; try assumption.
                apply le_trans with w2; try assumption.
                assumption.
                apply le_refl.
                apply (Cont_cforces_mon (w:=w2)); assumption.
          }
        }
      + simpl.
        apply IHC2 with E w.
        apply H.
        assumption.
        assumption.
  Defined.

  Theorem exp_meta_b : forall B D, forall w,
        Cont cforces w (explog0 B D) ->
        (forall w', le w w' -> Cont dforces w' D -> Cont bforces w' B).
  Proof.
    induction D.
    - intros w H w1 le1 H1.
      apply (cbbind (x := explog0 B (two c c0))).
      apply (Cont_cforces_mon (w:=w)).
      assumption.
      assumption.
      clear H.
      intros w2 le2 H2.
      apply (dbbind (x := two c c0)).
      apply (Cont_dforces_mon (w:=w1)).
      assumption.
      assumption.
      clear H1.
      intros w3 le3 H3.
      simpl in H2.
      destruct H2 as [H21 H22].
      destruct H3 as [H31|H32].
      apply H21; assumption.
      apply (cbbind (x := (con c0 B top))).
      apply (Cont_cforces_mon (w:=w2)).
      assumption.
      assumption.
      clear H22.
      intros w4 le4 H4.
      simpl in H4.      
      apply H4.
      apply le_refl.      
      apply (Cont_cforces_mon (w:=w3)).
      assumption.
      assumption.
    - intros w H w1 le1 H1.
      apply (cbbind (x := explog0 B (dis c D))).
      apply (Cont_cforces_mon (w:=w)).
      assumption.
      assumption.
      clear H.
      intros w2 le2 H2.
      apply (dbbind (x := dis c D)).
      apply (Cont_dforces_mon (w:=w1)).
      assumption.
      assumption.
      clear H1.
      intros w3 le3 H3.
      simpl in H2.
      destruct H2 as [H21 H22].
      destruct H3 as [H31|H32].
      apply H21; assumption.
      apply IHD with w2.
      assumption.
      assumption.
      assumption.      
  Defined.
  
  Lemma dforces_nplus_1 : forall e1 e2 w,
      Cont eforces w e1 -> Cont dforces w (nplus e1 e2).
  Proof.
    destruct e1.
    - destruct e2.
      + simpl.
        intros.
        apply dret.
        left.
        assumption.
      + simpl.
        intros.
        apply dret.
        left.
        assumption.
    - simpl.
      induction d.
      + simpl.
        intros.
        apply (ddbind (x := two c c0)).
        assumption.
        clear H.
        intros w1 le1 H1.
        destruct H1 as [H11|H12].
        apply dret.
        destruct e2.
        left.
        assumption.
        left.
        assumption.
        destruct e2.
        apply dret.
        right.
        apply dret.
        left.
        assumption.
        apply dret.
        right.
        apply dret.
        left.
        assumption.
      + simpl.
        intros.          
        apply (ddbind (x := dis c d)).
        assumption.
        intros w1 le1 H1.
        destruct H1 as [H11|H12].
        apply dret.
        left.
        assumption.
        apply dret.
        right.
        apply IHd.
        assumption.
  Defined.

  Lemma dforces_nplus_2 : forall w e1 e2,
      Cont eforces w e2 -> Cont dforces w (nplus e1 e2).
  Proof.
    destruct e1.
    - destruct e2.
      + simpl.
        intros.
        apply dret.
        right.
        assumption.
      + simpl.
        intros.
        apply dret.
        right.
        assumption.
    - simpl.
      generalize dependent w.
      induction d.
      + simpl.
        intros.
        apply (edbind (x := e2)).
        assumption.
        clear H.
        intros w1 le1 H1.
        apply dret.
        destruct e2.
        right.
        apply dret.
        right.
        apply cret.
        assumption.
        right.
        apply dret.
        right.
        apply dret.
        assumption.
      + simpl.
        intros.          
        apply (edbind (x := e2)).
        assumption.
        intros w1 le1 H1.
        apply dret.
        right.
        apply IHd.
        apply eret.
        assumption.
  Defined.

  Lemma dforces_nplus : forall e1 w e2,
      Cont dforces w (nplus e1 e2) ->
      Cont dforces w (two (enf2cnf e1) (enf2cnf e2)).
  Proof.
    destruct e1.
    - simpl.
      destruct e2.
      + simpl.
        intro H.
        apply H.
      + simpl.
        intros H.
        apply (ddbind (x := dis c d)).
        assumption.        
        intros w1 le1 H1.
        destruct H1 as [H11 | H12].
        apply dret.
        left.
        assumption.
        apply dret.
        right.
        apply lem2.
        assumption.
    - simpl.
      induction d.
      + simpl.
        intros.
        destruct e2.
        * simpl.
          apply (ddbind (x := (dis c (two c0 c1)))).
          assumption.
          intros w1 le1 H1.
          destruct H1 as [H11|H12].
          { apply dret.          
            left.
            apply lem2.
            apply bret.
            left.
            assumption. }
          { apply (ddbind (x := two c0 c1)).
            assumption.
            intros w2 le2 H2.
            destruct H2 as [H21|H22].
            { apply dret.
              left.
              apply lem2.
              apply bret.
              right.
              assumption. }
            { apply dret.
              right.
              assumption. }}
        * simpl.
          apply (ddbind (x := (dis c (dis c0 d)))).
          assumption.            
          intros w1 le1 H1.
          destruct H1 as [H11|H12].
          { apply dret.
            left.
            apply lem2.            
            apply bret.
            left.
            assumption. }
          { apply (ddbind (x := (dis c0 d))).
            assumption.
            intros w2 le2 H2.
            destruct H2 as [H21|H22].
            apply dret.
            left.
            apply lem2.            
            apply bret.
            right.
            assumption.
            apply dret.
            right.
            apply lem2.
            assumption. }
      + simpl.
        intros.
        apply (ddbind (x := (dis c (nplus1 d e2)))).
        assumption.
        intros w1 le1 H1.
        destruct H1 as [H11|H12].
        * apply dret.
          left.
          apply lem2.
          apply bret.
          left.
          assumption.
        * apply IHd in H12.
          apply (ddbind (x := (two (con top (bd d) top) (enf2cnf e2)))).
          assumption.
          intros w2 le2 H2.
          destruct H2 as [H21|H22].
          { apply lem1 in H21.
            apply dret.
            left.
            apply lem2.
            apply bret.
            right.
            assumption. }
          { apply dret.
            right.
            assumption. }
  Defined.

  Lemma eforces_distrib : forall e1 w e2,
      Cont eforces w e1 -> Cont eforces w e2 -> Cont eforces w (distrib e1 e2).
  Proof.
    destruct e1.
    - simpl.
      destruct e2.
      + simpl.
        apply cforces_ntimes_1.
      + simpl.
        intros Hc.
        intros Hd.
        generalize dependent w.
        induction d.
        * simpl.
          intros.
          apply (ddbind (x := (two c0 c1))).
          assumption.
          intros w1 le1 H1.
          destruct H1 as [H11|H12].
          apply dret.
          left.
          apply cforces_ntimes_1.
          apply (Cont_cforces_mon (w:=w)); assumption.
          assumption.          
          apply dret.
          right.
          apply cforces_ntimes_1.
          apply (Cont_cforces_mon (w:=w)); assumption.
          assumption.          
        * simpl.
          intros.
          apply (ddbind (x := dis c0 d)).
          assumption.
          intros w1 le1 H1.
          destruct H1 as [H11|H12].
          { destruct (distrib0 c d).
            apply dret.
            left.
            apply cforces_ntimes_1.
            apply (Cont_cforces_mon (w:=w)); assumption.
            assumption.          
            apply dret.
            left.
            apply cforces_ntimes_1.
            apply (Cont_cforces_mon (w:=w)); assumption.
            assumption. }
          { destruct (distrib0 c d).
            apply dret.
            right.
            apply IHd.
            apply (Cont_cforces_mon (w:=w)); assumption.
            assumption.
            apply dret.
            right.
            apply IHd.
            apply (Cont_cforces_mon (w:=w)); assumption.
            assumption. }
    - simpl.
      induction d.
      + simpl.
        intros.
        apply (ddbind (x := two c c0)).
        assumption.
        intros w1 le1 H1.
        destruct H1 as [H11|H12].
        { apply dforces_nplus_1.
          destruct e2.
          * simpl.
            apply cforces_ntimes_1.
            assumption.
            apply (Cont_cforces_mon (w:=w)); assumption.
          * simpl.
            generalize dependent w1.
            generalize dependent w.
            induction d.
            { simpl.
              intros.
              apply (ddbind (x := two c1 c2)).
              apply (Cont_dforces_mon (w:=w)); assumption.
              intros w2 le2 H2.
              destruct H2 as [H21|H22].            
              apply dret.
              left.
              apply cforces_ntimes_1.
              apply (Cont_cforces_mon (w:=w1)); assumption.
              assumption.
              apply dret.
              right.
              apply cforces_ntimes_1.
              apply (Cont_cforces_mon (w:=w1)); assumption.
              assumption. }
            { simpl.
              intros.
              destruct (distrib0 c d).
              { apply (ddbind (x := dis c1 d)).
                apply (Cont_dforces_mon (w:=w)); assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply dret.
                left.
                apply cforces_ntimes_1.
                apply (Cont_cforces_mon (w:=w1)); assumption.
                assumption.
                apply dret.
                right.
                apply IHd with w2.
                apply (Cont_dforces_mon (w:=w1)); try assumption.
                apply (Cont_dforces_mon (w:=w)); assumption.
                assumption.
                apply le_refl.            
                apply (Cont_cforces_mon (w:=w1)); assumption. }
              { apply (ddbind (x := dis c1 d)).
                apply (Cont_dforces_mon (w:=w)); assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply dret.
                left.
                apply cforces_ntimes_1.
                apply (Cont_cforces_mon (w:=w1)); assumption.
                assumption.
                apply dret.
                right.
                apply IHd with w2.
                apply dret.
                left.
                apply (Cont_cforces_mon (w:=w1)); assumption.
                assumption.
                apply le_refl.            
                apply (Cont_cforces_mon (w:=w1)); assumption. } } }
        { apply dforces_nplus_2.
          destruct e2.
          * simpl.
            apply cforces_ntimes_1.
            assumption.
            apply (Cont_cforces_mon (w:=w)); assumption.
          * simpl.
            generalize dependent w1.
            generalize dependent w.
            induction d.
            { simpl.
              intros.
              apply (ddbind (x := two c1 c2)).
              apply (Cont_dforces_mon (w:=w)); assumption.
              intros w2 le2 H2.
              destruct H2 as [H21|H22].            
              apply dret.
              left.
              apply cforces_ntimes_1.
              apply (Cont_cforces_mon (w:=w1)); assumption.
              assumption.
              apply dret.
              right.
              apply cforces_ntimes_1.
              apply (Cont_cforces_mon (w:=w1)); assumption.
              assumption. }
            { simpl.
              intros.
              destruct (distrib0 c0 d).
              { apply (ddbind (x := dis c1 d)).
                apply (Cont_dforces_mon (w:=w)); assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply dret.
                left.
                apply cforces_ntimes_1.
                apply (Cont_cforces_mon (w:=w1)); assumption.
                assumption.
                apply dret.
                right.
                apply IHd with w2.
                apply (Cont_dforces_mon (w:=w1)); try assumption.
                apply (Cont_dforces_mon (w:=w)); assumption.
                assumption.
                apply le_refl.            
                apply (Cont_cforces_mon (w:=w1)); assumption. }
              { apply (ddbind (x := dis c1 d)).
                apply (Cont_dforces_mon (w:=w)); assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply dret.
                left.
                apply cforces_ntimes_1.
                apply (Cont_cforces_mon (w:=w1)); assumption.
                assumption.
                apply dret.
                right.
                apply IHd with w2.
                apply dret.
                right.
                apply (Cont_cforces_mon (w:=w1)); assumption.
                assumption.
                apply le_refl.            
                apply (Cont_cforces_mon (w:=w1)); assumption. } } }
      + intros.
        simpl.
        apply (ddbind (x := dis c d)).
        assumption.
        intros w1 le1 H1.
        destruct H1 as [H11|H12].
        { apply dforces_nplus_1.
          clear H IHd.
          destruct e2.
          - simpl.
            apply cforces_ntimes_1.            
            assumption.
            apply (Cont_cforces_mon (w:=w)); assumption.
          - simpl.
            generalize dependent w1.
            generalize dependent w.
            induction d0.
            + simpl.            
              intros.
              apply (ddbind (x := two c0 c1)).
              apply (Cont_dforces_mon (w:=w)); assumption.
              intros w2 le2 H2.
              destruct H2 as [H21|H22].
              apply dret.
              left.
              apply cforces_ntimes_1.            
              apply (Cont_cforces_mon (w:=w1)); assumption.
              assumption.
              apply dret.
              right.
              apply cforces_ntimes_1.            
              apply (Cont_cforces_mon (w:=w1)); assumption.
              assumption.
            + simpl.
              intros.
              destruct (distrib0 c d0).
              { apply (ddbind (x := dis c0 d0)).
                apply (Cont_dforces_mon (w:=w)); assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                * apply dret.
                  left.
                  apply cforces_ntimes_1.
                  apply (Cont_cforces_mon (w:=w1)); assumption.
                  assumption.
                * apply dret.
                  right.
                  apply IHd0 with w2.
                  assumption.
                  apply le_refl.                
                  apply (Cont_cforces_mon (w:=w1)); assumption. }
              { apply (ddbind (x := dis c0 d0)).
                apply (Cont_dforces_mon (w:=w)); assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                * apply dret.
                  left.
                  apply cforces_ntimes_1.
                  apply (Cont_cforces_mon (w:=w1)); assumption.
                  assumption.
                * apply dret.
                  right.
                  apply IHd0 with w2.
                  assumption.
                  apply le_refl.                
                  apply (Cont_cforces_mon (w:=w1)); assumption. }
        }
        { apply dforces_nplus_2.
          apply IHd.          
          assumption.
          apply (Cont_eforces_mon (w:=w)); assumption. }
  Defined.

  Lemma eforces2cforces : forall e w,
      Cont eforces w e -> Cont cforces w (enf2cnf e).
  Proof.
    destruct e.
    - simpl.
      intros w H.
      apply H.
    - simpl.
      intros w H.
      apply cret.
      simpl.
      split.
      intros.
      apply (Cont_bforces_mon H0); assumption.
      apply cret.
      constructor.
  Defined.

  Lemma cforces2eforces : forall e w,
      Cont cforces w (enf2cnf e) -> Cont eforces w e.
  Proof.
    destruct e.
    - simpl.
      intros.
      apply H.
    - simpl.
      intros.
      apply (cdbind (x := (con top (bd d) top))).
      assumption.
      intros w1 le1 H1.
      simpl in H1.
      destruct H1 as [H1 _].
      apply H1.
      apply le_refl.
      apply cret.
      constructor.
  Defined.

  Lemma eforces_distrib' : forall e1 e2 w,
      Cont eforces w (distrib e1 e2) -> Cont eforces w e1 * Cont eforces w e2.
  Proof.
    destruct e1.
    - simpl.
      destruct e2.
      + simpl.
        intros.
        apply cforces_ntimes_2.
        assumption.
      + simpl.
        induction d.
        * simpl.
          intros.
          split.
          apply (dcbind (x := (two (ntimes c c0) (ntimes c c1)))).
          assumption.
          intros w1 le1 H1.
          destruct H1 as [H11|H12].
          apply (cforces_ntimes_2 c w1 c0).
          assumption.
          apply (cforces_ntimes_2 c w1 c1).
          assumption.
          apply (ddbind (x := (two (ntimes c c0) (ntimes c c1)))).
          assumption.
          intros w1 le1 H1.
          destruct H1 as [H11|H12].
          apply cforces_ntimes_2 in H11.
          apply dret.
          left.
          apply H11.
          apply cforces_ntimes_2 in H12.
          apply dret.
          right.
          apply H12.
        * simpl.
          intros.
          destruct (distrib0 c d).
          split.
          { apply (dcbind (x := (two (ntimes c c0) c1))).
            assumption.
            intros w1 le1 H1.
            destruct H1 as [H11|H12].
            apply (cforces_ntimes_2 c w1 c0).
            assumption.
            apply IHd.
            assumption. }         
          { apply (ddbind (x := (two (ntimes c c0) c1))).
            assumption.
            intros w1 le1 H1.
            destruct H1 as [H11|H12].
            apply cforces_ntimes_2 in H11.
            apply dret.
            left.
            apply H11.            
            apply dret.
            right.
            apply IHd.
            assumption. }
          split.
          { apply (dcbind (x := (dis (ntimes c c0) d0))).
            assumption.
            intros w1 le1 H1.
            destruct H1 as [H11|H12].
            apply (cforces_ntimes_2 c w1 c0).
            assumption.
            apply IHd.
            assumption. }         
          { apply (ddbind (x := (dis (ntimes c c0) d0))).
            assumption.
            intros w1 le1 H1.
            destruct H1 as [H11|H12].
            apply cforces_ntimes_2 in H11.
            apply dret.
            left.
            apply H11.            
            apply dret.
            right.
            apply IHd.
            assumption. }
    - simpl.
      induction d.
      + simpl.
        intros.
        apply dforces_nplus in H.
        split.
        * apply (ddbind (x := (two (enf2cnf (distrib1 c e2)) (enf2cnf (distrib1 c0 e2))))).        
          assumption.
          clear H.
          intros w1 le1 H1.
          destruct H1 as [H11|H12].          
          { destruct e2.
            simpl in *.
            apply cforces_ntimes_2 in H11.
            apply dret.
            left.
            apply H11.
            simpl in *.
            { generalize dependent w1.
              generalize dependent w.
              induction d.
              - simpl in *.
                intros.
                apply lem1 in H11.
                apply (ddbind (x := (two (ntimes c c1) (ntimes c c2)))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply cforces_ntimes_2 in H22.
                apply dret.
                left.
                apply H22.
              - simpl in *.
                intros.
                destruct (distrib0 c d).
                simpl in *.
                apply lem1 in H11.
                apply (ddbind (x := (two (ntimes c c1) c2))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply (IHd w1).              
                assumption.
                assumption.
                apply lem1 in H11.
                apply (ddbind (x := (dis (ntimes c c1) d0))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply (IHd w1).              
                assumption.
                apply lem2.
                assumption. }}
          { destruct e2.
            simpl in *.
            apply cforces_ntimes_2 in H12.
            apply dret.
            right.
            apply H12.
            simpl in *.
            { generalize dependent w1.
              generalize dependent w.
              induction d.
              - simpl in *.
                intros.
                apply lem1 in H12.
                apply (ddbind (x := (two (ntimes c0 c1) (ntimes c0 c2)))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                right.
                apply H21.
                apply cforces_ntimes_2 in H22.
                apply dret.
                right.
                apply H22.
              - simpl in *.
                intros.
                destruct (distrib0 c0 d).
                simpl in *.
                apply lem1 in H12.
                apply (ddbind (x := (two (ntimes c0 c1) c2))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                right.
                apply H21.
                apply (IHd w1).              
                assumption.
                assumption.
                apply lem1 in H12.
                apply (ddbind (x := (dis (ntimes c0 c1) d0))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                right.
                apply H21.
                apply (IHd w1).              
                assumption.
                apply lem2.
                assumption. }}
        * apply (debind (x := (two (enf2cnf (distrib1 c e2)) (enf2cnf (distrib1 c0 e2))))).        
          assumption.
          clear H.
          intros w1 le1 H1.
          destruct H1 as [H11|H12].          
          { destruct e2.
            simpl in *.
            apply cforces_ntimes_2 in H11.
            apply H11.
            simpl in *.
            { generalize dependent w1.
              generalize dependent w.
              induction d.
              - simpl in *.
                intros.
                apply lem1 in H11.
                apply (ddbind (x := (two (ntimes c c1) (ntimes c c2)))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply cforces_ntimes_2 in H22.
                apply dret.
                right.
                apply H22.
              - simpl in *.
                intros.
                destruct (distrib0 c d).
                simpl in *.
                apply lem1 in H11.
                apply (ddbind (x := (two (ntimes c c1) c2))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply dret.
                right.
                apply (IHd w1).              
                assumption.
                assumption.
                apply lem1 in H11.
                apply (ddbind (x := (dis (ntimes c c1) d0))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply dret.
                right.
                apply (IHd w1).              
                assumption.
                apply lem2.
                assumption. }}
          { destruct e2.
            simpl in *.
            apply cforces_ntimes_2 in H12.
            apply H12.
            simpl in *.
            { generalize dependent w1.
              generalize dependent w.
              induction d.
              - simpl in *.
                intros.
                apply lem1 in H12.
                apply (ddbind (x := (two (ntimes c0 c1) (ntimes c0 c2)))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply cforces_ntimes_2 in H22.
                apply dret.
                right.
                apply H22.
              - simpl in *.
                intros.
                destruct (distrib0 c0 d).
                simpl in *.
                apply lem1 in H12.
                apply (ddbind (x := (two (ntimes c0 c1) c2))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply dret.
                right.
                apply (IHd w1).              
                assumption.
                assumption.
                apply lem1 in H12.
                apply (ddbind (x := (dis (ntimes c0 c1) d0))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply dret.
                right.
                apply (IHd w1).              
                assumption.
                apply lem2.
                assumption. }}
      + simpl.
        intros.
        apply dforces_nplus in H.
        split.
        * apply (ddbind (x := (two (enf2cnf (distrib1 c e2)) (enf2cnf (distribn d e2))))).        
          assumption.
          clear H.
          intros w1 le1 H1.
          destruct H1 as [H11|H12].          
          { destruct e2.
            simpl in *.
            apply cforces_ntimes_2 in H11.
            apply dret.
            left.
            apply H11.
            simpl in *.
            { generalize dependent w1.
              generalize dependent w.
              induction d0.
              - simpl in *.
                intros.
                apply lem1 in H11.
                apply (ddbind (x := (two (ntimes c c0) (ntimes c c1)))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply cforces_ntimes_2 in H22.
                apply dret.
                left.
                apply H22.
              - simpl in *.
                intros.
                destruct (distrib0 c d0).
                simpl in *.
                apply lem1 in H11.
                apply (ddbind (x := (two (ntimes c c0) c1))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply (IHd0 w1).              
                assumption.
                assumption.
                apply lem1 in H11.
                apply (ddbind (x := (dis (ntimes c c0) d1))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply (IHd0 w1).              
                assumption.
                apply lem2.
                assumption. }}
          { apply dret.
            right.
            apply (IHd e2).
            apply cforces2eforces.
            assumption. }
        * apply (debind (x := (two (enf2cnf (distrib1 c e2)) (enf2cnf (distribn d e2))))).        
          assumption.
          clear H.
          intros w1 le1 H1.
          destruct H1 as [H11|H12].          
          { clear IHd.
            destruct e2.
            simpl in *.
            apply cforces_ntimes_2 in H11.
            apply H11.
            simpl in *.
            { generalize dependent w1.
              generalize dependent w.
              induction d0.
              - simpl in *.
                intros.
                apply lem1 in H11.
                apply (ddbind (x := (two (ntimes c c0) (ntimes c c1)))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply cforces_ntimes_2 in H22.
                apply dret.
                right.
                apply H22.
              - simpl in *.
                intros.
                destruct (distrib0 c d0).
                simpl in *.
                apply lem1 in H11.
                apply (ddbind (x := (two (ntimes c c0) c1))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply dret.
                right.
                apply (IHd0 w1).              
                assumption.
                assumption.
                apply lem1 in H11.
                apply (ddbind (x := (dis (ntimes c c0) d1))).
                assumption.
                intros w2 le2 H2.
                destruct H2 as [H21|H22].
                apply cforces_ntimes_2 in H21.
                apply dret.
                left.
                apply H21.
                apply dret.
                right.
                apply (IHd0 w1).              
                assumption.
                apply lem2.
                assumption. }}
          { apply IHd.
            apply cforces2eforces.
            assumption. }
  Defined.

  Theorem f2f :
    (forall F, forall w, Cont sforces w F -> Cont eforces w (enf F))
  with f2f' : 
    (forall F, forall w, Cont eforces w (enf F) -> Cont sforces w F).
  Proof.
    { induction F.
      - simpl.
        intros w H.
        apply lem2.
        apply H.
      - intros w H.
        simpl.
        apply (sfbind (x := disj F1 F2)).
        assumption.
        intros w1 le1 H1.
        destruct H1 as [H11 | H12].
        + apply dforces_nplus_1.
          apply IHF1.
          assumption.
        + apply dforces_nplus_2.
          apply IHF2.
          assumption.
      - intros w H.
        apply (sfbind (x := conj F1 F2)).
        assumption.
        intros w1 le1 H1.
        simpl in H1.
        destruct H1 as [H11 H12].
        apply IHF1 in H11.
        apply IHF2 in H12.
        simpl.
        simpl in *.
        apply eforces_distrib; assumption.
      - simpl.
        intros.
        apply (sfbind (x := impl F1 F2)).
        assumption.
        intros w1 le1 H1.
        simpl in H1.
        apply cret.        
        apply meta_exp.
        intros w2 le2 H2.
        apply eforces2cforces.
        apply IHF2.
        apply H1.
        assumption.        
        apply f2f'.
        assumption. }
    { - induction F.
        + intros w H.
          simpl in H.
          apply lem1 in H.
          apply H.
        + simpl.
          intros w H.
          apply dforces_nplus in H.
          apply (dsbind (x := (two (enf2cnf (enf F1)) (enf2cnf (enf F2))))).
          assumption.
          intros w1 le1 H1.
          simpl in H1.
          destruct H1 as [H11|H12].
          * apply sret.
            left.
            apply IHF1.          
            apply cforces2eforces.
            assumption.
          * apply sret.
            right.
            apply IHF2.          
            apply cforces2eforces.
            assumption.
        + simpl.
          intros w H.
          apply eforces_distrib' in H.
          destruct H as [H_1 H_2].
          apply IHF1 in H_1.
          apply IHF2 in H_2.
          apply sret.
          split; assumption.          
        + simpl.
          intros w H.
          set (H' := exp_meta (enf2cnf (enf F2)) (enf F1) w H).
          apply sret.
          simpl.
          intros w1 le1 H1.
          apply IHF2.          
          apply cforces2eforces.
          apply H'.
          assumption.          
          apply f2f.
          assumption. }
  Defined.
End Forcing.
