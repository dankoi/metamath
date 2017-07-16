(** Implementation of formula normalization for propositional
    formulas, including a formal proof of the Lemma and Theorem for
    transforming G4ip into HS proofs from the paper "An Intuitionistic
    Formula Hierarchy Based on High-School Identities" by Taus
    Brock-Nannestad and Danko Ilik

    Checked with Coq 8.5beta3 (November 2015)
*)
Variable Proposition : Set.

Inductive Formula : Set :=
  prop : Proposition -> Formula
| disj : Formula -> Formula -> Formula
| conj : Formula -> Formula -> Formula
| impl : Formula -> Formula -> Formula.

Inductive CNF : Set :=
     | top
     | con : CNF -> Base -> CNF -> CNF
with DNF : Set :=
     | two : CNF -> CNF -> DNF
     | dis : CNF -> DNF -> DNF
with Base : Set :=
     | prp : Proposition -> Base
     | bd : DNF -> Base
.

Inductive ENF : Set :=
  cnf : CNF -> ENF
| dnf : DNF -> ENF.

Section FormulaNormalization.

  Fixpoint nplus1 (d : DNF)(e2 : ENF) {struct d} : DNF :=
    match d with
    | two c c0 => match e2 with
                  | cnf c1 => dis c (two c0 c1)
                  | dnf d0 => dis c (dis c0 d0)
                  end
    | dis c d0 => dis c (nplus1 d0 e2)
    end.
    
  Definition nplus (e1 e2 : ENF) : DNF :=
    match e1 with
    | cnf a => match e2 with
               | cnf c => two a c
               | dnf d => dis a d
               end
    | dnf b => nplus1 b e2
    end.

  Fixpoint ntimes (c1 c2 : CNF) {struct c1} : CNF :=
    match c1 with
    | top => c2
    | con c10 d c13 => con c10 d (ntimes c13 c2)
    end.

  Fixpoint distrib0 (c : CNF)(d : DNF) : ENF :=
    match d with
    | two c0 c1 => dnf (two (ntimes c c0) (ntimes c c1))
    | dis c0 d0 => dnf match distrib0 c d0 with
                       | cnf c1 => two (ntimes c c0) c1
                       | dnf d1 => dis (ntimes c c0) d1
                       end
    end.
  
  Definition distrib1 (c : CNF)(e : ENF) : ENF :=
    match e with
    | cnf a => cnf (ntimes c a)
    | dnf b => distrib0 c b
    end.

  Fixpoint explog0 (d : Base)(d2 : DNF) {struct d2} : CNF :=
    match d2 with
    | two c1 c2 => ntimes (con c1 d top) (con c2 d top)
    | dis c d3 => ntimes (con c d top) (explog0 d d3)
    end.
  
  Definition explog1 (d : Base)(e : ENF) : CNF :=
    match e with
    | cnf c => con c d top
    | dnf d1 => explog0 d d1
    end.

  Fixpoint distribn (d : DNF)(e2 : ENF) {struct d} : ENF :=
    match d with
    | two c c0 => dnf (nplus (distrib1 c e2) (distrib1 c0 e2))
    | dis c d0 => dnf (nplus (distrib1 c e2) (distribn d0 e2))
    end.
  
  Definition distrib (e1 e2 : ENF) : ENF :=
    match e1 with
    | cnf a => distrib1 a e2
    | dnf b => distribn b e2
    end.

  Fixpoint explogn (c:CNF)(e2:ENF) {struct c} : CNF :=
    match c with
    | top => top
    | con c1 d c2 => ntimes (explog1 d (distrib1 c1 e2)) (explogn c2 e2)
    end.

  Definition p2c : Proposition -> CNF :=
    fun p => con top (prp p) top.

  Definition b2c : Base -> CNF := fun b =>
      match b with
      | prp p => p2c p
      | bd d => con top (bd d) top
      end.
      
  Fixpoint enf (f : Formula) {struct f} : ENF :=
    match f with
    | prop p => cnf (p2c p)
    | disj f0 f1 => dnf (nplus (enf f0) (enf f1))
    | conj f0 f1 => distrib (enf f0) (enf f1)
    | impl f0 f1 => cnf (explogn (enf_pos f1) (enf f0))
    end
  with
  enf_pos (f : Formula) {struct f} : CNF :=
    match f with
    | prop p => p2c p
    | disj f0 f1 => b2c (bd (nplus (cnf (enf_pos f0))
                                   (cnf (enf_pos f1))))
    | conj f0 f1 => ntimes (enf_pos f0) (enf_pos f1)
    | impl f0 f1 => explogn (enf_pos f1) (enf f0)
    end.

  Fixpoint enf2cnf (e:ENF) {struct e} : CNF :=
    match e with
    | cnf c => c
    | dnf d => b2c (bd d)
    end.
End FormulaNormalization.

Section Testing.
  Variables p q r s t u w : Proposition.

  Definition P := prop p.
  Definition Q := prop q.
  Definition R := prop r.
  Definition S := prop s.
  Definition T := prop t.
  Definition U := prop u.
  Definition W := prop w.

  Eval simpl in (enf (conj (conj P (conj Q R)) (conj S (conj T U)))).
  Eval simpl in (enf (disj (disj P Q) R)).
  Eval simpl in (enf (conj (disj (disj P Q) R) (disj S T))).
  Eval compute in (enf (impl (disj P Q) R)).
  Eval compute in (enf (impl (disj P Q) (disj R S))).
  Eval compute in (enf (impl (impl (disj P Q) R) R)).
  Eval compute in (enf (impl (impl (disj P Q) R) (impl (disj S T) U))).
  Eval compute in (enf (impl (impl (disj P Q) R) (impl (disj S T) (disj U W)))).
  Eval compute in (enf (impl (impl (disj P Q) R) (impl (disj S T) (conj U W)))).
End Testing.

Section Equations.
  Lemma ntimes_top : forall c, ntimes c top = c.
  Proof.
    intro c.
    induction c.
    - reflexivity.
    - simpl.
      rewrite IHc2.
      reflexivity.
  Defined.

  Lemma ntimes_assoc :
    forall e1 e2 e3,
      ntimes (ntimes e1 e2) e3 = ntimes e1 (ntimes e2 e3).
  Proof.
    intros.
    induction e1.
    - simpl; reflexivity.
    - simpl.
      rewrite IHe1_2.
      reflexivity.
  Qed.

  Lemma nplus1_assoc :
    forall d e2 e3,
      nplus1 d (dnf (nplus e2 e3)) = nplus1 (nplus1 d e2) e3.
  Proof.
    intros.
    induction d.
    - simpl.
      destruct e2; simpl.
      + destruct e3; reflexivity.
      + reflexivity.
    - simpl.
      rewrite IHd.
      reflexivity.
  Qed.
                                        
  Lemma nplus_assoc :
    forall e1 e2 e3,
      nplus e1 (dnf (nplus e2 e3)) = nplus (dnf (nplus e1 e2)) e3.
  Proof.
    intros.
    destruct e1.
    - simpl.
      destruct e2.
      + simpl.
        destruct e3; reflexivity.
      + simpl.
        reflexivity.
    - simpl.
      apply nplus1_assoc.
  Qed.
        
  Lemma distrib0_nplus1 :
    forall c d e,
      distrib0 c (nplus1 d e) =
      dnf (nplus (distrib0 c d) (distrib1 c e)).
  Proof.
    intros.
    induction d.
    - simpl.
      destruct e.
      + simpl.
        reflexivity.
      + simpl.
        destruct (distrib0 c d); reflexivity.
    - simpl.
      rewrite IHd.
      destruct (distrib0 c d).
      + simpl in *.
        destruct (distrib1 c e); reflexivity.
      + simpl in *.
        reflexivity.
  Qed.

  Lemma distrib0_nplus :
    forall c e1 e2,
      distrib0 c (nplus e1 e2) =
      dnf (nplus (distrib1 c e1) (distrib1 c e2)).
  Proof.
    intros.
    destruct e1, e2.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      rewrite distrib0_nplus1.
      simpl.
      reflexivity.
    - simpl.
      rewrite distrib0_nplus1.
      simpl.
      reflexivity.
  Qed.

  Lemma distribn_nplus1 :
    forall d e1 e2,
      distribn (nplus1 d e1) e2 =
      dnf (nplus (distribn d e2) (distrib e1 e2)).
  Proof.
    intros.
    induction d.
    - simpl.
      destruct e1.      
      + simpl.
        rewrite nplus_assoc.
        simpl.
        reflexivity.
      + simpl.        
        rewrite nplus_assoc.
        simpl.
        reflexivity.
    - simpl in *.
      rewrite IHd.
      rewrite nplus_assoc.
      simpl.
      reflexivity.
  Qed.
  
  Lemma distribn_nplus :
    forall e1 e2 e3,
      distribn (nplus e1 e2) e3 =
      dnf (nplus (distrib e1 e3) (distrib e2 e3)).
  Proof.
    intros.
    destruct e1, e2; simpl in *.
    - reflexivity.
    - reflexivity.
    - rewrite distribn_nplus1.
      simpl.
      reflexivity.
    - rewrite distribn_nplus1.
      simpl.
      reflexivity.
  Qed.

  Lemma distrib1_top : forall e, distrib1 top e = e.
  Proof.
    intro e.
    destruct e.
    - reflexivity.
    - unfold distrib1.
      induction d.
      + simpl.
        reflexivity.
      + simpl.
        rewrite IHd.
        reflexivity.
  Defined.

  Lemma distrib1_distrib0 :
    forall c c0 d,
      distrib1 c (distrib0 c0 d) = distrib0 (ntimes c c0) d.
  Proof.
    intros.
    induction d.
    - simpl.
      do 2 rewrite ntimes_assoc.
      reflexivity.
    - simpl.
      rewrite <- IHd.
      destruct (distrib0 c0 d).
      + simpl.
        rewrite ntimes_assoc.
        reflexivity.
      + simpl.        
        rewrite ntimes_assoc.
        reflexivity.
  Qed.
  
  Lemma distrib1_distrib1 :
    forall c c0 e3, 
      distrib1 c (distrib1 c0 e3) = distrib1 (ntimes c c0) e3.
  Proof.
    induction e3; simpl in *.
    - rewrite ntimes_assoc.
      reflexivity.
    - apply distrib1_distrib0.
  Qed.
          
  Lemma distrib1_distribn :
    forall c d e3,
      distrib1 c (distribn d e3) = distrib (distrib0 c d) e3.
  Proof.
    intros.
    induction d.
    - simpl.
      rewrite distrib0_nplus.
      rewrite distrib1_distrib1.
      rewrite distrib1_distrib1.
      reflexivity.
    - simpl distribn.
      simpl distrib1.
      rewrite distrib0_nplus.
      rewrite IHd.
      simpl.
      remember (distrib0 c d) as e.
      destruct e.
      + simpl in *.
        rewrite <- distrib1_distrib1.
        reflexivity.
      + simpl in *.
        rewrite <- distrib1_distrib1.
        reflexivity.
  Qed.
  
  Lemma distrib1_distrib :
    forall c e2 e3,
      distrib1 c (distrib e2 e3) = distrib (distrib1 c e2) e3.
  Proof.
    intros.
    destruct e2.
    - simpl.
      apply distrib1_distrib1.
    - simpl.
      apply distrib1_distribn.
  Qed.

  Lemma distribn_distrib :
    forall d e2 e3,
      distribn d (distrib e2 e3) = distrib (distribn d e2) e3.
  Proof.
    intros.
    induction d.
    - simpl.
      rewrite distrib1_distrib.
      rewrite distrib1_distrib.
      rewrite distribn_nplus.
      reflexivity.      
    - simpl.
      rewrite distrib1_distrib.
      rewrite IHd.
      rewrite distribn_nplus.
      reflexivity.      
  Qed.
    
  Lemma distrib_assoc :
    forall e1 e2 e3,
      distrib e1 (distrib e2 e3) = distrib (distrib e1 e2) e3.
  Proof.
    intros.
    destruct e1.
    - simpl.
      apply distrib1_distrib.
    - simpl.
      apply distribn_distrib.
  Qed.

  Lemma explogn_top : forall c, explogn c (cnf top) = c.
  Proof.
    induction c.
    - simpl.
      reflexivity.
    - simpl.      
      rewrite IHc2.
      rewrite ntimes_top.
      reflexivity.
  Qed.

  Lemma explogn_ntimes :
    forall c c' e,
      explogn (ntimes c c') e =
      ntimes (explogn c e) (explogn c' e).
  Proof.
    intros.
    induction c.
    - simpl.    
      reflexivity.
    - simpl.
      rewrite IHc2.
      rewrite ntimes_assoc.
      reflexivity.
  Qed.

  Lemma explog0_nplus1 :
    forall b d e,
      explog0 b (nplus1 d e) = ntimes (explog0 b d) (explog1 b e).
  Proof.
    intros.
    induction d.
    - simpl.
      destruct e; reflexivity.
    - simpl in *.
      rewrite IHd.
      reflexivity.
  Qed.
                                         
  Lemma explog0_nplus :
    forall b e1 e2,
      explog0 b (nplus e1 e2) = ntimes (explog1 b e1) (explog1 b e2).
  Proof.
    intros.
    induction e1.
    - simpl.
      destruct e2; simpl; reflexivity.
    - simpl.
      rewrite explog0_nplus1.
      reflexivity.
  Qed.

  Lemma explogn_explog1 :
    forall b e1 e2,
      explogn (explog1 b e1) e2 = explog1 b (distrib e1 e2).
  Proof.
    intros.
    induction e1.
    - simpl.
      rewrite ntimes_top.
      reflexivity.      
    - simpl.
      induction d.
      + simpl.
        rewrite ntimes_top.
        rewrite explog0_nplus.
        reflexivity.
      + simpl.
        rewrite IHd.
        rewrite explog0_nplus.
        reflexivity.
  Qed.

  Lemma explogn_distrib : forall c e1 e2,
      explogn c (distrib e1 e2) = explogn (explogn c e1) e2.
  Proof.
    intro c.
    induction c; intros; simpl in *.
    - reflexivity.
    - rewrite explogn_ntimes.
      rewrite explogn_explog1.
      rewrite IHc2.
      rewrite distrib1_distrib.
      reflexivity.
  Qed.
  
  Lemma explogn_nplus :
    forall c e1 e2,
      explogn c (dnf (nplus e1 e2)) =
      ntimes (explogn c e1) (explogn c e2).
  Proof.
    intros.
    induction c.
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHc2.
      rewrite distrib0_nplus.
      simpl.
      rewrite explog0_nplus.
      (* NOW THIS IS EQUAL MODULO COMMUTATIVITY OF ntimes *)
  Admitted.

  Lemma explogn_distribn_nplus :
    forall f g h e,
      ntimes (explogn h (distrib f e)) (explogn h (distrib g e)) =
      explogn h (distribn (nplus f g) e).
  Proof.
    intros.
    rewrite distribn_nplus.
    rewrite explogn_nplus.
    reflexivity.
  Qed.
End Equations.

Section SequentCalculi.

  (** Intuitionistic sequent calculus G4ip *)
  Inductive LJ : Formula -> Set :=
  (* non-invertible rules *)
  | LJ_init : forall Gamma p, 
      LJ (impl (conj (prop p) Gamma) (prop p))
  | LJ_disj_right_1 : forall Gamma F G,
      LJ (impl Gamma F) -> LJ (impl Gamma (disj F G))
  | LJ_disj_right_2 : forall Gamma F G,
      LJ (impl Gamma G) -> LJ (impl Gamma (disj F G))
  | LJ_impl_left_P : forall Gamma F G p,
      LJ (impl (conj F (conj (prop p) Gamma)) G) ->
      LJ (impl (conj (impl (prop p) F) (conj (prop p) Gamma)) G)
  | LJ_impl_left_impl : forall Gamma F G H I,
      LJ (conj (impl (conj (impl G H) Gamma) (impl F G))
               (impl (conj H Gamma) I)) ->
      LJ (impl (conj (impl (impl F G) H) Gamma) I)
  (* invertible rules *)
  | LJ_impl_right : forall Gamma F G,
      LJ (impl (conj F Gamma) G) ->
      LJ (impl Gamma (impl F G))
  | LJ_conj_right : forall Gamma F G,
      LJ (conj (impl Gamma F) (impl Gamma G)) ->
      LJ (impl Gamma (conj F G))
  | LJ_disj_left : forall Gamma F G H,
      LJ (conj (impl (conj F Gamma) H) (impl (conj G Gamma) H)) ->
      LJ (impl (conj (disj F G) Gamma) H)
  | LJ_impl_left_conj : forall Gamma F G H I,
      LJ (impl (conj (impl F (impl G H)) Gamma) I) ->
      LJ (impl (conj (impl (conj G F) H) Gamma) I)
  | LJ_impl_left_disj : forall Gamma F G H I,
      LJ (impl (conj (conj (impl F H) (impl G H)) Gamma) I) ->
      LJ (impl (conj (impl (disj F G) H) Gamma) I)
  | LJ_conj_left : forall Gamma F G H,
      LJ (impl (conj F (conj G Gamma)) H) ->
      LJ (impl (conj (conj F G) Gamma) H)
  .

  (** `High-school' sequent calculus *)
  Inductive HS : CNF -> Set :=
  | HS_init :
      forall p e, HS (explog1 (prp p) (distrib1 (p2c p) e))

  | HS_disj_1 :
      forall c1 c2 e,
        HS (explogn c1 e) ->
        HS (explog1 (bd (two c1 c2)) e)

  | HS_disj_2 :
      forall c1 c2 e,
        HS (explogn c2 e) ->
        HS (explog1 (bd (two c1 c2)) e)

  | HS_impl_p :
    forall p c F e,
      HS (explogn c (distrib (enf F) (distrib1 (p2c p) e))) ->
      HS (explogn c (distrib1 (explogn (enf_pos F) (cnf (p2c p))) (distrib1 (p2c p) e)))
         
  | HS_impl_impl :
    forall G e1 H c e2,
      HS (ntimes
            (explogn (explogn (enf_pos G) e1)
                     (distrib1 (explogn (enf_pos H) (enf G)) e2))
            (explogn c (distrib (enf H) e2))) ->
      HS (explogn c
                  (distrib1 (explogn (enf_pos H) (cnf (explogn (enf_pos G) e1))) e2))
  .
End SequentCalculi.

Section LJtoHS.
  Theorem embed : forall F, LJ F -> HS (enf2cnf (enf F)).
  Proof.
    intros F lj.
    induction lj; simpl in *; try rewrite ntimes_top; try rewrite distrib1_top. 
    - apply HS_init.
    - apply HS_disj_1; assumption.
    - apply HS_disj_2; assumption.
    - apply HS_impl_p; assumption.
    - apply HS_impl_impl; assumption.
    - rewrite <- explogn_distrib; assumption.
    - rewrite explogn_ntimes; assumption.
    - rewrite <- explogn_distribn_nplus; assumption.
    - rewrite explogn_distrib; assumption.
    - rewrite explogn_nplus; assumption.
    - rewrite explogn_distrib; assumption.
  Defined.
End LJtoHS.
