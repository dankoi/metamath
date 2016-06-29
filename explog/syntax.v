(** * syntax.v

This file defines:

- [Formula] - the language of types
- [ENF] - the language of type normal forms
- [ND] - typed lambda calculus 
- [HSc]/[HSb] - compact term calculus

- the fixpoints for normalizing a type to its normal form, resulting
  with [enf], as well as various correctness properties of these
  fixpoints that will be used in other files

*)

Definition Proposition := nat.

Inductive Formula : Set :=
| prop : Proposition -> Formula
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
     | bd : DNF -> Base.

Inductive ENF : Set :=
| cnf : CNF -> ENF
| dnf : DNF -> ENF.

Lemma CNF_dec : (forall x y:CNF, {x=y}+{~x=y})
with DNF_dec : (forall x y:DNF, {x=y}+{~x=y})
with Base_dec : (forall x y:Base, {x=y}+{~x=y}).
Proof.
  - decide equality.
  - decide equality.
  - decide equality.
    + unfold Proposition in *.
      decide equality.
Defined.

Lemma CNF_eqb (x y:CNF) : bool
with DNF_eqb (x y:DNF) : bool
with Base_eqb (x y:Base) : bool.
Proof.
  - compare x y.
    + intro. exact true.
    + intro. exact false.
    + apply Base_dec.
  - compare x y.
    + intro. exact true.
    + intro. exact false.
    + apply CNF_dec.
    + apply CNF_dec.
    + apply CNF_dec.
  - compare x y.
    + intro. exact true.
    + intro. exact false.
    + unfold Proposition in *.
      decide equality.
    + apply DNF_dec.
Defined.

Section TypeNormalization.
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

  Definition b2c : Base -> CNF :=
    fun b =>
      match b with
      | prp p => p2c p
      | bd d => con top (bd d) top
      end.

  Fixpoint enf2cnf (e:ENF) {struct e} : CNF :=
    match e with
    | cnf c => c
    | dnf d => b2c (bd d)
    end.

  Fixpoint enf (f : Formula) {struct f} : ENF :=
    match f with
    | prop p => cnf (p2c p)
    | disj f0 f1 => dnf (nplus (enf f0) (enf f1))
    | conj f0 f1 => distrib (enf f0) (enf f1)
    | impl f0 f1 => cnf (explogn (enf2cnf (enf f1)) (enf f0))
    end.
End TypeNormalization.

Section TypeNormalizationCorrectness.
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
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.

  Lemma distrib1_distrib1 :
    forall c c0 e3, 
      distrib1 c (distrib1 c0 e3) = distrib1 (ntimes c c0) e3.
  Proof.
    induction e3; simpl in *.
    - rewrite ntimes_assoc.
      reflexivity.
    - apply distrib1_distrib0.
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.

  Lemma explogn_top : forall c, explogn c (cnf top) = c.
  Proof.
    induction c.
    - simpl.
      reflexivity.
    - simpl.      
      rewrite IHc2.
      rewrite ntimes_top.
      reflexivity.
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.
End TypeNormalizationCorrectness.

Module NaturalDeduction.
  Inductive ND : list Formula -> Formula -> Set :=
  | hyp : forall {Gamma A},
      ND (A :: Gamma) A
  | wkn : forall {Gamma A B},
      ND Gamma A -> ND (B :: Gamma) A
  | lam : forall {Gamma A B},
      ND (A :: Gamma) B -> ND Gamma (impl A B)
  | app : forall {Gamma A B},
      ND Gamma (impl A B) -> ND Gamma A -> ND Gamma B
  | pair : forall {Gamma A B},
      ND Gamma A -> ND Gamma B -> ND Gamma (conj A B)
  | fst : forall {Gamma A B},
      ND Gamma (conj A B) -> ND Gamma A
  | snd : forall {Gamma A B},
      ND Gamma (conj A B) -> ND Gamma B
  | inl : forall {Gamma A B},
      ND Gamma A -> ND Gamma (disj A B)
  | inr : forall {Gamma A B},
      ND Gamma B -> ND Gamma (disj A B)
  | cas : forall {Gamma A B C},
      ND Gamma (disj A B) ->
      ND (A :: Gamma) C -> ND (B :: Gamma) C ->
      ND Gamma C.
End NaturalDeduction.

Module HighSchool.
  Inductive HSc : CNF -> Set :=
  | tt : HSc top
  | pair : forall {c1 b c2},
      HSb c1 b ->
      HSc c2 -> HSc (con c1 b c2)
  with HSb : CNF -> Base -> Set :=
       | app : forall {p c0 c1 c2},
           HSc (explogn c1 (cnf (ntimes c2 (con c1 (prp p) c0)))) ->
           HSb (ntimes c2 (con c1 (prp p) c0)) (prp p)
       | cas : forall {d b c0 c1 c2 c3},
           HSc (explogn c1 (cnf (ntimes c2 (con c1 (bd d) c0)))) ->
           HSc (explogn (explog0 b d)
                        (cnf (ntimes c3 (ntimes c2 (con c1 (bd d) c0))))) ->
           HSb (ntimes c3 (ntimes c2 (con c1 (bd d) c0))) b
       | wkn : forall {c0 c1 b1 b},
           HSb c0 b -> HSb (con c1 b1 c0) b
       | inl_two : forall {c0 c1 c2},
           HSc (explogn c1 (cnf c0)) -> HSb c0 (bd (two c1 c2))
       | inr_two : forall {c0 c1 c2},
           HSc (explogn c2 (cnf c0)) -> HSb c0 (bd (two c1 c2))
       | inl_dis : forall {c0 c d},
           HSc (explogn c (cnf c0)) -> HSb c0 (bd (dis c d))
       | inr_dis : forall {c0 c d},
           HSb c0 (bd d) -> HSb c0 (bd (dis c d)).
  
  Definition snd : forall {c1 b c2}, HSc (con c1 b c2) -> HSc c2.
  Proof.
    intros.
    inversion H.    
    assumption.
  Defined.
  
  Definition fst : forall {c1 b c2}, HSc (con c1 b c2) -> HSb c1 b.
  Proof.
    intros.
    inversion H.
    assumption.
  Defined.

  (** A version of HS suitable for printing the de Bruijn index of the
  variable implicitly used by app and cas *)
  Inductive HSc_ : CNF -> Set :=
  | tt_ : HSc_ top
  | pair_ : forall {c1 b c2},
      HSb_ c1 b ->
      HSc_ c2 -> HSc_ (con c1 b c2)
  with HSb_ : CNF -> Base -> Set :=
       | app_ : forall {p c0 c1 c2}, forall n:nat,
           HSc_ (explogn c1 (cnf (ntimes c2 (con c1 (prp p) c0)))) ->
           HSb_ (ntimes c2 (con c1 (prp p) c0)) (prp p)
       | cas_ : forall {d b c0 c1 c2 c3}, forall n:nat,
           HSc_ (explogn c1 (cnf (ntimes c2 (con c1 (bd d) c0)))) ->
           HSc_ (explogn (explog0 b d)
                        (cnf (ntimes c3 (ntimes c2 (con c1 (bd d) c0))))) ->
           HSb_ (ntimes c3 (ntimes c2 (con c1 (bd d) c0))) b
       | wkn_ : forall {c0 c1 b1 b},
           HSb_ c0 b -> HSb_ (con c1 b1 c0) b
       | inl_two_ : forall {c0 c1 c2},
           HSc_ (explogn c1 (cnf c0)) -> HSb_ c0 (bd (two c1 c2))
       | inr_two_ : forall {c0 c1 c2},
           HSc_ (explogn c2 (cnf c0)) -> HSb_ c0 (bd (two c1 c2))
       | inl_dis_ : forall {c0 c d},
           HSc_ (explogn c (cnf c0)) -> HSb_ c0 (bd (dis c d))
       | inr_dis_ : forall {c0 c d},
           HSb_ c0 (bd d) -> HSb_ c0 (bd (dis c d)).

  Fixpoint clength (c : CNF) {struct c} : nat :=
    match c with
    | top => 0
    | con c b c0 => S (clength c0)
    end.

  (** The "pretty-printer" *)
  Fixpoint ppc {c : CNF}(H : HSc c) {struct H} : HSc_ c :=
    match H with
    | tt => tt_
    | pair x x0 => pair_ (ppb x) (ppc x0)
    end
  with ppb {c : CNF}{b : Base}(H : HSb c b) {struct H} : HSb_ c b :=
    match H with
    | @app p c0 c1 c2 x => @app_ p c0 c1 c2 (clength c2) (ppc x)
    | @cas d b c0 c1 c2 c3 x x0 => @cas_ d b c0 c1 c2 c3 (clength c2 + clength c3) (ppc x) (ppc x0)
    | wkn x => wkn_ (ppb x)
    | inl_two x => inl_two_ (ppc x)
    | inr_two x => inr_two_ (ppc x)
    | inl_dis x => inl_dis_ (ppc x)
    | inr_dis x => inr_dis_ (ppb x)
    end.

  (** Also a boolean function comparing two terms for identity *)
  Lemma HSc_eqb (c:CNF)(p q:HSc c) : bool
  with HSb_eqb (c:CNF)(b:Base)(p q:HSb c b) : bool.
  Proof.
    { destruct c.
      - exact true.
      - inversion p.
        inversion q.
        apply andb.
        + apply (HSb_eqb c1 b H1 H6).
        + apply (HSc_eqb c2 H3 H8). }
    {  inversion p; inversion q; try congruence.
       - rewrite H3 in *.
         rewrite H0 in *.
         compare c1 c4.
         + intro Heq.
           rewrite Heq in *.
           apply (HSc_eqb _ H H2).
         + intro. exact false.
         + apply Base_dec.
       - exact false.
       - exact false.
       - exact false.
       - rewrite H1 in *.
         rewrite H5 in *.
         compare c1 c5.
         intro Heq.
         rewrite Heq in *.
         compare d0 d.
         intro Heq'.
         rewrite Heq' in *.
         compare c2 c6.
         intro Heq''.
         rewrite Heq'' in *.
         compare c0 c4.           
         intro Heq'''.
         rewrite Heq''' in *.
         apply andb.
         apply (HSc_eqb _ H H3).
         apply (HSc_eqb _ H0 H4).
         intro. exact false.
         apply Base_dec.       
         intro. exact false.
         apply Base_dec.       
         intro. exact false.
         apply CNF_dec.       
         apply CNF_dec.       
         apply CNF_dec.       
         intro. exact false.
         apply Base_dec.       
       - exact false.
       - exact false.
       - exact false.
       - exact false.
       - exact false.
       - exact false.
       - exact false.
       - assert (c0 = c2).
         congruence.
         rewrite H5 in *.
         apply (HSb_eqb _ _ H H2).       
       - exact false.
       - exact false.
       - exact false.
       - exact false.
       - exact false.
       - exact false.
       - assert (c1 = c4).
         congruence.       
         rewrite H5 in *.       
         apply (HSc_eqb _ H H2).
       - exact false.
       - exact false.
       - exact false.
       - exact false.
       - assert (c2 = c5).
         congruence.       
         rewrite H5 in *.       
         apply (HSc_eqb _ H H2).
       - exact false.
       - exact false.
       - assert (c1 = c3).
         congruence.       
         rewrite H5 in *.       
         apply (HSc_eqb _ H H2).
       - exact false.
       - exact false.
       - exact false.
       - exact false.
       - assert (d0 = d).
         congruence.       
         rewrite H5 in *.       
         apply (HSb_eqb _ _ H H2).       }
  Defined.
End HighSchool.




