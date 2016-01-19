(** Implementation of formula normalization for first-order formulas
    from the paper "An Intuitionistic Formula Hierarchy Based on
    High-School Identities" by Taus Brock-Nannestad and Danko Ilik

    Optimized version, i.e. where blocks of existential quantifiers
    are turned into one existential quantifier over a list of
    variables.

    Checked with Coq 8.5beta3 (November 2015)
*)

Parameters Proposition Var  : Set.

Require Import List.

Inductive Formula : Set :=
  _' : Proposition -> Formula
| disj : Formula -> Formula -> Formula
| conj : Formula -> Formula -> Formula
| impl : Formula -> Formula -> Formula
| ex   : Var -> Formula -> Formula
| all  : Var -> Formula -> Formula.

Inductive CNF : Set :=
     | top
     | con : list Var -> CNF -> Base -> CNF -> CNF
with DNF : Set :=
     | two : CNF -> CNF -> DNF
     | dis : CNF -> DNF -> DNF
with Base : Set :=
     | prp : Proposition -> Base
     | bd : DNF -> Base
     | exi : list Var -> CNF -> Base
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
    | con xs c10 d c13 => con xs c10 d (ntimes c13 c2)
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

  Fixpoint explog0 (d : Base)(d2 : DNF)(xs : list Var) {struct d2} : CNF :=
    match d2 with
    | two c1 c2 => ntimes (con xs c1 d top) (con xs c2 d top)
    | dis c d3 => ntimes (con xs c d top) (explog0 d d3 xs)
    end.
  
  Definition explog1 (d : Base)(e : ENF)(xs : list Var) : CNF :=
    match e with
    | cnf (con ys top (exi xs c) top) => con (xs++ys) c d top
    | cnf c => con xs c d top
    | dnf d1 => explog0 d d1 xs
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
    | con xs c1 d c2 => ntimes (explog1 d (distrib1 c1 e2) xs) (explogn c2 e2)
    end.

  Definition __ : Proposition -> CNF :=
    fun p => con nil top (prp p) top.

  Definition ___ : Base -> CNF := fun b =>
      match b with
      | prp p => __ p
      | bd d => con nil top (bd d) top
      | exi xs c => con nil top (exi xs c) top
      end.

  Fixpoint optimex (xs : list Var)(c : CNF) {struct c} : Base :=
    match c with
    | con nil top (exi ys c1) top => optimex (xs++ys) c1
    | _ => exi xs c
    end.
                
  Fixpoint distribexd (xs : list Var)(d : DNF) {struct d} : DNF :=
    match d with
    | two c1 c2 => two (___ (optimex xs c1)) (___ (optimex xs c2))
    | dis c1 d2 => dis (___ (optimex xs c1)) (distribexd xs d2)
    end.
    
  Definition distribex (xs : list Var)(e : ENF) : ENF :=
    match e with
    | cnf c => cnf (___ (optimex xs c))
    | dnf d => dnf (distribexd xs d)
    end.

  Fixpoint explogall (c : CNF)(xs : list Var) {struct c} : CNF :=
    match c with
    | top => top
    | con ys c1 b1 c2 => con (xs++ys) c1 b1 (explogall c2 xs)
    end.
    
  Fixpoint enf (f : Formula) {struct f} : ENF :=
    match f with
    | _' p => cnf (__ p)
    | disj f0 f1 => dnf (nplus (enf f0) (enf f1))
    | conj f0 f1 => distrib (enf f0) (enf f1)
    | impl f0 f1 => cnf (explogn (enf_pos f1) (enf f0))
    | ex x f => distribex (x :: nil) (enf f)
    | all x f => cnf (explogall (enf_pos f) (x :: nil))
    end
  with
  enf_pos (f : Formula) {struct f} : CNF :=
    match f with
    | _' p => __ p
    | disj f0 f1 => ___ (bd (nplus (cnf (enf_pos f0))
                                   (cnf (enf_pos f1))))
    | conj f0 f1 => ntimes (enf_pos f0) (enf_pos f1)
    | impl f0 f1 => explogn (enf_pos f1) (enf f0)
    | ex x f => ___ (exi (x :: nil) (enf_pos f))
    | all x f => explogall (enf_pos f) (x :: nil)
    end.
End FormulaNormalization.

Section Testing.
  Variables p q r s t u w : Proposition.

  Definition P := _' p.
  Definition Q := _' q.
  Definition R := _' r.
  Definition S := _' s.
  Definition T := _' t.
  Definition U := _' u.
  Definition W := _' w.

  Variables x y z x1 x2 x3 x4 : Var.

  Eval compute in (enf (all x P)).
  Eval compute in (enf (all y (all x P))).
  Eval compute in (enf (all y (all x (conj (conj (conj (all x1 P) (all x2 Q)) (all x3 R)) (all x4 S))))).
  Eval compute in (enf (impl Q (all x P))).
  Eval compute in (enf (all y (impl Q (all x P)))).
  Eval compute in (enf (all z (impl R (all y (impl Q (all x P)))))).
  Eval compute in (enf (all z (impl R (all y (conj (impl Q (all x P)) S))))).
  Eval compute in (enf (ex x (disj (disj P Q) R))).
  Eval compute in (enf (ex y (ex x (disj (disj P Q) R)))).
  Eval compute in (enf (ex y (ex x P))).
  Eval compute in (enf (ex x (conj (disj P Q) R))).
  Eval compute in (enf (impl (ex x P) Q)).
End Testing.
