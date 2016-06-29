(** * examples.v

This file first defines two normalizers, by combining syntax.v and
semantics.v:

- [nbe], mapping [ND] to [HSc]/[HSb]
- [ebn], mapping [HSc]/[HSb] to [ND]

Then, the examples mentioned in the paper are implemented

 *)
Require Export syntax.
Require Export semantics.
Require Export evaluate.
Require Export reify.

Set Implicit Arguments.

Open Scope type_scope.

Export ReifyND.
Export ReifyHS.

Module nd := NaturalDeduction.
Module hs := HighSchool.

Module ND2HS.
  Module evalND := EvalND structureHS.
  Export evalND.

  Lemma nbe : forall {F},
      nd.ND nil F ->
      match (enf F) with
        cnf cF => hs.HSc cF
      | dnf dF => hs.HSb top (bd dF)
      end.
  Proof.
    intros.
    set (Heval := eval H (w:=top) Datatypes.tt).
    apply f2f in Heval.
    destruct (enf F).
    - apply creify in Heval.
      simpl.
      rewrite explogn_top in Heval.
      exact Heval.
    - apply dreify in Heval.
      simpl.
      exact Heval.
  Defined.
End ND2HS.

Module HS2ND.
  Module evalHS := EvalHS structureND.
  Export evalHS.

  Lemma ebn : forall {F},
      match (enf F) with
        cnf cF => hs.HSc cF
      | dnf dF => hs.HSb top (bd dF)
      end ->
      nd.ND nil F.
  Proof.
    intros.
    remember (enf F) as e.
    destruct e.
    - set (Heval := evalc H (w:=nil)).
      replace (Cont cforces nil c) with (Cont eforces nil (enf F)) in Heval.
      apply f2f' in Heval.
      apply sreify in Heval.
      exact Heval.
      rewrite <- Heqe.
      reflexivity.
    - assert (Htop : Cont cforces nil top).
      apply cret.
      constructor.
      set (Heval := evalb H (w:=nil) Htop).
      replace (Cont bforces nil (bd d)) with (Cont eforces nil (enf F)) in Heval.
      apply f2f' in Heval.
      apply sreify in Heval.
      exact Heval.
      rewrite <- Heqe.
      reflexivity.
  Defined.
End HS2ND.

Definition P := prop 1.
Definition Q := prop 2.
Definition R := prop 3.
Definition S := prop 4.
Definition a := prop 5.
Definition b := prop 6.
Definition c := prop 7.
Definition d := prop 8.
Definition e := prop 9.
Definition f := prop 10.
Definition g := prop 11.
Definition h := prop 12.

Section Examples.
  Export NaturalDeduction.

  (** We first define deBruijn indices to help write shorter terms *)
  Definition _0 {F Gamma} : ND (cons F Gamma) F := hyp.
  Definition _1 {F0 F1 Gamma} : ND (cons F1 (cons F0 Gamma)) F0 := wkn hyp.
  Definition _2 {F0 F1 F2 Gamma} : ND (cons F2 (cons F1 (cons F0 Gamma))) F0 := wkn (wkn hyp).
  Definition _3 {F0 F1 F2 F3 Gamma} : ND (cons F3 (cons F2 (cons F1 (cons F0 Gamma)))) F0 := wkn (wkn (wkn hyp)).
  Definition _4 {F0 F1 F2 F3 F4 Gamma} : ND (cons F4 (cons F3 (cons F2 (cons F1 (cons F0 Gamma))))) F0 := wkn (wkn (wkn (wkn hyp))).
  Definition _5 {F0 F1 F2 F3 F4 F5 Gamma} : ND (cons F5 (cons F4 (cons F3 (cons F2 (cons F1 (cons F0 Gamma)))))) F0 := wkn (wkn (wkn (wkn (wkn hyp)))).
  Definition _6 {F0 F1 F2 F3 F4 F5 F6 Gamma} : ND (cons F6 (cons F5 (cons F4 (cons F3 (cons F2 (cons F1 (cons F0 Gamma))))))) F0 := wkn (wkn (wkn (wkn (wkn (wkn hyp))))).
  Definition _7 {F0 F1 F2 F3 F4 F5 F6 F7 Gamma} : ND (cons F7 (cons F6 (cons F5 (cons F4 (cons F3 (cons F2 (cons F1 (cons F0 Gamma)))))))) F0 := wkn (wkn (wkn (wkn (wkn (wkn (wkn hyp)))))).

  (** The examples from the paper *)
  Definition example1_1 : ND nil (impl (disj P Q) (impl (impl (disj P Q) R) R))
    := lam (lam (app _0 (cas _1 (inl _0) (inr _0)))).

  Definition example1_2 : ND nil (impl (disj P Q) (impl (impl (disj P Q) R) R))
    := lam (lam (cas _1 (app _1 (inl _0)) (app _1 (inr _0)))).
  
  Definition example1_3 : ND nil (impl (disj P Q) (impl (impl (disj P Q) R) R))
    := lam (cas _0 (lam (app _0 _2)) (lam (app _0 _2))).

  Definition example1_4 : ND nil (impl (disj P Q) (impl (impl (disj P Q) R) R))
    := lam (lam (app _0 _1)).

  Definition example2_1 : ND nil (impl (impl a b) (impl (impl c a) (impl c (impl (disj d e) b))))
    := lam (lam (lam (lam (app _3 (app _2 _1))))).

  Definition example2_2 : ND nil (impl (impl a b) (impl (impl c a) (impl c (impl (disj d e) b))))
    := lam (lam (lam (lam (cas _0 (app _4 (app _3 _2)) (app _4 (app _3 _2)))))).

  Definition example2_3 : ND nil (impl (impl a b) (impl (impl c a) (impl c (impl (disj d e) b))))
    := lam (lam (lam (lam (cas _0 (cas (inl _2) (app _5 (app _4 _0)) (app _5 _0)) (cas (inr (app _3 _2)) (app _5 (app _4 _0)) (app _5 _0)))))).

  Definition example2_4 : ND nil (impl (impl a b) (impl (impl c a) (impl c (impl (disj d e) b))))
    := lam (lam (lam (lam (cas (cas _0 (inl _2) (inr (app _3 _2))) (app _4 (app _3 _0)) (app _4 _0))))).
  Definition example3_app_1 : ND nil (impl S (impl (impl P (impl S R)) (impl (impl Q (impl S R)) (impl (disj P Q) R)))) :=
    lam
      (lam
         (lam
            (lam
               (app
                  (cas hyp (app (wkn (wkn (wkn hyp))) hyp)
                       (app (wkn (wkn hyp)) hyp)) (wkn (wkn (wkn hyp))))))).
    
  Definition example3_app_2 : ND nil (impl S (impl (impl P (impl S R)) (impl (impl Q (impl S R)) (impl (disj P Q) R)))) :=
    lam
      (lam
         (lam
            (lam
               (cas hyp
                    (app (app (wkn (wkn (wkn hyp))) hyp)
                         (wkn (wkn (wkn (wkn hyp)))))
                    (app (app (wkn (wkn hyp)) hyp) (wkn (wkn (wkn (wkn hyp))))))))).

  Definition example3_cas_1 : ND nil (impl (disj P Q) (impl (impl P (disj R S)) (impl (impl Q (disj R S)) (impl (impl R a) (impl (impl S a) a))))) :=
    lam
      (lam
         (lam
            (lam
               (lam
                  (cas
                     (cas (wkn (wkn (wkn (wkn hyp))))
                          (app (wkn (wkn (wkn (wkn hyp)))) hyp)
                          (app (wkn (wkn (wkn hyp))) hyp))
                     (app (wkn (wkn hyp)) hyp) (app (wkn hyp) hyp)))))).
  
  Definition example3_cas_2 : ND nil (impl (disj P Q) (impl (impl P (disj R S)) (impl (impl Q (disj R S)) (impl (impl R a) (impl (impl S a) a))))) :=
    lam
      (lam
         (lam
            (lam
               (lam
                  (cas (wkn (wkn (wkn (wkn hyp))))
                       (cas (app (wkn (wkn (wkn (wkn hyp)))) hyp)
                            (app (wkn (wkn (wkn hyp))) hyp) 
                            (app (wkn (wkn hyp)) hyp))
                       (cas (app (wkn (wkn (wkn hyp))) hyp)
                            (app (wkn (wkn (wkn hyp))) hyp) 
                            (app (wkn (wkn hyp)) hyp))))))).
  
  Definition example4_eta_arrow_1 : ND nil (impl (impl P P) (impl P P)) := lam hyp.
  
  Definition example4_eta_arrow_2 : ND nil (impl (impl P P) (impl P P)) := lam (lam (app (wkn hyp) hyp)).

  Definition example4_eta_product_1 : ND nil (impl (conj P Q) (conj P Q)) := lam hyp.

  Definition example4_eta_product_2 : ND nil (impl (conj P Q) (conj P Q)) := lam (pair (fst hyp) (snd hyp)).
    
  Definition example4_eta_sum_1 : ND nil (impl (impl (disj P Q) R) (impl (disj P Q) R)) := lam (lam (app (wkn hyp) hyp)).

  Definition example4_eta_sum_2 : ND nil (impl (impl (disj P Q) R) (impl (disj P Q) R)) :=
    lam
      (lam
         (cas hyp (app (wkn (wkn hyp)) (inl hyp)) (app (wkn (wkn hyp)) (inr hyp)))).

  Definition example4_eta_lambda_1 : ND nil (impl (impl P S) (impl (impl Q S) (impl (disj P Q) (impl R S)))) :=
    lam
      (lam
         (lam
            (lam
               (cas (wkn hyp) (app (wkn (wkn (wkn (wkn hyp)))) hyp)
                    (app (wkn (wkn (wkn hyp))) hyp))))).
  
  Definition example4_eta_lambda_2 : ND nil (impl (impl P S) (impl (impl Q S) (impl (disj P Q) (impl R S)))) :=
    lam
      (lam
         (lam
            (cas hyp (lam (app (wkn (wkn (wkn (wkn hyp)))) (wkn hyp)))
                 (lam (app (wkn (wkn (wkn hyp))) (wkn hyp)))))).

  Definition example4_eta_fst_1 : ND nil (impl (impl P (conj S R)) (impl (impl Q (conj S R)) (impl (disj P Q) S))) :=
    lam
      (lam
         (lam
            (fst
               (cas hyp (app (wkn (wkn (wkn hyp))) hyp) (app (wkn (wkn hyp)) hyp))))).
  
  Definition example4_eta_fst_2 : ND nil (impl (impl P (conj S R)) (impl (impl Q (conj S R)) (impl (disj P Q) S))) :=
    lam
      (lam
         (lam
            (cas hyp (fst (app (wkn (wkn (wkn hyp))) hyp))
                 (fst (app (wkn (wkn hyp)) hyp))))).
  
  Definition example4_eta_snd_1 : ND nil (impl (impl P (conj S R)) (impl (impl Q (conj S R)) (impl (disj P Q) R))) :=
    lam
      (lam
         (lam
            (snd
               (cas hyp (app (wkn (wkn (wkn hyp))) hyp) (app (wkn (wkn hyp)) hyp))))).
  
  Definition example4_eta_snd_2 : ND nil (impl (impl P (conj S R)) (impl (impl Q (conj S R)) (impl (disj P Q) R))) :=
    lam
      (lam
         (lam
            (cas hyp (snd (app (wkn (wkn (wkn hyp))) hyp))
                 (snd (app (wkn (wkn hyp)) hyp))))).

  Definition example5_1 : ND nil (impl (impl a b) (impl (impl c b) (impl d (impl (impl d (disj a  c)) b))))
    := lam (lam (lam (lam (cas (app _0 _1) (app _4 _0) (app _3 _0))))).

  Definition example5_2 : ND nil (impl (impl a b) (impl (impl c b) (impl d (impl (impl d (disj a  c)) b))))
    := lam (lam (lam (lam (cas (app _0 _1) (cas (app _1 _2) (app _5 _0) (app _4 _0)) (app _3 _0))))).

  Definition example6_1 : ND nil (impl f (impl g (impl (impl a (disj b  c)) (impl (impl a (disj d e)) (impl a (disj f g))))))
    := lam (lam (lam (lam (lam (cas (app _2 _0) (inl _5) (cas (app _3 _1) (inr _5) (inl _6))))))).

  Definition example6_2 : ND nil (impl f (impl g (impl (impl a (disj b  c)) (impl (impl a (disj d e)) (impl a (disj f g))))))
    := lam (lam (lam (lam (lam (cas (app _1 _0) (cas (app _2 _1) (inl _6) (inr _5) ) (inl _5)))))).

  (** Examples from the paper of Balat, Di Cosmo, and Fiore. The
  suffix "_n" denotes normal forms as given by them; "_n1" and "_n2"
  when they give two alternative normal forms. *)
  
  Definition B_ex_4_2_1 : ND nil (impl a a) := lam hyp.
  
  Definition B_ex_4_2_2 : ND nil (impl (disj a b) (disj a b)) := lam hyp.
  Definition B_ex_4_2_2_n : ND nil (impl (disj a b) (disj a b)) := lam (cas _0 (inl _0) (inr _0)).

  Definition B_ex_4_2_3 : ND nil (impl (conj (disj a b) (disj c d)) (conj (disj a b) (disj c d))) := lam hyp.
  Definition B_ex_4_2_3_n1 : ND nil (impl (conj (disj a b) (disj c d)) (conj (disj a b) (disj c d))) := lam (cas (fst _0) (cas (snd _1) (pair (inl _1) (inl _0)) (pair (inl _1) (inr _0))) (cas (snd _1) (pair (inr _1) (inl _0)) (pair (inr _1) (inr _0)))).
  Definition B_ex_4_2_3_n2 : ND nil (impl (conj (disj a b) (disj c d)) (conj (disj a b) (disj c d))) := lam (cas (snd _0) (cas (fst _1) (pair (inl _0) (inl _1)) (pair (inr _0) (inl _1))) (cas (fst _1) (pair (inl _0) (inr _1)) (pair (inr _0) (inr _1)))).

  Definition B_ex_4_2_4 : ND nil (impl (disj a b) (impl (disj c d) (conj (disj a b) (disj c d)))) := lam (lam (pair _1 _0)).
  Definition B_ex_4_2_4_n : ND nil (impl (disj a b) (impl (disj c d) (conj (disj a b) (disj c d)))) :=
    lam (cas _0 (lam (cas _0 (pair (inl _2) (inl _0)) (pair (inl _2) (inr _0)))) (lam (cas _0 (pair (inr _2) (inl _0)) (pair (inr _2) (inr _0))))).
  
  Definition B_ex_4_3_1 : ND nil (impl c (impl (disj a b) (disj (disj c c) (disj c c)))) :=
    lam (lam (cas (cas _0 (inl (inl _2)) (inr (inr _2))) (inr _0) (inl _0))).
  Definition B_ex_4_3_1_n : ND nil (impl c (impl (disj a b) (disj (disj c c) (disj c c)))) :=
    lam (lam (cas _0 (inr (inl _2)) (inl (inr _2)))).
  
  Definition B_ex_4_3_2 : ND nil (impl f (impl (impl a (disj b c)) (impl a (impl (impl a (disj d e)) (impl a (disj (disj f f) (disj f f))))))) :=
    lam (lam (lam (lam (lam (cas (app _1 _0) (cas (app _4 _3) (inl (inl _6)) (inl (inr _6))) (cas (app _2 _3) (inr (inl _6)) (inr (inr _6)))))))).

  Definition B_ex_4_3_2_n : ND nil (impl f (impl (impl a (disj b c)) (impl a (impl (impl a (disj d e)) (impl a (disj (disj f f) (disj f f))))))) :=
    lam (lam (lam (cas (app _1 _0) (lam (cas (app _0 _2) (lam (cas (app _2 _0) (inl (inl _7)) (inr (inl _7)))) (lam (cas (app _2 _0) (inl (inl _7)) (inr (inr _7)))))) (lam (cas (app _0 _2) (lam (cas (app _2 _0) (inl (inr _7)) (inr (inl _7)))) (lam (cas (app _2 _0) (inl (inr _7)) (inr (inr _7))))))))).

  Definition B_ex_4_3_3 :
    ND nil (impl h
              (impl
                 (impl
                    (impl (impl a (disj b c)) (impl (impl a (disj d e)) (impl a (disj h h))))
                    (disj f g))
                 (disj (disj h h) (disj h h)))) :=
    lam
      (lam
         (cas
            (app _0
                 (lam
                    (lam
                       (lam
                          (cas
                             (app _2 _0)
                             (inl _5)
                             (cas (app _2 _1) (inr _6) (inl _6)))))))
            (inl (inl _2))
            (cas
               (app _1
                    (lam
                       (lam
                          (lam
                             (cas
                                (app _1 _0)
                                (cas (app _3 _1) (inl _7) (inr _7))
                                (inl _6))))))
               (inl (inr _3))
               (inr (inl _3))))).
       
  Definition B_ex_4_3_3_n1 :
    ND nil (impl h
              (impl
                 (impl
                    (impl (impl a (disj b c)) (impl (impl a (disj d e)) (impl a (disj h h))))
                    (disj f g))
                 (disj (disj h h) (disj h h)))) :=
    lam
      (lam
         (cas
            (app _0
                 (lam
                    (lam
                       (lam
                          (cas
                             (app _2 _0)
                             (inl _5)
                             (cas (app _2 _1) (inr _6) (inl _6)))))))
            (inl (inl _2))
            (inr (inl _2)))).
       
  Definition B_ex_fff :
    ND nil
       (impl a (impl (impl (disj a a) (disj a a)) (impl (disj a a) (disj a a))))
    := lam (lam (lam (app _1 (app _1 (app _1 _0))))).
  
  Definition B_ex_fff_id :
    ND nil
       (impl a (impl (impl (disj a a) (disj a a)) (impl (disj a a) (disj a a))))
    := lam (lam _0).

  Definition B_ex_fff_n :
    ND nil
       (impl a (impl (impl (disj a a) (disj a a)) (impl (disj a a) (disj a a))))
    :=
      lam
        (lam
           (cas
              (app _0 (inl _1))
              (cas
                 (app _1 (inr _2))
                 (lam (inl _4))
                 (lam (cas _0 (inl _5) (inr _5))))
              (cas
                 (app _1 (inr _2))
                 (lam (cas _0 (inr _5) (inl _5)))
                 (lam (inr _4))))).

End Examples.

Export ND2HS.
Export HighSchool.

(** We can also define explicitly a decidability fixpoint
[compact_eqb] returning true or false, given two terms to compare *)

Definition compact_eqb : forall {F}, ND nil F -> ND nil F -> bool.
Proof.
  intros F p q.
  remember (enf F) as e.
  set (p' := nbe p).
  set (q' := nbe q).
  destruct e.
  - rewrite <- Heqe in *.
    apply (HSc_eqb _ p' q').
  - rewrite <- Heqe in *.
    apply (HSb_eqb _ _ p' q').
Defined.

(** Now we can normalize the examples to their compact forms. We use
the fixpoint [ppc] to produce a "pretty printed" version of the
output: when deBruijn indices are presentet explicitly, not through
implicit arguments. *)
Eval compute in (ppc (nbe example1_1)).
Eval compute in (ppc (nbe example1_2)).
Eval compute in (ppc (nbe example1_3)).
Eval compute in (ppc (nbe example1_4)).
Eval compute in (compact_eqb example1_1 example1_2).
Eval compute in (compact_eqb example1_2 example1_3).
Eval compute in (compact_eqb example1_3 example1_4).

Eval compute in (ppc (nbe example2_1)).
Eval compute in (ppc (nbe example2_2)).
Eval compute in (ppc (nbe example2_3)).
Eval compute in (ppc (nbe example2_4)).
Eval compute in (compact_eqb example2_1 example2_2).
Eval compute in (compact_eqb example2_2 example2_3).
Eval compute in (compact_eqb example2_3 example2_4).

Eval compute in (ppc (nbe example3_app_1)).
Eval compute in (ppc (nbe example3_app_2)).
Eval compute in (compact_eqb example3_app_1 example3_app_2).

Eval compute in (ppc (nbe example3_cas_1)).
Eval compute in (ppc (nbe example3_cas_2)).
Eval compute in (compact_eqb example3_cas_1 example3_cas_2).

Eval compute in (ppc (nbe example4_eta_arrow_1)).
Eval compute in (ppc (nbe example4_eta_arrow_2)).
Eval compute in (compact_eqb example4_eta_arrow_1 example4_eta_arrow_2).

Eval compute in (ppc (nbe example4_eta_product_1)).
Eval compute in (ppc (nbe example4_eta_product_2)).
Eval compute in (compact_eqb example4_eta_product_1 example4_eta_product_2).

Eval compute in (ppc (nbe example4_eta_sum_1)).
Eval compute in (ppc (nbe example4_eta_sum_2)).
Eval compute in (compact_eqb example4_eta_sum_1 example4_eta_sum_2).

Eval compute in (ppc (nbe example4_eta_lambda_1)).
Eval compute in (ppc (nbe example4_eta_lambda_2)).
Eval compute in (compact_eqb example4_eta_lambda_1 example4_eta_lambda_2).

Eval compute in (ppc (nbe example4_eta_fst_1)).
Eval compute in (ppc (nbe example4_eta_fst_2)).
Eval compute in (compact_eqb example4_eta_fst_1 example4_eta_fst_2).

Eval compute in (ppc (nbe example4_eta_snd_1)).
Eval compute in (ppc (nbe example4_eta_snd_2)).
Eval compute in (compact_eqb example4_eta_snd_1 example4_eta_snd_2).

Eval compute in (ppc (nbe example5_1)).
Eval compute in (ppc (nbe example5_2)).
Eval compute in (compact_eqb example5_1 example5_2).

Eval compute in (ppc (nbe example6_1)).
Eval compute in (ppc (nbe example6_2)).
Eval compute in (compact_eqb example6_1 example6_2).

Eval compute in (ppc (nbe B_ex_4_2_1)).

Eval compute in (ppc (nbe B_ex_4_2_2)).
Eval compute in (ppc (nbe B_ex_4_2_2_n)).
Eval compute in (compact_eqb B_ex_4_2_2 B_ex_4_2_2_n).

Eval compute in (ppc (nbe B_ex_4_2_3)).
Eval compute in (ppc (nbe B_ex_4_2_3_n1)).
Eval compute in (ppc (nbe B_ex_4_2_3_n2)).
Eval compute in (compact_eqb B_ex_4_2_3 B_ex_4_2_3_n1).
Eval compute in (compact_eqb B_ex_4_2_3 B_ex_4_2_3_n2).

Eval compute in (ppc (nbe B_ex_4_2_4)).
Eval compute in (ppc (nbe B_ex_4_2_4_n)).
Eval compute in (compact_eqb B_ex_4_2_4 B_ex_4_2_4_n).

Eval compute in (ppc (nbe B_ex_4_3_1)).
Eval compute in (ppc (nbe B_ex_4_3_1_n)).
Eval compute in (compact_eqb B_ex_4_3_1 B_ex_4_3_1_n).

Eval compute in (ppc (nbe B_ex_4_3_2)).
Eval compute in (ppc (nbe B_ex_4_3_2_n)).
Eval compute in (compact_eqb B_ex_4_3_2 B_ex_4_3_2_n).

Eval compute in (ppc (nbe B_ex_4_3_3)).
Eval compute in (ppc (nbe B_ex_4_3_3_n1)).
Eval compute in (compact_eqb B_ex_4_3_3 B_ex_4_3_3_n1).

Eval compute in (ppc (nbe B_ex_fff)).
Eval compute in (ppc (nbe B_ex_fff_n)).
Eval compute in (ppc (nbe B_ex_fff_id)).
Eval compute in (compact_eqb B_ex_fff B_ex_fff_n).
Eval compute in (compact_eqb B_ex_fff B_ex_fff_id).
Eval compute in (compact_eqb B_ex_fff_n B_ex_fff_id).

Export HS2ND.
Export NaturalDeduction.

(** Reverse-normalizing lambda terms to lambda terms *)
Definition ebn_nbe : forall {F}, ND nil F -> ND nil F.
Proof.
  intros.
  apply ebn.
  apply nbe.
  exact H.
Defined.

Eval compute in (ebn_nbe example1_1).
Eval compute in (ebn_nbe example1_2).
Eval compute in (ebn_nbe example1_3).
Eval compute in (ebn_nbe example1_4).

Eval compute in (ebn_nbe example2_1).
Eval compute in (ebn_nbe example2_2).
Eval compute in (ebn_nbe example2_3).
Eval compute in (ebn_nbe example2_4).

Eval compute in (ebn_nbe example3_app_1).
Eval compute in (ebn_nbe example3_app_2).

Eval compute in (ebn_nbe example3_cas_1).
Eval compute in (ebn_nbe example3_cas_2).

Eval compute in (ebn_nbe example4_eta_arrow_1).
Eval compute in (ebn_nbe example4_eta_arrow_2).
Eval compute in (example4_eta_arrow_2).

Eval compute in (ebn_nbe example4_eta_product_1).
Eval compute in (ebn_nbe example4_eta_product_2).
Eval compute in (example4_eta_product_2).

Eval compute in (ebn_nbe example4_eta_sum_1).
Eval compute in (ebn_nbe example4_eta_sum_2).
Eval compute in (example4_eta_sum_2).

Eval compute in (ebn_nbe example4_eta_lambda_1).
Eval compute in (ebn_nbe example4_eta_lambda_2).
Eval compute in (example4_eta_lambda_1).

Eval compute in (ebn_nbe example4_eta_fst_1).
Eval compute in (ebn_nbe example4_eta_fst_2).
Eval compute in (example4_eta_fst_2).

Eval compute in (ebn_nbe example4_eta_snd_1).
Eval compute in (ebn_nbe example4_eta_snd_2).
Eval compute in (example4_eta_snd_2).

Eval compute in (ebn_nbe example5_1).
Eval compute in example5_1.

Eval compute in (ebn_nbe example5_2).
Eval compute in example5_2.

Eval compute in (ebn_nbe example6_1).
Eval compute in example6_1.

Eval compute in (ebn_nbe example6_2).
Eval compute in example6_2.
