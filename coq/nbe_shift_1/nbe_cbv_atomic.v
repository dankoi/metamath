(** * Call-by-VALUE TDPE for shift and reset, restriction to an atomic
formula at reset-time *)

Require Import syntax.
Require Import model_structure.
Require Import model_validity_generic.
Require Import model_validity_cbv.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Evaluator of typed terms in Kripke models (aka Soundness) *)
Module Soundness (ks : Kripke_structure).
  Export ks.
  Module ks_monad := Kripke_structure_monad ks.
  Export ks_monad.
  Module cbv_validity := sforces_cbv ks.
  Export cbv_validity.
  Module generic_properties := forcing_generic_properties ks cbv_validity.
  Export generic_properties.

  Theorem soundness : 
    forall Gamma annot A, proof Gamma annot A -> 
      forall w, forall annot', leb annot annot' -> 
        w ||++ Gamma ; annot' -> w ||- A ; annot'.
  Proof.
    intros Gamma annot A p.
    induction p.

    intros w annot' Hleb wG.
    destruct annot'.
      intros w1 ww1 k.
      unfold Kont in IHp.
      apply (IHp w true).
      assumption.
      assumption.
      assumption.
      intros.
      apply k.
      assumption.
      simpl.
      left;assumption.
      intros C w1 ww1 k.
      unfold Kont in IHp.
      apply (IHp w false).
      assumption.
      assumption.
      assumption.
      intros.
      apply k.
      assumption.
      simpl.
      left;assumption.

    intros w annot' Hleb wG.
    destruct annot'.
      intros w1 ww1 k.
      unfold Kont in IHp.
      apply (IHp w true).
      assumption.
      assumption.
      assumption.
      intros.
      apply k.
      assumption.
      simpl.
      right;assumption.
      intros C w1 ww1 k.
      unfold Kont in IHp.
      apply (IHp w false).
      assumption.
      assumption.
      assumption.
      intros.
      apply k.
      assumption.
      simpl.
      right;assumption.

    intros w annot' Hleb wG.
    apply ret.
    simpl.
    intros w1 ww1 annot'' Hleb'' HA.
    simpl in IHp.
    apply IHp.
    eauto using leb_trans.
    split;
      eauto using sforces_cxt_mon,sforces_cxt_mon2.

    simpl.
    intros w annot' Hleb [Ha HGamma].
    apply ret.
    assumption.

    intros w annot' Hleb [wB wG].
    apply IHp.
    assumption.
    assumption.
    
    clear p1 p2 p3.
    intros w annot' Hleb' wGamma.
    destruct annot'.
      intros w1 ww1 k.
      unfold Kont in IHp1.
      apply (IHp1 w true); clear IHp1.
      assumption.
      assumption.
      assumption.
      intros w2 w1w2 HSum.
      simpl in HSum.
      case HSum.
      intro HA.
      unfold Kont in IHp2.
      apply (IHp2 w2 true).
      assumption.
      simpl.
      split.
      assumption.
      eauto using wle_trans,sforces_cxt_mon.
      apply wle_refl.
      intros; eauto using wle_trans.
      intro HB.
      unfold Kont in IHp3.
      apply (IHp3 w2 true).
      assumption.
      simpl.
      split.
      assumption.
      eauto using wle_trans,sforces_cxt_mon.
      apply wle_refl.
      intros; eauto using wle_trans.
      intros D w1 ww1 k.
      unfold Kont in IHp1.
      apply (IHp1 w false); clear IHp1.
      assumption.
      assumption.
      assumption.
      intros w2 w1w2 HSum.
      simpl in HSum.
      case HSum.
      intro HA.
      unfold Kont in IHp2.
      apply (IHp2 w2 false).
      assumption.
      simpl.
      split.
      assumption.
      eauto using wle_trans,sforces_cxt_mon.
      apply wle_refl.
      intros; eauto using wle_trans.
      intro HB.
      unfold Kont in IHp3.
      apply (IHp3 w2 false).
      assumption.
      simpl.
      split.
      assumption.
      eauto using wle_trans,sforces_cxt_mon.
      apply wle_refl.
      intros; eauto using wle_trans.

    intros w annot' Hleb' wGamma.
    destruct annot'.
      intros w1 ww1 k.
      unfold Kont in IHp1.
      apply (IHp1 w1 true).
      assumption.
      eauto using sforces_cxt_mon.
      apply wle_refl.
      simpl sforces.
      intros w2 w1w2 HAB.
      unfold Kont in IHp2.
      apply (IHp2 w true).
      assumption.
      assumption.
      eauto using wle_trans.
      intros w3 w2w3 HA.
      unfold Kont in HAB.
      apply (HAB w3 w2w3 true).
      reflexivity.
      assumption.
      apply wle_refl.
      intros w4 w3w4 HB'.
      apply k.
      eauto using wle_trans.
      assumption.
      intros C w1 ww1 k.
      unfold Kont in IHp1.
      apply (IHp1 w1 false).
      assumption.
      eauto using sforces_cxt_mon.
      apply wle_refl.
      simpl sforces.
      intros w2 w1w2 HAB.
      unfold Kont in IHp2.
      apply (IHp2 w false).
      assumption.
      assumption.
      eauto using wle_trans.
      intros w3 w2w3 HA.
      unfold Kont in HAB.
      apply (HAB w3 w2w3 false).
      constructor.
      assumption.
      apply wle_refl.
      intros w4 w3w4 HB'.
      apply k.
      eauto using wle_trans.
      assumption.

    intros w annot' Hleb' wGamma.
    apply ret.
    simpl.
    unfold Kont in IHp.
    destruct annot'.
      apply X_reset.
      apply (IHp w true).
      reflexivity.
      assumption.
      apply wle_refl.
      simpl.
      auto.
      apply X_reset.
      apply (IHp w true).
      reflexivity.
      apply sforces_cxt_mon2 with false.
      assumption.
      reflexivity.
      apply wle_refl.
      simpl;auto.

    intros w annot' Hleb' wGamma.
    inversion Hleb' as [Heq].
    rewrite Heq in *.
    intros w1 ww1 KK.
    (* apply run. *)
    apply (IHp w1 true).
    reflexivity.
    split.
    simpl.
    intros w2 w1w2 annot'' Heq'' HA.
    rewrite Heq'' in *.
    intros w3 w2w3 KK'.
    apply KK'.
    apply wle_refl.
    simpl.
    apply KK.
    eauto using wle_trans.
    eauto using sforces_mon.
    eauto using sforces_cxt_mon.
    apply wle_refl.
    simpl.
    auto.
  Defined.
End Soundness.

(** ** The reifyer from Kripke models to terms in normal form (aka Completeness for the Universal model) *)
Module Completeness.

  (** The "Universal" Kripke model [U] build from syntax *)
  Module U <: Kripke_structure.

    Definition K := context.

    Definition wle := prefix.

    Notation "w <= w'" := (wle w w').

    Definition wle_refl := prefix_refl.

    Definition wle_trans := prefix_trans.

    Definition X (w:context)(annot:bool)(A:formula) : Set :=  
      match A with
        | Bot => proof_ne w annot Bot
        | Atom a => proof_ne w annot (Atom a)
        | Sum A1 A2 => proof_nf w annot (Sum A1 A2)
        | Func A1 A2 => proof_nf w annot (Func A1 A2)
      end.
    
    Lemma X_mon : forall w annot A, X w annot A -> 
                  forall w', w <= w' -> X w' annot A.
    Proof.
      intros w annot A H w' ww'.
      destruct A; simpl in *;
      eauto using proof_nf_mon,proof_ne_mon.
    Defined.
    
    Lemma X_mon2 : forall w annot A, X w annot A -> 
                   forall annot', leb annot annot' -> X w annot' A.
    Proof.
      intros w annot A H annot' Hleb.
      destruct A; simpl in *;
      eauto using proof_nf_mon2,proof_ne_mon2.
    Defined.
    
    Lemma X_reset : forall w annot, X w true Bot -> X w annot Bot.
    Proof.
      simpl.
      intros w annot H.
    apply ne_Reset.
    apply H.
    Defined.
  End U.

  Export U.
  Module ks_monad := Kripke_structure_monad U.
  Export ks_monad.
  Module cbv_validity := sforces_cbv U.
  Export cbv_validity.
  Module generic_properties := forcing_generic_properties U cbv_validity.
  Export generic_properties.

  Theorem completeness : forall A w annot,
      (Kont sforces w annot A -> proof_nf w annot A) *
      (proof_ne w annot A -> Kont sforces w annot A).
  Proof.
    induction A.

    (* BASE TYPE *)
    intros.
    split.
    (* REIFY *)
    intro H.
    destruct annot.
    (* classical case *)
    apply nf_Shift.
    apply nf_ne.
    apply H.
    constructor.
    constructor.
    intros w2 Hincl2 Hatom.
    apply ne_App with (Atom a).
    apply proof_ne_mon with (Func (Atom a) Bot :: w).
    assumption.
    apply ne_Hyp.
    apply nf_ne.
    assumption.
    (* intuitionistic case *)
    apply nf_ne.
    unfold Kont in H.
    apply (H (Atom a)).
    apply wle_refl.
    auto.
    (* REFLECT *)
    intro e.
    apply ret.
    simpl.
    assumption.

    (* BOTTOM TYPE *)
    intros.
    split.
    (* REIFY *)
    intros c.
    destruct annot.
    (* classical case *)
    unfold Kont in c.
    simpl in c.
    apply nf_ne.
    apply c.
    apply wle_refl.
    auto.
    (* intuitionistic case *)
    unfold Kont in c.
    simpl in c.
    apply nf_ne.
    apply (c Bot).
    apply wle_refl.
    auto.
    (* REFLECT *)
    intros e.
    apply ret.
    simpl.
    assumption.

    (* ARROW TYPE *)
    intros.
    split.
    (* REIFY *)
    intro H.
    apply nf_Lam.
    apply IHA2.
    unfold Kont.
    destruct annot.
    (* classical case *)
    intros w1 incl1 k1.
    apply (IHA1 w1 true).
    apply proof_ne_mon with (A1::w).
    assumption.
    apply ne_Hyp.
    apply wle_refl.
    intros w2 incl2 H2.
    apply H.
    apply wle_trans with w1.
    apply wle_trans with (A1 :: w).
    constructor.
    constructor.
    assumption.
    assumption.
    intros w3 incl3 f3.
    simpl in f3.
    apply (f3 w3 (wle_refl w3) true).
    reflexivity.
    apply sforces_mon with w2; auto.
    apply wle_refl.
    intros w4 incl4 H4.
    apply k1.
    apply wle_trans with w3;
      eauto using wle_trans.
    assumption.
    (* intuitionistic case *)
    intros C w1 incl1 k1.
    apply (IHA1 w1 false).
    apply proof_ne_mon with (A1::w).
    assumption.
    apply ne_Hyp.
    constructor.
    intros w2 incl2 H2.
    apply H.
    apply wle_trans with w1.
    apply wle_trans with (A1 :: w).
    constructor.
    constructor.
    assumption.
    assumption.
    intros w3 incl3 f3.
    simpl in f3.
    apply (f3 w3 (wle_refl w3) false).
    constructor.
    apply sforces_mon with w2; auto.
    apply wle_refl.
    intros w4 incl4 H4.
    apply k1.
    apply wle_trans with w3;
      eauto using wle_trans.
    assumption.
    (* REFLECT *)
    intro e.
    apply ret.
    simpl.
    intros w' incl' annot' leb' H'.
    apply ret in H'.
    apply (IHA1 w' annot') in H'.
    apply (IHA2 w' annot').
    apply ne_App with A1.
    apply proof_ne_mon with (Gamma:=w).
    assumption.
    apply proof_ne_mon2 with annot.
    assumption.
    assumption.
    assumption.

    (* SUM TYPE *)
    intros.
    split.
    (* REIFY *)
    intro H.
    destruct annot.
    (* classical case *)
    apply nf_Shift.
    apply nf_ne.
    apply H.
    constructor.
    constructor.
    simpl.
    intros w1 incl1 H1.
    destruct H1 as [H11 | H12].
    apply ne_App with (Sum A1 A2).
    apply proof_ne_mon with (Func (Sum A1 A2) Bot :: w).
    assumption.
    apply ne_Hyp.
    apply nf_Inl.
    apply IHA1.
    apply ret.
    assumption.
    apply ne_App with (Sum A1 A2).
    apply proof_ne_mon with (Func (Sum A1 A2) Bot :: w).
    assumption.
    apply ne_Hyp.
    apply nf_Inr.
    apply IHA2.
    apply ret.
    assumption.
    (* intuitionistic case *)
    unfold Kont in H.
    apply (H (Sum A1 A2)).
    apply wle_refl.
    simpl.
    intros w1 incl1 H1.
    destruct H1 as [H11 | H12].
    apply nf_Inl.
    apply IHA1.
    apply ret.
    assumption.
    apply nf_Inr.
    apply IHA2.
    apply ret.
    assumption.
    (* REFLECT *)
    intro e.
    destruct annot.
    (* classical case *)
    intros w1 incl1 k1.
    apply ne_Case with A1 A2.
    eauto using proof_ne_mon.
    apply nf_ne.
    apply (IHA1 (A1::w1) true).
    apply ne_Hyp.
    apply wle_refl.
    intros w2 incl2 H2.
    apply k1.
    apply wle_trans with (A1::w1).
    constructor.
    constructor.
    assumption.
    simpl.
    left.
    assumption.
    apply nf_ne.
    apply (IHA2 (A2::w1) true).
    apply ne_Hyp.
    apply wle_refl.
    intros w2 incl2 H2.
    apply k1.
    apply wle_trans with (A2::w1).
    constructor.
    constructor.
    assumption.
    simpl.
    right.
    assumption.
    (* intuitionistic case *)
    intros C w1 incl1 k1.
    destruct C.
    apply ne_Case with A1 A2.
    eauto using proof_ne_mon.
    apply nf_ne.
    assert (Hhypo : proof_ne (A1 :: w1) false A1).
    apply ne_Hyp.
    eapply (snd (IHA1 (A1::w1) false) Hhypo (Atom a)).
    apply wle_refl.
    intros w2 incl2 H2.
    apply k1.
    apply wle_trans with (A1::w1).
    constructor; constructor.
    assumption.
    simpl.
    left.
    assumption.
    apply nf_ne.
    assert (Hhypo : proof_ne (A2 :: w1) false A2).
    apply ne_Hyp.
    eapply (snd (IHA2 (A2::w1) false) Hhypo (Atom a)).
    apply wle_refl.
    intros w2 incl2 H2.
    apply k1.
    apply wle_trans with (A2::w1).
    constructor; constructor.
    assumption.
    simpl.
    right.
    assumption.
    (* almost repeated 2 *)
    apply ne_Case with A1 A2.
    eauto using proof_ne_mon.
    apply nf_ne.
    assert (Hhypo : proof_ne (A1 :: w1) false A1).
    apply ne_Hyp.
    eapply (snd (IHA1 (A1::w1) false) Hhypo Bot).
    constructor; constructor.
    intros w2 incl2 H2.
    apply k1.
    apply wle_trans with (A1::w1).
    constructor; constructor.
    assumption.
    simpl.
    left.
    assumption.
    apply nf_ne.
    assert (Hhypo : proof_ne (A2 :: w1) false A2).
    apply ne_Hyp.
    eapply (snd (IHA2 (A2::w1) false) Hhypo Bot).
    apply wle_refl.
    intros w2 incl2 H2.
    apply k1.
    apply wle_trans with (A2::w1).
    constructor; constructor.
    assumption.
    simpl.
    right.
    assumption.
    (* almost repeated 3 *)
    apply nf_ne.
    apply ne_Case with A1 A2.
    eauto using proof_ne_mon.
    assert (Hhypo : proof_ne (A1 :: w1) false A1).
    apply ne_Hyp.
    eapply (snd (IHA1 (A1::w1) false) Hhypo (Func C1 C2)).
    apply wle_refl.
    intros w2 incl2 H2.
    apply k1.
    apply wle_trans with (A1::w1).
    constructor; constructor.
    assumption.
    simpl.
    left.
    assumption.
    assert (Hhypo : proof_ne (A2 :: w1) false A2).
    apply ne_Hyp.
    eapply (snd (IHA2 (A2::w1) false) Hhypo (Func C1 C2)).
    apply wle_refl.
    intros w2 incl2 H2.
    apply k1.
    apply wle_trans with (A2::w1).
    constructor; constructor.
    assumption.
    simpl.
    right.
    assumption.
    (* almost repeated 4 *)
    apply nf_ne.
    apply ne_Case with A1 A2.
    eauto using proof_ne_mon.
    assert (Hhypo : proof_ne (A1 :: w1) false A1).
    apply ne_Hyp.
    (* left; reflexivity. *)
    eapply (snd (IHA1 (A1::w1) false) Hhypo (Sum C1 C2)).
    apply wle_refl.
    intros w2 incl2 H2.
    apply k1.
    apply wle_trans with (A1::w1).
    constructor; constructor.
    assumption.
    simpl.
    left.
    assumption.
    assert (Hhypo : proof_ne (A2 :: w1) false A2).
    apply ne_Hyp.
    eapply (snd (IHA2 (A2::w1) false) Hhypo (Sum C1 C2)).
    apply wle_refl.
    intros w2 incl2 H2.
    apply k1.
    apply wle_trans with (A2::w1).
    constructor; constructor.
    assumption.
    simpl.
    right.
    assumption.
  Defined.

  (** ** Now we can define NbE as composition of soundness and completeness *)
  Module soundness_for_U := Soundness U.

  Definition NbE (annot:bool)(A:formula)(p:proof nil annot A) : proof_nf nil annot A.
  Proof.
    (* begin show *)
    set (compl := fst (completeness A nil annot)).
    set (empty_cxt := nil).
    assert (Hnil : sforces_cxt empty_cxt annot empty_cxt).
    simpl.
    constructor.
    set (sndns := soundness_for_U.soundness p (w:=nil) (leb_refl _) Hnil).
    exact (compl sndns).
  (* end show *)
  Defined.

End Completeness.

Extraction "nbe_cbv" Completeness.NbE.
