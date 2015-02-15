--
-- Normalization by Evaluation for System T+ (http://arxiv.org/abs/1301.5089)
-- 
-- Formal proofs of the equations relevant to the Soundness Theorem
-- 
-- Danko Ilik, 2014
--
-- Type-checked with Agda version 2.4.2, standard library version 0.8.1
--
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import System-T-Shift-NBE-CBN

module Soundness-Equations where

  wkn-p : ∀ {Γ A B} → (p : Γ ⊢ B) → (α : (A ∷ Γ) ⊩ A) →
          (ρ : (A ∷ Γ) ⊪ Γ) → ∀ {≥₁} → 
          {κ : (∀ {Γ₂} → Γ₂ ≥ (A ∷ Γ) → Γ₂ ⊩ˢ B → Γ₂ ⊢ʳ ℕ )} → 
          eval (wkn p) (α , ρ) ≥₁ κ 
          ≡ 
          eval p ρ ≥₁ κ
  wkn-p p α ρ = refl

  hyp-eq : ∀ {Γ A} → (α : (A ∷ Γ) ⊩ A) →
         (ρ : (A ∷ Γ) ⊪ Γ) → ∀ {≥₁} → 
         {κ : (∀ {Γ₂} → Γ₂ ≥ (A ∷ Γ) → Γ₂ ⊩ˢ A → Γ₂ ⊢ʳ ℕ )} → 
         eval hyp (α , ρ) ≥₁ κ 
         ≡ 
         α ≥₁ κ
  hyp-eq α ρ = refl

  fst-pair : ∀ {Γ A B} →
             (p : Γ ⊢ A) → (q : Γ ⊢ B) → (ρ : Γ ⊪ Γ) → ∀{≥₁} →
             {κ : (∀ {Γ₂} → Γ₂ ≥ Γ → Γ₂ ⊩ˢ A → Γ₂ ⊢ʳ ℕ)} → 
             eval (fst (pair p q)) ρ ≥₁ κ 
             ≡ 
             eval p ρ ≥₁ κ
  fst-pair p q ρ {≥-refl} = refl
  fst-pair p q ρ {≥-cons ≥₁} = refl

  snd-pair : ∀ {Γ A B} →
             (p : Γ ⊢ A) → (q : Γ ⊢ B) → (ρ : Γ ⊪ Γ) → ∀{≥₁} →
             {κ : (∀ {Γ₂} → Γ₂ ≥ Γ → Γ₂ ⊩ˢ B → Γ₂ ⊢ʳ ℕ)} → 
             eval (snd (pair p q)) ρ ≥₁ κ 
             ≡ 
             eval q ρ ≥₁ κ
  snd-pair p q ρ {≥-refl} = refl
  snd-pair p q ρ {≥-cons ≥₁} = refl

  fst-ℕ : ∀ {Γ B} →
             (q : Γ ⊢ (ℕ * B)) → (ρ : Γ ⊪ Γ) →
             reify {ℕ * B} (eval q ρ)
             ≡ 
             pair ((eval q ρ) ≥-refl (λ ≥₂ γ → run (proj₁ γ))) (reify {B} (eval (snd q) ρ))
  fst-ℕ q ρ = refl

  snd-ℕ : ∀ {Γ A} →
             (q : Γ ⊢ (A * ℕ)) → (ρ : Γ ⊪ Γ) →
             reify {A * ℕ} (eval q ρ)
             ≡ 
             pair (reify {A} (eval (fst q) ρ)) ((eval q ρ) ≥-refl (λ ≥₂ γ → run (proj₂ γ)))
  snd-ℕ q ρ = refl

  app-lam : ∀ {Γ A B} → 
            (p : (A ∷ Γ) ⊢ B) → (q : Γ ⊢ A) →
            (ρ : (A ∷ Γ) ⊪ Γ) → 
            {κ : (∀ {Γ₂} → Γ₂ ≥ (A ∷ Γ) → Γ₂ ⊩ˢ B → Γ₂ ⊢ʳ ℕ)} → 
            eval (app (lam p) q) ρ ≥-refl ≡ 
            eval p (eval q ρ , ρ) ≥-refl
  app-lam p q ρ = refl

  rec-zero : ∀ {Γ C} → (p : Γ ⊢ C) → (q : Γ ⊢ (ℕ ⟶ (C ⟶ C))) →
             (ρ : Γ ⊪ Γ) → 
             {κ : (∀ {Γ₂} → Γ₂ ≥ Γ → Γ₂ ⊩ˢ C → Γ₂ ⊢ʳ ℕ)} →
             eval (rec zero p q) ρ ≥-refl κ ≡
             eval p ρ ≥-refl κ
  rec-zero p q ρ = refl

  rec-succ : ∀ {Γ C} → (s : Γ ⊢ ℕ) → (p : Γ ⊢ C) → (q : Γ ⊢ (ℕ ⟶ (C ⟶ C))) →
             (ρ : Γ ⊪ Γ) →
             {κ : (∀ {Γ₂} → Γ₂ ≥ Γ → Γ₂ ⊩ˢ C → Γ₂ ⊢ʳ ℕ)} →
             eval (rec (succ s) p q) ρ ≥-refl κ ≡
             eval (app (app q s) (rec s p q)) ρ ≥-refl κ
  rec-succ s p q ρ = refl

  shift-p : ∀ {Γ A} → (p : (ℕ ⟶ A ⟶ ℕ ∷ Γ) ⊢ ℕ) → 
            ∀ {ρ} → ∀ {≥₁} → 
            {κ : (∀ {Γ₂} → Γ₂ ≥ Γ → Γ₂ ⊩ˢ A → Γ₂ ⊢ʳ ℕ)} → 
            eval (shift p) {Γ' = Γ} ρ ≥₁ κ 
            ≡
            reify {ℕ}
              (eval p
                (return {ℕ ⟶ A ⟶ ℕ}
                  (λ ≥₂ _ →
                    return {A ⟶ ℕ}
                    (λ ≥₃ α₃ → return (α₃ ≥-refl (λ ≥₄ → κ (≥₄ ∙ ≥₃ ∙ ≥₂)))))
                  , ⊪-≥ ≥₁ ρ))
  shift-p p = refl

  shift-p-ℕ : ∀ {Γ} → (p : (ℕ ⟶ ℕ ⟶ ℕ ∷ Γ) ⊢ ℕ) → ∀ {ρ} → 
              reify {ℕ} (eval (shift p) {Γ' = Γ} ρ)
              ≡
              reify {ℕ} (eval p (return {ℕ ⟶ ℕ ⟶ ℕ}
                                  (λ ≥₂ _ →
                                    return {ℕ ⟶ ℕ}
                                    (λ ≥₃ α₃ → return (run α₃)))
                                  , ρ))
  shift-p-ℕ p = refl

  φ : ∀{Γ} → (ℕ ⟶ ℕ ⟶ ℕ ∷ Γ) ⊩ (ℕ ⟶ ℕ ⟶ ℕ)
  φ = return {ℕ ⟶ ℕ ⟶ ℕ}
                  (λ ≥₂ _ →
                    return {ℕ ⟶ ℕ}
                    (λ ≥₃ α₃ → return (run α₃)))

  cont-eq : ∀ {Γ} → (x : (ℕ ⟶ ℕ ⟶ ℕ ∷ Γ) ⊢ ℕ) → 
            (y : (ℕ ⟶ ℕ ⟶ ℕ ∷ Γ) ⊢ ℕ) →
            ∀ {ρ : (ℕ ⟶ ℕ ⟶ ℕ ∷ Γ) ⊪ Γ} → 
            reify {ℕ} (eval (app (app hyp x) y) (φ , ρ))
            ≡
            reify {ℕ} (eval y (φ , ρ))
  cont-eq x y {ρ} = refl

  shift-p-* : ∀ {Γ A B} → (p : (ℕ ⟶ (A * B) ⟶ ℕ ∷ Γ) ⊢ ℕ) → ∀ {ρ} →
            reify {A * B} (eval (shift p) {Γ' = Γ} ρ)
            ≡
            pair
            (reify {A} (eval (fst (shift p)) ρ))
            (reify {B} (eval (snd (shift p)) ρ))
  shift-p-* p = refl

  φ₁ : ∀{Γ} → (ℕ ⟶ ℕ * ℕ ⟶ ℕ ∷ Γ) ⊩ (ℕ ⟶ ℕ * ℕ ⟶ ℕ)
  φ₁ = return {ℕ ⟶ ℕ * ℕ ⟶ ℕ}
                  (λ ≥₁ _ →
                    return {ℕ * ℕ ⟶ ℕ}
                    (λ ≥₃ α₃ → return (α₃ ≥-refl (λ ≥₄ γ → run (proj₁ γ)))))

  cont-eq₁ : ∀ {Γ} → (x : (ℕ ⟶ ℕ * ℕ ⟶ ℕ ∷ Γ) ⊢ ℕ) → 
            (y : (ℕ ⟶ ℕ * ℕ ⟶ ℕ ∷ Γ) ⊢ ℕ * ℕ) →
            ∀ {ρ : (ℕ ⟶ ℕ * ℕ ⟶ ℕ ∷ Γ) ⊪ Γ} → 
            reify {ℕ} (eval (app (app hyp x) y) (φ₁ , ρ))
            ≡
            reify {ℕ} (eval (fst y) (φ₁ , ρ))
  cont-eq₁ x y {ρ} = refl

  φ₂ : ∀{Γ} → (ℕ ⟶ ℕ * ℕ ⟶ ℕ ∷ Γ) ⊩ (ℕ ⟶ ℕ * ℕ ⟶ ℕ)
  φ₂ = return {ℕ ⟶ ℕ * ℕ ⟶ ℕ}
                  (λ ≥₂ _ →
                    return {ℕ * ℕ ⟶ ℕ}
                    (λ ≥₂ α₂ → return (α₂ ≥-refl (λ ≥₄ γ → run (proj₂ γ)))))

  cont-eq₂ : ∀ {Γ} → (x : (ℕ ⟶ ℕ * ℕ ⟶ ℕ ∷ Γ) ⊢ ℕ) → 
            (y : (ℕ ⟶ ℕ * ℕ ⟶ ℕ ∷ Γ) ⊢ ℕ * ℕ) →
            ∀ {ρ : (ℕ ⟶ ℕ * ℕ ⟶ ℕ ∷ Γ) ⊪ Γ} → 
            reify {ℕ} (eval (app (app hyp x) y) (φ₂ , ρ))
            ≡
            reify {ℕ} (eval (snd y) (φ₂ , ρ))
  cont-eq₂ x y {ρ} = refl

  shift-p-⟶-ℕ : ∀ {Γ} → (p : (ℕ ⟶ (ℕ ⟶ ℕ) ⟶ ℕ ∷ Γ) ⊢ ℕ) → 
            {ρ : Γ ⊪ Γ} →
            reify {ℕ ⟶ ℕ} (eval (shift p) {Γ' = Γ} ρ)
            ≡
            lam (reify {ℕ} {ℕ ∷ Γ} (eval p
                                      (return {ℕ ⟶ (ℕ ⟶ ℕ) ⟶ ℕ}
                                       (λ ≥₂ ν₂ →
                                          return {(ℕ ⟶ ℕ) ⟶ ℕ}
                                          (λ ≥₃ α₃ →
                                             return
                                             (α₃ ≥-refl
                                              (λ ≥₄ φ → run (φ ≥-refl (⊩-≥ (≥₄ ∙ ≥₃ ∙ ≥₂) (reflect hyp)))))))
                                       , ⊪-≥ (≥-cons ≥-refl) ρ)))
  shift-p-⟶-ℕ p = refl

  shift-p-⟶-ℕ-z : ∀ {Γ} → (p : (ℕ ⟶ (ℕ ⟶ ℕ) ⟶ ℕ ∷ Γ) ⊢ ℕ) → 
                (z : Γ ⊢ ℕ) →
            {ρ : Γ ⊪ Γ} →
            reify {ℕ} (eval (app (shift p) z) {Γ' = Γ} ρ)
            ≡
            reify
              (eval p
               (return {ℕ ⟶ (ℕ ⟶ ℕ) ⟶ ℕ}
                (λ ≥₂ ν₂ →
                   return {(ℕ ⟶ ℕ) ⟶ ℕ}
                   (λ ≥₃ α₃ →
                      return
                      (α₃ ≥-refl
                       (λ ≥₄ φ → run (φ ≥-refl (eval z (⊪-≥ (≥₄ ∙ ≥₃ ∙ ≥₂) ρ)))))))
                , ρ))
  shift-p-⟶-ℕ-z p z {ρ} = refl

  eval-equations-suffice : ∀{Γ A} → (p : Γ ⊢ A) → (q : Γ ⊢ A) → 
                           (ρ : Γ ⊪ Γ) →
                           (λ {Γ₁} → eval p ρ {Γ₁}) ≡ (λ {Γ₁} → eval q ρ {Γ₁}) →
                           reify (eval p ρ) ≡ reify (eval q ρ)
  eval-equations-suffice {Γ} {A} p q ρ H = cong {A = Γ ⊩ A}  {B = Γ ⊢ʳ A} reify {x = eval p ρ} {y = eval q ρ} H

