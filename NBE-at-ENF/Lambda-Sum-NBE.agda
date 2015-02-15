--
-- Lambda-Sum-NBE.agda
-- 
-- This file implements a normalizer (normalization-by-evaluation) for
-- the lambda calculus with sum types. It is used for the paper "The
-- Exp-Log Normal Form of Types and Canonical Terms for Lambda
-- Calculus with Sums"
-- 
-- Danko Ilik, 2014
--
-- Type-checked with Agda version 2.4.2, standard library version 0.8.1
--
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.List

module Lambda-Sum-NBE (Proposition : Set) where

  data Type : Set where
    `_  : Proposition → Type
    _⟶_ : Type → Type → Type
    _*_ : Type → Type → Type
    _+_ : Type → Type → Type

  infixr 100 _⟶_
  infixr 101 _+_
  infixr 102 _*_

  Context = List Type

  -- Source language
  data _⊢_ : Context → Type → Set where
    hyp : ∀ {Γ A} → (A ∷ Γ) ⊢ A
    wkn : ∀ {Γ A B} → Γ ⊢ A → (B ∷ Γ) ⊢ A
    lam : ∀ {Γ A B} → (A ∷ Γ) ⊢ B → Γ ⊢ (A ⟶ B)
    app : ∀ {Γ A B} → Γ ⊢ (A ⟶ B) → Γ ⊢ A → Γ ⊢ B
    pair : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A * B
    fst : ∀ {Γ A B} → Γ ⊢ A * B → Γ ⊢ A
    snd : ∀ {Γ A B} → Γ ⊢ A * B → Γ ⊢ B
    inl : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ A + B
    inr : ∀ {Γ A B} → Γ ⊢ B → Γ ⊢ A + B
    case : ∀ {Γ A B C} → Γ ⊢ A + B → (A ∷ Γ) ⊢ C → (B ∷ Γ) ⊢ C → Γ ⊢ C

  -- Target language
  mutual
    data _⊢ʳ_ : Context → Type → Set where
      lam : ∀ {Γ A B} → (A ∷ Γ) ⊢ʳ B → Γ ⊢ʳ (A ⟶ B)
      e2r : ∀ {Γ A} → Γ ⊢ᵉ A → Γ ⊢ʳ A
      pair : ∀ {Γ A B} → Γ ⊢ʳ A → Γ ⊢ʳ B → Γ ⊢ʳ A * B
      inl : ∀ {Γ A B} → Γ ⊢ʳ A → Γ ⊢ʳ A + B
      inr : ∀ {Γ A B} → Γ ⊢ʳ B → Γ ⊢ʳ A + B
      case : ∀ {Γ A B C} → Γ ⊢ᵉ A + B → (A ∷ Γ) ⊢ʳ C → (B ∷ Γ) ⊢ʳ C → Γ ⊢ʳ C
    data _⊢ᵉ_ : Context → Type → Set where
      hyp : ∀ {Γ A} → (A ∷ Γ) ⊢ᵉ A
      app : ∀ {Γ A B} → Γ ⊢ᵉ (A ⟶ B) → Γ ⊢ʳ A → Γ ⊢ᵉ B
      wkn : ∀ {Γ A B} → Γ ⊢ʳ A → (B ∷ Γ) ⊢ᵉ A
      fst : ∀ {Γ A B} → Γ ⊢ᵉ (A * B) → Γ ⊢ᵉ A
      snd : ∀ {Γ A B} → Γ ⊢ᵉ (A * B) → Γ ⊢ᵉ B

  data _≥_ : Context → Context → Set where 
    ≥-refl : ∀ {Γ} → Γ ≥ Γ
    ≥-cons : ∀ {Γ₁ Γ₂ A} → Γ₁ ≥ Γ₂ → (A ∷ Γ₁) ≥ Γ₂

  infixr 120 _∙_

  _∙_ : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ≥ Γ₂ → Γ₂ ≥ Γ₃ → Γ₁ ≥ Γ₃
  _∙_ ≥₂ ≥-refl = ≥₂
  _∙_ ≥-refl ≥₃ = ≥₃
  _∙_ (≥-cons ≥₂) ≥₃ = ≥-cons (_∙_ ≥₂ ≥₃)

  ⊢ᵉ-≥ : ∀ {A Γ₁ Γ₂} → Γ₂ ≥ Γ₁ → Γ₁ ⊢ᵉ A → Γ₂ ⊢ᵉ A
  ⊢ᵉ-≥ ≥-refl H₁ = H₁
  ⊢ᵉ-≥ (≥-cons ≥₂) H₁ = wkn (e2r (⊢ᵉ-≥ ≥₂ H₁))

  ⊢ʳ-≥ : ∀ {A Γ₁ Γ₂} → Γ₂ ≥ Γ₁ → Γ₁ ⊢ʳ A → Γ₂ ⊢ʳ A
  ⊢ʳ-≥ ≥-refl H₁ = H₁
  ⊢ʳ-≥ (≥-cons ≥₂) H₁ = e2r (wkn (⊢ʳ-≥ ≥₂ H₁))

  -- Forcing: a continuation monad over terms in normal form
  mutual
    _⊩_ : Context → Type → Set
    Γ ⊩ A = ∀ {C Γ₁} → Γ₁ ≥ Γ → (∀ {Γ₂} → Γ₂ ≥ Γ₁ → Γ₂ ⊩ˢ A → Γ₂ ⊢ʳ C) → Γ₁ ⊢ʳ C

    _⊩ˢ_ : Context → Type → Set
    Γ ⊩ˢ (` P) = Γ ⊢ʳ (` P)
    Γ ⊩ˢ (A ⟶ B) = {Γ' : Context} → Γ' ≥ Γ → Γ' ⊩ A → Γ' ⊩ B
    Γ ⊩ˢ (A * B) = Γ ⊩ A × Γ ⊩ B
    Γ ⊩ˢ (A + B) = Γ ⊩ A ⊎ Γ ⊩ B

  _⊪_ : Context → Context → Set
  Γ' ⊪ [] = ⊤
  Γ' ⊪ (A ∷ Γ) = (Γ' ⊩ A) × (Γ' ⊪ Γ)

  ⊩-≥ : ∀ {A Γ₁ Γ₂} → Γ₂ ≥ Γ₁ → Γ₁ ⊩ A → Γ₂ ⊩ A
  ⊩-≥ ≥-refl H₁ = H₁
  ⊩-≥ (≥-cons ≥₂) H₁ = λ ≥₃ → H₁ (≥₃ ∙ ≥-cons ≥₂)

  ⊩ˢ-≥ : ∀ {A Γ₁ Γ₂} → Γ₂ ≥ Γ₁ → Γ₁ ⊩ˢ A → Γ₂ ⊩ˢ A
  ⊩ˢ-≥ ≥-refl H₁ = H₁
  ⊩ˢ-≥ {A ⟶ B} ≥₂ H₁ = λ ≥₃ → H₁ (≥₃ ∙ ≥₂)
  ⊩ˢ-≥ {A * B} ≥₂ (H₁ , H₂) = (⊩-≥ {A} ≥₂ H₁) , (⊩-≥ {B} ≥₂ H₂)
  ⊩ˢ-≥ {A + B} ≥₂ (inj₁ H) = inj₁ (⊩-≥ {A} ≥₂ H)
  ⊩ˢ-≥ {A + B} ≥₂ (inj₂ H) = inj₂ (⊩-≥ {B} ≥₂ H)
  ⊩ˢ-≥ {` P} ≥₂ H₁ = ⊢ʳ-≥ ≥₂ H₁
    
  ⊪-≥ : ∀ {Γ Γ₁ Γ₂} → Γ₂ ≥ Γ₁ → Γ₁ ⊪ Γ → Γ₂ ⊪ Γ
  ⊪-≥ ≥-refl H₁ = H₁
  ⊪-≥ {[]} ≥₂ H₁ = H₁
  ⊪-≥ {A ∷ Γ} ≥₂ H₁ = (⊩-≥ {A} ≥₂ (proj₁ H₁)) , (⊪-≥ {Γ} ≥₂ (proj₂ H₁))

  return : ∀ {A Γ} → Γ ⊩ˢ A → Γ ⊩ A
  return = λ H ≥₁ k₁ → k₁ ≥-refl (⊩ˢ-≥ ≥₁ H)

  eval : ∀ {A Γ} → Γ ⊢ A → ∀ {Γ'} → Γ' ⊪ Γ → Γ' ⊩ A
  eval hyp ρ = proj₁ ρ
  eval {A ⟶ B} (lam p) ρ = return {A ⟶ B} (λ ≥₁ α₁ → eval p (α₁ , ⊪-≥ ≥₁ ρ))
  eval (app {Γ} {A} {B} p q) ρ = 
    λ ≥₁ κ₁ →
        eval p ρ ≥₁
        (λ ≥₂ φ₂ →
           φ₂ ≥-refl (eval q (⊪-≥ (≥₂ ∙ ≥₁) ρ)) ≥-refl
           (λ ≥₃ → κ₁ (≥₃ ∙ ≥₂)))
  eval (wkn p) ρ = eval p  (proj₂ ρ)
  eval {A * B} (pair p q) ρ = return {A * B} ((eval p ρ) , (eval q ρ)) 
  eval (fst {Γ} {A} {B} p) ρ = 
    λ ≥₁ κ₁ →
        eval p ρ ≥₁ (λ ≥₂ γ₂ → proj₁ γ₂ ≥-refl (λ ≥₃ → κ₁ (≥₃ ∙ ≥₂)))
  eval (snd {Γ} {A} {B} p) ρ = 
    λ ≥₁ κ₁ →
        eval p ρ ≥₁ (λ ≥₂ γ₂ → proj₂ γ₂ ≥-refl (λ ≥₃ → κ₁ (≥₃ ∙ ≥₂)))
  eval (inl {Γ} {A} {B} p) ρ = return {A + B} (inj₁ (eval p ρ))
  eval (inr {Γ} {A} {B} p) ρ = return {A + B} (inj₂ (eval p ρ))
  eval (case {Γ} {A} {B} {C} p q r) ρ = 
    λ ≥₁ κ₁ →
        eval p ρ ≥₁
        (λ ≥₂ γ₂ →
           [
           (λ α →
              eval q ((λ x y → α x y) , ⊪-≥ {Γ} (≥₂ ∙ ≥₁) ρ) ≥-refl
              (λ ≥₃ → κ₁ (≥₃ ∙ ≥₂)))
           ,
           (λ β →
              eval r ((λ x y → β x y) , ⊪-≥ {Γ} (≥₂ ∙ ≥₁) ρ) ≥-refl
              (λ ≥₃ → κ₁ (≥₃ ∙ ≥₂)))
           ]′
           γ₂)

  run : ∀ {P Γ} → Γ ⊩ ` P → Γ ⊩ˢ ` P
  run H = H ≥-refl (λ _ π → π)

  mutual
    reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ʳ A
    reify {` P} H = run H
    reify {A ⟶ B} H =
      lam
        (reify {B}
         (λ ≥₁ κ₁ →
            H (≥₁ ∙ ≥-cons ≥-refl)
            (λ ≥₂ φ₂ →
               φ₂ ≥-refl (⊩-≥ (≥₂ ∙ ≥₁) (reflect {A} hyp)) ≥-refl
               (λ ≥₃ → κ₁ (≥₃ ∙ ≥₂)))))
    reify {A * B} H = 
      pair
        (reify {A}
           (λ ≥₁ κ₁ → H ≥₁ (λ ≥₂ γ₂ → proj₁ γ₂ ≥-refl (λ ≥₃ → κ₁ (≥₃ ∙ ≥₂)))))
        (reify {B}
           (λ ≥₁ κ₁ → H ≥₁ (λ ≥₂ γ₂ → proj₂ γ₂ ≥-refl (λ ≥₃ → κ₁ (≥₃ ∙ ≥₂)))))
    reify {A + B} H = H ≥-refl (λ ≥₁ γ₁ → [ (λ α → inl (reify {A} α)) , (λ β → inr (reify {B} β)) ]′ γ₁)

    reflect : ∀ {A Γ} → Γ ⊢ᵉ A → Γ ⊩ A
    reflect {` P} p = return (e2r p)
    reflect {A ⟶ B} p = return {A ⟶ B}
                          (λ ≥₂ α₂ → reflect {B} (app (⊢ᵉ-≥ ≥₂ p) (reify {A} α₂)))
    reflect {A * B} p = return {A * B} (reflect {A} (fst p) , reflect {B} (snd p))
    reflect {A + B} p = λ ≥₁ κ → case (⊢ᵉ-≥ ≥₁ p) (κ (≥-cons ≥-refl) (inj₁ (reflect {A} hyp))) (κ (≥-cons ≥-refl) (inj₂ (reflect {B} hyp))) 

  reflect-context : ∀ {Γ} → Γ ⊪ Γ
  reflect-context {[]} = tt
  reflect-context {A ∷ Γ} = (reflect {A} hyp) , ⊪-≥ (≥-cons ≥-refl) (reflect-context {Γ})

  nbe : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ʳ A
  nbe p = reify (eval p (reflect-context))
