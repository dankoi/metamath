--
-- Normalization by Evaluation for System T+ (http://arxiv.org/abs/1301.5089)
-- 
-- Danko Ilik, 2014
--
-- Type-checked with Agda version 2.4.2, standard library version 0.8.1
--
open import Data.Unit
open import Data.Product
open import Data.List

module System-T-Shift-NBE-CBN where

  data Type : Set where
    ℕ  : Type
    _⟶_ : Type → Type → Type
    _*_ : Type → Type → Type

  infixr 100 _⟶_
  infixr 102 _*_

  infixr 120 _∙_

  Context = List Type

  -- Source language: terms of System T extended with a control
  -- operator (shift) for composable continuations
  data _⊢_ : Context → Type → Set where
    hyp : ∀ {Γ A} → (A ∷ Γ) ⊢ A
    wkn : ∀ {Γ A B} → Γ ⊢ A → (B ∷ Γ) ⊢ A
    lam : ∀ {Γ A B} → (A ∷ Γ) ⊢ B → Γ ⊢ (A ⟶ B)
    app : ∀ {Γ A B} → Γ ⊢ (A ⟶ B) → Γ ⊢ A → Γ ⊢ B
    pair : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A * B)
    fst : ∀ {Γ A B} → Γ ⊢ (A * B) → Γ ⊢ A
    snd : ∀ {Γ A B} → Γ ⊢ (A * B) → Γ ⊢ B
    zero : ∀ {Γ} → Γ ⊢ ℕ
    succ : ∀ {Γ} → Γ ⊢ ℕ → Γ ⊢ ℕ
    rec : ∀ {Γ C} → Γ ⊢ ℕ → Γ ⊢ C → Γ ⊢ (ℕ ⟶ (C ⟶ C)) → Γ ⊢ C
    shift : ∀ {Γ A} → (ℕ ⟶ A ⟶ ℕ ∷ Γ) ⊢ ℕ → Γ ⊢ A

  -- Target language: terms of System T in beta-normal form
  mutual
    data _⊢ʳ_ : Context → Type → Set where
      lam : ∀ {Γ A B} → (A ∷ Γ) ⊢ʳ B → Γ ⊢ʳ (A ⟶ B)
      e2r : ∀ {Γ A} → Γ ⊢ᵉ A → Γ ⊢ʳ A
      pair : ∀ {Γ A B} → Γ ⊢ʳ A → Γ ⊢ʳ B → Γ ⊢ʳ (A * B)
      zero : ∀ {Γ} → Γ ⊢ʳ ℕ
      succ : ∀ {Γ} → Γ ⊢ʳ ℕ → Γ ⊢ʳ ℕ
    data _⊢ᵉ_ : Context → Type → Set where
      hyp : ∀ {Γ A} → (A ∷ Γ) ⊢ᵉ A
      app : ∀ {Γ A B} → Γ ⊢ᵉ (A ⟶ B) → Γ ⊢ʳ A → Γ ⊢ᵉ B
      wkn : ∀ {Γ A B} → Γ ⊢ʳ A → (B ∷ Γ) ⊢ᵉ A
      fst : ∀ {Γ A B} → Γ ⊢ᵉ (A * B) → Γ ⊢ᵉ A
      snd : ∀ {Γ A B} → Γ ⊢ᵉ (A * B) → Γ ⊢ᵉ B
      rec : ∀ {Γ C} → Γ ⊢ᵉ ℕ → Γ ⊢ʳ C → Γ ⊢ʳ (ℕ ⟶ (C ⟶ C)) → Γ ⊢ᵉ C

  data _≥_ : Context → Context → Set where 
    ≥-refl : ∀ {Γ} → Γ ≥ Γ
    ≥-cons : ∀ {Γ₁ Γ₂ A} → Γ₁ ≥ Γ₂ → (A ∷ Γ₁) ≥ Γ₂

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
    Γ ⊩ A = ∀ {Γ₁} → Γ₁ ≥ Γ → (∀ {Γ₂} → Γ₂ ≥ Γ₁ → Γ₂ ⊩ˢ A → Γ₂ ⊢ʳ ℕ) → Γ₁ ⊢ʳ ℕ

    _⊩ˢ_ : Context → Type → Set
    Γ ⊩ˢ (ℕ) = Γ ⊢ʳ ℕ
    Γ ⊩ˢ (A ⟶ B) = {Γ' : Context} → Γ' ≥ Γ → Γ' ⊩ A → Γ' ⊩ B
    Γ ⊩ˢ (A * B) = Γ ⊩ A × Γ ⊩ B

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
  ⊩ˢ-≥ {ℕ} ≥₂ H₁ = ⊢ʳ-≥ ≥₂ H₁
    
  ⊪-≥ : ∀ {Γ Γ₁ Γ₂} → Γ₂ ≥ Γ₁ → Γ₁ ⊪ Γ → Γ₂ ⊪ Γ
  ⊪-≥ ≥-refl H₁ = H₁
  ⊪-≥ {[]} ≥₂ H₁ = H₁
  ⊪-≥ {A ∷ Γ} ≥₂ H₁ = (⊩-≥ {A} ≥₂ (proj₁ H₁)) , (⊪-≥ {Γ} ≥₂ (proj₂ H₁))

  return : ∀ {A Γ} → Γ ⊩ˢ A → Γ ⊩ A
  return = λ H ≥₁ k₁ → k₁ ≥-refl (⊩ˢ-≥ ≥₁ H)

  run : ∀ {Γ} → Γ ⊩ ℕ → Γ ⊩ˢ ℕ
  run H = H ≥-refl (λ _ π → π)

  mutual
    reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ʳ A
    reify {ℕ} H = run H
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

    reflect : ∀ {A Γ} → Γ ⊢ᵉ A → Γ ⊩ A
    reflect {ℕ} p = return (e2r p)
    reflect {A ⟶ B} p = return {A ⟶ B}
                          (λ ≥₂ α₂ → reflect {B} (app (⊢ᵉ-≥ ≥₂ p) (reify {A} α₂)))
    reflect {A * B} p = return {A * B} (reflect {A} (fst p) , reflect {B} (snd p))

  mutual
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
    eval zero ρ = return zero
    eval (succ n) ρ = return (succ (run (eval n ρ)))
    eval {A} (shift p) ρ =
      λ ≥₁ κ₁ →
          run
          (eval p
           (return {ℕ ⟶ A ⟶ ℕ}
            (λ ≥₂ _ →
               return {A ⟶ ℕ}
               (λ ≥₃ α₃ → return (α₃ ≥-refl (λ ≥₄ → κ₁ (≥₄ ∙ ≥₃ ∙ ≥₂)))))
            , ⊪-≥ ≥₁ ρ))
    eval (rec n a f) ρ ≥₁ κ₁ = 
      eval n ρ ≥₁
        (λ ≥₂ ν₂ →
           eval-rec ν₂ a f (⊪-≥ (≥₂ ∙ ≥₁) ρ) ≥-refl
           (λ ≥₃ α₃ → κ₁ (≥₃ ∙ ≥₂) α₃))

    eval-rec : ∀ {A Γ Γ'} → Γ' ⊢ʳ ℕ → Γ ⊢ A → Γ ⊢ (ℕ ⟶ (A ⟶ A)) → Γ' ⊪ Γ → Γ' ⊩ A
    eval-rec (e2r e) a f ρ = reflect (rec e (reify (eval a ρ)) (reify (eval f ρ)))
    eval-rec zero a f ρ = eval a ρ
    eval-rec (succ r) a f ρ ≥₁ κ₁ = 
      eval f (⊪-≥ ≥₁ ρ) ≥-refl
        (λ ≥₂ γ₂ →
           γ₂ ≥-refl (return (⊢ʳ-≥ (≥₂ ∙ ≥₁) r)) ≥-refl
           (λ ≥₃ δ₃ →
              eval-rec r a f ρ (≥₃ ∙ ≥₂ ∙ ≥₁)
              (λ ≥₄ α₄ →
                 δ₃ ≥₄ (return α₄) ≥-refl (λ ≥₅ → κ₁ (≥₅ ∙ ≥₄ ∙ ≥₃ ∙ ≥₂)))))

  reflect-context : ∀ {Γ} → Γ ⊪ Γ
  reflect-context {[]} = tt
  reflect-context {A ∷ Γ} = (reflect {A} hyp) , ⊪-≥ (≥-cons ≥-refl) (reflect-context {Γ})

  nbe : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ʳ A
  nbe p = reify (eval p (reflect-context))

  nbe' : ∀ {A Γ} → Γ ⊢ A → Γ ⊪ Γ → Γ ⊢ʳ A
  nbe' p ρ = reify (eval p ρ)

  mutual
    flatten : ∀ {A Γ} → Γ ⊢ʳ A → Γ ⊢ A
    flatten (lam r) = lam (flatten r)
    flatten (e2r e) = flattenᵉ e
    flatten (pair r₁ r₂) = pair (flatten r₁) (flatten r₂)
    flatten zero = zero
    flatten (succ r) = succ (flatten r)

    flattenᵉ : ∀ {A Γ} → Γ ⊢ᵉ A → Γ ⊢ A
    flattenᵉ hyp = hyp
    flattenᵉ (app e r) = app (flattenᵉ e) (flatten r)
    flattenᵉ (wkn r) = wkn (flatten r)
    flattenᵉ (fst e) = fst (flattenᵉ e)
    flattenᵉ (snd e) = snd (flattenᵉ e)
    flattenᵉ (rec e r₁ r₂) = rec (flattenᵉ e) (flatten r₁) (flatten r₂)

