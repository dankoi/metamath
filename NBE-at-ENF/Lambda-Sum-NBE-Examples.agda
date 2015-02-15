--
-- Lambda-Sum-NBE-Examples.agda
-- 
-- Danko Ilik, 2014
--
-- This file gives the examples of normalization considered in the
-- paper "The Exp-Log Normal Form of Types and Canonical Terms for
-- Lambda Calculus with Sums" implements uses the normalizer the
-- lambda calculus with sum types.
--
-- Example-M-N is normalized under the goal of the term
-- test-example-M-N, while the normalization at ENF type is done in
-- test-example-M-N-enf.
--
-- For the "-enf" tests, explicit type isomorphisms that coerce ⊩f
-- into ⊩enf(f) are contructed beforehand.
-- 
-- Type-checked with Agda version 2.4.2, standard library version 0.8.1
--
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.List

module Lambda-Sum-NBE-Examples (Proposition : Set) where
  import Lambda-Sum-NBE
  module my-Lambda-Sum-NBE = Lambda-Sum-NBE Proposition
  open my-Lambda-Sum-NBE

  postulate
    A B C D E F G : Proposition

  a = ` A
  b = ` B
  c = ` C
  d = ` D
  e = ` E
  f = ` F
  g = ` G

  --
  -- Shortcuts for de Bruijn indices
  --
  ~0 : ∀ {Γ A} → (A ∷ Γ) ⊢ A
  ~0 = hyp

  ~1 : ∀ {Γ A B} → (B ∷ A ∷ Γ) ⊢ A
  ~1 = wkn ~0

  ~2 : ∀ {Γ A A' B} → (B ∷ A' ∷ A ∷ Γ) ⊢ A
  ~2 = wkn ~1

  ~3 : ∀ {Γ A A' A'' B} → (B ∷ A' ∷ A'' ∷ A ∷ Γ) ⊢ A
  ~3 = wkn ~2

  ~4 : ∀ {Γ A A' A'' A''' B} → (B ∷ A' ∷ A'' ∷ A''' ∷ A ∷ Γ) ⊢ A
  ~4 = wkn ~3

  ~5 : ∀ {Γ A A' A'' A''' A'''' B} → (B ∷ A' ∷ A'' ∷ A''' ∷ A'''' ∷ A ∷ Γ) ⊢ A
  ~5 = wkn ~4

  ~6 : ∀ {Γ A A' A'' A''' A'''' A''''' B} → (B ∷ A' ∷ A'' ∷ A''' ∷ A'''' ∷ A''''' ∷ A ∷ Γ) ⊢ A
  ~6 = wkn ~5

  example-1-1 : [] ⊢ (a + b ⟶ (a + b ⟶ c) ⟶ c)
  example-1-1 = lam (lam (app hyp (case ~1 (inl ~0) (inr ~0))))

  example-1-2 : [] ⊢ (a + b ⟶ (a + b ⟶ c) ⟶ c)
  example-1-2 = lam (lam (case ~1 (app ~1 (inl ~0)) (app ~1 (inr ~0))))

  example-1-3 : [] ⊢ (a + b ⟶ (a + b ⟶ c) ⟶ c)
  example-1-3 = lam (case ~0 (lam (app ~0 (inl ~1))) (lam (app ~0 (inr ~1))))

  example-1-4 : [] ⊢ (a + b ⟶ (a + b ⟶ c) ⟶ c)
  example-1-4 = lam (lam (app ~0 ~1))

  example-2-1 : [] ⊢ ((a ⟶ b) ⟶ (c ⟶ a) ⟶ c ⟶ d + e ⟶ b)
  example-2-1 = lam (lam (lam (lam (app ~3 (app ~2 ~1)))))

  example-2-2 : [] ⊢ ((a ⟶ b) ⟶ (c ⟶ a) ⟶ c ⟶ d + e ⟶ b)
  example-2-2 = lam (lam (lam (lam (case ~0 (app ~4 (app ~3 ~2)) (app ~4 (app ~3 ~2))))))

  example-2-3 : [] ⊢ ((a ⟶ b) ⟶ (c ⟶ a) ⟶ c ⟶ d + e ⟶ b)
  example-2-3 = lam (lam (lam (lam (case ~0 (case (inl ~2) (app ~5 (app ~4 ~0)) (app ~5 ~0)) (case (inr (app ~3 ~2)) (app ~5 (app ~4 ~0)) (app ~5 ~0))))))

  example-2-4 : [] ⊢ ((a ⟶ b) ⟶ (c ⟶ a) ⟶ c ⟶ d + e ⟶ b)
  example-2-4 = lam (lam (lam (lam (case (case ~0 (inl ~2) (inr (app ~3 ~2))) (app ~4 (app ~3 ~0)) (app ~4 ~0)))))

  example-3-1 : [] ⊢ ((a ⟶ b) ⟶ (c ⟶ b) ⟶ d ⟶ (d ⟶ a + c) ⟶ b)
  example-3-1 = lam (lam (lam (lam (case (app hyp (wkn hyp)) (app (wkn (wkn (wkn (wkn hyp)))) hyp) (app (wkn (wkn (wkn hyp))) hyp)))))

  example-3-2 : [] ⊢ ((a ⟶ b) ⟶ (c ⟶ b) ⟶ d ⟶ (d ⟶ a + c) ⟶ b)
  example-3-2 = lam (lam (lam (lam (case (app hyp (wkn hyp)) (case (app (wkn hyp) (wkn (wkn hyp))) (app (wkn (wkn (wkn (wkn (wkn hyp))))) hyp) (app (wkn (wkn (wkn (wkn hyp)))) hyp)) (app (wkn (wkn (wkn hyp))) hyp)))))

  example-4-1 : [] ⊢ (f ⟶ g ⟶ (a ⟶ b + c) ⟶ (a ⟶ d + e) ⟶ a ⟶ f + g)
  example-4-1 = lam (lam (lam (lam (lam (case (app ~2 ~0) (inl ~5) (case (app ~3 ~1) (inr ~5) (inl ~6)))))))

  example-4-2 : [] ⊢ (f ⟶ g ⟶ (a ⟶ b + c) ⟶ (a ⟶ d + e) ⟶ a ⟶ f + g)
  example-4-2 = lam (lam (lam (lam (lam (case (app ~1 ~0) (case (app ~2 ~1) (inl ~6) (inr ~5) ) (inl ~5)))))) -- to check!

  example-5-1 : [] ⊢ (a + b ⟶ c ⟶ c ⟶ c)
  example-5-1 = lam (lam (lam ~1))

  example-5-2 : [] ⊢ (a + b ⟶ c ⟶ c ⟶ c)
  example-5-2 = lam (lam (lam ~0))

  example-5-3 : [] ⊢ (a + b ⟶ c ⟶ c ⟶ c)
  example-5-3 = lam (lam (lam (case ~2 ~2 ~1)))

  bind : ∀ {A B w} → w ⊩ A → (∀ {w'} → w' ≥ w → w' ⊩ˢ A → w' ⊩ B) → w ⊩ B
  bind H f = λ ≥₁ k₁ →
                 H ≥₁ (λ ≥₂ H₂ → f (≥₂ ∙ ≥₁) H₂ ≥-refl (λ ≥₃ H₃ → k₁ (≥₃ ∙ ≥₂) H₃))

  hsi-sum-exp : ∀ {f g h Γ} → Γ ⊩ ((g + h) ⟶ f) → Γ ⊩ ((g ⟶ f) * (h ⟶ f))
  hsi-sum-exp {f} {g} {h} H = 
    bind {g + h ⟶ f} {(g ⟶ f) * (h ⟶ f)} H
      (λ ≥₁ φ₁ →
         return {(g ⟶ f) * (h ⟶ f)}
         (return {g ⟶ f} (λ ≥₂ γ₂ → φ₁ ≥₂ (return {g + h} (inj₁ γ₂))) ,
          return {h ⟶ f} (λ ≥₂ γ₂ → φ₁ ≥₂ (return {g + h} (inj₂ γ₂)))))

  hsi-exp-sum : ∀ {f g h Γ} → Γ ⊩ ((g ⟶ f) * (h ⟶ f)) → Γ ⊩ ((g + h) ⟶ f)
  hsi-exp-sum {f} {g} {h} H = 
    λ ≥₁ κ₁ →
        H ≥₁
        (λ ≥₂ α₂ →
           κ₁ ≥₂
           (λ ≥₃ α₃ →
              λ ≥₄ κ₄ →
                α₃ ≥₄
                (λ ≥₅ α₅ →
                   [
                   (λ x →
                      proj₁ α₂ (≥₅ ∙ ≥₄ ∙ ≥₃)
                      (λ ≥₆ φ₆ →
                         φ₆ ≥-refl (λ ≥₇ α₇ → x (≥₇ ∙ ≥₆) α₇) ≥-refl
                         (λ ≥₇ → κ₄ (≥₇ ∙ ≥₆ ∙ ≥₅))))
                   ,
                   (λ x →
                      proj₂ α₂ (≥₅ ∙ ≥₄ ∙ ≥₃)
                      (λ ≥₆ φ₆ →
                         φ₆ ≥-refl (λ ≥₇ α₇ → x (≥₇ ∙ ≥₆) α₇) ≥-refl
                         (λ ≥₇ → κ₄ (≥₇ ∙ ≥₆ ∙ ≥₅))))
                   ]′
                   α₅)))

  hsi-exp-congr : ∀ {f₁ f₂ g₁ g₂ Γ} → (∀ {Γ₁} → Γ₁ ≥ Γ → Γ₁ ⊩ f₁ → Γ₁ ⊩ g₁) → (∀ {Γ₂} → Γ₂ ≥ Γ → Γ₂ ⊩ g₂ → Γ₂ ⊩ f₂) → (Γ ⊩ (f₂ ⟶ f₁))  → (Γ ⊩ (g₂ ⟶ g₁))
  hsi-exp-congr {f₁} {f₂} {g₁} {g₂} α β γ = 
    bind {f₂ ⟶ f₁} {g₂ ⟶ g₁} γ
      (λ ≥₁ φ₁ →
         return {g₂ ⟶ g₁} (λ ≥₂ γ₂ → α (≥₂ ∙ ≥₁) (φ₁ ≥₂ (β (≥₂ ∙ ≥₁) γ₂))))

  hsi-prod-exp : ∀ {f g h Γ} → Γ ⊩ (h ⟶ (f * g)) → Γ ⊩ ((h ⟶ f) * (h ⟶ g))
  hsi-prod-exp {f} {g} {h} {Γ} H = 
    bind {h ⟶ f * g} {(h ⟶ f) * (h ⟶ g)} H
      (λ ≥₁ φ₁ →
         return {(h ⟶ f) * (h ⟶ g)}
         (return {h ⟶ f}
          (λ ≥₂ γ₂ → bind {f * g} {f} (φ₁ ≥₂ γ₂) (λ ≥₃ α₃ → proj₁ α₃))
          ,
          return {h ⟶ g}
          (λ ≥₂ γ₂ → bind {f * g} {g} (φ₁ ≥₂ γ₂) (λ ≥₃ α₃ → proj₂ α₃))))

  hsi-exp-exp : ∀ {f g h Γ} → Γ ⊩ (h ⟶ (g ⟶ f)) → Γ ⊩ ((h * g) ⟶ f)
  hsi-exp-exp {f} {g} {h} {Γ} H = 
    λ ≥₁ κ₁ →
        H ≥₁
        (λ ≥₂ α →
           κ₁ ≥₂
           (λ ≥₃ β ≥₄ κ₄ →
              β ≥₄
              (λ ≥₅ γ →
                 α (≥₅ ∙ ≥₄ ∙ ≥₃) (proj₁ γ) ≥-refl
                 (λ ≥₆ δ →
                    δ ≥-refl (⊩-≥ {g} ≥₆ (proj₂ γ)) ≥-refl
                    (λ ≥₇ η → κ₄ (≥₇ ∙ ≥₆ ∙ ≥₅) η)))))

  hsi-prod-sum : ∀ {f g h Γ} → Γ ⊩ (f * (g + h)) → Γ ⊩ ((f * g) + (f * h))
  hsi-prod-sum {f} {g} {h} {Γ} H =
    λ {C₁} ≥₁ κ₁ →
        H {C₁} ≥₁
        (λ ≥₂ α₂ →
           proj₂ α₂ {C₁} ≥-refl
           (λ ≥₃ α₃ →
              [
              (λ α₄ →
                 κ₁ (≥₃ ∙ ≥₂)
                 (inj₁ (return {f * g} (⊩-≥ {f} ≥₃ (proj₁ α₂) , (λ κ → α₄ κ)))))
              ,
              (λ α₄ →
                 κ₁ (≥₃ ∙ ≥₂)
                 (inj₂ (return {f * h} (⊩-≥ {f} ≥₃ (proj₁ α₂) , (λ κ → α₄ κ)))))
              ]′
              α₃))

  hsi-sum-prod : ∀ {f g h Γ} → Γ ⊩ ((f * g) + (f * h)) → Γ ⊩ (f * (g + h))
  hsi-sum-prod {f} {g} {h} H = 
    λ ≥₁ κ₁ →
        H ≥₁
        (λ ≥₂ →
           [
           (λ x →
              x ≥-refl
              (λ ≥₃ α₃ →
                 κ₁ (≥₃ ∙ ≥₂) (proj₁ α₃ , return {g + h} (inj₁ (proj₂ α₃)))))
           ,
           (λ x →
              x ≥-refl
              (λ ≥₃ α₃ →
                 κ₁ (≥₃ ∙ ≥₂) (proj₁ α₃ , return {g + h} (inj₂ (proj₂ α₃)))))
           ]′)

  exp-left : ∀ {a a' b Γ} → (∀{Γ'} → Γ' ⊩ a → Γ' ⊩ a') → Γ ⊩ (a' ⟶ b) → Γ ⊩ (a ⟶ b)
  exp-left {a} {a'} {b} φ H = λ ≥₁ κ₁ → H ≥₁ (λ ≥₂ ψ → κ₁ ≥₂ (λ ≥₃ α → ψ ≥₃ (φ α)))

  exp-right : ∀ {a b b' Γ} → (∀{Γ'} → Γ' ⊩ b → Γ' ⊩ b') → Γ ⊩ (a ⟶ b) → Γ ⊩ (a ⟶ b')
  exp-right {a} {b} {b'} φ H = λ ≥₁ κ₁ → H ≥₁ (λ ≥₂ ψ → κ₁ ≥₂ (λ ≥₃ α → φ (ψ ≥₃ α)))

  prod-right : ∀ {a b b' Γ} → (∀{Γ'} → Γ' ⊩ b → Γ' ⊩ b') → Γ ⊩ (a * b) → Γ ⊩ (a * b')
  prod-right {a} {b} {b'} {Γ} φ H = λ ≥₁ κ₁ → H ≥₁ (λ ≥₂ α → κ₁ ≥₂ ((proj₁ α) , φ (proj₂ α)))

  prod-left : ∀ {a a' b Γ} → (∀{Γ'} → Γ' ⊩ a → Γ' ⊩ a') → Γ ⊩ (a * b) → Γ ⊩ (a' * b)
  prod-left {a} {a'} {b} {Γ} φ H = λ ≥₁ κ₁ → H ≥₁ (λ ≥₂ α → κ₁ ≥₂ (φ (proj₁ α) , (proj₂ α)))

  -- An intermediary, not the canonical type, but maybe it will be
  -- enough for this example
  iso-example-1-' : 
    [] ⊩ ((a + b) ⟶ (((a + b) ⟶ c) ⟶ c)) →
    [] ⊩ ((a ⟶ (((a + b) ⟶ c) ⟶ c)) * (b ⟶ (((a + b) ⟶ c) ⟶ c)))
  iso-example-1-' α = hsi-sum-exp {(((a + b) ⟶ c) ⟶ c)} {a} {b} α

  example-1-iso : [] ⊩ ((a + b) ⟶ (((a + b) ⟶ c) ⟶ c)) →
       [] ⊩ ((a * (a ⟶ c) * (b ⟶ c) ⟶ c) * (b * (a ⟶ c) * (b ⟶ c) ⟶ c))
  example-1-iso α = 
    prod-left {a ⟶ (a + b ⟶ c) ⟶ c} {a * (a ⟶ c) * (b ⟶ c) ⟶ c}
      {b * (a ⟶ c) * (b ⟶ c) ⟶ c}
      (λ H →
         hsi-exp-exp {c} {(a ⟶ c) * (b ⟶ c)} {a}
         (exp-right {a} {(a + b ⟶ c) ⟶ c} {(a ⟶ c) * (b ⟶ c) ⟶ c}
          (exp-left {(a ⟶ c) * (b ⟶ c)} {a + b ⟶ c} {c}
           (hsi-exp-sum {c} {a} {b}))
          H))
      (prod-right {a ⟶ (a + b ⟶ c) ⟶ c} {b ⟶ (a + b ⟶ c) ⟶ c}
       {b * (a ⟶ c) * (b ⟶ c) ⟶ c}
       (λ H →
          hsi-exp-exp {c} {(a ⟶ c) * (b ⟶ c)} {b}
          (exp-right {b} {(a + b ⟶ c) ⟶ c} {(a ⟶ c) * (b ⟶ c) ⟶ c}
           (exp-left {(a ⟶ c) * (b ⟶ c)} {a + b ⟶ c} {c}
            (hsi-exp-sum {c} {a} {b}))
           H))
       (hsi-sum-exp {(a + b ⟶ c) ⟶ c} {a} {b} α))

  example-2-iso : ∀ {a b c d e Γ} 
    → Γ ⊩ ((a ⟶ b) ⟶ (c ⟶ a) ⟶ c ⟶ d + e ⟶ b) 
    → Γ ⊩ (((a ⟶ b) * (c ⟶ a) * c * d ⟶ b) * ((a ⟶ b) * (c ⟶ a) * c * e ⟶ b))
  example-2-iso {a} {b} {c} {d} {e} {Γ} H = 
    hsi-sum-exp {f = b} {g = (a ⟶ b) * (c ⟶ a) * c * d}
      {h = (a ⟶ b) * (c ⟶ a) * c * e}
      (exp-left
       {a = (a ⟶ b) * (c ⟶ a) * c * d + (a ⟶ b) * (c ⟶ a) * c * e}
       {a' = (a ⟶ b) * (c ⟶ a) * c * (d + e)} {b = b}
       (λ x →
          prod-right {a = a ⟶ b} {b = (c ⟶ a) * (c * d + c * e)}
          {b' = (c ⟶ a) * c * (d + e)}
          (prod-right {c ⟶ a} {c * d + c * e} {c * (d + e)}
           (hsi-sum-prod {c} {d} {e}))
          (prod-right {a = a ⟶ b} {b = (c ⟶ a) * c * d + (c ⟶ a) * c * e}
           {b' = (c ⟶ a) * (c * d + c * e)}
           (hsi-sum-prod {c ⟶ a} {c * d} {c * e})
           (hsi-sum-prod {f = a ⟶ b} {g = (c ⟶ a) * c * d}
            {h = (c ⟶ a) * c * e} x)))
       (hsi-exp-exp {f = b} {g = (c ⟶ a) * c * (d + e)} {h = a ⟶ b}
        (exp-right {a = a ⟶ b} {b = (c ⟶ a) ⟶ c ⟶ d + e ⟶ b}
         {b' = (c ⟶ a) * c * (d + e) ⟶ b}
         (λ x →
            hsi-exp-exp {f = b} {g = c * (d + e)} {h = c ⟶ a}
            (exp-right {a = c ⟶ a} {b = c ⟶ d + e ⟶ b} {b' = c * (d + e) ⟶ b}
             (hsi-exp-exp {f = b} {g = d + e} {h = c}) x))
         H)))

  example-3-iso : ∀ {a b c d Γ} 
    → Γ ⊩ ((a ⟶ b) ⟶ (c ⟶ b) ⟶ d ⟶ (d ⟶ a + c) ⟶ b)
    → Γ ⊩ ((((a ⟶ b) * (c ⟶ b)) * d) * (d ⟶ a + c) ⟶ b)
  example-3-iso {a} {b} {c} {d} {Γ} H = 
    hsi-exp-exp {b} {d ⟶ a + c} {((a ⟶ b) * (c ⟶ b)) * d}
      (hsi-exp-exp {(d ⟶ a + c) ⟶ b} {d} {(a ⟶ b) * (c ⟶ b)}
       (hsi-exp-exp {d ⟶ (d ⟶ a + c) ⟶ b} {c ⟶ b} {a ⟶ b} H))

  example-4-iso : ∀ {Γ} 
    → Γ ⊩ (f ⟶ g ⟶ (a ⟶ b + c) ⟶ (a ⟶ d + e) ⟶ a ⟶ f + g)
    → Γ ⊩ (((((f * g) * (a ⟶ b + c)) * (a ⟶ d + e)) * a) ⟶ f + g)
  example-4-iso {Γ} H = 
    hsi-exp-exp {f + g} {a} {((f * g) * (a ⟶ b + c)) * (a ⟶ d + e)}
      (hsi-exp-exp {a ⟶ f + g} {a ⟶ d + e} {(f * g) * (a ⟶ b + c)}
       (hsi-exp-exp {(a ⟶ d + e) ⟶ a ⟶ f + g} {a ⟶ b + c} {f * g}
        (hsi-exp-exp {(a ⟶ b + c) ⟶ (a ⟶ d + e) ⟶ a ⟶ f + g} {g} {f} H)))

  example-5-iso : ∀ {Γ} 
    → Γ ⊩ (a + b ⟶ c ⟶ c ⟶ c)
    → Γ ⊩ (((a * c) * c ⟶ c) * ((b * c) * c ⟶ c))
  example-5-iso {Γ} H = 
    prod-right {(a * c) * c ⟶ c} {b ⟶ c ⟶ c ⟶ c} {(b * c) * c ⟶ c}
      (λ H' →
         hsi-exp-exp {c} {c} {b * c} (hsi-exp-exp {c ⟶ c} {c} {b} H'))
      (prod-left {a ⟶ c ⟶ c ⟶ c} {(a * c) * c ⟶ c} {b ⟶ c ⟶ c ⟶ c}
       (λ H' →
          hsi-exp-exp {c} {c} {a * c} (hsi-exp-exp {c ⟶ c} {c} {a} H'))
       (hsi-sum-exp {c ⟶ c ⟶ c} {a} {b} H))

  -- open namespace for nicer output
  open Lambda-Sum-NBE._⊢ʳ_
  open Lambda-Sum-NBE._⊢ᵉ_

  -- try with example-1-1, -1-2, -1-3
  test-example-1 : [] ⊢ʳ (a + b ⟶ (a + b ⟶ c) ⟶ c)
  test-example-1 = {! reify {(a + b ⟶ (a + b ⟶ c) ⟶ c)} (eval example-1-1 tt)!} 

  -- try with example-1-1, -1-2, -1-3
  test-example-1-enf : [] ⊢ʳ ((a * (a ⟶ c) * (b ⟶ c) ⟶ c) * (b * (a ⟶ c) * (b ⟶ c) ⟶ c))
  test-example-1-enf = {! reify {((a * (a ⟶ c) * (b ⟶ c) ⟶ c) * (b * (a ⟶ c) * (b ⟶ c) ⟶ c))} (example-1-iso (eval example-1-1 tt)) !}

  -- try with example-2-1, -2-2, -2-3, -2-4
  test-example-2 : [] ⊢ʳ ((a ⟶ b) ⟶ (c ⟶ a) ⟶ c ⟶ d + e ⟶ b)
  test-example-2 = {! reify {((a ⟶ b) ⟶ (c ⟶ a) ⟶ c ⟶ d + e ⟶ b)} (eval example-2-1 tt) !}

  -- try with example-2-1, -2-2, -2-3, -2-4
  test-example-2-enf : [] ⊢ʳ (((a ⟶ b) * (c ⟶ a) * c * d ⟶ b) * ((a ⟶ b) * (c ⟶ a) * c * e ⟶ b))
  test-example-2-enf = {! reify {(((a ⟶ b) * (c ⟶ a) * c * d ⟶ b) * ((a ⟶ b) * (c ⟶ a) * c * e ⟶ b))} (example-2-iso {a = a} {b = b} {c = c} {d = d} {e = e} (eval example-2-1 tt)) !}

  -- try with example-3-1, -3-2
  test-example-3 : [] ⊢ʳ ((a ⟶ b) ⟶ (c ⟶ b) ⟶ d ⟶ (d ⟶ a + c) ⟶ b)
  test-example-3 = {! reify {((a ⟶ b) ⟶ (c ⟶ b) ⟶ d ⟶ (d ⟶ a + c) ⟶ b)} (eval example-3-1 tt) !} 

  -- try with example-3-1, -3-2
  test-example-3-enf : [] ⊢ʳ ((((a ⟶ b) * (c ⟶ b)) * d) * (d ⟶ a + c) ⟶ b)
  test-example-3-enf = {! reify {((((a ⟶ b) * (c ⟶ b)) * d) * (d ⟶ a + c) ⟶ b)} (example-3-iso {a = a} {b = b} {c = c} {d = d} (eval example-3-2 tt)) !} 

  -- try with example-4-1, -4-2
  test-example-4 : [] ⊢ʳ (f ⟶ g ⟶ (a ⟶ b + c) ⟶ (a ⟶ d + e) ⟶ a ⟶ f + g)
  test-example-4 = {! reify {(f ⟶ g ⟶ (a ⟶ b + c) ⟶ (a ⟶ d + e) ⟶ a ⟶ f + g)} (eval example-4-1 tt) !} 

  -- try with example-4-1, -4-2
  test-example-4-enf : [] ⊢ʳ (((((f * g) * (a ⟶ b + c)) * (a ⟶ d + e)) * a) ⟶ f + g)
  test-example-4-enf = {! reify {(((((f * g) * (a ⟶ b + c)) * (a ⟶ d + e)) * a) ⟶ f + g)} (example-4-iso (eval example-4-1 tt)) !} 

  -- try with example-5-1, -5-2, -5-3
  test-example-5 : [] ⊢ʳ (a + b ⟶ c ⟶ c ⟶ c)
  test-example-5 = {! reify {(a + b ⟶ c ⟶ c ⟶ c)} (eval example-5-1 tt) !} 

  -- try with example-5-1, -5-2, -5-3
  test-example-5-enf : [] ⊢ʳ (((a * c) * c ⟶ c) * ((b * c) * c ⟶ c))
  test-example-5-enf = {! reify {(((a * c) * c ⟶ c) * ((b * c) * c ⟶ c))} (example-5-iso (eval example-5-3 tt)) !} 
