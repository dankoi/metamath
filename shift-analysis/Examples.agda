--
-- Normalization by Evaluation for System T+ (http://arxiv.org/abs/1301.5089)
-- 
-- Example of the Ackermann function (do Ctrl+c+n+ inside the goal in
-- order to normalize)
-- 
-- Danko Ilik, 2014
--
-- Type-checked with Agda version 2.4.2, standard library version 0.8.1
--
open import Data.List
open import System-T-Shift-NBE-CBN

module Examples where

  one : ∀ {Γ} → Γ ⊢ ℕ
  one = succ zero

  two : ∀ {Γ} → Γ ⊢ ℕ
  two = succ (succ zero)

  three : ∀ {Γ} → Γ ⊢ ℕ
  three = succ (succ (succ zero))

  four : ∀ {Γ} → Γ ⊢ ℕ
  four = succ (succ (succ (succ zero)))

  ack : ∀ {Γ} → Γ ⊢ ℕ ⟶ ℕ ⟶ ℕ
  ack = lam
          (rec hyp (lam (succ hyp))
           (lam
            (lam
             (lam
              (rec hyp (app (wkn hyp) (succ zero))
               (lam (lam (app (wkn (wkn (wkn hyp))) hyp))))))))

  -- ack(3,2) = 29 takes about a minute to compute (with 8GB RAM free)
  -- ack(3,1) = 13 is reasonably fast
  test-ack-1 : [] ⊢ ℕ
  test-ack-1 = {! nbe (app (app ack (succ (succ (succ zero)))) ((succ zero))) !}
