--
-- The ExpLog Normal Form of Types
--
-- Primitive recursive definition, with some examples
--
-- Danko Ilik, Inria, 2014
--

module ENF (Proposition : Set) where

  infixr 6 _×_
  infixr 5 _+_
  infixr 4 _⊃_

  mutual
    data Atom : Set where
      _⊃ₚ_ : CNF → Proposition → Atom
      _⊃₊_⊹_ : CNF → CNF → DNF → Atom
      `_  : Proposition → Atom

    data CNF : Set where
      _×_ : Atom → CNF → CNF
      ᶜ   : Atom → CNF

    data DNF : Set where
      _+_ : CNF → DNF → DNF
      ᵈ   : CNF → DNF

  assoc× : CNF → CNF → CNF
  assoc× (ᶜ a) c' = a × c'
  assoc× (a × c) c' = a × (assoc× c c')

  assoc+ : DNF → DNF → DNF
  assoc+ (ᵈ c) d' = c + d'
  assoc+ (c + d) d' = c + (assoc+ d d')

  distrib₁ : CNF → DNF → DNF
  distrib₁ c (ᵈ c') = ᵈ (assoc× c c')
  distrib₁ c (c' + d) = (assoc× c c') + (distrib₁ c d)

  distrib : DNF → DNF → DNF
  distrib (ᵈ c) d' = distrib₁ c d'
  distrib (c + d) d' = assoc+ (distrib₁ c d') (distrib d d')

  explog₁ : CNF → DNF → CNF
  explog₁ c (c' + d') = ᶜ (c ⊃₊ c' ⊹ d')
  explog₁ c (ᵈ (ᶜ (c' ⊃ₚ p'))) = ᶜ (assoc× c c' ⊃ₚ p')
  explog₁ c (ᵈ (ᶜ (c' ⊃₊ c₁ ⊹ d₁))) = ᶜ (assoc× c c' ⊃₊ c₁ ⊹ d₁)
  explog₁ c (ᵈ (ᶜ (` p))) = ᶜ (c ⊃ₚ  p)
  explog₁ c (ᵈ ((c' ⊃ₚ p') × c'')) = (assoc× c c' ⊃ₚ p') × explog₁ c (ᵈ c'')
  explog₁ c (ᵈ ((c' ⊃₊ c₁ ⊹ d₁) × c'')) = (assoc× c c' ⊃₊ c₁ ⊹ d₁) × explog₁ c (ᵈ c'')
  explog₁ c (ᵈ (` p × c'')) = (c ⊃ₚ p) × explog₁ c (ᵈ c'')

  explog : DNF → DNF → CNF
  explog (ᵈ c) d' = explog₁ c d'
  explog (c + d) d' = assoc× (explog₁ c d') (explog d d')

  data Formula : Set where
    `_  : Proposition → Formula
    _+_ : Formula → Formula → Formula
    _×_ : Formula → Formula → Formula
    _⊃_ : Formula → Formula → Formula

  enf : Formula → DNF
  enf (` p) =  ᵈ (ᶜ (` p))
  enf (f₁ + f₂) = assoc+ (enf f₁) (enf f₂)
  enf (f₁ × f₂) = distrib (enf f₁) (enf f₂)
  enf (f₁ ⊃ f₂) = ᵈ (explog (enf f₁) (enf f₂))

  postulate
    A : Proposition
    B : Proposition
    C : Proposition
    D : Proposition
    E : Proposition
    F : Proposition
    G : Proposition

  a : Formula
  a = ` A

  b : Formula
  b = ` B

  c : Formula
  c = ` C

  d : Formula
  d = ` D

  e : Formula
  e = ` E

  f : Formula
  f = ` F

  g : Formula
  g = ` G

  -- This function is used only for pretty-printing, so we don't care
  -- if it is not primitive recursive
  mutual
    forget : DNF → Formula
    forget (ᵈ c) = forget-CNF c
    forget (c + d) = forget-CNF c + forget d

    forget-CNF : CNF → Formula
    forget-CNF (ᶜ p) = forget-Atom p
    forget-CNF (p × c) = forget-Atom p × forget-CNF c

    forget-Atom : Atom → Formula
    forget-Atom (c ⊃ₚ p) = forget-CNF c ⊃ forget-Atom (` p)
    forget-Atom (c ⊃₊ c₁ ⊹ d₁) = forget-CNF c ⊃ forget (c₁ + d₁)
    forget-Atom (` p) = ` p

  test1 = forget (enf ((a × b + c) × (d + e) × f))
  -- ` A × ` B × ` D × ` F +
  -- ` A × ` B × ` E × ` F + ` C × ` D × ` F + ` C × ` E × ` F

  test2 = forget (enf (a + b ⊃ c + d ⊃ e + f))
  -- (` A × ` C ⊃ ` E + ` F) ×
  -- (` A × ` D ⊃ ` E + ` F) ×
  -- (` B × ` C ⊃ ` E + ` F) × (` B × ` D ⊃ ` E + ` F)

  test3 = forget (enf ((a + b ⊃ c + d ⊃ e + f) × (a + b ⊃ c + d ⊃ e + f)))
  -- (` A × ` C ⊃ ` E + ` F) ×
  -- (` A × ` D ⊃ ` E + ` F) ×
  -- (` B × ` C ⊃ ` E + ` F) ×
  -- (` B × ` D ⊃ ` E + ` F) ×
  -- (` A × ` C ⊃ ` E + ` F) ×
  -- (` A × ` D ⊃ ` E + ` F) ×
  -- (` B × ` C ⊃ ` E + ` F) × (` B × ` D ⊃ ` E + ` F)

  test4 = forget (enf ((a + b ⊃ c + d ⊃ e + f) ⊃ (a + b ⊃ c + d ⊃ e + f)))
  -- ((` A × ` C ⊃ ` E + ` F) ×
  -- (` A × ` D ⊃ ` E + ` F) ×
  -- (` B × ` C ⊃ ` E + ` F) × (` B × ` D ⊃ ` E + ` F) × ` A × ` C
  -- ⊃ ` E + ` F)
  -- ×
  -- ((` A × ` C ⊃ ` E + ` F) ×
  -- (` A × ` D ⊃ ` E + ` F) ×
  -- (` B × ` C ⊃ ` E + ` F) × (` B × ` D ⊃ ` E + ` F) × ` A × ` D
  -- ⊃ ` E + ` F)
  -- ×
  -- ((` A × ` C ⊃ ` E + ` F) ×
  -- (` A × ` D ⊃ ` E + ` F) ×
  -- (` B × ` C ⊃ ` E + ` F) × (` B × ` D ⊃ ` E + ` F) × ` B × ` C
  -- ⊃ ` E + ` F)
  -- ×
  -- ((` A × ` C ⊃ ` E + ` F) ×
  -- (` A × ` D ⊃ ` E + ` F) ×
  -- (` B × ` C ⊃ ` E + ` F) × (` B × ` D ⊃ ` E + ` F) × ` B × ` D
  -- ⊃ ` E + ` F)

  test5 = forget (enf ((a + b + c ⊃ d + e + f) ⊃ (a + b + c ⊃ d + e + f) ⊃ (a + b + c ⊃ d + e + f)))
  -- ((` A ⊃ ` D + ` E + ` F) ×
  -- (` B ⊃ ` D + ` E + ` F) ×
  -- (` C ⊃ ` D + ` E + ` F) ×
  -- (` A ⊃ ` D + ` E + ` F) ×
  -- (` B ⊃ ` D + ` E + ` F) × (` C ⊃ ` D + ` E + ` F) × ` A
  -- ⊃ ` D + ` E + ` F)
  -- ×
  -- ((` A ⊃ ` D + ` E + ` F) ×
  -- (` B ⊃ ` D + ` E + ` F) ×
  -- (` C ⊃ ` D + ` E + ` F) ×
  -- (` A ⊃ ` D + ` E + ` F) ×
  -- (` B ⊃ ` D + ` E + ` F) × (` C ⊃ ` D + ` E + ` F) × ` B
  -- ⊃ ` D + ` E + ` F)
  -- ×
  -- ((` A ⊃ ` D + ` E + ` F) ×
  -- (` B ⊃ ` D + ` E + ` F) ×
  -- (` C ⊃ ` D + ` E + ` F) ×
  -- (` A ⊃ ` D + ` E + ` F) ×
  -- (` B ⊃ ` D + ` E + ` F) × (` C ⊃ ` D + ` E + ` F) × ` C
  -- ⊃ ` D + ` E + ` F)
