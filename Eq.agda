module Eq where
open import Agda.Primitive

-- 1.12 Identity types


data _≡_ {ℓ : Level} {A : Set ℓ} : A → A → Set ℓ where 
    refl : {a : A } → a ≡ a 

data Unit : Set where 
    unit : Unit

_ : (unit ≡ unit)
_ = refl

_ : (unit ≡ unit) ≡ (unit ≡ unit)
_ = refl

_ : ((unit ≡ unit) ≡ (unit ≡ unit)) ≡ ((unit ≡ unit) ≡ (unit ≡ unit))
_ = refl


data Bool : Set₀ where 
    tt ff : Bool

not : Bool → Bool
not tt = ff
not ff = tt

_ : (not tt ≡ ff) ≡ (ff ≡ ff)
_ = refl


id :  {A : Set } → A → A 
id a = a

-- Indiscernibility of identicals
module IndofId 
    (A : Set)
    (C : A → Set)
    (f : (∀ (x y : A)(p : x ≡ y) → C x → C y))
    where

    _ : {a : A} {c : C a} → (f a a refl)  ≡ id {C a} 
    _ = {!   !}

module PathInduction -- induction principle for Id type
    {A : Set}
    (C : ∀ {x y : A} → 
        (x ≡ y → Set)) -- predicate
    (c : ∀ {x : A} → 
        C {x} {x} refl) -- base case
    (f : ∀ {x y : A} 
        (p : x ≡ y) → C p)
    where

    {-
        If we have a predicate on (x ≡ y)
        and a proof that it holds for any (x ≡ x)
        then the predicate is true for any (x ≡ y)

    -}

    _ : {a : A} → f {a} {a} refl ≡ c  
    _ = {!  !}

    -- Unit and Id are types with one inhabitant
    -- Induction for Unit is similar to J, Induction for Id
    Ind-Unit : ∀ (P : Unit → Set) → (base : P unit ) → ∀ (x : Unit) → P x
    Ind-Unit P Punit unit = Punit

module Jdef where
    -- Predicate is the "logical" interpretation of X → Set
    J : {A : Set} → 
        ∀ (P : ∀(x y : A)→ (x ≡ y → Set)) → -- forall Predicates "P" over x ≡ y
            (Prefl : ∀ (x : A)→ P x x refl) →  -- a proof "Prefl : P refl" at refl : x ≡ x
            (∀ (x y : A)(p : x ≡ y) → P x y p) -- suffices to show a proof "P p" for any p : x ≡ y
    J P Prefl x x refl = Prefl x

    -- using J

    -- what is an example property over x ≡ y ? ...
    -- Any path in Bool is equal to itself
        -- note)
        -- the only paths in bool are (tt ≡ tt) and (ff ≡ ff)
    P : Set
    P = ∀ (x y : Bool)(p : x ≡ y) → p ≡ p

    sym : {A : Set} → ∀ {x y : A} → (x ≡ y) → (y ≡ x)
    sym refl = refl

    trans : {A : Set} → ∀{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
    trans refl refl = refl

    lemma₁ₐ : {A : Set} {x y : A} {p : x ≡ y} → p ≡ trans p refl
    lemma₁ₐ {A} {x} {y} {refl} = refl

    lemma₁b : {A : Set} {x y : A} {p : x ≡ y} → p ≡ trans refl p 
    lemma₁b {A} {x} {y} {refl} = refl

    lemma₂ₐ : {A : Set} {x y : A} {p : x ≡ y} → trans (sym p) p ≡ refl
    lemma₂ₐ {A} {x} {y} {refl} = refl

    lemma₂b : {A : Set} {x y : A} {p : x ≡ y} → trans p (sym p) ≡ refl
    lemma₂b {A} {x} {y} {refl} = refl 

    lemma₃ : {A : Set} {x y : A} {p : x ≡ y} → sym (sym p) ≡ p
    lemma₃ {A} {x} {y} {refl} = refl

    lemma₄ : {A : Set} {x y w z : A} {p : x ≡ y}{q : y ≡ w}{r : w ≡ z} → 
            trans p (trans q r) ≡ trans (trans p q) r
    lemma₄ {A} {x} {y} {w} {z} {refl} {refl} {refl} = refl 

    Ω² : {ℓ : Level}{A : Set ℓ}{a : A} → Set ℓ 
    Ω² {ℓ}{A} {a} = refl {ℓ} {A} {a} ≡ refl

    --Eckmann-Hilton : {!   !}
    --Eckmann-Hilton = {!   !}
    open import Agda.Builtin.Sigma

    pointed : {ℓ : Level } → (Set (lsuc ℓ)) 
    pointed {ℓ} = Σ (Set ℓ) λ x → x
    
    data Unitℓ {ℓ : Level} : Set ℓ where 
        unitℓ : Unitℓ

    _ : {ℓ : Level} → pointed {ℓ}
    _ = Unitℓ , unitℓ


    -- cong
    ap : {A B : Set}{x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
    ap f refl = refl

    lemma2ᵢ : {A B : Set}{x y z : A}{f : A → B}{p : x ≡ y}{q : y ≡ z} → 
        ap f (trans p q) ≡ trans (ap f p) (ap f q)
    lemma2ᵢ {A}{B}{x}{y}{z}{f}{refl}{refl} = refl
    
    lemma2ᵢᵢ : {A B : Set}{x y z : A}{f : A → B}{p : x ≡ y} → 
        ap f (sym p) ≡ sym (ap f p)
    lemma2ᵢᵢ {A}{B}{x}{y}{z}{f}{refl} = refl 
      
    
    _∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
    g ∘ f = λ x → g (f x)

    lemma2ᵢᵢᵢ : {A B C : Set}{x y z : A}{f : A → B}{g : B → C}{p : x ≡ y} → 
        ap g (ap f p) ≡ ap (g ∘ f) p
    lemma2ᵢᵢᵢ {A}{B}{C}{x}{y}{z}{f}{g}{refl} = refl

    lemma2ᵢᵥ : {A : Set}{x y : A}{p : x ≡ y} → 
        ap (λ x → x) p ≡ p 
    lemma2ᵢᵥ {A}{x}{y}{refl}= refl

    --_ : {A : Set} {x y z : A} → (trans (x ≡ y) refl) ≡ refl
    --_ = ?

    --_ : P
   -- _ = J {Bool} {!   !}  {!   !} tt tt refl
    
-- same as J but you fix the lhs of the "path" to 'a'
module Jbased where
    Jbase : {A : Set} → 
            ∀ (a : A) → 
            ∀ (C : ∀ (x : A) → (a ≡ x) → Set) → 
            C a refl → 
            ∀ (x : A)(p : a ≡ x) → C x p 
    Jbase a C c a refl = c



 -- clame J and Jbase are equivalent