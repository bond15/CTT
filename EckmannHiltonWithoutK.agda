{-# OPTIONS --without-K #-}
module EckmannHiltonWithoutK where
open import Agda.Primitive

data _≡_ {ℓ : Level} {A : Set ℓ} : A → A → Set ℓ where 
    refl : {a : A } → a ≡ a 

sym : {A : Set} → ∀ {x y : A} → (x ≡ y) → (y ≡ x)
sym refl = refl

trans : {A : Set} → ∀{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
trans refl refl = refl

Ω : (A : Set₀) (a : A) → Set₀ 
Ω A a = a ≡ a

_⊙_ : {A : Set₀} {a : A} → Ω A a → Ω A a → Ω A a
x ⊙ y = trans x y

Ω² : (A : Set₀) (a : A) → Set₀
Ω² A a = Ω (a ≡ a) (refl {lzero} {A} {a})

_⨀_ : {A : Set₀} {a : A} → Ω² A a → Ω² A a → Ω² A a 
x ⨀ y = {!   !}

Eckmann-Hilton : {A : Set₀} {a : A} (α : Ω² A a) (β : Ω² A a)
    → (α ⨀ β) ≡ (β ⨀ α)
Eckmann-Hilton x y = {!   !}