{-# OPTIONS --with-K #-}
module EckmannHiltonWithK where
open import Agda.Primitive

data _≡_ {ℓ : Level} {A : Set ℓ} : A → A → Set ℓ where 
    refl : {a : A } → a ≡ a 

Ω : (A : Set₀) (a : A) → Set₀ 
Ω A a = a ≡ a

_⊙_ : {A : Set₀} {a : A} → Ω A a → Ω A a → Ω A a
refl ⊙ refl = refl 

Ω² : (A : Set₀) (a : A) → Set₀
Ω² A a = Ω (a ≡ a) (refl {lzero} {A} {a})

_⨀_ : {A : Set₀} {a : A} → Ω² A a → Ω² A a → Ω² A a 
refl ⨀ refl = refl

Eckmann-Hilton : {A : Set₀} {a : A} (α : Ω² A a) (β : Ω² A a)
    → (α ⨀ β) ≡ (β ⨀ α)
Eckmann-Hilton refl refl = refl