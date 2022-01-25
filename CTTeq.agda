{-# OPTIONS --cubical #-}
module CTTeq where
open import Cubical.Core.Everything

data Bool : Set where 
    tt ff : Bool

data FooBar : Set where 
    Foo Bar : FooBar


not : Bool → Bool 
not tt = ff
not ff = tt

nn : ∀ (b : Bool) → not (not b) ≡ b 
nn = λ{ tt → λ i → tt
     ; ff → λ i → ff }

open import Cubical.Foundations.Isomorphism

-- show that Bool and FooBar are isomorphic types
BoolFooIso : Iso Bool FooBar
BoolFooIso = iso (λ{ tt → Foo
                   ; ff → Bar})
                   
                 (λ{ Foo → tt
                   ; Bar → ff}) 
                 
                 (λ{ Foo i → Foo
                   ; Bar i → Bar})
                 
                  λ{tt i → tt
                  ; ff i → ff}

-- Isomorphic types are equivalent               
eqT : Bool ≡ FooBar
eqT = isoToPath BoolFooIso

-- define transport (transfer in isabelle)
transport : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

-- tranport the term `tt : Bool` across the equivalence eqT 
-- to get element `Foo : FooBar`
_ : FooBar
_ = transport eqT tt

-- transport the definition of `not` across the equivalence
not' : FooBar → FooBar
not' = transport (λ i → eqT i → eqT i) not

-- now you can compute with not'
_ : not' Foo ≡ Bar 
_ = λ i → Bar

-- proof that not and not' are equal modulo representation
noteq : PathP (λ i → eqT i → eqT i) not not'
noteq  i = transp (λ j → eqT (i ∧ j) → eqT (i ∧ j))  (~ i) not


-- tranportint the proof (not (not b) ≡ b) over the equivalence
_ : ∀ (fb : FooBar) → not' (not' fb) ≡ fb 
_ = transport ((λ i → (x : eqT i) → noteq i (noteq i x) ≡ x)) nn

