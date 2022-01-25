{-# OPTIONS --copatterns #-}
module typeclasses where
    open import Agda.Builtin.Nat
    open import Agda.Builtin.List
    open import Cubical.Core.Everything

    -- agda doesnt necessarity have type classes.. but it does have implicit instance resolution

    refl : {A : Set}{a : A} → a ≡ a 
    refl {A} {a} = λ i → a

    _ : 2 + 2 ≡ 4
    _ = refl

    -- taking a regual record.. lets make a type class
    record Monoid (A : Type) : Type where
        field
            e : A 
            _●_ : A → A → A
 

    -- this is some magic sauce
    -- it opens the fields of the record and makes them functions taking in instance arguemnts
    -- e : {A : Type} → ⦃ Monoid A ⦄ → A
    -- _●_ : { A : Type } → ⦃ Monoid A ⦄ → A → A → A  
    open Monoid ⦃...⦄ public


    -- now define an Instance (similar to Scala, this defines an implicit)
    -- HOWEVER this does not use the same implicit reolution algorithms as this expression "{A : Set}"

    --instance 
    --   NatMonoid : Monoid Nat 
    --   NatMonoid = record { e = 0 ; _●_ = _+_ }

    -- orrr be fancy and use copatterns to define a record
    instance
        NatMonoid : Monoid Nat
        e   ⦃ NatMonoid ⦄ = 0
        _●_ ⦃ NatMonoid ⦄ = _+_ 


    -- defining a function using an instance argument
    mconcat : {A : Type} → ⦃ Monoid A ⦄ → List A → A 
    mconcat []       = e
    mconcat (x ∷ xs) = x ● mconcat xs

    -- now we have an implicit instance of Monoid for nat. and can use it!
    _ : Nat
    _ = mconcat (1 ∷ 2 ∷ 3 ∷ 4 ∷ [] )

    module datainstances where
        -- what the hell is this..?
        -- constructor 
        data _≣_ {A : Type}(x : A) : A → Set where
            instance refll : x ≣ x

        len : {A : Type} → List A → Nat
        len [] = 0
        len (x ∷ x₁) = 1 + len x₁

        tl : {A : Type} → List A → List A 
        tl [] = []
        tl (x ∷ xs) = xs

        -- note this complains of an incomplete pattern match
        --f : List Nat → List Nat → List Nat
        --f [] [] = {!   !}
        --f (x ∷ xs) (y ∷ ys) = {!   !}

        --instance
        --    postulate thing : {A : Type}{xs ys : List A} → ⦃ len xs ≣ len ys ⦄ → len (tl xs) ≡ len (tl ys)
            --thing {A} {[]} {[]} ⦃ p ⦄ = λ i → 0
            --thing {A} {x ∷ xs'} {y ∷ ys'} ⦃ p ⦄ = {!   !}

        -- with this implicit argument that the lengths are equal, we eliminat the incomplete pattern match!
        combine : {A : Type} → (xs : List A) → (ys : List A) → ⦃ len xs ≣ len ys ⦄ → List A
        combine [] [] = []
        combine (x ∷ xs') (y ∷ ys') = ys'
            --(x ● y) ∷ combine xs' ys' 