{-# OPTIONS --cubical #-}
module RepInd where

-- POPL 2021
-- Internalizing Representation Independence with Univalence

open import Data.Product

data Maybe (A : Set ) : Set where
    None : Maybe A 
    Just : A → Maybe A    

record Queue(A : Set) : Set₁ where 
    field 
        Q : Set
        empty : Q 
        enqueue : A → Q → Q
        dequeue : Q → Maybe (Q × A)

open import Data.List

last' : {A : Set} → List A → Maybe (List A × A)
last' [] = None
last' (x ∷ xs) = Just (xs , x)

ListQueue : (A : Set) → Queue A 
ListQueue A = record { 
                Q = List A ; 
                empty = [] ;
                enqueue = _∷_ ; 
                dequeue = last' }

module CTT where 
    open import Cubical.Core.Everything
    _ : I 
    _ = i0

    _ : I 
    _ = i1 

    refl : {A : Set}{x : A} → x ≡ x
    refl {x = x} = λ _ → x

    cong : {A : Type} {B : A → Type} 
        (f : (a : A) → B a)
        {x y : A}
        (p : x ≡ y) 
        → PathP (λ i → B (p i)) (f x) (f y)
    cong f p i = f (p i)

    funExt : {A B : Set} 
            {f g : A → B} → 
            ((x : A) → f x ≡ g x) → 
            f ≡ g 
    funExt p i x = p x i

    transport : {A B : Set} → A ≡ B → A → B 
    transport p a = transp ((λ i → p i)) i0 a

    subst : {A : Set} → 
        ( B : A → Set) → 
        {x y : A} → 
        x ≡ y → 
        B x → B y 
    subst B p bx = transport (λ i → B (p i)) bx

    -- based path induction
    J : {A : Set} {x : A} → 
        (P : ∀ y → x ≡ y → Set )
        (d : P x refl)
        {y : A}
        (p : x ≡ y) → 
        P y p
    J P d p = transport (λ i → P (p i) λ j → p ( i ∧ j)) d 

    open import Cubical.Foundations.Equiv.Base using (idEquiv ; fiber)
    open import Cubical.Foundations.Prelude using (isContr)
    -- The ua constant
    -- wtf is going on in this definition?
    -- what the hell is `Glue` and partial types?
    ua : ∀ {A B : Type } → A ≃ B → A ≡ B
    ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                       ; (i = i1) → (B , idEquiv B) })

    module ExampleEquiv where
        data Bool : Set where 
            tt ff : Bool 
        
        not : Bool → Bool 
        not tt = ff 
        not ff = tt 

        {- 
            Definition of equivalence
                record isEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
                    field
                        equiv-proof : (y : B) → isContr (fiber f y)


            Definition of contractible
                isContr : ∀ {ℓ} → Set ℓ → Set ℓ
                isContr A = Σ A (λ x → (∀ y → x ≡ y))

            Definition of fiber
                fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ ⊔ ℓ')
                fiber {A = A} f y = Σ A (λ x → f x ≡ y)


        -}
    
        data Empty : Set where
        data Unit : Set where unit : Unit
        -- can no longer use the 'absurd' pattern??
        huh : ff ≡ tt → Empty 
        huh p = subst f p unit
            where 
                f : Bool → Set 
                f tt = Empty 
                f ff = Unit

        exfalso : {A : Set} → Empty → A 
        exfalso ()

        tt-fiber : fiber not tt 
        tt-fiber = ff , refl

        ff-fiber : fiber not ff 
        ff-fiber = tt , refl

        Σ-eq : {A : Set}{F : A → Set}{a b : A} → 
            (p : a ≡ b)→ 
            { r : F a} {s : F a}
            (w : r ≡ s) → 
            ( (a , r) ≡ (b , s))
        Σ-eq p w = λ i → p i , w i

        tt-fiber-contr : isContr (fiber not tt)
        tt-fiber-contr = tt-fiber , λ{ (tt , ff≡tt) → {! Σ-eq{Bool}{?}{ff}{tt} ? ?  !}
                                     ; (ff , tt≡tt) → {! Σ-eq refl refl   !}}


        not≃ : isEquiv not 
        not≃ = record {
             equiv-proof = λ{ tt → tt-fiber-contr
                            ; ff → {!   !} }
            }
            
        -- Give up on getting an equivalence from contractable fiber.. 
        open import Cubical.Foundations.Isomorphism using (isoToEquiv ; Iso ; iso)


        notnot : ∀ x → not (not x) ≡ x 
        notnot tt = refl 
        notnot ff = refl
        
        notIso : Iso Bool Bool
        notIso = iso 
                    not 
                    not
                    notnot 
                    notnot

        _ : Bool ≃ Bool 
        _ = isoToEquiv notIso

        -- get an equivalence because `not` is an involution
        -- isInvolution f = ∀ x → f (f x) ≡ x
        open import Cubical.Functions.Involution using (involIsEquiv)
        not≃' : isEquiv not 
        not≃' = involIsEquiv notnot


        beq : Bool ≃ Bool 
        beq = not , not≃'

        _ : transport (ua beq) ff ≡ tt -- tt ≡ tt
        _ = refl

        -- there are 2 equivalences on Bool
        -- id and not

    isProp : Set → Set 
    isProp A = (x y : A) → x ≡ y 

    isSet : Set → Set 
    isSet A = (x y : A) → isProp (x ≡ y)

    data Unit : Set where unit : Unit

    _ : isProp Unit 
    _ = λ { unit unit → refl }

   -- _ : isSet Unit 
   -- _ = λ {unit unit  → λ u≡u u≡u' → λ i j → {! unit  !} }
    -- can't just pattern match on refl anymore since equality types can have more inhabitants  


    module _ where
        -- propositional trunctaion
        data ∥_∥ (A : Set) : Set where 
            inj : A → ∥ A ∥ 
            squash : (x y : ∥ A ∥) → x ≡ y

        tmap : {A B : Set}→ (A → B) → ∥ A ∥ → ∥ B ∥
        tmap f (inj x) = inj (f x)
        tmap f (squash x y i) = squash (tmap f x) (tmap f y) i

    module SIP where 
        -- Structure is a function S : Type → Type 
        TypeWithStr : (Set₀ → Set₀) → Set₁ 
        TypeWithStr S = Σ Set₀ S

        -- Structure preserving equivalences
        StrEquiv : (Set₀ → Set₀) → Set₁
        StrEquiv S = (A B : TypeWithStr S) → fst A ≃ fst B → Set₀

        _≃_[_] : {S : Set₀ → Set₀} (A B : TypeWithStr S)(ι : StrEquiv S) → Set₀
        A ≃ B [ ι ] = Σ (fst A ≃ fst B) λ e → ι A B e

        UnivalentStr : (S : Set₀ → Set₀) → StrEquiv S → Set₁
        UnivalentStr S ι = {A B : TypeWithStr S}(e : fst A ≃ fst B) → 
                (ι A B e) ≃ PathP (λ i → S (ua e i)) (snd A) (snd B)

        SIP : {S : Set₀ → Set₀}{ι : StrEquiv S} → UnivalentStr S ι → (A B : TypeWithStr S) → 
            (_≃_[_] A B ι) ≃ (A ≡ B)
        SIP = {!   !} 

        sip : {S : Set₀ → Set₀}{A B : TypeWithStr S}{ι : StrEquiv S}{θ : UnivalentStr S ι} → (_≃_[_] A B ι) → A ≡ B
        sip{S}{A}{B}{ι}{θ} (e , p) i = (ua e i) , equivFun (θ e) p i

        module SIP-Ex where
            RawMonoidStructure : Set₀ → Set₀
            RawMonoidStructure X = X × (X → X → X)

            RawMonoid : Set₁
            RawMonoid = TypeWithStr RawMonoidStructure

            MonoidAxioms : RawMonoid → Set 
            MonoidAxioms (X , ε , _⋆_) = (isSet X) 
                                        × (∀ x y z → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z)
                                        × (∀ x → (x ⋆ ε ≡ x) × (ε ⋆ x ≡ x))
            
            MonoidStructure : Set₀ → Set₀
            MonoidStructure X = Σ (RawMonoidStructure X) λ{( ε , _⋆_) → MonoidAxioms (X , ε , _⋆_)}

            Monoid : Set₁
            Monoid = TypeWithStr MonoidStructure

            
            MonoidEquiv : (M N : Monoid) → fst M ≃ fst N → Set 
            MonoidEquiv (_ , (εₘ , _⋆ₘ_) , _) (_ , (εₙ , _⋆ₙ_), _ ) (ϕ , _) =
                 -- monoid homomorphism
                 (ϕ εₘ ≡ εₙ) -- 
                 × (∀ x y → ϕ (x ⋆ₘ y) ≡ ϕ x ⋆ₙ ϕ y)

            _ : UnivalentStr RawMonoidStructure {!   !}
            _ = {!   !}

        module buildingStructures where
            data Structures (S T : Set₀ → Set₀)(X : Set₀): Set₁ where 
                var : X → Structures S T X
                const : (A : Set₀) → Structures S T X
                prod : S X × T X → Structures S T X
                fun : (S X → T X) → Structures S T X
                may : Maybe (S X) → Structures S T X 
