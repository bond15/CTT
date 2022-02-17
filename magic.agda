module magic where

-- Uses Agdas reflection mechanism and generic programming 
-- to automatically generate definitions of..
-- structured equivalences
-- proofs that they are univalent
-- See https://github.com/agda/cubical/blob/master/Cubical/Papers/RepresentationIndependence.agda
-- and Internalizing Representation Independence with Univalence
-- for details

import Cubical.Foundations.Prelude as Prelude
open Prelude using (_≡_ ; isSet ; ℓ-zero ; isProp ; refl ; cong ; J ; Lift)
import Cubical.Foundations.HLevels             as HLevels
open HLevels using (isPropΠ) public
import Cubical.Structures.Auto as Auto
open Auto using (AutoEquivStr ; autoUnivalentStr)
import Cubical.Algebra.Semigroup.Base          as Semigroup
import Cubical.Structures.Axioms as Axioms
open Axioms using (AxiomsStructure ; AxiomsEquivStr ; axiomsUnivalentStr)
import Cubical.Foundations.SIP as SIP
open SIP using (TypeWithStr ; UnivalentStr ; _≃[_]_ ; StrEquiv ; SIP ; typ)
import Cubical.Foundations.Equiv as Equivalences
open Equivalences using (_≃_)
open import Cubical.Data.Sigma.Base



{-
Univalence for structures


SIP : A ≃[ ι ] B ≃ (A ≡ B)
  in the context
    {S : Type ℓ₁ → Type ℓ₂} {ι : StrEquiv S ℓ₃}
    (θ : UnivalentStr S ι) (A B : TypeWithStr ℓ₁ S)

with the specific example in mind
  (M N : Monoid) → (M ≃[ MonoidEquivStr ] N) ≃ (M ≡ N)



All of the following is to provide a framework for the following idea

InducedMonoid : (M : Monoid) (N : RawMonoid) (e : typ M ≃ typ N ) → RawMonoidEquivStr (Monoid→RawMonoid M) N e → Monoid

-}


-- A Raw Monoid on for carrier X is a neutral element and a binary operation
RawMonoidStructure : Set₀ → Set₀ 
RawMonoidStructure X = X × (X → X → X)

-- Monoid axioms take in a carrier M, a neutral element, and a binary operation
-- It returns the type representing all the laws a raw monoid should obey
MonoidAxioms : (M : Set₀) → RawMonoidStructure M → Set₀
MonoidAxioms M (e , _·_) = Semigroup.IsSemigroup _·_
                         × ((x : M) → (x · e ≡ x) × (e · x ≡ x))


-- AxiomsStructure S axioms X = Σ[ s ∈ S X ] (axioms X s)
-- An axiom structure is a pair
-- in this case, a monoid s and a proof that s obeys the monoid laws
MonoidStructure : Set₀ → Set₀
MonoidStructure = AxiomsStructure RawMonoidStructure MonoidAxioms


{-
TypeWithStr : (ℓ : Level) (S : Type ℓ → Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
TypeWithStr ℓ S = Σ[ X ∈ Type ℓ ] S X
-}
Monoid : Set₁
Monoid = TypeWithStr _ MonoidStructure

RawMonoid : Set₁
RawMonoid = TypeWithStr _ RawMonoidStructure

Monoid→RawMonoid : Monoid → RawMonoid
Monoid→RawMonoid (A , (op , e ) , _) = A , (op , e)

-- Derived..
RawMonoidEquivStr = AutoEquivStr RawMonoidStructure -- This derives Monoid homomorphism
{-
-- An S-structure should have a notion of S-homomorphism, or rather S-isomorphism.
-- This will be implemented by a function ι : StrEquiv S ℓ'
-- that gives us for any two types with S-structure (X , s) and (Y , t) a family:
--    ι (X , s) (Y , t) : (X ≃ Y) → Type ℓ''
StrEquiv : (S : Type ℓ → Type ℓ'') (ℓ' : Level) → Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓ')) ℓ'')
StrEquiv {ℓ} S ℓ' = (A B : TypeWithStr ℓ S) → typ A ≃ typ B → Type ℓ'
-}



{-
Roughly, this derives univalence for a particular structure

UnivalentStr : (S : Type ℓ₁ → Type ℓ₂) (ι : StrEquiv S ℓ₃) → Type (ℓ-max (ℓ-max (ℓ-suc ℓ₁) ℓ₂) ℓ₃)
UnivalentStr {ℓ₁} S ι =
  {A B : TypeWithStr ℓ₁ S} (e : typ A ≃ typ B)
  → ι A B e ≃ PathP (λ i → S (ua e i)) (str A) (str B)
-}
rawMonoidUnivalentStr : UnivalentStr _ RawMonoidEquivStr
rawMonoidUnivalentStr = autoUnivalentStr RawMonoidStructure
{-
IGNORE


isPropMonoidAxioms : (M : Set₀) (s : RawMonoidStructure M) → isProp (MonoidAxioms M s)
isPropMonoidAxioms M (e , _·_) =
  HLevels.isPropΣ
    (Semigroup.isPropIsSemigroup _·_)
    (λ α → isPropΠ λ _ →
      HLevels.isProp×
        (Semigroup.IsSemigroup.is-set α _ _)
        (Semigroup.IsSemigroup.is-set α _ _))


MonoidEquivStr : StrEquiv MonoidStructure ℓ-zero
MonoidEquivStr = AxiomsEquivStr RawMonoidEquivStr MonoidAxioms

monoidUnivalentStr : UnivalentStr MonoidStructure MonoidEquivStr
monoidUnivalentStr = axiomsUnivalentStr _ isPropMonoidAxioms rawMonoidUnivalentStr

MonoidΣPath : (M N : Monoid) → (M ≃[ MonoidEquivStr ] N) ≃ (M ≡ N)
MonoidΣPath = SIP monoidUnivalentStr
-}
InducedMonoid : (M : Monoid) (N : RawMonoid) (e : typ M ≃ typ N )
                → RawMonoidEquivStr (Monoid→RawMonoid M) N e → Monoid
InducedMonoid M N e r =
  Axioms.inducedStructure rawMonoidUnivalentStr M N (e , r)


-- Now for an example

module Example where

    open import Data.Bool renaming (_∧_ to _&_ ; _∨_ to _||_)

    data ⊥ : Set where 
    
    -- what is going on in this isSet proof??
    K-Bool : 
        {ℓ : Level}
        (P : {b : Bool} → b ≡ b → Set ℓ) → 
        (∀ {b} → P {b} refl) → 
        ∀ {b} → (q : b ≡ b) → P q 
    K-Bool P Prefl {false} = J (λ { false q → P q
                                  ; true _ → Lift ⊥}) Prefl
    K-Bool P Prefl {true} = J (λ{ false _ → Lift ⊥
                                ; true q → P q }) Prefl

    {-
    isProp : Type ℓ → Type ℓ
    isProp A = (x y : A) → x ≡ y

    isSet : Type ℓ → Type ℓ
    isSet A = (x y : A) → isProp (x ≡ y) 
    -}
    𝔹-isSet : isSet Bool 
    𝔹-isSet a b = J (λ _ p → ∀ q → p ≡ q) (K-Bool (refl ≡_) refl)

    &-assoc : ∀ x y z → x & (y & z) ≡ (x & y) & z 
    &-assoc false y z = refl
    &-assoc true y z = refl

    &-zero : ∀ x → x & true ≡ x 
    &-zero false = refl
    &-zero true = refl
    
    -- Proof that (Bool, true, _&_) is a monoid
    𝔹∧-Monoid : Monoid 
    𝔹∧-Monoid = Bool , (true , _&_) , 
        Semigroup.issemigroup 𝔹-isSet &-assoc , λ x → &-zero x , refl

    𝔹∨-Raw : RawMonoid
    𝔹∨-Raw = Bool , false , _||_

    open import Cubical.Foundations.Isomorphism using (isoToEquiv ; iso ; Iso)

    {- don't use this equivalence
    -- because it breaks the monoid homomorphism
    𝔹≃𝔹' : Bool ≃ Bool 
    𝔹≃𝔹' = isoToEquiv (iso 
                        (λ x → x) 
                        (λ x → x) 
                        (λ b → refl) 
                        (λ b → refl))
    -}


    -- an involution
    notnot : ∀ x → not (not x) ≡ x 
    notnot true = refl
    notnot false = refl

    𝔹≃𝔹 : Bool ≃ Bool 
    𝔹≃𝔹 = isoToEquiv (iso 
                        not 
                        not
                        notnot 
                        notnot)

    DeMorgan : ∀ a b → not (a & b) ≡ not a || not b 
    DeMorgan false b = refl
    DeMorgan true b = refl 

    -- monoid homomorphisms (on raw)
    monoidHomo : RawMonoidEquivStr (Monoid→RawMonoid 𝔹∧-Monoid) 𝔹∨-Raw 𝔹≃𝔹
    monoidHomo = -- not ε∧ ≡ ε∨ 
                 -- not true ≡ false  Check!
                refl      
                -- not (s & t) ≡ not s || not t
                -- DeMorgan's law  Check!
                , DeMorgan  
                   
    B∨-Monoid : Monoid
    B∨-Monoid = InducedMonoid 𝔹∧-Monoid 𝔹∨-Raw 𝔹≃𝔹 monoidHomo
   -- Proof that (Bool, false. _||_) is a monoid given:
   -- A proof that (Bool, true, _&_) is a monoid
   -- Raw monoid (Bool, false, _||_)
   -- An equivalence that obeys the monoid homomorpism
   -- a raw monoid homomorphism between the two structures
    open Semigroup.IsSemigroup

    -- derived proof of the monoid laws from the induced monoid
    _ : ∀ x y z → x || (y || z) ≡ (x || y) || z 
    _ = B∨-Monoid .snd .snd .fst .assoc

    _ : ∀ x → ((x || false) ≡ x) × ((false || x) ≡ x)
    _ = B∨-Monoid .snd .snd .snd 