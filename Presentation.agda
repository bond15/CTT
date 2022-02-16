module Presentation where 

{-


Topics

Agda ~ Dependent type theory

    Agda
        Refl
        Sym
        Trans

-}
module Agda where 
    open import Agda.Primitive

    -- Everything is Refl!
    data _≡_ {ℓ : Level} {A : Set ℓ} : A → A → Set ℓ where 
        refl : {a : A } → a ≡ a 

    data Unit : Set where 
        unit : Unit

    -- iterated Identity types
    _ : (unit ≡ unit)
    _ = refl

    _ : (unit ≡ unit) ≡ (unit ≡ unit)
    _ = refl

    _ : ((unit ≡ unit) ≡ (unit ≡ unit)) ≡ ((unit ≡ unit) ≡ (unit ≡ unit))
    _ = refl

    sym : {A : Set} → ∀ {x y : A} → (x ≡ y) → (y ≡ x)
    sym refl = refl

    trans : {A : Set} → ∀{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
    trans refl refl = refl

    -- cong
    ap : {A B : Set}{x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
    ap f refl = refl



    _ : Unit ≡ Unit
    _ = refl
    
    data Unit' : Set where 
        unit' : Unit'
    _ : Unit ≡ Unit'
    _ = {!   !} --can't prove

    -- Axiom
    postulate
        extensionality : ∀ {A B : Set }{f g : A -> B}
            -> (∀ (x : A) -> f x ≡ g x)
            ---------------------------
            -> f ≡ g
    postulate 
        Extensionality : {A : Set } {B : A → Set } {f g : (x : A) → B x} 
            → (∀ x → f x ≡ g x) → f ≡ g

    transport : {A : Set}{P : A → Set} → ∀(x y : A)→ (p : x ≡ y ) → P x → P y
    transport {A} {P} x y refl = λ x → x

        -- Predicate is the "logical" interpretation of X → Set
    J : {A : Set} → 
        ∀ (P : ∀(x y : A)→ (x ≡ y → Set)) → -- forall Predicates "P" over x ≡ y
            (Prefl : ∀ (x : A)→ P x x refl) →  -- a proof "Prefl : P refl" at refl : x ≡ x
            (∀ (x y : A)(p : x ≡ y) → P x y p) -- suffices to show a proof "P p" for any p : x ≡ y
    J P Prefl x x refl = Prefl x


{- 

What is Cubical Agda?
    Where is this `cubical` stuff coming from?

    In HoTT, they talk about paths.. but they don't talk about the structure of those paths..

        When it comes to typechecking, the notion of path needs to be concrete.
        More importantly, equations about paths need to be decidable so that typechecking is decidable.

        Unrestricted paths are a non starter. (something about undecidable)

            The model of type theory with the Univalence Axiom given by Voevodsky [15] is based on Kan
            simplicial sets. A problem with a constructive approach to Kan simplicial sets is that degeneracy is in
            general undecidable [3]. This problem makes it impossible to use the Kan simplicial set model as it is to
            obtain a computational interpretation of univalence.
                https://www.cse.chalmers.se/~coquand/mod1.pdf

        Instead, it was found that Cubical Sets give a computational interpretation of univalence.

        So paths in CTT involve reasoning about n-cubes.

        Cubical agda Extends Contexts with an Interval "Sort/Type?" (Not a Type, it has special rules about pattern matching etc.)

        An interval is a "Type" with 2 end points, 0 and 1.

-}
module Interval where
    open import Cubical.Core.Everything
    
    -- endpoints
    _ : I
    _ = i0

    _ : I 
    _ = i1

    -- operations on Intervals (deMorgan algebra)

    _ : I 
    _ = i0 ∨ i1

    _ : I 
    _ = i0 ∧ i1

    _ : I 
    _ = ~ i0

    -- Path types
    -- Paths are defined as lambdas from intervals into a type

    open import Data.Bool
    -- There is a path in Bool from true to true
    -- The endpoints 1 and 0 are both `true`
    ex₁ : Path Bool true true 
    ex₁ =  λ i → true 

    -- we can observe that the path sampled at 0 is `true`
    _ : ex₁ i0 ≡ true
    _ = λ i → true 

    -- and that the path sampled at 1 is 'true'
    _ : ex₁ i1 ≡ true 
    _ = λ i → true 



    data Unit : Set where 
        tt : Unit
    
    --line : Path Unit tt tt
    line : tt ≡ tt
    line =  λ i → tt  

    --square : Path ( Path Unit tt tt ) line line
    square : line ≡ line
    square = λ i j → tt

    --cube : Path (Path ( Path Unit tt tt ) line line) square square
    cube : square ≡ square
    cube = λ i j k → tt

    -- Equality types are defined using dependent path types
    {-
        _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
        _≡_ {A = A} = PathP (λ i → A) 


            -- Non dependent path types

            --Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
            --Path A a b = PathP (λ _ → A) a b

            --where
            --This is builtin
            --PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

    -}

    -- so lets now define refl, sym, and trans
    refl' : {ℓ : Level}{A : Set ℓ}{a : A} → Path A a a
    refl' {ℓ}{A}{a}= λ i → a   

    -- alternatively, since we know Path A a a is a ≡ a..
    refl : {ℓ : Level}{A : Set ℓ}{a : A} → a ≡ a
    refl {ℓ}{A}{a}= λ i → a   

    sym : {ℓ : Level}{A : Set ℓ}{a b : A} → a ≡ b → b ≡ a
    sym = λ p i → p ( ~ i )  

    {-
       x ∙ ∙ ∙ > w
       ^         ^
   p⁻¹ |         | r        ^
       |         |        j |
       y — — — > z          ∙ — >
            q                 i

   `p ∙∙ q ∙∙ r` gives the line at the top,


       a ∙ ∙ ∙ > c
       ‖         ^
  refl ‖         | r        ^
       ‖         |        j |
       a — — — > b          ∙ — >
            q   

    -}
    open import Cubical.Foundations.Prelude  using (_∙∙_∙∙_)
    trans : {ℓ : Level}{A : Set ℓ}{a b c : A} → a ≡ b → b ≡ c → a ≡ c 
    trans = λ q r → (refl ∙∙ q ∙∙ r)



    -- cong
    cong : {A : Type} {B : A → Type} 
        (f : (a : A) → B a)
        {x y : A}
        (p : x ≡ y) 
        → PathP (λ i → B (p i)) (f x) (f y)
    cong f p i = f (p i)

    -- Extensionality is now inhabited/provable (where previously it had to be assumed as an axiom)
    funExt : {A B : Set} 
            {f g : A → B} → 
            ((x : A) → f x ≡ g x) → 
            f ≡ g 
    funExt p i a = p a i
    
    transport : {A B : Set} → A ≡ B → A → B 
    transport p a = transp ((λ i → p i)) i0 a

    subst : {A : Set} → 
        ( B : A → Set) → 
        {x y : A} → 
        x ≡ y → 
        B x → B y 
    subst B p bx = transport (λ i → B (p i)) bx




-- ua
module univalence where
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.Univalence using (ua)
    open import Cubical.Foundations.Isomorphism using (isoToPath ; isoToEquiv ; Iso ; iso)



    data Foo : Set where
        foo : Foo
    data Bar : Set where 
        bar : Bar
    
    {-
    -- The ua constant
    ua : ∀ {A B : Type ℓ} → A ≃ B → A ≡ B
    ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                       ; (i = i1) → (B , idEquiv B) }) 
    -}
    isofb : Iso Foo Bar 
    isofb = iso 
        (λ{ foo → bar })  
        (λ{ bar → foo })
        (λ{ bar → refl})
        (λ{ foo → refl})

    _ : Foo ≡ Bar
    _ = ua (isoToEquiv isofb)


    open import Data.Nat
    open import Data.List
    open import Data.Product
    listn : ℕ → Set₀ 
    listn n = Σ (List ℕ) (λ l → length l ≡ n)

    np1 : {n : ℕ} → n + 1 ≡ 1 + n 
    np1 = {!   !}

    data ty (n : ℕ) : Set₀ where 
        c : ty n

    tyeq : {n : ℕ} → (ty (n + 1)) ≡ (ty( 1 + n))
    tyeq = cong ty np1
    open import Cubical.Core.Everything

    -- something we can't write in coq? (or w/o eq_rect)
    huh : ( n : ℕ) → (a : ty (n + 1)) →  (b : ty (1 + n)) → PathP (λ i → tyeq {n} i) a b
    huh n c c i = transp (λ j → tyeq {n} (i ∧ j) ) ( ~ i ) c

    listnp1 : {n : ℕ} → (listn (n + 1)) ≡ (listn (1 + n))
    listnp1 = cong listn np1

    omg : ( n : ℕ) → (a : listn (n + 1)) →  (b : listn (1 + n)) → PathP (λ i → listnp1  {n} i) a b
    omg n (x , prf1) (y , prf2)  i =  {!   !}



-- CTTeq example

-- HIT
module HITs where
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.Isomorphism
    open import Agda.Builtin.Nat
    

    data Int : Type where
        pos : Nat → Int
        neg : Nat → Int
        zro : pos 0 ≡ neg 0

    succ : Int → Int
    succ (pos x) = pos (suc x)
    succ (neg 0) = pos 1
    succ (neg (suc x)) = neg x
    succ (zro i) = pos 1
    -- last pattern is subject to the constraint 
    --  f (p i0) ≐ f (p i1)  where ≐ denotes definitional equality
    -- or 
    -- succ (pos 0) ≐ succ (neg 0)

    -- asymetric integer type
    data Int' : Type where
        pos' : Nat → Int' 
        neg' : Nat → Int'

    asym→sym : Int' → Int 
    asym→sym (pos' x) = pos x
    asym→sym (neg' x) = neg (suc x)

    sym→asym : Int → Int' 
    sym→asym (pos x) = pos' x
    sym→asym (neg 0) = pos' 0
    sym→asym (neg (suc x)) = neg' x
    sym→asym (zro i) = pos' 0


    isoint : Iso Int Int'
    isoint = iso 
        sym→asym 
        asym→sym 
        (λ{ (pos' x) → refl
          ; (neg' x) → refl}) 
        (λ{ (pos x) → refl
          ; (neg zero) → zro
          ; (neg (suc x)) → refl
          ; (zro i) → λ j → zro (i ∧ j)})

    inteq : Int ≡ Int'
    inteq = isoToPath isoint

-- SIP



{- 
    Bonus
        Observational Type Theory - McBride 2006 is making a comeback
-}