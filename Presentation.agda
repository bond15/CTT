module Presentation where 

{-


Topics
    Agda
    Cubical Agda
        Interval / Paths
        Univalence
        Transport w/ univalence
        HITs
    Structure Identity Principle 

https://arxiv.org/pdf/2009.05547.pdf
































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
    



    data Foo : Set where
        foo : Foo
    data Bar : Set where 
        bar : Bar

    _ : Foo ≡ Bar
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

        An interval is a "Type" with 2 end points, i0 and i1.

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

    -- Equality types are defined using path types
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
    -- constant path
    refl' : {ℓ : Level}{A : Set ℓ}{a : A} → Path A a a
    refl' {a = a} = λ i → a   

    -- alternatively, since we know Path A a a is a ≡ a..
    refl : {ℓ : Level}{A : Set ℓ}{a : A} → a ≡ a
    refl {a = a} = λ i → a   

    -- inversion of paths
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
    -- concatenation of paths
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

    -- heres something you can't prove in Coq

    data Foo : Set where
        foo : Foo
    data Bar : Set where 
        bar : Bar

    -- Show Foo ≡ Bar
    
    -- recall univalence says (A ≃ B) ≃ (A ≡ B)
    isofb : Iso Foo Bar 
    isofb = iso 
        (λ{ foo → bar })  
        (λ{ bar → foo })
        (λ{ bar → refl})
        (λ{ foo → refl})

    _ : Foo ≡ Bar
    _ = ua (isoToEquiv isofb)
    {-
    -- The ua constant
    ua : ∀ {A B : Type ℓ} → A ≃ B → A ≡ B
    ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                       ; (i = i1) → (B , idEquiv B) }) 
    -}



    -- Types can be equal through different equivalences (example Bool)
    open import Data.Bool using (Bool ; true ; false)

    data Bool' : Set where 
        t f : Bool'

    equiv₁ : Iso Bool Bool'
    equiv₁ = iso 
                (λ{ false → f
                  ; true → t})
                (λ{ t → true
                  ; f → false})
                (λ{t → refl
                 ; f → refl})
                λ{ false → refl
                 ; true → refl } 

    _ : Bool ≡ Bool'
    _ = isoToPath equiv₁

    equiv₂ : Iso Bool Bool'
    equiv₂ = iso 
                (λ{ false → t
                  ; true → f})
                (λ{ t → false
                  ; f → true})
                (λ{t → refl
                 ; f → refl})
                λ{ false → refl
                 ; true → refl } 

    _ : Bool ≡ Bool'
    _ = isoToPath equiv₂

{- ignore
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

    -- Coq eq_rect
    huh : ( n : ℕ) → (a : ty (n + 1)) →  (b : ty (1 + n)) → PathP (λ i → tyeq {n} i) a b
    huh n c c i = transp (λ j → tyeq {n} (i ∧ j) ) ( ~ i ) c
    
    
    Inductive ty (n : nat) : Type := c.
    Lemma bar : forall (n : nat)(a : ty (n+1)) (b : ty (1 +n)), @eq_rect nat (n + 1) ty a (1 + n) (np1 n) = b.
    Proof.
      intros. destruct (eq_rect (n + 1) ty a (1 + n) (np1 n)). destruct b. reflexivity.
    Qed.
    where bar = 
    fun (n : nat) (a : ty (n + 1)) (b : ty (1 + n)) =>
    let t : ty (1 + n) := eq_rect (n + 1) ty a (1 + n) (np1 n) in
    match t as t0 return (t0 = b) with
    | c _ => match b as t0 return (c (1 + n) = t0) with
             | c _ => eq_refl
             end
    end
    -}







































-- Transporting operations and proofs across equality/paths

module Bools where 
    open import Cubical.Core.Everything
    open import Cubical.Foundations.Prelude using (refl)
    
    data Bool : Set where 
        tt ff : Bool

    data FooBar : Set where 
        Foo Bar : FooBar

    not : Bool → Bool 
    not tt = ff
    not ff = tt

    nn : ∀ (b : Bool) → not (not b) ≡ b 
    nn = λ{ tt → refl
          ; ff → refl }

    open import Cubical.Foundations.Isomorphism

    -- show that Bool and FooBar are isomorphic types
    BoolFooIso : Iso Bool FooBar
    BoolFooIso = iso 
                    (λ{ tt → Foo
                    ; ff → Bar})
                    
                    (λ{ Foo → tt
                    ; Bar → ff}) 
                    
                    (λ{ Foo → refl
                    ; Bar → refl })
                    
                    λ{tt → refl 
                    ; ff → refl}

    -- Isomorphic types are equivalent               
    eqT : Bool ≡ FooBar
    eqT = isoToPath BoolFooIso

    -- define transport (think transfer in isabelle)
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


    -- tranporting the proof (not (not b) ≡ b) over the equivalence
    _ : ∀ (fb : FooBar) → not' (not' fb) ≡ fb 
    _ = transport ((λ i → (x : eqT i) → noteq i (noteq i x) ≡ x)) nn





















-- HIT
module HITs where
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.Isomorphism
    open import Agda.Builtin.Nat
    

    -- HITs are types that can also specify equations/paths


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
    import Cubical.Foundations.HLevels as HLevels
    open HLevels using (isPropΠ) public
    import Cubical.Structures.Auto as Auto
    open Auto using (AutoEquivStr ; autoUnivalentStr)
    import Cubical.Algebra.Semigroup.Base as Semigroup
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

    -- "forgetful" mapping, drops the axioms
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
        given,
            a monoid M
            a raw monoid N
            an equivalence between the carriers of N and M
            a monoid homomorphism between N and the underlying raw monoid of M..

            transfer the monoid laws from M to N
    -}
    InducedMonoid : (M : Monoid) (N : RawMonoid) (e : typ M ≃ typ N )
                    → RawMonoidEquivStr (Monoid→RawMonoid M) N e → Monoid
    InducedMonoid M N e r = Axioms.inducedStructure rawMonoidUnivalentStr M N (e , r)


    -- Now for an example

    module Example where

        open import Data.Bool renaming (_∧_ to _&_ ; _∨_ to _||_)

        data ⊥ : Set where 
        
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


{- 
    Bonus
        Observational Type Theory - Altenkirch McBride is making a comeback
-}
  