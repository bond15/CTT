module Cat where
-- definitions taken from 1Lab

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Data.Nat using (ℕ ; zero ; suc)
open import Agda.Primitive using (Level ; lsuc ; _⊔_)

-- hlevels

record is-contr {ℓ} (A : Set ℓ) : Set ℓ where
    constructor contr 
    field 
        centre : A 
        paths : (x : A) → centre ≡ x
open is-contr public

is-prop : ∀{ℓ} → Set ℓ → Set _ 
is-prop A = (x y : A) → x ≡ y  

is-hlevel : ∀{ℓ} → Set ℓ → ℕ → Set _ 
is-hlevel A 0 = is-contr A
is-hlevel A 1 = is-prop A
is-hlevel A (suc n) = (x y : A) → is-hlevel (x ≡ y) n

is-set : ∀{ℓ} → Set ℓ → Set ℓ 
is-set A = is-hlevel A 2

is-groupoid : ∀{ℓ} → Set ℓ → Set ℓ 
is-groupoid A = is-hlevel A 3


module hlevelExamples where 
    data ⊤ : Set where 
        t : ⊤

    _ : is-contr ⊤
    _ = contr t λ{ t → refl}

    _ : is-prop ⊤
    _ = λ{ t t → refl}

    _ : is-set ⊤ -- how do you prove this?
    _ = λ{ t t x≡y₁ x≡y₂ → {! refl !}}

{-
    i0,j1          i1,j1


    i0,j0          i1, j0


    left wall is specified by i = 0, j varies
    right wall is specified by i = 1, j varies
    bottom is specified by j = 0 , i varies
-}

    eq-centre : {A : Set} → (C : is-contr A) → (x : A) → C .centre ≡ x
    eq-centre C x = C .paths x

    is-contr→is-prop : {A : Set} → is-contr A → is-prop A 
    is-contr→is-prop C x y i = hcomp (λ{ j → λ{ (i = i0) → eq-centre C x j
                                             ;  (i = i1) → eq-centre C y j}}) (C .centre) 
                                             -- show x ≡ y when you have that centre ≡ x , centre ≡ y , and centre ≡ centre, fill in the lid of the square

    is-prop→is-set : {A : Set} → is-prop A → is-set A 
    is-prop→is-set h x y p q i j = hcomp (λ k → λ{ (i = i0) → h x (p j) k 
                                                    ; (i = i1) → h x (q j) k 
                                                    ; (j = i0) → h x x k
                                                    ; (j = i1) → h x y k }) x 

record PreCat (o h : Level) : Set (lsuc (o ⊔ h)) where 
    field 
        Ob : Set o
        Hom : Ob → Ob → Set h
        Hom-set : (x y : Ob) → is-set (Hom x y) -- if p : x ≡ y, q : x ≡ y, then p ≡ q
        id : ∀ {x} → Hom x x
        _∘_ : ∀{x y z} → Hom y z → Hom x y → Hom x z

        idr : ∀{x y} → (f : Hom x y) → f ∘ id ≡ f 
        idl : ∀{x y} → (f : Hom x y) → id ∘ f ≡ f
        assoc : ∀{w x y z} → (f : Hom y z)(g : Hom x y)(h : Hom w x) → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
    infixr 40 _∘_

_≡˘⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ≡˘⟨ p ⟩ q = (sym p) ∙ q

-- tools for reasoning about composition of "2 morphisms"/ commuting squares
module CompSqr {o ℓ} (C : PreCat o ℓ) where 
    open PreCat C

    private variable
        x y : Ob 
        f g h i a b c : Hom x y

    module _ (ab≡c : a ∘ b ≡ c) where 
        pulll : a ∘ (b ∘ f) ≡ c ∘ f
        pulll {f = f} = 
            (a ∘ (b ∘ f)) ≡⟨ assoc a b f ⟩ 
            ((a ∘ b) ∘ f ) ≡⟨ cong (_∘ f) ab≡c ⟩ 
            c ∘ f ∎

        pullr : (f ∘ a) ∘ b ≡ f ∘ c 
        pullr {f = f} = 
            ((f ∘ a) ∘ b) ≡˘⟨ assoc f a b ⟩ 
            ((f ∘ (a ∘ b)) ≡⟨ cong (f ∘_) ab≡c ⟩ 
            f ∘ c ∎)

    module _ (p :  f ∘ h ≡ g ∘ i) where
        extendl : f ∘ (h ∘ b) ≡ g ∘ (i ∘ b)
        extendl {b = b} = 
            (f ∘ (h ∘ b)) ≡⟨ assoc f h b ⟩ 
            ((f ∘ h) ∘ b) ≡⟨ cong (_∘ b) p ⟩ 
            (((g ∘ i) ∘ b) ≡˘⟨ assoc g i b ⟩ 
            (g ∘ (i ∘ b) ∎))

        extendr : (a ∘ f) ∘ h ≡ (a ∘ g) ∘ i 
        extendr {a = a} = 
            ((a ∘ f) ∘ h) ≡˘⟨ assoc a f h ⟩ 
            ((a ∘ (f ∘ h)) ≡⟨ cong (a ∘_) p ⟩ 
            (a ∘ (g ∘ i)) ≡⟨ assoc a g i ⟩ 
            (a ∘ g) ∘ i ∎)




record Functor {o₁ h₁ o₂ h₂} (C : PreCat o₁ h₁) (D : PreCat o₂ h₂) : Set (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂) where 
    no-eta-equality 
    private 
        module C = PreCat C 
        module D = PreCat D
    field
        F₀ : C.Ob → D.Ob 
        F₁ : ∀{x y} → C.Hom x y → D.Hom (F₀ x) (F₀ y)

        F-id : ∀{x} → F₁ (C.id {x}) ≡ D.id
        F-∘ : ∀{x y z} → (f : C.Hom y z)(g : C.Hom x y ) → F₁ (f C.∘ g) ≡ (F₁ f) D.∘ (F₁ g)

record _⇒_ {o₁ h₁ o₂ h₂} {C : PreCat o₁ h₁}{D : PreCat o₂ h₂}(F G : Functor C D) : Set (o₁ ⊔ h₁ ⊔ h₂) where 
    no-eta-equality
    constructor NT 
    private 
        open Functor F 
        open Functor G renaming (F₀ to G₀ ; F₁ to G₁)
        module D = PreCat D 
        module C = PreCat C 
    field 
        η : (x : C.Ob) → D.Hom (F₀ x) (G₀ x)
        is-natural : (x y : C.Ob) (f : C.Hom x y) → (η y) D.∘ (F₁ f) ≡ (G₁ f) D.∘ (η x)


_F∘_ : {o₁ h₁ o₂ h₂ o₃ h₃ : Level} → {B : PreCat o₁ h₁}{C : PreCat o₂ h₂}{D : PreCat o₃ h₃}
    → Functor C D → Functor B C → Functor B D 
_F∘_ {B = B} {C} {D} F G = comps -- note usage of {B = B} here starts the implicit arguments at B 
                                 -- instead of o₁
    where 
        module B = PreCat B
        module C = PreCat C 
        module D = PreCat D 

        open Functor F 
        open Functor G renaming (F₀ to G₀ ; F₁ to G₁ ; F-id to G-id ; F-∘ to G-∘ )

        comp₀ : B.Ob → D.Ob 
        comp₀ x = F₀ (G₀ x)

        comp₁ : {x y : B.Ob} → B.Hom x y → D.Hom (comp₀ x) (comp₀ y)
        comp₁ f = F₁ (G₁ f)
        
        abstract -- makes the definition like a postulate? doesn't unfold in type checking?
            comp-id : {x : B.Ob} → comp₁ (B.id {x}) ≡ D.id {comp₀ x}
            comp-id {x} = 
                F₁ (G₁ B.id) ≡⟨ cong F₁ (G-id) ⟩ 
                F₁ C.id ≡⟨ F-id ⟩ 
                D.id ∎

            comp-∘ : {x y z : B.Ob} → (f : B.Hom y z) → (g : B.Hom x y) → 
                comp₁ (f B.∘ g) ≡ (comp₁ f D.∘ comp₁ g)
            comp-∘ f g = F₁ (G₁ (f B.∘ g))       ≡⟨ cong F₁ (G-∘ f g) ⟩ 
                         F₁ ((G₁ f) C.∘ G₁ g )   ≡⟨ F-∘ (G₁ f) (G₁ g)  ⟩  
                         F₁ (G₁ f) D.∘ F₁ (G₁ g) ∎

        comps : Functor B D 
        comps .Functor.F₀ = comp₀
        comps .Functor.F₁ = comp₁
        comps .Functor.F-id = comp-id
        comps .Functor.F-∘ = comp-∘

adj-level : ∀ {o₁ h₁ o₂ h₂} (C : PreCat o₁ h₁) (D : PreCat o₂ h₂) → Level
adj-level {o₁ = o₁} {h₁} {o₂} {h₂} _ _ = o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂

Id : {o₁ h₁ : Level} → {Cat : PreCat o₁ h₁} → Functor Cat Cat  
Id = record { F₀ = λ x → x ; F₁ = λ x → x ; F-id = refl ; F-∘ = λ f g → refl}

record _⊣_ {o₁ h₁ o₂ h₂}{C : PreCat o₁ h₁}{D : PreCat o₂ h₂}
            (L : Functor C D )(R : Functor D C) : Type (adj-level C D) where 
    private
        module C = PreCat C 
        module D = PreCat D
        open Functor L renaming (F₀ to L₀ ; F₁ to L₁)
        open Functor R renaming (F₀ to R₀ ; F₁ to R₁)
    field 
        unit : Id {Cat = C} ⇒ (R F∘ L)  
        counit : (L F∘ R) ⇒ Id {Cat = D} 
    {-
        unit : 

            note that  Id {C}   : Functor C C
            and 
                       (R F∘ L) : Functor C C    
            
            unit is a natural transformation from Id {C} to (R F∘ L)
            thus there is an η where 
                η : (x : C.Ob) → (C.Hom (Id₀ x) ((R F∘ L) x))
                or 
                    (x : C.Ob) → (C.Hom x ((R F∘ L) x))

        likewise

        counit :
            note that Id {D} : Functor D D 
            and 
                    (L F∘ R) : Functor D D 
    
            counit is a natrual transformation from (L F∘ R) to Id {D}
            thus ther is an η where 
                ε : (x : D.Ob) → (D.Hom ((L F∘ R) x) x)
    
        unit and counit must obey these laws
    -}
    module unit = _⇒_ unit
    open unit  
    module counit = _⇒_ counit renaming (η to ε)
    open counit
    field 
        zig : ∀{A : C.Ob} → ε (L₀ A) D.∘ L₁ (η A) ≡ D.id
        zag : ∀{B : D.Ob} → R₁ (ε B) C.∘ η (R₀ B) ≡ C.id






-- Displayed Categories
-- https://arxiv.org/pdf/1705.04296.pdf
-- https://1lab.dev/Cat.Displayed.Base.html#682

-- idea, add structure to some base category
-- example: Sets & functions -> monoids & monoid homs

record Displayed {o ℓ} (B : PreCat o ℓ) (o' ℓ' : Level) : Set (o ⊔ ℓ ⊔ lsuc o' ⊔ lsuc ℓ') where 
    open PreCat B
    -- data 
    field 
        Ob[_] : Ob → Set o'
        Hom[_] : ∀{x y : Ob} → Hom x y → Ob[ x ] → Ob[ y ] → Set ℓ'
        id' : ∀ {a : Ob} {x : Ob[ a ]} → Hom[ id ] x x  
        _∘'_ : ∀ {a b c x y z}{f : Hom b c}{g : Hom a b} → 
            Hom[ f ] y z → Hom[ g ] x y → Hom[ f ∘ g ] x z

    infixr 40 _∘'_

    -- equalities in the displayed category should respect equalities in the base?
    -- not quite what this is
    _≡[_]_ : ∀ {a b x y}{f g : Hom a b} → Hom[ f ] x y → f ≡ g → Hom[ g ] x y → Type ℓ'
    _≡[_]_ {a} {b} {x} {y} f' p g' = PathP (λ i → Hom[ p i ] x y) f' g'

    infix 30 _≡[_]_

    -- laws 
    field 
        Hom[_]-set : ∀{a b : Ob} (f : Hom a b) → (x : Ob[ a ]) → (y : Ob[ b ]) → is-set (Hom[ f ] x y)
        idr' : ∀ {a b x y}{f : Hom a b} → (f' : Hom[ f ] x y) → (f' ∘' id') ≡[ idr f ] f'
        idl' : ∀ {a b x y}{f : Hom a b} → (f' : Hom[ f ] x y) → (id' ∘' f') ≡[ idl f ] f'
        assoc' : ∀ {a b c d w x y z}{f : Hom c d} {g : Hom b c}{h : Hom a b} → 
            (f' : Hom[ f ] y z) → (g' : Hom[ g ] x y) → (h' : Hom[ h ] w x) → 
            f' ∘' (g' ∘' h') ≡[ assoc f g h ] ((f' ∘' g') ∘' h' )


-- is there a map from Displayed to PreCat??
module maybe where 
    open Displayed
    open PreCat

    postulate
        o ℓ : Level 
        C : PreCat o ℓ
    {-
    huh : Displayed C o ℓ → PreCat o ℓ
    huh record 
            { Ob[_] = Ob[_] ; 
            Hom[_] = Hom[_] ; 
            id' = id' ; 
            _∘'_ = _∘'_ ; 
            Hom[_]-set = Hom[_]-set ; 
            idr' = idr' ; 
            idl' = idl' ; 
            assoc' = assoc' } = record
                                    { Ob = ∀{O} → Ob[_] O
                                    ; Hom = λ x x₁ → {! Hom[_]  !}
                                    ; Hom-set = {!   !}
                                    ; id = {!   !}
                                    ; _∘_ = {!   !}
                                    ; idr = {!   !}
                                    ; idl = {!   !}
                                    ; assoc = {!   !}
                                    }
-}
     

module SliceCat {o ℓ} (C : PreCat o ℓ) where 
    open PreCat C


    -- a morphism into x
    record Slice (x : Ob) : Set (o ⊔ ℓ) where 
        constructor slice 
        field 
            over : Ob 
            index : Hom over x
    open Slice


    record Slice-hom {x y} (f : Hom x y) (px : Slice x) (py : Slice y) : Set (o ⊔ ℓ) where
        constructor slice-hom 
        private
            module px = Slice px -- some map O₁ -> x
            module py = Slice py -- some map O₂ -> y
        field
            to : Hom px.over py.over
            commute : f ∘ px.index ≡ py.index ∘ to

    open Slice-hom


    {-} idea, a Slice Category is an kind of displayed category

        for C : PreCat 

        Ob[_] := (X : Ob) → Slice X
        Hom[_] := {X Y : Ob}{f : Hom X Y} → 
                    (A : Ob[ X ]) → (B : Ob[ Y ]) → Slice-hom {X Y} f A B 
    
    -}

    -- need a type for equality of slice morphisms
    module _ {x y}{f g : Hom x y}{px : Slice x}{py : Slice y}
             {f' : Slice-hom f px py}{g' : Slice-hom g px py} where
        
        -- if the underlying morphisms f and g are the same..
        -- and the .to components are the same..
        -- then the commuting diagram should be the same and you have an equality of 
        -- slice homomorphisms
        Slice-pathp : (p : f ≡ g) → (f' .to ≡ g' .to) → PathP (λ i → Slice-hom (p i) px py) f' g'
        Slice-pathp p p' i .to = p' i
        Slice-pathp p p' i .commute = {!   !}

    open Displayed
    open CompSqr C

    Slices : Displayed C (o ⊔ ℓ) (o ⊔ ℓ)
    Slices .Ob[_] = Slice
    Slices .Hom[_] = Slice-hom
    Slices .id' {x = x} = 
        slice-hom id 
            ((id ∘ index x) ≡⟨ idl _ ⟩ 
            index x ≡⟨ sym (idr _) ⟩ 
            index x ∘ id ∎)
    Slices ._∘'_ {x = x}{y = y}{z = z}{f = f}{g = g} px py = 
        slice-hom (px .to ∘ py .to) 
            (((f ∘ g) ∘ (x .index)) ≡⟨ pullr (py .commute) ⟩ 
            f ∘ y .index ∘ py .to ≡⟨ extendl (px .commute) ⟩ 
            z .index ∘ px .to ∘ py .to ∎)
    Slices .Hom[_]-set = {!   !} -- The tricky one...
    Slices .idr' = {!   !}
    Slices .idl' = {!   !}
    Slices .assoc' = {!   !}
 