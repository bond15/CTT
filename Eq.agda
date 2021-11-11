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

    -- all of this follows from refl (base case of ID)
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

    _∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
    g ∘ f = λ x → g (f x)

    -- all of this follows from refl (base case of Id)
    -- claim here is that "functions are functorial over paths"
    -- aka functions respect equality
    -- topologically, every function is "continuous" i.e. preserves paths
    lemma2ᵢ : {A B : Set}{x y z : A}{f : A → B}{p : x ≡ y}{q : y ≡ z} → 
        ap f (trans p q) ≡ trans (ap f p) (ap f q)
    lemma2ᵢ {A}{B}{x}{y}{z}{f}{refl}{refl} = refl
    
    lemma2ᵢᵢ : {A B : Set}{x y z : A}{f : A → B}{p : x ≡ y} → 
        ap f (sym p) ≡ sym (ap f p)
    lemma2ᵢᵢ {A}{B}{x}{y}{z}{f}{refl} = refl 

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

-- Type Families are fibrations
module 2,3 where
    open import Agda.Builtin.Sigma

    transport : {A : Set}{P : A → Set} → ∀(x y : A)→ (p : x ≡ y ) → P x → P y
    transport {A} {P} x y refl = λ x → x

    totalSpace : {ℓ : Level} → Set (lsuc ℓ)
    totalSpace {ℓ} = {A  : Set ℓ}{P : A → Set ℓ} → Σ A (λ a → P a)

    -- lemma 2.3.2
    lift : {A : Set}{P : A → Set}{x y : A} → (u : P x ) → (p : x ≡ y) → 
        (x , u) ≡ (y , transport {A}{P} x y p u)
    lift {A}{P}{x}{y} u refl = refl

    --lemma 2.3.4 
    adpf : {A : Set}{P : A → Set} → (f : ∀(x : A) → P x ) 
        → {x y : A} → ∀(p : x ≡ y) → 
            transport {A}{P} x y p (f x) ≡ f y
    adpf {A}{P} f {x}{y} refl = refl


    {-transportconst : {A B : Set}{P : A → Set}→ {∀ (x : A) → P x ≡ B} → 
        {x y : A}{p : x ≡ y}{b : B} → 
        transport {A} {P} x y p {! b  !} ≡ {! b  !}
    transportconst = {!   !}
    -}

    sym : {A : Set} → ∀ {x y : A} → (x ≡ y) → (y ≡ x)
    sym refl = refl

    trans : {A : Set} → ∀{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
    trans refl refl = refl

    _∘_ : {A B  : Set} → (B → Set) → (A → B) → (A → Set)
    g ∘ f = λ x → g (f x)
    --lemma 2.3.9
    lemma2,3,9 : {A : Set}{x y z : A}{P : A → Set}{p : x ≡ y}{q : y ≡ z}{u : P x}
        → transport {A} {P} y z q (transport {A} {P} x y p u) ≡ transport {A}{P} x z (trans p q) u
    lemma2,3,9{A}{x}{y}{z}{P}{refl}{refl}{u} = refl

    --lemma2,3,10 : {A B : Set}{x y : A}{f : A → B}{P : B → Set}{p : x ≡ y}{u : P (f x)}
     --→ transport {A} {P ∘ f} {!   !} {!   !} {!   !} {!   !}  ≡ transport {B} {P} {!   !}  {!   !} {!   !} {!   !} 
    --lemma2,3,10 = {!   !}

open 2,3 using (transport)

module 2,4 where
    sym : {A : Set} → ∀ {x y : A} → (x ≡ y) → (y ≡ x)
    sym refl = refl
    
    trans : {A : Set} → ∀{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
    trans refl refl = refl

    infix  3 _∎
    infixr 2 _≡⟨⟩_ step-≡ step-≡˘
    infix  1 begin_

    begin_ : {A : Set} → ∀{x y : A} → x ≡ y → x ≡ y
    begin_ x≡y = x≡y

    _≡⟨⟩_ : {A : Set} → ∀ (x {y} : A) → x ≡ y → x ≡ y
    _ ≡⟨⟩ x≡y = x≡y

    step-≡ : {A : Set} → ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
    step-≡ _ y≡z x≡y = trans x≡y y≡z

    step-≡˘ :{A : Set} →  ∀ (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
    step-≡˘ _ y≡z y≡x = trans (sym y≡x) y≡z

    _∎ :{A : Set} →  ∀ (x : A) → x ≡ x
    _∎ _ = refl

    syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
    syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

    _∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
    g ∘ f = λ x → g (f x)

    ap : {A B : Set}{x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
    ap f refl = refl
    --Def 2.4.1
    -- homotopy
    _∼_ : {A : Set}{P : A → Set} → (f g : ∀ (x : A) → P x) → Set
    _∼_ {A} {P} f g = ∀ ( x : A) → f x ≡ g x

    -- lemma 2.4.2 homotopy is an equivalence relation on each dependent function type
    -- proof
    r : {A : Set} {P : A → Set} → (∀ (f : (∀ (x : A)→ P x)) 
        → f ∼ f)
    r f x = refl

    s : {A : Set} {P : A → Set} → (∀ (f g : (∀ (x : A)→ P x)) → 
        (f ∼ g) → (g ∼ f))
    s f g h x = sym (h x)

    t :{A : Set} {P : A → Set} → (∀ (f g h : (∀ (x : A)→ P x)) → 
        (f ∼ g) → (g ∼ h) → (f ∼ h))
    t f g h fg gh x = trans (fg x) (gh x)

    -- claim just as function are automatically "functors" (over paths)
    -- then homotopies are automatically natural transformations
    
    -- notation
    -- f : A → B , p : x ≡ y then f(p) ≐ ap f p // 


    lemma₁ₐ : {A : Set} {x y : A} {p : x ≡ y} → p ≡ trans p refl
    lemma₁ₐ {A} {x} {y} {refl} = refl

    lemma₁b : {A : Set} {x y : A} {p : x ≡ y} → p ≡ trans refl p 
    lemma₁b {A} {x} {y} {refl} = refl

    -- natural transformation
    lemma2,4,3 : {A B : Set}{x y : A}{f g : A → B}{p : x ≡ y} → 
        (H : f ∼ g)  → 
        trans (H x) (ap g p) ≡ trans (ap f p) (H y)
    lemma2,4,3 {A}{B}{x}{y}{f}{g}{refl} H with H x
    ...   | eq = begin (trans eq refl ≡⟨ sym lemma₁ₐ ⟩ eq ≡⟨⟩ lemma₁b) 



    corollary2,4,4 : {A : Set}{x : A}{f : A → A} → 
        (H : f ∼ (λ x → x)) → 
        H (f x) ≡ ap f (H x)
    corollary2,4,4 {A}{x}{f} H with H x 
    ... | eq = {!   !} 
    -- (f (f x) ≡ f x) ≡ (f(f x) ≡ f x )


    -- Page 77
    -- Claims that ISO is not well behaved
    -- Instead, use adjoint equivalences?

    -- Def 2.4.6
    -- quasi-inverse
    open import Agda.Builtin.Sigma 
    open import Data.Product
    qinv⦅_⦆ : {A B : Set} → (f : A → B) → Set
    qinv⦅_⦆ {A} {B} f = Σ (B → A) λ g → ((f ∘ g) ∼ λ x → x) × ((g ∘ f) ∼ λ x → x)
     
    -- quasi inverse of id is id
    _ : {A : Set} → qinv⦅ id{A} ⦆ 
    _ = id , ((λ x → refl) , λ x → refl)

    qt : {A : Set}{x y : A}{P : A → Set}{p : x ≡ y} → 
        qinv⦅ transport {A} {P} x y p ⦆
    qt {A}{x}{y}{P}{refl}= transport {A} {P} y x refl , ((λ x₁ → refl) , λ x → refl)

    isequiv⦅_⦆ : {A B : Set}(f : A → B) → Set 
    isequiv⦅_⦆ {A} {B} f = (Σ (B → A) (λ g → (f ∘ g) ∼ id)) × (Σ (B → A) λ h → (h ∘ f) ∼ id)

    _≈_ : (A B : Set) → Set 
    A ≈ B = Σ (A → B) λ f → isequiv⦅ f ⦆

    data FooBar : Set where 
        Foo Bar : FooBar

    _ : Bool ≈ FooBar
    _ = (λ{ tt → Foo
          ; ff → Bar}) ,
         (((λ{ Foo → tt
             ; Bar → ff }) , λ{Foo → refl
                             ; Bar → refl}) , 
        ((λ{Foo → tt
          ; Bar → ff }) , λ{tt → refl
                          ; ff → refl}))

    -- type equivalence is an equivalence
    tr : {A : Set} → A ≈ A 
    tr = id , ((id , (λ x → refl)) , id , (λ x → refl))

    ts : {A B : Set} → A ≈ B → B ≈ A 
    ts = λ{(A→B , (B→A , snd₁) , B→A' , snd₂) → 
            B→A , (A→B , {!  snd₂ !}) , A→B , snd₁}

    ttr : {A B C : Set} → (A ≈ B) → (B ≈ C) → A ≈ C 
    ttr {A} {B} {C} (f , (finv₁ , fprf₁) , (finv₂ , fprf₂)) 
                    (g , (ginv₁ , gprf₁) , (ginv₂ , gprf₂)) = 
                    
                    (g ∘ f) , ((finv₁ ∘  ginv₁) , {!   !} ) , (finv₂ ∘ ginv₂) , {!   !}


-- 2.5
module 2,5 where 
    open import Data.Product
    -- Product
    _ : {A B : Set} → {x y : A × B} → (p : x ≡ y) → 
        (fst x ≡ fst y) × (snd x ≡ snd y)
    _ = ?