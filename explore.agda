{-# OPTIONS --type-in-type #-}
{-# OPTIONS --cubical #-}
module explore where
open import Cubical.Core.Everything


-- An abstract interval with the 2 endoints

_ : I 
_ = i0

_ : I 
_ = i1

-- operations on Intervals

_ : I 
_ = i0 ∨ i1

_ : I 
_ = i0 ∧ i1

_ : I 
_ = ~ i0

-- cubical agda interval obeys rules of a De Morgan algebra

-- Paths are defined as lambdas from intervals into a type
constPath : {A : Set}→ (a : A) → Path A a a 
constPath a i =  a

data Bool : Set where
    tt ff : Bool

not : Bool → Bool
not tt = ff
not ff = tt

module boolpathexampes where

    _ : Path Bool tt tt
    _ = λ i → tt

    -- equality is defined using Paths
    _ : tt ≡ tt
    _ = λ i → tt
    {- 
     _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
     _≡_ {A = A} = PathP (λ i → A)
    -}

module pathoperations where

    -- Paths are lambdas from intervals
    -- so paths can be applied to intervals
    -- p i0 ≡ tt
    -- p i1 ≡ ff
    _ : (p : tt ≡ tt) → p i0 ≡ tt
    _ = λ p → p


    
    _ : not tt ≡ ff
    _ = λ i → ff
    -- previously this would just be `refl`
    -- it would be a check that both sides are definitionally equivalent

    

    -- define symmetry of paths/equality 
    -- using operations on the interval
    _ : {A : Type}{a b : A} → Path A a b → Path A b a
    _ = λ p → λ i → p (~ i) 

    _ : {A : Type}{a b : A} → a ≡ b → b ≡ a 
    _ = λ p → λ i → p (~ i) 


module congAndFunExt where

    -- cong and funext come up alot in type theoretic reasoning
    -- however, in most type theories fun ext is taken as an axiom
    -- as it can not be proven within the type theory
    
    -- fun ext is provable in cubical type theory

    cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
    cong f p = λ i → f (p i)
--  cong f refl = refl  
--  ^ previous definition

    funExt : {A B : Set} 
            {f g : A → B} → 
            (∀ (x : A) → f x ≡ g x) → f ≡ g
    funExt p i = λ a → p a i

    not' : Bool → Bool
    not' tt = ff
    not' ff = tt

    _ : not' ≡ not
    _ = funExt λ{tt → λ i → ff
               ; ff → λ i → tt}


module higherDimensions where

    -- so refl is just a path between two elements of a type
    -- We can parameterize with more intervals to have higher dimensional paths

    ttPath : tt ≡ tt
    ttPath = λ i → tt

    --  tt---tt

    -- we can also have paths between equality proofs!
    -- this is very new teritory since the only thing allowed in 
    -- previous type theories is `refl` which is a path between 
    -- two points
    ttSquare : ttPath ≡ ttPath
    ttSquare = λ i j → tt
    --  tt---tt
    ---  |   |
    --- tt---tt

    ttCube : ttSquare ≡ ttSquare
    ttCube = λ i j k → tt

    -- this is different than ttSquare..
    -- euqality type equality?
    -- this can be encoded it regular old Agda
    _ : (tt ≡ tt) ≡ (tt ≡ tt)
    _ = λ i → tt ≡ tt   

module squareOps
    {A : Set}
    (a b c d : A)
    (p : a ≡ b)
    (q : a ≡ b)
    (s : p ≡ q)
    where 

    -- b---b
    -- |   |
    -- a---a

    left : a ≡ b
    left = s i0

    right : a ≡ b 
    right = s i1 

    top : b ≡ b 
    top = λ i → s i i1

    bot : a ≡ a 
    bot = λ i → s i i0

    diag : a ≡ b 
    diag = λ i → s i i


    -- fancy ops
    -- flip a square
    sym : {A : Set} {a b : A} → a ≡ b → b ≡ a 
    sym = λ p i → p (~ i )

    flip : (sym q) ≡ (sym p)
    flip = λ i j → s (~ i) (~ j)


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

module squarehcomp
        {A : Type}
        ( a b c d : A)
        (p : a ≡ b)
        (q : a ≡ c)
        (r : b ≡ d)
    where

    np : c ≡ d 
    np i = hcomp 
        (λ j → 
            λ{ (i = i0) → q j ; 
               (i = i1) → r j }) 
        (p i)

module hcomp where
    open import Agda.Builtin.Nat


    data ΔInt : Type where
        _⊙_ : Nat → Nat → ΔInt
        cancel : ∀ a b → a ⊙ b ≡ suc a ⊙ suc b

    --question : ∀ a b i → cancel a b i ≡ cancel (suc a) (suc b) i 
    --question a b i j = hcomp {!   !} {!   !}