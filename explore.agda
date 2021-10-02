{-# OPTIONS --type-in-type #-}
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

    -- this is different that ttSquare..
    -- type equality?
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

    
