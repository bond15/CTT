{-# OPTIONS --cubical #-}
module CTTeq where
open import Cubical.Core.Everything


sym : {A : Set} {x y : A} → x ≡ y → y ≡ x 
sym p = λ i → p (~ i)

lemma : {A : Set} {x y : A} {p : x ≡ y} → sym (sym p) ≡ p
lemma {A} {x} {y} {p} = λ i → p

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z 
trans p q = λ i → {!   !} 