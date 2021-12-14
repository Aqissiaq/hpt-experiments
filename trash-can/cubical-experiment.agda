{-# OPTIONS --cubical --rewriting #-}
{-
  attempt at a cubical, HIT-based VC in the simplest HIT: S¹
-}

open import Cubical.Data.Sigma
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  hiding(_+_)
open import Cubical.Data.Int

data R : Type₀ where
  context : Int → R
  addn    : (n m : Int) → context n ≡ context (n + m)

Span : R → R → Type₀
Span y y' = Σ[ x ∈ R ] (x ≡ y) × (x ≡ y')

CoSpan : R → R → Type₀
CoSpan y y' = Σ[ z ∈ R ] (y ≡ z) × (y' ≡ z)

swapPair : {A : Type₀} {B C : A → Type₀}
           → Σ[ a ∈ A ] B a × C a → Σ[ a ∈ A ] C a × B a
swapPair (a , b , c) = a , c , b

filled : ∀ {y y'} → Span y y' → CoSpan y y' → Type₀
filled (_ , (p , q)) (_ , (p' , q')) = p ∙ p' ≡ q ∙ q'


merge : ∀ {y y'} → Span y y' → CoSpan y y'
merge {context n} {context m} (context b , p , q) = context ((b + n) + m) ,
                                                    lid1 , sym lid2
      where
        -n = sym p
        +m = q
        +n+m = addn b n ∙ addn (b + n) m
        lid1 : (context n) ≡ context ((b + n) + m)
        lid1 = -n ∙ +n+m
        lid2 : context ((b + n) + m) ≡ context m
        lid2 = sym +n+m ∙' +m
merge {context k} {addn n m i} (context b , p , q) = {!!} ,
                                                     {!!} , {!!}
      where
        botLeft = sym p ∙ addn b k
        topLeft = botLeft
merge {context k} {addn n m i} (addn n' m' i₁ , p , q) = {!!}
merge {context x} {context x₁} (addn n m i , p , q) = {!!}
merge {addn n m i} {y'} (b , p , q) = {!!}


-- merge properties
reconcile : ∀ {y y'} → (s : Span y y')
            → filled s (merge s)
reconcile (_ , p , q) = {!!}

symmetric : ∀ {y y'} {s : Span y y'}
            → swapPair (merge s) ≡ merge (swapPair s)
symmetric = {!!}
