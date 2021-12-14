{-# OPTIONS --without-K --rewriting #-}
{-
experimenting with alternative descriptions of version control in HoTT
-}


module non-cubical where

open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality
open import Function.Base

subst-const : ∀ {i j} {A : Set i}{X : Set j}
            → {a a' : A}(p : a ≡ a')(x : X)
            → subst (λ _ → X) p x ≡ x
subst-const refl x = refl

ap : ∀ {i j}{A : Set i}{B : Set j}{x y : A}
     → (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

ap' : ∀ {i j} {X : Set i}{Y : X → Set j}
        {x x' : X}(f : (x : X) → Y x)(p : x ≡ x')
        → subst Y p (f x) ≡ f x'
ap' _ refl = refl

_∙_ : ∀ {i}{X : Set i}{x y z : X}
      → x ≡ y → y ≡ z → x ≡ z
refl ∙ p = p
infixr 30 _∙_

data S¹ : Set where
  base : S¹

postulate loop : base ≡ base

private
  module Eliminators' {i}(B : S¹ → Set i)
                      (m : B base)
                      (l : subst B loop m ≡ m) where
         elim' : (x : S¹) → B x
         elim' base = m

         β-base' : elim' base ≡ m
         β-base' = refl

         postulate β-loop' : ap' elim' loop ≡ l

private
  module Eliminators {i} {B : Set i}
                     (m : B) (l : m ≡ m) where
         open Eliminators' (λ _ → B) m (subst-const loop m ∙ l)

         elim : S¹ → B
         elim = elim'

         β-base : elim base ≡ m
         β-base = refl

         postulate β-loop : ap elim loop ≡ l

open Eliminators public
open Eliminators' public

data 𝟚 : Set where
  one two : 𝟚

foo : S¹ → 𝟚
foo x = elim {!!} {!!} {!!}

  {- path constructors
     Agda does not do this natively, but there is a hack here:
     https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/types/HIT_README.txt
  -}

