{-# OPTIONS --cubical --rewriting #-}
{-
experimenting with alternative descriptions of version control in HoTT
-}


open import Cubical.Data.Sigma
open import Cubical.Core.Everything
  hiding (I)
open import Cubical.Foundations.Prelude
  hiding (I)
open import Data.String
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Data.Fin
open import Data.Vec
open import Function.Base

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

module hpt-experiment where

data R : Type₀ where
  context : {size : ℕ} → Vec String size → R
  add     : {size : ℕ} → (s : String) (v : Vec String size) (i : Fin (suc size))
                       → context v ≡ context (insert v i s)

Span : R → R → Type₀
Span y y' = Σ[ x ∈ R ] (x ≡ y) × (x ≡ y')

CoSpan : R → R → Type₀
CoSpan y y' = Σ[ z ∈ R ] (y ≡ z) × (y' ≡ z)

swapPair : {A : Type₀} {B C : A → Type₀}
              → Σ[ a ∈ A ] B a × C a → Σ[ a ∈ A ] C a × B a
swapPair (a , b , c) = a , c , b

filled : ∀ {y y'} → Span y y' → CoSpan y y' → Type₀
filled (_ , (p , q)) (_ , (p' , q')) = p ∙ p' ≡ q ∙ q'

{-
  thoughts from Håkon:
    - the equivalences *do* in fact hold
    - but they are deceptive, 'cause we actually want the info
    - maybe try to define useful elimination rules
      - ask Jonathan, he's struggled w/ this
-}
merge : ∀ {y y'} → Span y y' → CoSpan y y'
merge {y} {y'} (b , p , q) = {!!}

-- merge properties
reconcile : ∀ {y y'} → (s : Span y y')
          → filled s (merge s)
reconcile (_ , p , q) = {!!}

symmetric : ∀ {y y'} {s : Span y y'}
          → swapPair (merge s) ≡ merge (swapPair s)
symmetric = {!!}

{-
it should suffice to assign values to add for paths

ex.
f : (x y : S^1) -> x≡y -> X
f x .x loop = whatever
HOWEVER - might need J stuff to convince Agda
"whatever" is now the function from a path to X

not sure if this↑ is actually true, what about f (loop ∙ loop) or f (loop ⁻¹)?

actually ((x y : HIT) x ≡ y → X) ≃ (HIT → X)
by dependent currying + contractibility of (Σ[ a ∈ A ] a ≡ b)

also: (Span y y') ≃ (y ≡ y') again by contractibility
  not sure about this↑ either, doesn't x carry some info?

plan: look for lemmas about functions out of groupoids (HITs?) in
  - cubical library
  - hott book
  - symmetry?

det sure eplet
  - construct some cubes

further spins:
  other types of repositories (file hierarchy?)
  separable/extensible models (files on their own vs. folder structure)
-}
