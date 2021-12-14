{-# OPTIONS --cubical #-}
{-
  Trying out some ways to define functions based on paths in HITs

  ideally I want:
  f : x ≡ y → X
  f loop  = ?
  f loop' = ?
  ...
-}
-- at this point we're just using cubical because the Int definitions are nice..
open import Cubical.Foundations.Prelude
open import Cubical.Data.Int
open import Cubical.Data.Nat
  hiding (_+_)

open import Cubical.Data.Sigma
  using (_×_)

module minimal-VC where

data Repo : Type₀ where
  num : Int → Repo

data Patch : Repo → Repo → Type₀ where
  add1   : (n : Int) → Patch (num n) (num (sucInt n))
  set    : ∀ {m} → (n : Int) → Patch (num m) (num n)
  -- alternative to ∘p, to keep the info for later?
  --compP  : ∀ {x} {y} {z} → Patch x y → Patch y z → Patch x z

_∘p_ : ∀ {x} {y} {z} → Patch x y → Patch y z → Patch x z
add1 n ∘p add1 .(sucInt n) = set (sucInt (sucInt n))
set n ∘p add1 .n = set (sucInt n)
add1 n ∘p set m = set m
set n ∘p set m = set m

Span : Repo → Repo → Type₀
Span y y' = Σ[ x ∈ Repo ] Patch x y × Patch x y'

CoSpan : Repo → Repo → Type₀
CoSpan y y' = Σ[ z ∈ Repo ] Patch y z × Patch y' z

swapPair : {A : Type₀} {B C : A → Type₀}
  → Σ[ a ∈ A ] B a × C a → Σ[ a ∈ A ] C a × B a
swapPair (a , b , c) = a , c , b

merge : ∀ {y} {y'} → Span y y' → CoSpan y y'
merge {.(num (sucInt n))} {.(num (sucInt n))} (.(num n) , add1 n , add1 .n) =
  num (n + 2) , add1 (n + 1) , add1 (n + 1)
merge {.(num (sucInt n))} {.(num m)} (.(num n) , add1 n , set m) =
  num (m + 1) , set m ∘p add1 m , add1 m
merge {.(num n)} {.(num (sucInt _))} (.(num _) , set n , add1 _) =
  num (n + 1) , add1 n , set n ∘p add1 n
merge {.(num n)} {.(num m)} (num x , set n , set m) =
 num x , set x , set x --ideally I would want inverse here, and signal a merge conflict

-- does merge behave itself?

filled : ∀ {y y'} → Span y y' → CoSpan y y' → Type₀
filled (_ , (p , q)) (_ , (p' , q')) = p ∘p p' ≡ q ∘p q'

reconcile : ∀ {y y'} → (s : Span y y')
            → filled s (merge s)
reconcile (_ , add1 n , add1 .n) = refl
reconcile (_ , add1 n , set n₁)  = refl
reconcile (_ , set n , add1 _)   = refl
reconcile (_ , set n , set n₁)   = refl

symmetric : ∀ {y y'} {s : Span y y'}
            → swapPair (merge s) ≡ merge (swapPair s)
symmetric {.(num (sucInt n))} {.(num (sucInt n))} {.(num n) , add1 n , add1 .n} = refl
symmetric {.(num (sucInt n))} {.(num n₁)} {.(num n) , add1 n , set n₁}          = refl
symmetric {.(num n)} {.(num (sucInt _))} {.(num _) , set n , add1 _}            = refl
symmetric {.(num n)} {.(num n₁)} {.(num _) , set n , set n₁}                    = refl

-- it does, trivially so

private
  module test where
    init : Repo
    init = num 0

    y : Repo
    y = num 1

    y' : Repo
    y' = num 42

    addPatch : Patch init y
    addPatch = add1 0

    addPatch' : Patch y (num 2)
    addPatch' = add1 1

    setPatch : Patch init y'
    setPatch = set 42

    mergeResult : CoSpan y y'
    mergeResult = merge (init , addPatch , setPatch)

    mergeResult' : CoSpan (num 2) y'
    mergeResult' = merge (init , (addPatch ∘p addPatch') , setPatch)
    -- this is a merge conflict because aP ∘ aP' becomes (set 2)

open test public


-- this is terrible, but it was a pain so I don't want to delete it
{-
helper : ∀ x y → context x ≡ context y
helper (pos zero) (pos zero)             = refl
helper (negsuc zero) (negsuc zero)       = refl
helper (pos zero) (pos (suc m))          = helper (pos zero) (pos m) ∙ add1 (pos m)
helper (pos (suc n)) (pos zero)          = sym (add1 (pos n)) ∙ helper (pos n) (pos zero)
helper (pos (suc n)) (pos (suc m))       = sym (add1 (pos n)) ∙ helper (pos n) (pos m) ∙ add1 (pos m)
helper (pos zero) (negsuc zero)          = sym (add1 (negsuc zero))
helper (pos zero) (negsuc (suc m))       = helper (pos zero) (negsuc m) ∙ sym (add1 (negsuc (suc m)))
helper (pos (suc n)) (negsuc m)          = (sym (add1 (pos n))) ∙ helper (pos n) (negsuc m)
helper (negsuc zero) (pos zero)          = add1 (negsuc zero)
helper (negsuc zero) (pos (suc m))       = helper (negsuc zero) (pos m) ∙ add1 (pos m)
helper (negsuc (suc n)) (pos m)          = (add1 (negsuc (suc n))) ∙ helper (negsuc n) (pos m)
helper (negsuc zero) (negsuc (suc m))    = helper (negsuc zero) (negsuc m) ∙ sym (add1 (negsuc (suc m)))
helper (negsuc (suc n)) (negsuc zero)    = (add1 (negsuc (suc n))) ∙ helper (negsuc n) (negsuc zero)
helper (negsuc (suc n)) (negsuc (suc m)) =
  (add1 (negsuc (suc n))) ∙ (helper (negsuc n) (negsuc m)) ∙ sym (add1 (negsuc (suc m)))
-}
