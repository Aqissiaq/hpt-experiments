{-# OPTIONS --cubical --rewriting #-}

-- trying to recreate the non-reduction problems in a minimal setting
module minimal-no-reduce where

open import Cubical.Data.Sigma
open import Cubical.Data.Int
open import Cubical.Data.Vec
open import Cubical.Data.Empty
  renaming(rec to ⊥-elim)
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Everything

open import decidable-ints
  renaming (_ℤ=?_ to _=?_)

targetType : Type₀
targetType = ℤ × ℤ

data R : Type₀ where
  point : R
  path : (point ≡ point)

test : targetType ≃ targetType
test = isoToEquiv (iso foo foo foobar barfoo)
  where
  foo : targetType → targetType
  foo (x , y) with x =? y
  ... | yes _ = (x , y)
  ... | no _ = (y , x)

  foobar : section foo foo
  foobar (x , y) with x =? y
  ... | yes x=y
    with x =? y
  ... | yes _ = refl
  ... | no x≠y = ⊥-elim (x≠y x=y)
  foobar (x , y) | no x≠y
    with y =? x
  ... | yes x=y = ⊥-elim (x≠y (sym x=y))
  ... | no _ = refl

  barfoo : retract foo foo
  barfoo (x , y) with x =? y
  ... | yes x=y
    with x =? y
  ... | yes _ = refl
  ... | no x≠y = ⊥-elim (x≠y x=y)
  barfoo (x , y) | no x≠y
    with y =? x
  ... | yes y=x = ⊥-elim (x≠y (sym y=x))
  ... | no _ = refl

toTarget : R → Type₀
toTarget point = targetType
toTarget (path i) = (ua test) i

interp : point ≡ point → targetType ≃ targetType
interp p = pathToEquiv (cong toTarget p)

apply : point ≡ point → targetType → targetType
apply p x = equivFun (interp p) x

result : targetType
result = apply path (1 , 2)

_ : result ≡ (pos 2 , pos 1)
_ = refl

{-
I expect result to be (2 , 1), but normalizing gives:
  transp (λ i → Σ ℤ (λ _ → ℤ)) i0 (pos 2 , pos 1)

It seems we need two elements:
  1. using `with` in the definition of the equivalence
  2. targetType not being a basic type (ℤ works as expected, Vectors and pairs do not)
-}
