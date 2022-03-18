{-# OPTIONS --cubical --rewriting #-}

-- trying to recreate the non-reduction problems in a minimal setting
module minimal-no-reduce where

open import Cubical.Data.Sigma
open import Cubical.Data.Int
open import Cubical.Data.Vec
open import Cubical.Data.Empty
  renaming(rec to ⊥-elim)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Everything

open import decidable-ints
  renaming (_ℤ=?_ to _=?_)

repoType : Type₀
repoType = ℤ × ℤ

data R : Type₀ where
  point : R
  path : (point ≡ point)

test : repoType ≃ repoType
test = isoToEquiv (iso foo foo foobar barfoo)
  where
  foo : repoType → repoType
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

toRepo : R → Type₀
toRepo point = repoType
toRepo (path i) = (ua test) i

interp : point ≡ point → repoType ≃ repoType
interp p = pathToEquiv (cong toRepo p)

apply : point ≡ point → repoType → repoType
apply p x = equivFun (interp p) x

resultNop : repoType
resultNop = apply path (1 , 2)
