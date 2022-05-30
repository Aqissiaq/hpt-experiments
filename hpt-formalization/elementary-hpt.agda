{-# OPTIONS --cubical --rewriting #-}

module elementary-hpt where

open import Function.Base
open import Data.Product
open import Cubical.Data.Int
open import Cubical.Data.Nat
  using(zero ; suc)

open import Cubical.Core.Everything
  hiding (I)
open import Cubical.Foundations.Prelude
  using (
    _≡_
  ; refl
  ; _∙_
  ; _≡⟨_⟩_
  ; _∎
  ; cong
  ; cong₂
  ; sym
  ; transport
  )

open import Cubical.HITs.S1.Base
  renaming(
    S¹ to R
  ; base to num
  ; loop to add1
  ; ΩS¹ to Patch
  ; helix to I
  )

open import Cubical.Foundations.Univalence
  using (pathToEquiv)

{-
  interpretation of a Patch as an equivalence of Ints
  this has the effect of making add1 equivalent to (+1)
-}
interp : Patch → ℤ ≃ ℤ
interp p = pathToEquiv (cong I p)

apply : Patch → ℤ → ℤ
apply p n = equivFun (interp p) n
{-
  definition of a merge operation on these very simple Int-patches
  since + is commutative, we just swap them
-}
merge : ( Patch × Patch ) → ( Patch × Patch )
merge = swap

{-
  properties of merge

  symmetric:
    order doesn't matter

  reconcile:
    the patches actually perform a merge

     f1 ↙ ↘ f2       f2 ↙ ↘ f1
                 ≡
     g1 ↘ ↙ g2       g2 ↘ ↙ g1

-}
-- symmetry is basically trivial, applying merge to both sides of the equality
symmetric : { f1 f2 g1 g2 : Patch }
            → merge ( f1 , f2 ) ≡ ( g1 , g2 ) → merge ( f2 , f1 ) ≡ ( g2 , g1 )
symmetric p = cong merge p

-- reconcile turns out to be much more difficult, and we have to go via the interpretation of patches
{-
with this interpretation, patches commute
this relies on two facts:
  1) intLoop is surjective     (intLoop-sur)
  2) intLoop is a homomorphism (intLoop-hom from HITs.S¹)
then we can use +-comm
-}

intLoop-sur : (p : Patch) → ∃[ n ] (p ≡ intLoop n)
intLoop-sur p = equivFun (interp p) 0 , sym (decodeEncode num p)

patch-comm : (p q : Patch) → p ∙ q ≡ q ∙ p
patch-comm p q = let (n , p-is-n) = intLoop-sur p
                     (m , q-is-m) = intLoop-sur q
                     n-is-p = sym p-is-n
                     m-is-q = sym q-is-m in
  p ∙ q ≡⟨ cong₂ _∙_ p-is-n q-is-m ⟩  intLoop n ∙ intLoop m
        ≡⟨ intLoop-hom n m ⟩          intLoop (n + m)
        ≡⟨ cong intLoop (+Comm n m) ⟩ intLoop (m + n)
        ≡⟨ sym (intLoop-hom m n) ⟩    intLoop m ∙ intLoop n
        ≡⟨ cong₂ _∙_ m-is-q n-is-p ⟩
  q ∙ p ∎

-- with this fact established, reconcile is suddenly quite easy
reconcile : { f1 f2 g1 g2 : Patch }
            → merge ( f1 , f2 ) ≡ ( g1 , g2 ) → f1 ∙ g1 ≡ f2 ∙ g2
reconcile {f1} {f2} {g1} {g2} p = let f1=g2 = cong snd p
                                      g1=f2 = cong fst (sym p) in
  f1 ∙ g1 ≡⟨ cong₂ _∙_ f1=g2 g1=f2 ⟩ g2 ∙ f2
          ≡⟨ patch-comm g2 f2 ⟩
  f2 ∙ g2 ∎

nopPatch : Patch
nopPatch = refl

succPatch : Patch
succPatch = add1

invSuccPatch : Patch
invSuccPatch = sym add1

compPatch : Patch
compPatch = succPatch ∙ invSuccPatch
