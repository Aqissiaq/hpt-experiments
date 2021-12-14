{-# OPTIONS --cubical --rewriting #-}

module first-attempt where

open import Function.Base public
open import Data.Product

open import Cubical.Core.Everything
  hiding (I)
open import Cubical.Foundations.Prelude
  using (_≡_
    ; refl
    ; _∙_
    ; _≡⟨_⟩_
    ; _∎
    ; cong
    ; subst
    ; J
    )
  renaming (
      transport to coe
    ; sym to !
    )

open import Cubical.Foundations.Id
    using (ap)

open import Cubical.Foundations.GroupoidLaws
    using (lUnit ; rUnit ; assoc ; lCancel ; rCancel)

open import Cubical.HITs.S1.Base
  using(
     S¹
    ; ΩS¹
    ; helix
    ; base
    ; loop
    )

open import Cubical.Data.Int.Properties
  using (sucPathInt
    ; +-comm)

open import Cubical.Data.Bool

open import Cubical.Foundations.Univalence
  using ( ua
    ; univalence
    ; pathToEquiv
    )

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
  using(idEquiv)

open import Cubical.Data.Int
open import Cubical.Data.Nat
  hiding(_+_ ; +-comm)

{- 2.3 Univalence -}
{- This first attempt typechecks, but does not have the properties claimed in hpt
Bijection : Type₀ → Type₀ → Type₀
Bijection A B = A ≃ B

reflb : {A : Type₀} → Bijection A A
reflb = pathToEquiv refl

!b : {A B : Type₀} → Bijection A B → Bijection B A
!b p = pathToEquiv (sym (ua p))

_∘b_ : {A B C : Type₀} → Bijection B C → Bijection A B → Bijection A C
-- _∙_ : x ≡ y → y ≡ z → x ≡ z
_∘b_ p q = pathToEquiv (ua q ∙ ua p)
-}

coe-biject = pathToEquiv

{- 4. An Elementary Patch Theory -}
-- R is the type of possible repositories, in this case a single num
data R : Type₀ where
  num  : R -- patch context
  add1 : num ≡ num -- basic patch


I : R → Type₀
I num      = Int
I (add1 i) = sucPathInt i

interp : (num ≡ num) → Int ≃ Int
interp p = coe-biject λ i → I ( p i ) -- I'm sure there is a function to do this, but it's apparently not ap
-- it is cong

-- arguably it would be prettier to do interp p = fst (...), to only preserve the bijective function

module Int-interp-test where
  test1 : Int
  test1 = fst ( interp add1 ) 0 -- pos 1

  test2 : Int
  test2 = fst ( interp (add1 ∙ add1 )) 0 -- pos 2

  test0 : Int
  test0 = fst ( interp ( ! add1 ∙ ! add1 )) 0 -- negsuc 1 (-2)

module Bool-interp-test where
  I' : R → Type₀
  I' num = Bool
  I' (add1 i) = notEq i

  interp' : (num ≡ num) → Bool ≃ Bool
  interp' p = coe-biject λ i → I' ( p i )

  testTrue : Bool
  testTrue = fst ( interp' add1 ) false -- true

  testFalse : Bool
  testFalse = fst ( interp' add1 ) testTrue -- false

Patch : Type₀
Patch = num ≡ num

merge : ( Patch × Patch ) → ( Patch × Patch )
merge (f1 , f2) = f2 , f1

sym-helper : (a b c d : Patch) → merge ( a , b ) ≡ ( c , d ) → ( a , b ) ≡ ( d , c )
sym-helper a b c d p = a , b
                     ≡⟨ ! refl ⟩ merge ( merge ( a , b ))
                     ≡⟨ cong merge p ⟩ merge ( c , d )
                     ≡⟨ refl ⟩ d , c ∎

symmetric : ( f1 f2 g1 g2 : Patch ) → merge ( f1 , f2 ) ≡ ( g1 , g2 ) → merge ( f2 , f1 ) ≡ ( g2 , g1 )
symmetric f1 f2 g1 g2 p = merge ( f2 , f1 )
                        ≡⟨ refl ⟩ f1 , f2
                        ≡⟨ sym-helper f1 f2 g1 g2 p ⟩ g2 , g1 ∎

R≃S¹ : R ≃ S¹
R≃S¹ = isoToEquiv (iso there back sect retr)
                  where
                    there : R → S¹
                    there num = base
                    there (add1 i) = loop i

                    back : S¹ → R
                    back base = num
                    back (loop i) = add1 i

                    retr : (r : R) → back ( there ( r )) ≡ r
                    retr num = refl
                    retr (add1 i) = refl

                    sect : (s : S¹) → there ( back ( s )) ≡ s
                    sect base = refl
                    sect (loop i) = refl


R≡S¹ : R ≡ S¹
R≡S¹ = ua R≃S¹
-- ↑ this whole thing is probably not necessary at all tbh

-- shamelessly rewriting ΩS¹≡Int from HITs.S1

encode : ∀ x → num ≡ x → I x
encode x p = subst I p (pos zero)

winding : Patch → Int
winding p = encode num refl -- this refl is not needed in HITs.S1 ...

back : Int → Patch -- intLoop?
back (pos zero) = refl
back (pos (suc n)) = back (pos n) ∙ add1
back (negsuc zero) = ! add1
back (negsuc (suc n)) = back (negsuc n) ∙ ! add1

decodeSquare : (n : Int) → PathP (λ i → num ≡ add1 i) (back (predInt n)) (back n)
decodeSquare (pos zero) i j    = add1 (i ∨ ~ j)
decodeSquare (pos (suc n)) i j = hfill (λ k → λ { (j = i0) → num
                                                ; (j = i1) → add1 k } )
                                       (inS (back (pos n) j)) i
decodeSquare (negsuc n) i j = hfill (λ k → λ { (j = i0) → num
                                             ; (j = i1) → add1 (~ k) })
                                    (inS (back (negsuc n) j)) (~ i)

decode : (x : R) → I x → num ≡ x
decode num         = back
decode (add1 i) y j =
  let n : Int
      n = unglue (i ∨ ~ i) y
  in hcomp (λ k → λ { (i = i0) → back (predSuc y k) j
                    ; (i = i1) → back y j
                    ; (j = i0) → num
                    ; (j = i1) → add1 i })
           (decodeSquare n i j)

decodeEncode : (x : R) (p : num ≡ x) → decode x (encode x p) ≡ p
decodeEncode x p = J (λ y q → decode y (encode y q) ≡ q) (λ _ → refl) p

there : Patch → Int
there p = fst (interp p) ( pos zero )

back-there : (n : Int) → there ( back ( n )) ≡ n
back-there (pos zero) = refl
back-there (pos (suc n)) = cong sucInt (back-there (pos n))
back-there (negsuc zero) = refl
back-there (negsuc (suc n)) = cong predInt (back-there (negsuc n))

Patch≃Int : Patch ≃ Int
Patch≃Int = isoToEquiv (iso there back back-there (decodeEncode num))

Int≃Patch : Int ≃ Patch
Int≃Patch = isoToEquiv (iso back there (decodeEncode num) back-there)


{-
This appears to be a dead end for two reason:
  1) patch-comm requires two ints, and it is obvious that they are ϕ f2 and ϕ f2 in reconcile
  2) I haven't actually proven back-homomorphism
back-homomorphism : ∀ n m → back n ∙ back m ≡ back (n + m)
back-homomorphism n m = {!!}

patch-comm : ∀ x y → back x ∙ back y ≡ back y ∙ back x
patch-comm x y = back x ∙ back y
               ≡⟨ back-homomorphism x y ⟩ back (x + y)
               ≡⟨ cong back (+-comm x y) ⟩ back (y + x)
               ≡⟨ ! (back-homomorphism y x) ⟩ back y  ∙ back x ∎
-}

back-surjective : (p : Patch) → ∃[ n ] (back n ≡ p )
back-surjective p = there p , decodeEncode num p

back-suc : (n : Int) → back (sucInt n) ≡ back n ∙ add1
back-suc (pos n)          = refl
back-suc (negsuc 0)       = ! (lCancel add1)
back-suc (negsuc (suc n)) =                      -- back (sucInt (negsuc (suc n)))
  rUnit (back (negsuc n))                        -- = back (sucPathInt (negsuc (suc n))) ∙ refl
  ∙ (λ i → back (negsuc n) ∙ lCancel add1 (~ i)) -- = hcomp ? ?
  ∙ assoc (back (negsuc n)) (! add1) add1        -- cancel add1's

back-pred : (n : Int) → back (predInt n) ≡ back n ∙ ! add1
back-pred (pos 0) = lUnit (! add1)
back-pred (pos (suc n)) =
  rUnit (back (pos n))                        -- = back (predPathInt (pos (suc n))) ∙ refl
  ∙ (λ i → back (pos n) ∙ rCancel add1 (~ i)) -- = hcomp ? ?
  ∙ assoc (back (pos n)) add1 (! add1)        -- cancel add1's
back-pred (negsuc n) = refl

back-hom : (n m : Int) → back n ∙ back m ≡ back (n + m)
back-hom n (pos 0) = ! (rUnit (back n))
back-hom n (pos (suc m)) =
  assoc (back n) (back (pos m)) add1
  ∙ (λ i → (back-hom n (pos m) i) ∙ add1)
  ∙ ! (back-suc (n + pos m))
back-hom a (negsuc zero)    = ! (back-pred a)
back-hom a (negsuc (suc n)) =
  assoc (back a) (back (negsuc n)) (! add1)
  ∙ (λ i → (back-hom a (negsuc n) i) ∙ (! add1))
  ∙ ! (back-pred (a + negsuc n))

there-hom : (p q : Patch) → there (p ∙ q) ≡ there p + there q
there-hom p q i =
  hcomp (λ t → λ { (i = i0) → there (decodeEncode num p t ∙ decodeEncode num q t)
                 ; (i = i1) → back-there (there p + there q) t })
        (there (back-hom (there p) (there q) i))

justPatch : {a b c d : Patch}
            → merge ( a , b ) ≡ ( c , d ) → a ≡ d × b ≡ c
justPatch p = cong snd (p) , cong fst (p)

uncurry-helper : {A : Type₀} (a b c d : A)
                 →(f : A → A → A) → a ≡ d × b ≡ c
                 → f a c ≡ f d b
-- I would prefer if the patches were implicit, but alas
uncurry-helper a b c d f (a≡d , b≡c) = f a c
                                     ≡⟨ refl ⟩ (uncurry f) ( a , c )
                                     ≡⟨ cong (λ x → f x c) a≡d ⟩ (uncurry f) ( d , c )
                                     ≡⟨ cong (λ x → f d x) (! b≡c) ⟩ (uncurry f) ( d , b )
                                     -- this should be just one step, but at least it's very clear
                                     ≡⟨ refl ⟩ f d b ∎

∙-comm : (p q : Patch) → p ∙ q ≡ q ∙ p
∙-comm p q =
  p ∙ q ≡⟨ uncurry-helper p (back m) q (back n) _∙_ (f  , g) ⟩ back n ∙ back m
        ≡⟨ back-hom n m ⟩ back (n + m)
        ≡⟨ cong back (+-comm n m) ⟩ back (m + n)
        ≡⟨ ! (back-hom m n) ⟩ back m ∙ back n
        ≡⟨ uncurry-helper (back m) p (back n) q _∙_ (g , f) ⟩ q ∙ p ∎
  where
    n = fst (back-surjective p)
    m = fst (back-surjective q)
    f = ! (snd (back-surjective p))
    g = snd (back-surjective q)

reconcile : ( f1 f2 g1 g2 : Patch ) → merge ( f1 , f2 ) ≡ ( g1 , g2 ) → f1 ∙ g1 ≡ f2 ∙ g2
reconcile f1 f2 g1 g2 p = ( f1 ∙ g1 )
                        ≡⟨ uncurry-helper f1 f2 g1 g2 _∙_ (justPatch p) ⟩ ( g2 ∙ f2 )
                        ≡⟨ ∙-comm g2 f2 ⟩ f2 ∙ g2 ∎

