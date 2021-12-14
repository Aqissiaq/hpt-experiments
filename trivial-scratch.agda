{-# OPTIONS --cubical --rewriting #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Int


{-# BUILTIN REWRITE _≡_ #-}

module trivial-scratch where

module repo (A : Type₀) where
  data Maybe : Type₀ where
    Nothing : Maybe
    Just    : A → Maybe

  data Simple : Type₀ where
    [_] : Maybe → Simple
    sett    : ∀ a → [ Nothing ] ≡ [ Just a ]
    -- apply : (f : A → A) →  [ (Just a) ] ≡ [ (Just (f a)) ]

{-
thought:
  - add path constructors for patches
  - instead of re-proving induction principle, prove equivalent to a coequalizer

this file is different from trivial-hpt in that it uses J-style induction, instead of Paulin-Mohring
hopefully that is equivalent, but need to prove at some point
-}

  postulate
    Simple-path-ind :
      {ℓ : Level}
      (P : {x y : Maybe} → [ x ] ≡ [ y ] → Type ℓ)
      → ({x : Maybe} → P {x = x} refl)
      → ({x : Maybe} {a : A} → (p : [ x ] ≡ [ Nothing ]) → P p ≃ P (p ∙ sett a))
      -------------------------------------------------------------------
      → {x y : Maybe} → (q : [ x ] ≡ [ y ]) → P q

    β-refl :
      {ℓ : Level}
      {P : {x y : Maybe} → [ x ] ≡ [ y ] → Type ℓ}
      {r : {x : Maybe} → P {x = x} refl}
      {e : {x : Maybe} {a : A} → (p : [ x ] ≡ [ Nothing ]) → P p ≃ P (p ∙ sett a)}
      {x : Maybe} →
      Simple-path-ind P r e {x = x} refl ≡ r

    β-sett :
      {ℓ : Level}
      {P : {x y : Maybe} → [ x ] ≡ [ y ] → Type ℓ}
      {r : {x : Maybe} → P {x = x} refl}
      {e : {x : Maybe} {a : A} → (p : [ x ] ≡ [ Nothing ]) → P p ≃ P (p ∙ sett a)} →
      {q : {x y : Maybe} → [ x ] ≡ [ y ]} {a : A}
      {x : Maybe} →
      Simple-path-ind P r e {x = x} (q ∙ sett a) ≡ equivFun (e q) (Simple-path-ind P r e q)

  bin-path-ind : {ℓ : Level}
           → (P  : {x y z w : Maybe} → [ x ] ≡ [ y ] → [ z ] ≡ [ w ] → Type ℓ)
           → ({x z : Maybe} → P {x = x} {z = z} refl refl)
           → ({x z : Maybe}{a : A} → (p : [ z ] ≡ [ Nothing ]) → P {x = x} refl p ≃ P {x = x} refl (p ∙ sett a))
           → ({x : Maybe}{a : A} (p : [ x ] ≡ [ Nothing ]) →
              ({z w : Maybe} (q : [ z ] ≡ [ w ]) → P p q) ≃
              ({z w : Maybe} (q : [ z ] ≡ [ w ]) → P (p ∙ sett a) q))
           --------------------------------------------------------------------------
           → {x y : Maybe} → (p : [ x ] ≡ [ y ]) → {z w : Maybe} → (q : [ z ] ≡ [ w ]) → P p q
  bin-path-ind P r e e' = Simple-path-ind (λ p → ({z w : Maybe} → (q : [ z ] ≡ [ w ]) → P p q)) ind-helper e'
    where
      ind-helper : {x z w : Maybe} (q : [ z ] ≡ [ w ]) → P {x = x} refl q
      ind-helper = Simple-path-ind (λ q → P refl q) r e

  -- {-# REWRITE β-refl #-}
  -- breaks something in src/full/Agda/TypeChecking/Rewriting/NonLinPattern.hs:152

  Span : Maybe → Maybe → Type₀
  Span x y = Σ[ a ∈ Maybe ] ([ a ] ≡ [ x ]) × ([ a ] ≡ [ y ])

  CoSpan : Maybe → Maybe → Type₀
  CoSpan x y = Σ[ b ∈ Maybe ] ([ x ] ≡ [ b ]) × ([ y ] ≡ [ b ])

  Simple-CoSpan : Simple → Simple → Type₀
  Simple-CoSpan x y = Σ[ b ∈ Simple ] (x ≡ b) × (y ≡ b)

  cospan-is-contr : {x y : Simple} → isContr (Simple-CoSpan x y)
  cospan-is-contr {x = x} {y = y} = ([ Nothing ] , foo , foo) , {!!}
    where
      foo : {base : Simple} → base ≡ [ Nothing ]
      foo {base = [ Nothing ]} = refl
      foo {base = [ Just x ]} = sym (sett x)
      foo {base = sett a i} = λ j → sett a  (i ∧ ~ j)

      bar :  (cs : Simple-CoSpan x y) → ([ Nothing ] , foo , foo) ≡ cs
      bar (base , p , q) = λ i → (foo {base = base} (~ i)) , (λ j → p (~ i ∧ j)), λ j → q {!!}
      -- ?0 : x ≡ foo (~ i)
      -- ?1 : y ≡ foo (~ i)

  -- the dumbest merge, mapping everything to (base, p⁻¹, q⁻¹)
  thunk : {x y : Maybe} → Span x y → CoSpan x y
  thunk {x = x} {y = y} (base , p , q) = bin-path-ind (λ _ _ → CoSpan x y)
                                                      (base , sym p , sym q)
                                                      (λ _ → idEquiv (CoSpan x y))
                                                      (λ _ → idEquiv ({z w : Maybe} (_ : [ z ] ≡ [ w ]) → CoSpan x y))
                                                      {y = x} p
                                                      {w = y} q

  contract-left-equiv : {left right : Maybe} → ({x z : Maybe}{a : A} → (p : [ z ] ≡ [ Nothing ]) → CoSpan left right ≃ CoSpan left right)
  contract-left-equiv {left = left} {right = right} _ = func , {!!}
    where
      func : CoSpan left right → CoSpan left right
      func (_ , p , q) = left , refl , q ∙ sym p

  merge : {x y : Maybe} → Span x y → CoSpan x y
  merge = thunk

open module test = repo Int

sett0 = sett 0
sett1 = sett 1

span1 : Span (Just 0) (Just 1)
span1 = Nothing , (sett0 , sett1)

merge1 = merge span1

span2 : Span Nothing Nothing
span2 = Nothing , (refl , refl)

merge2 = merge span2
