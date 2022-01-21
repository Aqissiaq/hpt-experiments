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
open import Cubical.Foundations.GroupoidLaws

open import Data.Bool
  using(if_then_else_)

module trivial-hpt where

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
-}

  postulate
    Simple-path-ind :
      {ℓ : Level}
      {a0 : Maybe}
      (P : {x : Maybe} → [ a0 ] ≡ [ x ] → Type ℓ)
      → P refl
      → ({x : A} → (p : [ a0 ] ≡ [ Nothing ]) → P p ≃ P (p ∙ sett x))
      -------------------------------------------------------------------
      → {b : Maybe} → (q : [ a0 ] ≡ [ b ]) → P q

    β-refl :
      {a0 : Maybe}
      {P : {x : Maybe} → [ a0 ] ≡ [ x ] → Type₀}
      {r : P refl}
      {e : {x : A} → (p : [ a0 ] ≡ [ Nothing ]) → P p ≃ P (p ∙ sett x)} →
      Simple-path-ind P r e refl ≡ r

    β-path :
      {a0 : Maybe}
      {P : {x : Maybe} → [ a0 ] ≡ [ x ] → Type₀}
      {r : P refl}
      {e : {x : A} → (p : [ a0 ] ≡ [ Nothing ]) → P p ≃ P (p ∙ sett x)}
      {q : [ a0 ] ≡ [ Nothing ]} {x : A} → -- note 100% sure this x:A is free
      Simple-path-ind P r e (q ∙ (sett x)) ≡ equivFun (e q) (Simple-path-ind P r e q)

  bin-path-ind : {ℓ : Level} → (a0 : Maybe)
           → (P  : {b c : Maybe} → [ a0 ] ≡ [ b ] → [ a0 ] ≡ [ c ] → Type ℓ)
           → (P refl refl)
           → ({x : A} → (p : [ a0 ] ≡ [ Nothing ]) → P refl p ≃ P refl (p ∙ sett x))
           → ({x : A} (p : [ a0 ] ≡ [ Nothing ]) →
              ({c : Maybe} (q : [ a0 ] ≡ [ c ]) → P p q) ≃
              ({c : Maybe} (q : [ a0 ] ≡ [ c ]) → P (p ∙ sett x) q))
           --------------------------------------------------------------------------
           → {b : Maybe} → (p : [ a0 ] ≡ [ b ]) → {c : Maybe} → (q : [ a0 ] ≡ [ c ]) → P p q
  bin-path-ind a0 P r e e' = Simple-path-ind (λ p → ({c : Maybe} → (q : [ a0 ] ≡ [ c ]) → P p q)) ind-helper e'
    where
      ind-helper : {c : Maybe} (q : [ a0 ] ≡ [ c ]) → P refl q
      ind-helper = Simple-path-ind (λ p → P refl p) r e

  -- {-# REWRITE β-refl #-}
  -- breaks something in src/full/Agda/TypeChecking/Rewriting/NonLinPattern.hs:152
  -- https://github.com/agda/agda/issues/5589

  Span : Maybe → Maybe → Type₀
  Span x y = Σ[ a ∈ Maybe ] ( [ a ] ≡ [ x ] ) × ([ a ] ≡ [ y ])

  CoSpan : Maybe → Maybe → Type₀
  CoSpan x y = Σ[ b ∈ Maybe ] ([ x ] ≡ [ b ]) × ([ y ] ≡ [ b ])

  merge : {x y : Maybe} → Span x y → CoSpan x y
  merge {x = x} {y = y} (base , p , q) =
    bin-path-ind base
                 (λ _ _ → CoSpan x y)
                 (base , (sym p , sym q))
                 (λ _ → idEquiv (CoSpan x y))
                 (λ _ → idEquiv ({c : Maybe} (q₁ : [ base ] ≡ [ c ]) → CoSpan x y))
                 p q

  merge' : {x y : Maybe} → Span x y → CoSpan x y
  merge' (Nothing , p , q) = bin-path-ind Nothing (λ {b} {c} _ _ → CoSpan b c)
                                                  (Nothing , refl , refl)
                                                  (λ {a} _ → e a)
                                                  (λ {a} _ → e' a)
                             p q
    where
      glue-on : (a : A) → CoSpan Nothing Nothing → CoSpan Nothing (Just a)
      glue-on a (nadir , p' , q') = nadir , p' , (sym (sett a)) ∙ q'

      un-glue : (a : A) → CoSpan Nothing (Just a) → CoSpan Nothing Nothing
      un-glue a (nadir , p' , q') = nadir , p' , (sett a) ∙ q'

      unglue-glue : (a : A) → section (glue-on a) (un-glue a)
      unglue-glue a (nadir , p' , q') = glue-on a (un-glue a (nadir , p' , q'))
        ≡⟨ refl ⟩ nadir , p' , sym (sett a) ∙ (sett a ∙ q')
        ≡⟨ cong (λ r → (nadir , p' , r)) (assoc _ _ _) ⟩ nadir , p' , (sym (sett a) ∙ sett a) ∙ q'
        ≡⟨ cong (λ r → (nadir , p' , r ∙ q')) (lCancel _) ⟩ nadir , p' , refl ∙ q'
        ≡⟨ cong (λ r → (nadir , p' , r)) (sym (lUnit _)) ⟩ (nadir , p' , q') ∎

      glue-unglue : (a : A) → retract (glue-on a) (un-glue a)
      glue-unglue a (nadir , p' , q') = un-glue a (glue-on a (nadir , p' , q'))
        ≡⟨ refl ⟩ nadir , p' , sett a ∙ (sym (sett a) ∙ q')
        ≡⟨ cong (λ r → (nadir , p' , r)) (assoc _ _ _) ⟩ nadir , p' , (sett a ∙ sym (sett a)) ∙ q'
        ≡⟨ cong (λ r → (nadir , p' , r ∙ q')) (rCancel _) ⟩ nadir , p' , refl ∙ q'
        ≡⟨ cong (λ r → (nadir , p' , r)) (sym (lUnit _)) ⟩ (nadir , p' , q') ∎

      e : (a : A) → CoSpan Nothing Nothing ≃ CoSpan Nothing (Just a)
      e a = isoToEquiv (iso (glue-on a) (un-glue a) (unglue-glue a) (glue-unglue a))

      e' : (a : A) → ({c : Maybe} → (q' : [ Nothing ] ≡ [ c ]) → CoSpan Nothing c)
                  ≃ ({c : Maybe} → (q' : [ Nothing ] ≡ [ c ]) → CoSpan (Just a) c)
      e' a = {!!}

  merge' (Just a , p , q) = bin-path-ind (Just a) (λ {b} {c} _ _ → CoSpan b c)
                                         (Just a , refl , refl)
                                         (λ {x} _ → e x)
                                         (λ _ → {!!})
                            p q
         where
           unset : (x : A) → CoSpan (Just a) Nothing → CoSpan (Just a) (Just x)
           unset x (nadir , p' , q') = nadir , p' , (sym (sett x)) ∙ q'

           set : (x : A) → CoSpan (Just a) (Just x) → CoSpan (Just a) Nothing
           set x (nadir , p' , q') = nadir , p' , (sett x) ∙ q'

           set-unset : (x : A) → section (unset x) (set x)
           set-unset x (nadir , p' , q') = unset x (set x (nadir , p' , q'))
             ≡⟨ refl ⟩ (nadir , p' , sym (sett x) ∙ sett x ∙ q')
             ≡⟨ cong (λ r → (nadir , p' , r)) (assoc _ _ _) ⟩ (nadir , p' , (sym (sett x) ∙ sett x) ∙ q')
             ≡⟨ cong (λ r → (nadir , p' , r ∙ q')) (lCancel _) ⟩ (nadir , p' , refl ∙ q')
             ≡⟨ cong (λ r → (nadir , p' , r)) (sym (lUnit _)) ⟩ (nadir , p' , q') ∎

           unset-set : (x : A) → retract (unset x) (set x)
           unset-set x (nadir , p' , q') = set x (unset x (nadir , p' , q'))
             ≡⟨ refl ⟩ nadir , p' , sett x ∙ (sym (sett x) ∙ q')
             ≡⟨ cong (λ r → (nadir , p' , r)) (assoc _ _ _) ⟩ nadir , p' , (sett x ∙ sym (sett x)) ∙ q'
             ≡⟨ cong (λ r → (nadir , p' , r ∙ q')) (rCancel _) ⟩ nadir , p' , refl ∙ q'
             ≡⟨ cong (λ r → (nadir , p' , r)) (sym (lUnit _)) ⟩ (nadir , p' , q') ∎

           e : (x : A) → CoSpan (Just a) Nothing ≃ CoSpan (Just a) (Just x)
           e x = isoToEquiv (iso (unset x) (set x) (set-unset x) (unset-set x))
