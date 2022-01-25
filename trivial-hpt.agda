{-# OPTIONS --cubical --rewriting #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws

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
      {q : [ a0 ] ≡ [ Nothing ]} {x : A} →
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

  -- massaging the types of equivΠ to fit in my holes
  lemma-compEquiv : {X : Type} {A B C : X → Type} → ({x : X} → A x ≃ B x)
                  → ({x : X} → (q : C x) → A x) ≃ ({x : X} → (q : C x) → B x)
  lemma-compEquiv e = equivImplicitΠCod (equivΠCod λ _ → e)

  merge' : {x y : Maybe} → Span x y → CoSpan x y
  merge' (Nothing , p , q) = bin-path-ind Nothing (λ {b} {c} _ _ → CoSpan b c)
                                                  (Nothing , refl , refl)
                                                  (λ {a} _ → e a)
                                                  (λ {a} _ → lemma-compEquiv (e' a))
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

      glue-on' : (a : A) {x : Maybe} → CoSpan Nothing x → CoSpan (Just a) x
      glue-on' a (nadir , p' , q') = nadir , (sym (sett a)) ∙ p' , q'

      un-glue' : (a : A) {x : Maybe}  → CoSpan (Just a) x → CoSpan Nothing x
      un-glue' a (nadir , p' , q') = nadir , (sett a) ∙ p' , q'

      unglue-glue' : (a : A) {x : Maybe} → section (glue-on' a {x}) (un-glue' a)
      unglue-glue' a {x} (nadir , p' , q') = glue-on' a (un-glue' a (nadir , p' , q'))
        ≡⟨ refl ⟩ nadir , sym (sett a) ∙ (sett a ∙ p') , q'
        ≡⟨ cong (λ r → (nadir , r , q')) (assoc _ _ _) ⟩ nadir , (sym (sett a) ∙ sett a) ∙ p' , q'
        ≡⟨ cong compExplicit (lCancel _) ⟩ nadir , refl ∙ p' , q'
        ≡⟨ cong (λ r → (nadir , r , q')) (sym (lUnit _)) ⟩ (nadir , p' , q') ∎
          where
          -- need to explicitly type this for warnings (why?)
          compExplicit : [ Just a ] ≡ [ Just a ] → CoSpan (Just a) x
          compExplicit r = (nadir , r ∙ p' , q')

      glue-unglue' : (a : A) {x : Maybe} → retract (glue-on' a {x}) (un-glue' a)
      glue-unglue' a {x} (nadir , p' , q') = un-glue' a (glue-on' a (nadir , p' , q'))
        ≡⟨ refl ⟩ nadir , sett a ∙ (sym (sett a) ∙ p') , q'
        ≡⟨ cong (λ r → (nadir , r , q')) (assoc _ _ _) ⟩ nadir , (sett a ∙ sym (sett a)) ∙ p' , q'
        ≡⟨ cong compExplicit (rCancel _ ) ⟩ nadir , refl ∙ p' , q'
        ≡⟨ cong (λ r → nadir , r , q') (sym (lUnit _)) ⟩ (nadir , p' , q') ∎
          where
          compExplicit : [ Nothing ] ≡ [ Nothing ] → CoSpan Nothing x
          compExplicit r = (nadir , r ∙ p' , q')


      e' : (a : A) → {x : Maybe} → CoSpan Nothing x ≃ CoSpan (Just a) x
      e' a = isoToEquiv (iso (glue-on' a) (un-glue' a) (unglue-glue' a) (glue-unglue' a))

-- this basically identical, but the types are different. not very elegant
  merge' (Just a , p , q) = bin-path-ind (Just a) (λ {b} {c} _ _ → CoSpan b c)
                                         (Just a , refl , refl)
                                         (λ {x} _ → e x)
                                         (λ {x} _ → lemma-compEquiv (e' x))
                            p q
         where
           un-glue : (x : A) → CoSpan (Just a) Nothing → CoSpan (Just a) (Just x)
           un-glue x (nadir , p' , q') = nadir , p' , (sym (sett x)) ∙ q'

           glue-on : (x : A) → CoSpan (Just a) (Just x) → CoSpan (Just a) Nothing
           glue-on x (nadir , p' , q') = nadir , p' , (sett x) ∙ q'

           glue-un-glue-on : (x : A) → section (un-glue x) (glue-on x)
           glue-un-glue-on x (nadir , p' , q') = un-glue x (glue-on x (nadir , p' , q'))
             ≡⟨ refl ⟩ (nadir , p' , sym (sett x) ∙ sett x ∙ q')
             ≡⟨ cong (λ r → (nadir , p' , r)) (assoc _ _ _) ⟩ (nadir , p' , (sym (sett x) ∙ sett x) ∙ q')
             ≡⟨ cong (λ r → (nadir , p' , r ∙ q')) (lCancel _) ⟩ (nadir , p' , refl ∙ q')
             ≡⟨ cong (λ r → (nadir , p' , r)) (sym (lUnit _)) ⟩ (nadir , p' , q') ∎

           un-glue-glue-on : (x : A) → retract (un-glue x) (glue-on x)
           un-glue-glue-on x (nadir , p' , q') = glue-on x (un-glue x (nadir , p' , q'))
             ≡⟨ refl ⟩ nadir , p' , sett x ∙ (sym (sett x) ∙ q')
             ≡⟨ cong (λ r → (nadir , p' , r)) (assoc _ _ _) ⟩ nadir , p' , (sett x ∙ sym (sett x)) ∙ q'
             ≡⟨ cong (λ r → (nadir , p' , r ∙ q')) (rCancel _) ⟩ nadir , p' , refl ∙ q'
             ≡⟨ cong (λ r → (nadir , p' , r)) (sym (lUnit _)) ⟩ (nadir , p' , q') ∎

           e : (x : A) → CoSpan (Just a) Nothing ≃ CoSpan (Just a) (Just x)
           e x = isoToEquiv (iso (un-glue x) (glue-on x) (glue-un-glue-on x) (un-glue-glue-on x))

           -- all the _' stuff is identical to unprimed *including* types ?¿
           glue-on' : (a : A) {x : Maybe} → CoSpan Nothing x → CoSpan (Just a) x
           glue-on' a (nadir , p' , q') = nadir , (sym (sett a)) ∙ p' , q'

           un-glue' : (a : A) {x : Maybe}  → CoSpan (Just a) x → CoSpan Nothing x
           un-glue' a (nadir , p' , q') = nadir , (sett a) ∙ p' , q'

           unglue-glue' : (a : A) {x : Maybe} → section (glue-on' a {x}) (un-glue' a)
           unglue-glue' a {x} (nadir , p' , q') = glue-on' a (un-glue' a (nadir , p' , q'))
             ≡⟨ refl ⟩ nadir , sym (sett a) ∙ (sett a ∙ p') , q'
             ≡⟨ cong (λ r → (nadir , r , q')) (assoc _ _ _) ⟩ nadir , (sym (sett a) ∙ sett a) ∙ p' , q'
             ≡⟨ cong compExplicit (lCancel _) ⟩ nadir , refl ∙ p' , q'
             ≡⟨ cong (λ r → (nadir , r , q')) (sym (lUnit _)) ⟩ (nadir , p' , q') ∎
               where
               -- need to explicitly type this for warnings (why?)
               compExplicit : [ Just a ] ≡ [ Just a ] → CoSpan (Just a) x
               compExplicit r = (nadir , r ∙ p' , q')

           glue-unglue' : (a : A) {x : Maybe} → retract (glue-on' a {x}) (un-glue' a)
           glue-unglue' a {x} (nadir , p' , q') = un-glue' a (glue-on' a (nadir , p' , q'))
             ≡⟨ refl ⟩ nadir , sett a ∙ (sym (sett a) ∙ p') , q'
             ≡⟨ cong (λ r → (nadir , r , q')) (assoc _ _ _) ⟩ nadir , (sett a ∙ sym (sett a)) ∙ p' , q'
             ≡⟨ cong compExplicit (rCancel _ ) ⟩ nadir , refl ∙ p' , q'
             ≡⟨ cong (λ r → nadir , r , q') (sym (lUnit _)) ⟩ (nadir , p' , q') ∎
               where
               compExplicit : [ Nothing ] ≡ [ Nothing ] → CoSpan Nothing x
               compExplicit r = (nadir , r ∙ p' , q')

           e' : (a : A) → {x : Maybe} → CoSpan Nothing x ≃ CoSpan (Just a) x
           e' a = isoToEquiv (iso (glue-on' a) (un-glue' a) (unglue-glue' a) (glue-unglue' a))
