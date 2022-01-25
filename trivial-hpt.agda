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

  mergeId : {x y : Maybe} → Span x y → CoSpan x y
  mergeId {x = x} {y = y} (base , p , q) =
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

  -- the equivalences for merge
  mergeEqRight : {x : Maybe} (a : A) → CoSpan x Nothing → CoSpan x (Just a)
  mergeEqRight a (nadir , p' , q') = nadir , p' , (sym (sett a)) ∙ q'

  mergeEqLeft : {x : Maybe} (a : A) → CoSpan x (Just a) → CoSpan x Nothing
  mergeEqLeft a (nadir , p' , q') = nadir , p' , (sett a) ∙ q'

  mergeEquiv : {x : Maybe} (a : A) → CoSpan x Nothing ≃ CoSpan x (Just a)
  mergeEquiv a = isoToEquiv (iso (mergeEqRight a) (mergeEqLeft a) (unglue-glue a) (glue-unglue a))
    where
    unglue-glue : (a : A) → section (mergeEqRight a) (mergeEqLeft a)
    unglue-glue a (nadir , p' , q') = mergeEqRight a (mergeEqLeft a (nadir , p' , q'))
      ≡⟨ refl ⟩ nadir , p' , sym (sett a) ∙ (sett a ∙ q')
      ≡⟨ cong (λ r → (nadir , p' , r)) (assoc _ _ _) ⟩ nadir , p' , (sym (sett a) ∙ sett a) ∙ q'
      ≡⟨ cong (λ r → (nadir , p' , r ∙ q')) (lCancel _) ⟩ nadir , p' , refl ∙ q'
      ≡⟨ cong (λ r → (nadir , p' , r)) (sym (lUnit _)) ⟩ (nadir , p' , q') ∎

    glue-unglue : (a : A) → retract (mergeEqRight a) (mergeEqLeft a)
    glue-unglue a (nadir , p' , q') = mergeEqLeft a (mergeEqRight a (nadir , p' , q'))
      ≡⟨ refl ⟩ nadir , p' , sett a ∙ (sym (sett a) ∙ q')
      ≡⟨ cong (λ r → (nadir , p' , r)) (assoc _ _ _) ⟩ nadir , p' , (sett a ∙ sym (sett a)) ∙ q'
      ≡⟨ cong (λ r → (nadir , p' , r ∙ q')) (rCancel _) ⟩ nadir , p' , refl ∙ q'
      ≡⟨ cong (λ r → (nadir , p' , r)) (sym (lUnit _)) ⟩ (nadir , p' , q') ∎

  mergeEqRight' : (a : A) {x : Maybe} → CoSpan Nothing x → CoSpan (Just a) x
  mergeEqRight' a (nadir , p' , q') = nadir , (sym (sett a)) ∙ p' , q'

  mergeEqLeft' : (a : A) {x : Maybe}  → CoSpan (Just a) x → CoSpan Nothing x
  mergeEqLeft' a (nadir , p' , q') = nadir , (sett a) ∙ p' , q'

  mergeEquiv' : (a : A) → {x : Maybe} → CoSpan Nothing x ≃ CoSpan (Just a) x
  mergeEquiv' a = isoToEquiv (iso (mergeEqRight' a)
                             (mergeEqLeft' a)
                             (left-right a)
                             (right-left a))
    where
    left-right : (a : A) {x : Maybe} → section (mergeEqRight' a {x}) (mergeEqLeft' a)
    left-right a {x} (nadir , p' , q') = mergeEqRight' a (mergeEqLeft' a (nadir , p' , q'))
      ≡⟨ refl ⟩ nadir , sym (sett a) ∙ (sett a ∙ p') , q'
      ≡⟨ cong (λ r → (nadir , r , q')) (assoc _ _ _) ⟩ nadir , (sym (sett a) ∙ sett a) ∙ p' , q'
      ≡⟨ cong compExplicit (lCancel _) ⟩ nadir , refl ∙ p' , q'
      ≡⟨ cong (λ r → (nadir , r , q')) (sym (lUnit _)) ⟩ (nadir , p' , q') ∎
        where
        -- need to explicitly type this for warnings (why?)
        compExplicit : [ Just a ] ≡ [ Just a ] → CoSpan (Just a) x
        compExplicit r = (nadir , r ∙ p' , q')

    right-left : (a : A) {x : Maybe} → retract (mergeEqRight' a {x}) (mergeEqLeft' a)
    right-left a {x} (nadir , p' , q') = mergeEqLeft' a (mergeEqRight' a (nadir , p' , q'))
      ≡⟨ refl ⟩ nadir , sett a ∙ (sym (sett a) ∙ p') , q'
      ≡⟨ cong (λ r → (nadir , r , q')) (assoc _ _ _) ⟩ nadir , (sett a ∙ sym (sett a)) ∙ p' , q'
      ≡⟨ cong compExplicit (rCancel _ ) ⟩ nadir , refl ∙ p' , q'
      ≡⟨ cong (λ r → nadir , r , q') (sym (lUnit _)) ⟩ (nadir , p' , q') ∎
        where
        compExplicit : [ Nothing ] ≡ [ Nothing ] → CoSpan Nothing x
        compExplicit r = (nadir , r ∙ p' , q')

  merge : {x y : Maybe} → Span x y → CoSpan x y
  merge (Nothing , p , q) = bin-path-ind Nothing (λ {b} {c} _ _ → CoSpan b c)
                                                  (Nothing , refl , refl)
                                                  (λ {a} _ → mergeEquiv a)
                                                  (λ {a} _ → lemma-compEquiv (mergeEquiv' a))
                             p q
  merge (Just a , p , q) = bin-path-ind (Just a) (λ {b} {c} _ _ → CoSpan b c)
                                         (Just a , refl , refl)
                                         (λ {b} _ → mergeEquiv b)
                                         (λ {b} _ → lemma-compEquiv (mergeEquiv' b))
                            p q

  -- computing
  -- actually nvm, I want to factor out the equivalences before we do this
  -- sett-sett : {a b : A} → merge' (Nothing , (sett a) , (sett b)) ≡ (Nothing , sym (sett a) , sym (sett b))
  -- sett-sett {a} {b} = merge' (Nothing , (sett a) , (sett b))
  --   ≡⟨ {!!} ⟩ ?
  --   ≡⟨ {!!} ⟩ (Nothing , sym (sett a) , sym (sett b)) ∎
  --     where
  --     P {b} {c} _ _ = CoSpan b c
  --     r = (Nothing , refl , refl)
  --     e = (λ {a} _ → e a)
  --     (λ {a} _ → lemma-compEquiv (e' a))
