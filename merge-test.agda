{-# OPTIONS --cubical --rewriting #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws

module merge-test where

module repo (A : Type₀) where
  data Maybe : Type₀ where
    Nothing : Maybe
    Just    : A → Maybe

  data Simple : Type₀ where
    [_] : Maybe → Simple
    sett    : ∀ a → [ Nothing ] ≡ [ Just a ]
    -- apply : (f : A → A) →  [ (Just a) ] ≡ [ (Just (f a)) ]

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

  makeCoSpan : {x y : Maybe} → (nadir : Maybe) → (p : [ x ] ≡ [ nadir ]) → (q : [ y ] ≡ [ nadir ]) → CoSpan x y
  makeCoSpan n p q = n , p , q

  -- massaging the types of equivΠ to fit in my holes
  lemma-compEquiv : {X : Type} {A B C : X → Type} → ({x : X} → A x ≃ B x)
                  → ({x : X} → (q : C x) → A x) ≃ ({x : X} → (q : C x) → B x)
  lemma-compEquiv e = equivImplicitΠCod (equivΠCod λ _ → e)


  merge : {z : Maybe} →
          {x : Maybe} → (p : [ z ] ≡ [ x ]) →
          {y : Maybe} → (q : [ z ] ≡ [ y ]) →
          {n : Maybe} → ([ x ] ≡ [ n ]) × ([ y ] ≡ [ n ])
  merge {Nothing} = bin-path-ind Nothing
                           (λ {b} {c} p q → ({n : Maybe} → ([ b ] ≡ [ n ]) × ([ c ] ≡ [ n ] )))
                           r e e'
    where
    r : {n : Maybe} → ([ Nothing ] ≡ [ n ]) × ([ Nothing ] ≡ [ n ])
    r {Nothing} = refl , refl
    r {Just x} = sett x , sett x

    e-right : {a : A} {x : Maybe} →
              ([ Nothing ] ≡ [ x ]) × ([ Nothing ] ≡ [ x ]) →
              ([ Nothing ] ≡ [ x ]) × ([ Just a ] ≡ [ x ])
    e-right {a} (p , q) = p , sym (sett a) ∙ q

    e-left : {a : A} {x : Maybe} →
            ([ Nothing ] ≡ [ x ]) × ([ Just a ] ≡ [ x ]) →
            ([ Nothing ] ≡ [ x ]) × ([ Nothing ] ≡ [ x ])
    e-left {a} (p , q) = p , sett a ∙ q

    left-inverse : {a : A} {x : Maybe} →
                   section (e-right {a} {x}) e-left
    left-inverse {a} (p , q) = (p , sym (sett a) ∙ ((sett a) ∙ q))
      ≡⟨ ≡-× refl (assoc _ _ _) ⟩ p , (sym (sett a) ∙ (sett a) ) ∙ q
      ≡⟨ ≡-× refl (cong (λ r → r ∙ q) (lCancel _)) ⟩ p , refl ∙ q
      ≡⟨ ≡-× refl (sym (lUnit _)) ⟩ (p , q) ∎

    right-inverse : {a : A} {x : Maybe} →
                    retract (e-right {a} {x}) e-left
    right-inverse {a} (p , q) = (p , (sett a) ∙ (sym (sett a) ∙ q))
      ≡⟨ ≡-× refl (assoc _ _ _) ⟩ (p , ((sett a) ∙ (sym (sett a))) ∙ q)
      ≡⟨ ≡-× refl (cong (λ r → r ∙ q) (rCancel _)) ⟩ (p , refl ∙ q)
      ≡⟨ ≡-× refl (sym (lUnit _)) ⟩ (p , q) ∎

    e : {x : A} (p : [ Nothing ] ≡ [ Nothing ]) →
        ({n : Maybe} → ([ Nothing ] ≡ [ n ]) × ([ Nothing ] ≡ [ n ])) ≃
        ({n : Maybe} → ([ Nothing ] ≡ [ n ]) × ([ Just x ] ≡ [ n ]))
    e _ = equivImplicitΠCod (isoToEquiv (iso e-right e-left left-inverse right-inverse))

    e'-right : {a : A} {x : Maybe} →
               ({n : Maybe} → ([ Nothing ] ≡ [ n ]) × ([ x ] ≡ [ n ])) →
               {n : Maybe} → ([ Just a ] ≡ [ n ]) × ([ x ] ≡ [ n ])
    e'-right {a} f {n} = (sym (sett a)) ∙ (fst (f {n})) , snd (f {n})

    e'-left : {a : A} {x : Maybe} →
              ({n : Maybe} → ([ Just a ] ≡ [ n ]) × ([ x ] ≡ [ n ])) →
              {n : Maybe} → ([ Nothing ] ≡ [ n ]) × ([ x ] ≡ [ n ])
    e'-left {a} f {n} = (sett a) ∙ (fst (f {n})) , snd (f {n})

    left'-inverse : {a : A} {x : Maybe} →
                    section (e'-right {a} {x}) e'-left
    left'-inverse {a} {x} f = implicitFunExt pointwise
      where
      pointwise : {n : Maybe} →
                  PathP (λ _ → ([ Just a ] ≡ [ n ]) × ([ x ] ≡ [ n ]))
                  (e'-right {a} {x} (e'-left f)) f
      -- this is a nicer way to do the ×-proofs imo
      pointwise {n} = ≡-×
        (sym (sett a) ∙ (sett a) ∙ (fst f)
          ≡⟨ assoc _ _ _ ⟩ (sym (sett a) ∙ (sett a)) ∙ (fst f)
          ≡⟨ cong (λ p → p ∙ (fst (f {n}))) (rCancel _) ⟩ refl ∙ (fst f)
          ≡⟨ sym (lUnit _) ⟩ fst f ∎)
        refl

    right'-inverse : {a : A} {x : Maybe} →
                     retract (e'-right {a} {x}) e'-left
    right'-inverse {a} {x} f = implicitFunExt pointwise
      where
      pointwise : {n : Maybe} →
                  PathP (λ _ → ([ Nothing ] ≡ [ n ]) × ([ x ] ≡ [ n ]))
                        (e'-left {a} {x} (e'-right f)) f
      pointwise {n} = ≡-×
        (sett a ∙ (sym (sett a)) ∙ fst f
          ≡⟨ assoc _ _ _ ⟩ ((sett a) ∙ (sym (sett a))) ∙ fst f
          ≡⟨ cong (λ p → p ∙ (fst (f {n}))) (lCancel _) ⟩ refl ∙ fst f
          ≡⟨ sym (lUnit _) ⟩ fst f ∎)
        refl

    e' : {x : A} (p : [ Nothing ] ≡ [ Nothing ]) →
        ({c : Maybe} (q : [ Nothing ] ≡ [ c ]) {n : Maybe} →
            ([ Nothing ] ≡ [ n ]) × ([ c ] ≡ [ n ]))
        ≃ ({c : Maybe} (q : [ Nothing ] ≡ [ c ]) {n : Maybe} →
              ([ Just x ] ≡ [ n ]) × ([ c ] ≡ [ n ]))
    e' _ = lemma-compEquiv (isoToEquiv (iso e'-right e'-left left'-inverse right'-inverse))

  merge {Just a} = bin-path-ind (Just a)
    (λ {b} {c} p q → ({n : Maybe} → ([ b ] ≡ [ n ]) × ([ c ] ≡ [ n ] )))
    r e {!!}
    where
    r : {n : Maybe} → ([ Just a ] ≡ [ n ]) × ([ Just a ] ≡ [ n ])
    r {Nothing} = sym (sett a) , sym (sett a)
    r {Just x} = (sym (sett a)) ∙ (sett x) , (sym (sett a)) ∙ (sett x)

    e-right : {x : A} {n : Maybe} →
              ([ Just a ] ≡ [ n ]) × ([ Nothing ] ≡ [ n ]) →
              ([ Just a ] ≡ [ n ]) × ([ Just x ] ≡ [ n ])
    e-right {x} (left , right) = left , sym (sett x) ∙ right

    e-left : {x : A} {n : Maybe} →
             ([ Just a ] ≡ [ n ]) × ([ Just x ] ≡ [ n ]) →
             ([ Just a ] ≡ [ n ]) × ([ Nothing ] ≡ [ n ])
    e-left {x} (left , right) = {!!} , {!!}

    e : {x : A} (p : [ Just a ] ≡ [ Nothing ]) →
        ({n : Maybe} → ([ Just a ] ≡ [ n ]) × ([ Nothing ] ≡ [ n ])) ≃
        ({n : Maybe} → ([ Just a ] ≡ [ n ]) × ([ Just x ] ≡ [ n ]))
    e p = equivImplicitΠCod (isoToEquiv (iso e-right e-left {!!} {!!}))
