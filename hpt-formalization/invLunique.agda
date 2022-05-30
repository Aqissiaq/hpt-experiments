{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

result : {X : Type} {x y : X} →
         (p q : x ≡ y) → (sym p ∙ q ≡ refl) ≡ (q ≡ p)
result {X} {x}= J P r
  where
  P : (y' : X) → x ≡ y' → Type (ℓ-suc ℓ-zero)
  P y' p' = (q' : x ≡ y') → (sym p' ∙ q' ≡ refl) ≡ (q' ≡ p')

  r : P x refl
  r q' = sym refl ∙ q' ≡ refl ≡⟨ cong (λ p → p ∙ q' ≡ refl) symRefl ⟩
         refl ∙ q' ≡ refl     ≡⟨ sym (cong (_≡ refl) (lUnit q')) ⟩
         (q' ≡ refl) ∎

