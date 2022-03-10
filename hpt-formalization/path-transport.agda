{-# OPTIONS --cubical --rewriting #-}
{-
Implementing Theorem 2.11.3 from the book because I need it
-}

module path-transport where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.GroupoidLaws

private
  variable
    ℓ ℓ' : Level

module _ {A B : Type ℓ} {a a' : A} where

  -- Lemma 2.3.10
  transport-comp : (f : A → B) → (P : B → Type ℓ') → (p : a ≡ a') → (u : P (f a)) →
    subst (P ∘ f) p u ≡ subst P (cong f p) u
  transport-comp f P p u = J (λ x q → (subst (P ∘ f) q u) ≡ (subst P (cong f q) u))
    (substRefl {B = P ∘ f} u ∙ sym (substRefl {B = P} u)) p

  -- Theorem 2.11.3
  transport-in-paths : (f g : A → B) → (p : a ≡ a') (q : f a ≡ g a) →
    subst (λ x → f x ≡ g x) p q ≡ sym (cong f p) ∙ q ∙ cong g p
  transport-in-paths f g p q =
    J (λ x p' → (subst (λ y → f y ≡ g y) p' q) ≡ (sym (cong f p') ∙ q ∙ cong g p'))
    p=refl p
    where
    p=refl : subst (λ y → f y ≡ g y) refl q ≡
          (λ i → f (refl {x = a} (~ i))) ∙ q ∙ (λ i → g (refl {x = a} i))
    p=refl = subst (λ y → f y ≡ g y) refl q
           ≡⟨ substRefl {B = (λ y → f y ≡ g y)} q ⟩ q
           ≡⟨ (rUnit q) ∙ lUnit (q ∙ refl) ⟩ refl {x = f a} ∙ q ∙ refl {x = g a} ∎
