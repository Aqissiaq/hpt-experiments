module J-test where
open import Relation.Binary.PropositionalEquality
-- attempting to use J to define binary path induction
-- in the hopes that this will be enlightening for the HIT case

J : ∀ {ℓ ℓ'} → {A : Set ℓ}
             → (P : (x y : A) → x ≡ y → Set ℓ')
             → ((x : A) → P x x refl)
             -----------------------------------------------------------
             → ((x y : A) → (p : x ≡ y) → P x y p)
J P c x .x refl = c x

bin-J : ∀ {ℓ ℓ'} → {A : Set ℓ}
        → (P : (x y : A) → x ≡ y → (z w : A) → z ≡ w → Set ℓ')
        → ((x y : A) → P x x refl y y refl)
        -----------------------------------------------------------
        → ((x y : A) → (p : x ≡ y) → (z w : A) → (q : z ≡ w) → P x y p z w q)
bin-J P c x .x refl z .z refl = c x z
-- it wasn't

bin-ind : ∀ {ℓ ℓ'} → {A : Set ℓ}
          → (P : (x y : A) → x ≡ y → (z w : A) → z ≡ w → Set ℓ')
          → ((x : A) → ((z w : A) → (q : z ≡ w) → P x x refl z w q))
          → ((x y : A) → (p : x ≡ y) → (z : A) → (P x y p z z refl))
          -----------------------------------------------------------
          → ((x y : A) → (p : x ≡ y) → (z w : A) → (q : z ≡ w) → P x y p z w q)
bin-ind {A = A} P c c' = λ x y p z w q → ψ x y p (ϕ x y p) z w q
  where
  Q : (x y : A) → x ≡ y → Set _
  Q x y p = (z w : A) → (q : z ≡ w) → P x y p z w q

  ϕ : (x y : A) → (p : x ≡ y) → Q x y p
  ϕ = J Q c

  ψ : (x y : A) → (p : x ≡ y) → Q x y p
      → (z w : A) → (q : z ≡ w) → P x y p z w q
  ψ x y p f = J (λ z w q → P x y p z w q) (c' x y p)

-- same problem as before: we don't actually use the f!

-- Paulin-Mohring style
PM-J : ∀ {ℓ ℓ'} {A : Set ℓ} → (x : A)
       → (P : (y : A) → x ≡ y → Set ℓ')
       → P x refl
       ----------------------------------------
       → (y : A) → (p : x ≡ y) → P y p
PM-J x P c .x refl = c

bin-PM : ∀ {ℓ ℓ'} {A : Set ℓ} → (x z : A)
         → (P : (y w : A) → x ≡ y → z ≡ w → Set ℓ')
         → P x z refl refl
         -----------------------------------------
         → (y w : A) → (p : x ≡ y) → (q : z ≡ w) → P y w p q
bin-PM x z P c .x .z refl refl = c
-- we can do this, but that doesn't help much

bin-PM' : ∀ {ℓ ℓ'} {A : Set ℓ} → (x z : A)
          → (P : (y w : A) → x ≡ y → z ≡ w → Set ℓ')
          -----------------------------------------
          → (y w : A) → (p : x ≡ y) → (q : z ≡ w) → P y w p q
bin-PM' {ℓ = ℓ} {A = A} x z P = {!!}
  where
  foo : (y w : A) (q : z ≡ w) → Set ℓ
  foo y = {!!}
