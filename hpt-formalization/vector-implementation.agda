{-# OPTIONS --cubical --rewriting #-}
{-
  The actual implementation on vectors of strings
  for use with richer-hpt
-}

module vector-implementation where

open import indexing

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Equality
  using (reflp ; _≡p_ ; ptoc)

open import Relation.Binary.PropositionalEquality.Core
  using(_≢_ ; ≢-sym)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Data.Empty
open import Data.Fin
open import Data.Fin.Properties
open import Data.String
  hiding (_<_)

-- Vector operations
add : {n : ℕ} → (s : String) → Fin (suc n) →
      Vec String n → Vec String (suc n)
add s zero v = s ∷ v
add s (suc i) (x ∷ v) = x ∷ add s i v

rm : {n : ℕ} → Fin (suc n) →
     Vec String (suc n) → Vec String n
rm zero (x ∷ v) = v
rm (suc i) (x ∷ y ∷ v) = x ∷ (rm i (y ∷ v))

-- Properties
add-add-< : {n : ℕ} (l1 : Fin (suc n)) (l2 : Fin (suc (suc n)))
            (s1 s2 : String) → (v : Vec String n) → (inject₁ l1) < l2 →
            (add s2 l2 (add s1 l1 v))
            ≡ (add s1 (inject₁ l1) (add s2 (lower-pred l2) v))
add-add-< {zero} zero (suc zero) _ _ [] _ = refl
add-add-< {suc .zero} zero (suc zero) _ _ (_ ∷ []) _ = refl
add-add-< {suc .zero} zero (suc (suc zero)) _ _ (_ ∷ []) _ = refl
add-add-< {suc .(suc _)} zero (suc _) _ _ (_ ∷ _ ∷ _) _ = refl
add-add-< n@{suc .zero} (suc zero) (suc zero) _ _ (_ ∷ []) l1<l2 =
  ⊥-elim (<-irrefl (reflp {x = suc (zero {n = n})}) l1<l2)
add-add-< {suc .zero} (suc zero) (suc (suc zero)) _ _ (_ ∷ []) _ = refl
add-add-< n@{suc .(suc _)} (suc zero) (suc zero) _ _ (_ ∷ _ ∷ _) l1<l2 =
  ⊥-elim (<-irrefl (reflp {x = suc (zero {n = n})}) l1<l2)
add-add-< {suc .(suc _)} (suc zero) (suc (suc _)) _ _ (_ ∷ _ ∷ _) _ = refl
add-add-< {suc .(suc _)} (suc (suc l1)) (suc zero) s1 s2 (x ∷ y ∷ xs) l1<l2 =
  ⊥-elim (<-asym (Nat.s≤s NatP.0<1+n) l1<l2)
add-add-< {suc .(suc _)} (suc (suc l1)) (suc (suc l2)) s1 s2 (x ∷ y ∷ xs) l1<l2 =
  cong (x ∷_) (add-add-< (suc l1) (suc l2) s1 s2 (y ∷ xs) (NatP.+-cancelˡ-< 1 l1<l2))


add-add-≥ : {n : ℕ} (l1 : Fin (suc n)) (l2 : Fin (suc (suc n)))
            (s1 s2 : String) → (v : Vec String n) → (l1≥l2 : l2 ≤ (inject₁ l1)) →
            (add s2 l2 (add s1 l1 v))
            ≡ (add s1 (suc l1) (add s2 (lower≤ l2 l1≥l2) v))
add-add-≥ {zero} zero zero _ _ _ _ = refl
add-add-≥ {suc .zero} zero zero _ _ (_ ∷ []) _ = refl
add-add-≥ {suc .(suc _)} zero zero _ _ (_ ∷ _ ∷ _) _ = refl
add-add-≥ {suc _} (suc zero) zero _ _ _ _ = refl
add-add-≥ {suc .1} (suc (suc _)) zero _ _ (_ ∷ _ ∷ []) _ = refl
add-add-≥ {suc .(suc (suc _))} (suc (suc _)) zero _ _ (_ ∷ _ ∷ _ ∷ _) _ = refl
add-add-≥ {suc .zero} (suc zero) (suc zero) _ _ (_ ∷ []) _ = refl
add-add-≥ {suc .zero} (suc zero) (suc (suc zero)) s1 s2 (x ∷ []) (l1≥l2) =
  ⊥-elim (<⇒≢ {n = 3} (≤̄⇒inject₁< {n = 3} l1≥l2) reflp)
add-add-≥ {suc .(suc _)} (suc _) (suc zero) _ _ (_ ∷ _ ∷ _) _ = refl
add-add-≥ {suc .(suc _)} (suc zero) (suc (suc _)) _ _ (_ ∷ _ ∷ _) (Nat.s≤s p) =
  ⊥-elim (NatP.1+n≢0 (NatP.n≤0⇒n≡0 p))
add-add-≥ {suc .(suc _)} (suc (suc _)) (suc (suc zero)) _ _ (_ ∷ _ ∷ _) _ = refl
add-add-≥ {suc .(suc _)} (suc (suc l1)) (suc (suc (suc l2))) s1 s2 (x ∷ y ∷ xs) l1≥l2 =
  x ∷ y ∷ add s2 (suc l2) (add s1 l1 xs)
    ≡⟨ cong (λ v → x ∷ v)
            (add-add-≥ (suc l1) (suc (suc l2)) s1 s2 (y ∷ xs) (NatP.+-cancelˡ-≤ 1 l1≥l2)) ⟩
  x ∷ y ∷ add s1 (suc l1) (add s2 (suc (lower₁ l2 _)) xs)
    ≡⟨ cong (λ l → x ∷ y ∷ add s1 (suc l1) (add s2 (suc l) xs))
            (ptoc (lower₁-irrelevant l2 _ _)) ⟩
  x ∷ y ∷ add s1 (suc l1) (add s2 (suc (lower₁ l2 _)) xs) ∎

rm-add : {n : ℕ} (l : Fin (suc n)) (s : String) (v : Vec String n) →
         rm l (add s l v) ≡ v
rm-add zero _ _ = refl
rm-add (suc zero) s (x ∷ []) = refl
rm-add (suc zero) s (x ∷ y ∷ xs) = refl
rm-add (suc (suc zero)) s (x ∷ y ∷ []) = refl
rm-add (suc (suc l)) s (x ∷ y ∷ z ∷ xs) = cong (x ∷_) (rm-add (suc l) s (y ∷ z ∷ xs))

module tests where
  n : ℕ
  n = 2

  v : Vec String n
  v = "hello" ∷ "world" ∷ []

  l1 : Fin (suc n)
  l1 = (suc zero)

  l2 : Fin (suc (suc n))
  l2 = zero

  l1≥l2 : l2 ≤ (inject₁ l1)
  l1≥l2 = Nat.z≤n
  -- ≤-reflexive {n = suc (suc n)} reflp
  --   where open import Data.Fin.Properties

  s1 s2 : String
  s1 = "s1"
  s2 = "s2"

  foo bar : Vec String 4
  foo = add s2 l2 (add s1 l1 v)
  bar = add s1 (suc l1) (add s2 (lower≤ l2 l1≥l2) v)
