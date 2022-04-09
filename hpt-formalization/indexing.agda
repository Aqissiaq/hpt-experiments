{-# OPTIONS --cubical --rewriting #-}
{-
  Helper functions for finite types used for indexing in richer-hpt
-}

module indexing where

open import Data.Empty
open import Data.Fin
open import Data.Fin.Properties
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality.Core

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE toℕ-inject₁ #-}


-- subtract one and reduce Fin-level
lower-pred : ∀ {n} → Fin (Nat.suc (Nat.suc n)) → Fin (Nat.suc n)
lower-pred {Nat.zero} zero = zero
lower-pred {Nat.zero} (suc i) = pred i
lower-pred {Nat.suc n} zero = zero
lower-pred {Nat.suc n} (suc i) = i

-- lower Fin-level knowing l2 is smaller than an l1 in lower level
lower≤ : ∀ {n} → (l2 : Fin (Nat.suc (Nat.suc n))) → {l1 : Fin (Nat.suc n)}
         → l2 ≤ inject₁ l1 → Fin (Nat.suc n)
lower≤ {Nat.zero} l2 {zero} l1≥l2 = zero
lower≤ {Nat.suc n} zero l1≥l2 = zero
lower≤ {Nat.suc n} l2 {l1} l1≥l2 = lower₁ l2
  (≢-sym (NatP.<⇒≢ (NatP.<-transʳ l1≥l2 (toℕ<n l1))))

-- this has turned out to be unnecessary
-- instead lower₁-irrelevant does the job
toℕ-lower≤ : ∀ {n} → (l2 : Fin (Nat.suc (Nat.suc n))) → {l1 : Fin (Nat.suc n)}
             → (p : l2 ≤ inject₁ l1) → toℕ (lower≤ l2 p) ≡ toℕ l2
toℕ-lower≤ {Nat.zero} zero {zero} p = refl
toℕ-lower≤ {Nat.zero} (suc l2) {zero} p = ⊥-elim (NatP.1+n≢0 (NatP.n≤0⇒n≡0 p))
toℕ-lower≤ {Nat.zero} (suc l2) {suc ()} p
toℕ-lower≤ {Nat.suc n} zero _ = refl
toℕ-lower≤ {Nat.suc n} (suc l2) {suc l1} (Nat.s≤s p) =
  toℕ (lower≤ (suc l2) (Nat.s≤s p))
  ≡⟨ cong toℕ refl ⟩ toℕ (lower₁ (suc l2) ≢-proof)
  ≡⟨ toℕ-lower₁ (suc l2) ≢-proof ⟩ toℕ (suc l2) ∎
  where
  open ≡-Reasoning
  ≢-proof : Nat.suc (Nat.suc n) ≢ Nat.suc (toℕ l2)
  ≢-proof = (≢-sym (NatP.<⇒≢ (NatP.<-transʳ (Nat.s≤s p) (Nat.s≤s (toℕ<n l1)))))
