{-# OPTIONS --cubical --rewriting #-}
{-
  Implementation of the patch theory described in
  6. A Patch Theory With Richer Context (Angiuli et al.)


  NOTE: uses Nats in place of Fin, because Fin was really fiddly
-}

module richer-hpt where

open import Cubical.Core.Everything
  renaming (I to Interval)
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Data.String
  hiding (_<_)
open import Function.Base

data History : ℕ → ℕ → Type₀ where
  -- the empty history
  []         : {m : ℕ} → History m m
  -- inserting a line at position
  ADD_AT_::_ : {m n : ℕ} (s : String) (l : ℕ)
              → History m n → History m (n + 1)
  -- removing a line
  RM_::_     : {m n : ℕ} (l : ℕ)
              → History m (n + 1) → History m n
  -- path constructors enforce patch laws

  -- adding two lines in opposite order
  ADD-ADD-< : {m n : ℕ} (l1 l2 : ℕ) (s1 s2 : String)
              (h : History m n) → l1 < l2
              → (ADD s2 AT l2 :: ADD s1 AT l1 :: h)
              ≡ (ADD s1 AT l1 :: ADD s2 AT (l2 ∸ 1) :: h)

  ADD-ADD-≥ : {m n : ℕ} (l1 l2 : ℕ) (s1 s2 : String)
              (h : History m n) → l2 ≤ l1
              → (ADD s2 AT l2 :: ADD s1 AT l1 :: h)
              ≡ (ADD s1 AT l1 + 1 :: ADD s2 AT l2 :: h)

  -- adding, then removing a line
  ADD-RM : {m n : ℕ} (l : ℕ) (s : String) (h : History m (n + 1))
           → (ADD s AT l :: RM l :: h) ≡ h

  -- text also mentions:
    -- RM-ADD removing, then adding?
    -- RM-RM removing twice?

fibration : {n : ℕ} {h : History 0 n} {s1 s2 : String} {l1 l2 : ℕ}
             → (ADD s2 AT l2 :: ADD s1 AT l1 :: h)
                ≡ (ADD s1 AT l1 :: ADD s2 AT (l2 ∸ 1) :: h)
             → (B : History 0 (n + 1 + 1) → Type₀) → Interval → Type₀
fibration p B = λ i → B (p i)

data R : Type₀ where
  doc  : {n : ℕ} → History 0 n → R

  addP : {n : ℕ} (s : String) (l : ℕ)
         (h : History 0 n) → doc h ≡ doc (ADD s AT l :: h)
  rmP  : {n : ℕ} (l : ℕ)
         (h : History 0 (n + 1)) → doc h ≡ doc (RM l :: h)


  addP-addP-< : {n : ℕ} (l1 l2 : ℕ) (s1 s2 : String)
                (h : History 0 n) → (l1<l2 : l1 < l2)
                → PathP {!!}
                        {!!}
                        {!!}
                -- PathP is heterogenous equality, analogous to PathOver
                -- (I hope)


-- fibers are individual strands!!

