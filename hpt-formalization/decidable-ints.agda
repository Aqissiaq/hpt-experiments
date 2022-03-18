{-# OPTIONS --cubical --rewriting #-}

module decidable-ints where

open import Cubical.Foundations.Everything

open import Cubical.Data.Int
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary


injSuc' : (n m : ℕ) → ¬ (n ≡ m) → ¬ (suc n ≡ suc m)
injSuc' n m n≠m sn=sm = n≠m (injSuc sn=sm)

_ℕ=?_ : (n m : ℕ) → Dec (n ≡ m)
zero ℕ=? zero = yes refl
zero ℕ=? suc m = no znots
suc n ℕ=? zero = no snotz
suc n ℕ=? suc m = mapDec (cong suc) (injSuc' n m) (n ℕ=? m)

injPos' : (n m : ℕ) →  ¬ (n ≡ m) → ¬ (pos n ≡ pos m)
injPos' n m n≠m pn=pm = n≠m (injPos pn=pm)

injNegsuc' : (n m : ℕ) →  ¬ (n ≡ m) → ¬ (negsuc n ≡ negsuc m)
injNegsuc' n m n≠m nn=nm = n≠m (injNegsuc nn=nm)

_ℤ=?_ : (n m : ℤ) → Dec (n ≡ m)
pos n ℤ=? pos m = mapDec (cong pos) (injPos' n m) (n ℕ=? m)
pos n ℤ=? negsuc m = no (posNotnegsuc n m)
negsuc n ℤ=? pos m = no (negsucNotpos n m)
negsuc n ℤ=? negsuc m = mapDec (cong negsuc) (injNegsuc' n m) (n ℕ=? m)
