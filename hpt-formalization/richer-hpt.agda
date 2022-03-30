{-# OPTIONS --cubical --rewriting #-}
{-
  Implementation of the patch theory described in
  6. A Patch Theory With Richer Context (Angiuli et al.)


  NOTE: uses Nats in place of Fin, because Fin was really fiddly
-}

module richer-hpt where

open import Agda.Builtin.Cubical.HCompU
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Data.String
  hiding (_<_)
open import Function.Base

open import Cubical.Data.Vec

data History : ℕ → ℕ → Type₀ where
  -- the empty history
  []         : {m : ℕ} → History m m
  -- inserting a line at position
  ADD_AT_::_ : {m n : ℕ} (s : String) (l : ℕ)
              → History m n → History m (suc n)
  -- removing a line
  RM_::_     : {m n : ℕ} (l : ℕ)
              → History m (suc n) → History m n
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
  ADD-RM : {m n : ℕ} (l : ℕ) (s : String) (h : History m (suc n))
           → (ADD s AT l :: RM l :: h) ≡ h

  -- text also mentions:
    -- RM-ADD removing, then adding?
    -- RM-RM removing twice?

data R : Type₀ where
  doc  : {n : ℕ} → History 0 n → R

  addP : {n : ℕ} (s : String) (l : ℕ)
         (h : History 0 n) → doc h ≡ doc (ADD s AT l :: h)
  rmP  : {n : ℕ} (l : ℕ)
         (h : History 0 (suc n)) → doc h ≡ doc (RM l :: h)

  addP-addP-< : {n : ℕ} (l1 l2 : ℕ) (s1 s2 : String)
                (h : History 0 n) → (l1<l2 : l1 < l2)
                → PathP (λ i → doc h ≡ doc ((ADD-ADD-< l1 l2 s1 s2 h l1<l2) i))
                        ((addP s1 l1 h) ∙ (addP s2 l2 (ADD s1 AT l1 :: h)))
                        ((addP s2 (l2 ∸ 1) h) ∙ (addP s1 l1 (ADD s2 AT l2 ∸ 1 :: h)))

  addP-addP-≥ : {n : ℕ} (l1 l2 : ℕ) (s1 s2 : String)
                (h : History 0 n) → (l1≥l2 : l2 ≤ l1)
                → PathP (λ i → doc h ≡ doc (ADD-ADD-≥ l1 l2 s1 s2 h l1≥l2 i))
                        ((addP s1 l1 h) ∙ (addP s2 l2 (ADD s1 AT l1 :: h)))
                        ((addP s2 l2 h) ∙ (addP s1 (l1 + 1) (ADD s2 AT l2 :: h)))


add : {n : ℕ} → (s : String) → ℕ →
      Vec String n → Vec String (suc n)
add {.zero} s zero [] = s ∷ []
add {zero} s (suc _) [] = s ∷ [] -- this is bad and wrong because Fin is annoying
add {.(suc _)} s zero v@(_ ∷ _) = s ∷ v
add {.(suc _)} s (suc l) (x ∷ xs) = x ∷ (add s l xs)

rm : {n : ℕ} → ℕ →
     Vec String (suc n) → Vec String n
rm {n} zero (_ ∷ v) = v
rm {zero} (suc _) _ = [] -- bad and wrong for the same reason
rm {suc n} (suc l) (x ∷ v) = x ∷ (rm l v)

v : Vec String 2
v = "hello" ∷ "world" ∷ []

v' : Vec String 3
v' = add "," 2 v

v'' : Vec String 2
v'' = rm 2 v'


{- 6.2 Interpreter -}

mapSingl : {A B : Type} → (f : A → B) → {M : A} → singl M → singl (f M)
mapSingl f (x , p) = (f x) , (λ i → f (p i))

contrEquiv : {A B : Type} → (A → B) → isContr A → isContr B → A ≃ B
contrEquiv f (aCtr , aContr) contrB = isoToEquiv
  (iso f (λ _ → aCtr) (λ b → isContr→isProp contrB (f aCtr) b) aContr)

singl-biject : {A B : Type} {a : A} {b : B} → (singl a → singl b) → singl a ≃ singl b
singl-biject {a = a} {b = b} f = contrEquiv f (isContrSingl a) (isContrSingl b)

replay : {n : ℕ} → History 0 n → Vec String n
replay [] = []
replay (ADD s AT l :: h) = add s l (replay h)
replay (RM l :: h) = rm l (replay h)
-- aaand annoying cubes
replay (ADD-ADD-< l1 l2 s1 s2 h x i) = {!!}
replay (ADD-ADD-≥ l1 l2 s1 s2 h x i) = {!!}
replay (ADD-RM l s h i) = {!!}

Interpreter : R → Type
Interpreter (doc x) = singl (replay x)
Interpreter (addP s l h i) = ua (singl-biject {a = replay h} (mapSingl (add s l))) i
Interpreter (rmP l h i) = ua (singl-biject {a = replay h} (mapSingl (rm l))) i
Interpreter (addP-addP-< l1 l2 s1 s2 h l1<l2 i i₁) = {!!}
Interpreter (addP-addP-≥ l1 l2 s1 s2 h l1≥l2 i i₁) = {!!}

interp : {n1 n2 : ℕ} {h1 : History 0 n1} {h2 : History 0 n2} →
         doc h1 ≡ doc h2 → Interpreter (doc h1) ≃ Interpreter (doc h2)
interp p = pathToEquiv (cong Interpreter p)

apply : {n1 n2 : ℕ} {h1 : History 0 n1} {h2 : History 0 n2} →
        doc h1 ≡ doc h2 → Interpreter (doc h1) → Interpreter (doc h2)
apply p h = equivFun (interp p) h
