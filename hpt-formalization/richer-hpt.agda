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
  hiding(_+_)
open import Cubical.Data.Vec
open import Cubical.Data.Equality
  using (reflp ; _≡p_)

open import Relation.Nullary
  using(¬_)
open import Relation.Binary.PropositionalEquality.Core
  using(_≢_ ; ≢-sym)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Data.Empty
open import Data.Fin
open import Data.Fin.Properties
open import Data.String
  hiding (_<_)
open import Function.Base

-- it's weird that it's not in Fin
lower-pred : ∀ {n} → Fin (suc (suc n)) → Fin (suc n)
lower-pred {zero} zero = zero
lower-pred {zero} (suc i) = pred i
lower-pred {suc n} zero = zero
lower-pred {suc n} (suc i) = i

lower≤ : ∀ {n} → (l2 : Fin (suc (suc n))) → {l1 : Fin (suc n)} → l2 ≤ inject₁ l1 → Fin (suc n)
lower≤ {zero} l2 {zero} l1≥l2 = zero
lower≤ {suc n} zero l1≥l2 = zero
lower≤ {suc n} l2 {l1} l1≥l2 = lower₁ l2 (≢-sym ssn≠l2)
  where
  -- there's gotta be a better way here
  cmon : toℕ (inject₁ l1) ≡p toℕ l1
  cmon = toℕ-inject₁ l1
  {-# BUILTIN REWRITE _≡p_ #-}
  {-# REWRITE cmon #-}
  l2<ssn : toℕ l2 Nat.< suc (suc n)
  l2<ssn = NatP.<-transʳ l1≥l2 (toℕ<n l1)

  ssn≠l2 : toℕ l2 ≢ suc (suc n)
  ssn≠l2 = NatP.<⇒≢ l2<ssn

data History : ℕ → ℕ → Type₀ where
  -- the empty history
  []         : {m : ℕ} → History m m
  -- inserting a line at position
  ADD_AT_::_ : {m n : ℕ} (s : String) (l : Fin (suc n))
              → History m n → History m (suc n)
  -- removing a line
  RM_::_     : {m n : ℕ} (l : Fin (suc n))
              → History m (suc n) → History m n
  -- path constructors enforce patch laws

  -- adding two lines in opposite order
  ADD-ADD-< : {m n : ℕ} (l1 : Fin (suc n)) (l2 : Fin (suc (suc n)))
              (s1 s2 : String) (h : History m n) → (inject₁ l1) < l2
              → (ADD s2 AT l2 :: ADD s1 AT l1 :: h)
              ≡ (ADD s1 AT (inject₁ l1) :: ADD s2 AT (lower-pred l2) :: h)

  ADD-ADD-≥ : {m n : ℕ} (l1 : Fin (suc n)) (l2 : Fin (suc (suc n)))
              (s1 s2 : String) (h : History m n) → (l1≥l2 : l2 ≤ (inject₁ l1))
              → (ADD s2 AT l2 :: ADD s1 AT l1 :: h)
              ≡ (ADD s1 AT (suc l1) :: ADD s2 AT (lower≤ l2 l1≥l2) :: h)

  RM-ADD : {m n : ℕ} (l : Fin (suc n)) (s : String) (h : History m n)
           → (RM l :: (ADD s AT l :: h)) ≡ h
  -- text also mentions:
  -- ADD-RM : {m n : ℕ} (l : Fin (suc n)) (s : String) (h : History m (suc n))
  --          → (ADD s AT l :: RM l :: h) ≡ h
  -- RM-RM removing twice?

data R : Type₀ where
  doc  : {n : ℕ} → History 0 n → R

  addP : {n : ℕ} (s : String) (l : Fin (suc n))
         (h : History 0 n) → doc h ≡ doc (ADD s AT l :: h)
  rmP  : {n : ℕ} (l : Fin (suc n))
         (h : History 0 (suc n)) → doc h ≡ doc (RM l :: h)

  addP-addP-< : {n : ℕ} (l1 : Fin (suc n)) (l2 : Fin (suc (suc n)))
                (s1 s2 : String) (h : History 0 n) → (l1<l2 : (inject₁ l1) < l2)
                -- this gets pretty ugly, but it's just Pathover ADD-ADD-<
                → PathP (λ i → doc h ≡ doc ((ADD-ADD-< l1 l2 s1 s2 h l1<l2) i))
                        ((addP s1 l1 h) ∙ (addP s2 l2 (ADD s1 AT l1 :: h)))
                        ((addP s2 (lower-pred l2) h)
                          ∙ (addP s1 (inject₁ l1) (ADD s2 AT lower-pred l2 :: h)))

  addP-addP-≥ : {n : ℕ} (l1 : Fin (suc n)) (l2 : Fin (suc (suc n)))
                (s1 s2 : String) (h : History 0 n) → (l1≥l2 : l2 ≤ (inject₁ l1))
                → PathP (λ i → doc h ≡ doc (ADD-ADD-≥ l1 l2 s1 s2 h l1≥l2 i))
                        ((addP s1 l1 h) ∙ (addP s2 l2 (ADD s1 AT l1 :: h)))
                        (addP s2 (lower≤ l2 l1≥l2) h
                          ∙ addP s1 (suc l1) (ADD s2 AT lower≤ l2 l1≥l2 :: h))
  rmP-addP : {n : ℕ} (l : Fin (suc n)) (s : String) (h : History 0 n)
           → PathP (λ i → doc h ≡ doc (RM-ADD l s h i))
                   ((addP s l h) ∙ (rmP l (ADD s AT l :: h)))
                   refl

  -- addP-rmP : {n : ℕ} (l : Fin (suc n)) (s : String) (h : History 0 (suc n))
  --          → PathP (λ i → doc h ≡ doc (ADD-RM l s h i))
  --                  (rmP l h ∙ addP s l (RM l :: h))
  --                  refl


add : {n : ℕ} → (s : String) → Fin (suc n) →
      Vec String n → Vec String (suc n)
add s zero v = s ∷ v
add s (suc i) (x ∷ v) = x ∷ add s i v

rm : {n : ℕ} → Fin (suc n) →
     Vec String (suc n) → Vec String n
rm zero (x ∷ v) = v
rm (suc i) (x ∷ y ∷ v) = x ∷ (rm i (y ∷ v))

{- 6.2 Interpreter -}

mapSingl : {A B : Type} → (f : A → B) → {M : A} → singl M → singl (f M)
mapSingl f (x , p) = (f x) , (λ i → f (p i))

contrEquiv : {A B : Type} → (A → B) → isContr A → isContr B → A ≃ B
contrEquiv f (aCtr , aContr) contrB = isoToEquiv
  (iso f (λ _ → aCtr) (λ b → isContr→isProp contrB (f aCtr) b) aContr)

-- some results about < that I rely on
cong-<-suc : ∀ {s} {n m : Fin (suc s)} → n < m → suc n < suc m
cong-<-suc n<m = {!!}

suc-<-cong : ∀ {s} {n m : Fin (suc s)} → suc n < suc m → n < m
suc-<-cong {s} {n} {m} sn<sm = {!!}

0<sn : ∀ {s} {n : Fin s} → zero < suc n
0<sn = {!!}

singl-biject : {A B : Type} {a : A} {b : B} → (singl a → singl b) → singl a ≃ singl b
singl-biject {a = a} {b = b} f = contrEquiv f (isContrSingl a) (isContrSingl b)

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
  ⊥-elim (<-asym (cong-<-suc 0<sn) l1<l2)
add-add-< {suc .(suc _)} (suc (suc l1)) (suc (suc l2)) s1 s2 (x ∷ y ∷ xs) l1<l2 =
  cong (x ∷_) (add-add-< (suc l1) (suc l2) s1 s2 (y ∷ xs) (suc-<-cong l1<l2))

-- and similar results about ≤
cong-≤-suc : ∀ {s} {n m : Fin (suc s)} → n ≤ m → suc n ≤ suc m
cong-≤-suc n≤m = {!!}

suc-≤-cong : ∀ {s} {n m : Fin (suc s)} → suc n ≤ suc m → n ≤ m
suc-≤-cong {s} {n} {m} sn≤sm = {!!}

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
add-add-≥ {suc .zero} (suc zero) (suc zero) s1 s2 (x ∷ []) l1≥l2 = refl
add-add-≥ {suc .zero} (suc zero) (suc (suc zero)) s1 s2 (x ∷ []) l1≥l2 =
  x ∷ add s2 ((suc zero)) (add s1 (zero) ([]))
  ≡⟨ {!!} ⟩
  add s1 (suc (suc zero)) (add s2 (lower≤ (suc (suc zero)) l1≥l2) (x ∷ [])) ∎
add-add-≥ {suc .(suc _)} (suc l1) (suc zero) s1 s2 (x ∷ x₁ ∷ xs) l1≥l2 = refl
add-add-≥ {suc .(suc _)} (suc l1) (suc (suc l2)) s1 s2 (x ∷ y ∷ xs) l1≥l2 = {!!}

rm-add : {n : ℕ} (l : Fin (suc n)) (s : String) (v : Vec String n) →
         rm l (add s l v) ≡ v
rm-add zero _ _ = refl
rm-add (suc zero) s (x ∷ []) = refl
rm-add (suc zero) s (x ∷ y ∷ xs) = refl
rm-add (suc (suc zero)) s (x ∷ y ∷ []) = refl
rm-add (suc (suc l)) s (x ∷ y ∷ z ∷ xs) = x ∷ rm (suc l) (add s (suc l) (y ∷ z ∷ xs))
  ≡⟨ cong (x ∷_) (rm-add (suc l) s (y ∷ z ∷ xs)) ⟩ x ∷ y ∷ z ∷ xs ∎
{-

replay : {n : ℕ} → History 0 n → Vec String n
replay [] = []
replay (ADD s AT l :: h) = add s l (replay h)
replay (RM l :: h) = rm l (replay h)
-- aaand annoying cubes
replay (ADD-ADD-< l1 l2 s1 s2 h l1<l2 i) = add-add-< l1 l2 s1 s2 (replay h) l1<l2 i
replay (ADD-ADD-≥ l1 l2 s1 s2 h l1≥l2 i) = add-add-≥ l1 l2 s1 s2 (replay h) l1≥l2 i
replay (RM-ADD l s h i) = rm-add l s (replay h) i

Interpreter : R → Type
Interpreter (doc x) = singl (replay x)
Interpreter (addP s l h i) = ua (singl-biject {a = replay h} (mapSingl (add s l))) i
Interpreter (rmP l h i) = ua (singl-biject {a = replay h} (mapSingl (rm l))) i
Interpreter (addP-addP-< l1 l2 s1 s2 h l1<l2 i i₁) = {!!}
Interpreter (addP-addP-≥ l1 l2 s1 s2 h l1≥l2 i i₁) = {!!}
Interpreter (rmP-addP l s h i i₁) = {!!}

interp : {n1 n2 : ℕ} {h1 : History 0 n1} {h2 : History 0 n2} →
         doc h1 ≡ doc h2 → Interpreter (doc h1) ≃ Interpreter (doc h2)
interp p = pathToEquiv (cong Interpreter p)

apply : {n1 n2 : ℕ} {h1 : History 0 n1} {h2 : History 0 n2} →
        doc h1 ≡ doc h2 → Interpreter (doc h1) → Interpreter (doc h2)
apply p h = equivFun (interp p) h
-}
