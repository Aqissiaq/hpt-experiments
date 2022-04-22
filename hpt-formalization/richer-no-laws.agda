{-# OPTIONS --cubical --rewriting #-}
{-
  Implementation of the patch theory described in
  6. A Patch Theory With Richer Context (Angiuli et al.)

-}

module richer-no-laws where

open import indexing
open import vector-implementation

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Data.Fin
open import Data.String
  hiding (_<_)

data History : ℕ → ℕ → Type₀ where
  -- the empty history
  []         : {m : ℕ} → History m m
  -- inserting a line at position
  ADD_AT_::_ : {m n : ℕ} (s : String) (l : Fin (suc n))
              → History m n → History m (suc n)
  -- removing a line
  RM_::_     : {m n : ℕ} (l : Fin (suc n))
              → History m (suc n) → History m n

data R : Type₀ where
  doc  : {n : ℕ} → History 0 n → R

  addP : {n : ℕ} (s : String) (l : Fin (suc n))
         (h : History 0 n) → doc h ≡ doc (ADD s AT l :: h)
  rmP  : {n : ℕ} (l : Fin (suc n))
         (h : History 0 (suc n)) → doc h ≡ doc (RM l :: h)


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

Interpreter InterpreterH : R → Type
Interpreter (doc x) = singl (replay x)
Interpreter (addP s l h i) = ua (singl-biject {a = replay h} (mapSingl (add s l))) i
Interpreter (rmP l h i) = ua (singl-biject {a = replay h} (mapSingl (rm l))) i

InterpreterH (doc x) = singl x
InterpreterH (addP s l h i) = ua (singl-biject {a = h} (mapSingl (λ h → ADD s AT l :: h))) i
InterpreterH (rmP l h i) = ua (singl-biject {a = h} (mapSingl (λ h → RM l :: h))) i

interpH : ∀ {n m}{h : History 0 n}{h' : History 0 m} → doc h ≡ doc h' → singl h → singl h'
interpH p = equivFun (pathToEquiv (cong InterpreterH p))

interp : {n1 n2 : ℕ} {h1 : History 0 n1} {h2 : History 0 n2} →
         doc h1 ≡ doc h2 → Interpreter (doc h1) ≃ Interpreter (doc h2)
interp p = pathToEquiv (cong Interpreter p)

apply : {n1 n2 : ℕ} {h1 : History 0 n1} {h2 : History 0 n2} →
        doc h1 ≡ doc h2 → Interpreter (doc h1) → Interpreter (doc h2)
apply p h = equivFun (interp p) h

-- testing
emptyR : R
emptyR = doc []

patch1 : doc [] ≡ doc (ADD "hello" AT zero :: [])
patch1 = addP "hello" zero []

patch2 : doc (ADD "hello" AT zero :: []) ≡ doc (RM zero :: (ADD "hello" AT zero :: []))
patch2 = rmP zero (ADD "hello" AT zero :: [])

result : Interpreter (doc (ADD "hello" AT zero :: []))
result = apply patch1 ([] , λ _ → [])

result' : Interpreter (doc (RM zero :: (ADD "hello" AT zero :: [])))
result' = apply patch2 (apply patch1 ([] , refl))

result'' : Interpreter (doc (RM zero :: (ADD "hello" AT zero :: [])))
result'' = apply (patch1 ∙ patch2) ([] , refl)

-- as expected
_ : result ≡ ("hello" ∷ [] , refl)
_ = transportRefl ("hello" ∷ [] , refl)

-- correct(?) but not very interesting
_ : result' ≡ (rm zero (fst (apply patch1 ([] , refl)))
              , (λ i → rm zero (snd (apply patch1 ([] , refl)) i)))
_ = transportRefl (rm zero (fst (apply patch1 ([] , refl)))
                  , (λ i → rm zero (snd (apply patch1 ([] , refl)) i)))

-- this does not work, since hcomp does not compute
-- _ : result' ≡ result''
-- _ = {!!}

_+++_ : {n1 n2 n3 : ℕ} → History n1 n2 → History n2 n3 → History n1 n3
h1 +++ [] = h1
h1 +++ (ADD s AT l :: h2) = ADD s AT l :: (h1 +++ h2)
h1 +++ (RM l :: h2) = RM l :: (h1 +++ h2)

+++-left-id : ∀ {n m} → (h : History n m) → ([] +++ h) ≡ h
+++-left-id [] = refl
+++-left-id (ADD s AT l :: h) = cong (ADD s AT l ::_) (+++-left-id h)
+++-left-id (RM l :: h) = cong (RM l ::_) (+++-left-id h)

+++-assoc : ∀ {n m k l}
            → (h1 : History n m)
            → (h2 : History m k)
            → (h3 : History k l)
            → (h1 +++ h2) +++ h3 ≡ (h1 +++ (h2 +++ h3))
+++-assoc h1 h2 [] = refl
+++-assoc h1 h2 (ADD s AT l :: h3) = cong (ADD s AT l ::_) (+++-assoc h1 h2 h3)
+++-assoc h1 h2 (RM l :: h3) = cong (RM l ::_) (+++-assoc h1 h2 h3)

Extension : {n m : ℕ} → History 0 n → History 0 m → Type
Extension {n} {m} h1 h2 = Σ[ h3 ∈ History n m ] (h1 +++ h3) ≡ h2

reflExt : ∀ {n} {h : History 0 n} → Extension h h
reflExt = [] , refl

-- there has got to be a canonical (pretty) solution for this
fromSingl : {A : Type}{a : A} → singl a → A
fromSingl (a , _) = a

interpH-lemma : ∀ {n m}{h : History 0 n}{h' : History 0 m}
                → (p : doc h ≡ doc h')
                → h' ≡ fromSingl (interpH p (h , refl))
interpH-lemma {h = h} p = let (_ , proof) = interpH p (h , refl) in proof

module merging {
  mergeH : {n m : ℕ} →
           (h1 : History 0 n) (h2 : History 0 m) →
           Σ[ n' ∈ ℕ ] (Σ[ h' ∈ History 0 n' ] (Extension h1 h' × Extension h2 h'))
  } where

  toPath : {n : ℕ} (h : History 0 n) → doc [] ≡ doc h
  toPath [] = refl
  toPath (ADD s AT l :: h) = (toPath h) ∙ addP s l h
  toPath (RM l :: h) = (toPath h) ∙ rmP l h

  extToPath : {n m : ℕ} {h : History 0 n} {h' : History 0 m} →
              Extension h h' → doc h ≡ doc h'
  extToPath {h = h} {h' = h'} _ = sym (toPath h) ∙ toPath h'

  merge : {n1 n2 : ℕ}{h1 : History 0 n1}{h2 : History 0 n2}
        → (doc [] ≡ doc h1) → (doc [] ≡ doc h2)
        → Σ[ n' ∈ ℕ ] (Σ[ h' ∈ History 0 n' ] (doc h1 ≡ doc h') × (doc h2 ≡ doc h'))
  merge {n1} {n2} {h1} {h2} p1 p2 = let (n' , (h' , (e1 , e2))) = mergeH (fromSingl (interpH p1 ([] , refl))) (fromSingl (interpH p2 ([] , refl)))
                                        e1' = fst e1 , cong (_+++ (fst e1)) (interpH-lemma p1) ∙ snd e1
                                        e2' = fst e2 , cong (_+++ (fst e2)) (interpH-lemma p2) ∙ snd e2
    in (n' , (h' , extToPath e1' , extToPath e2'))

postulate
  undo : ∀ {n m} → History n m → History m n
  undo-inverse : ∀ {n m } → (h : History n m)
                → h +++ undo h ≡ []

mergeH : {n m : ℕ} →
         (h1 : History 0 n) (h2 : History 0 m) →
         Σ[ n' ∈ ℕ ] (Σ[ h' ∈ History 0 n' ] (Extension h1 h' × Extension h2 h'))
mergeH [] h2 = _ , h2 , (h2 , +++-left-id h2) , reflExt
mergeH h1 [] = _ , (h1 , reflExt , h1 , +++-left-id h1)
mergeH h1 h2 = _ , h1 , reflExt , (undo h2 +++ h1) ,
  sym (+++-assoc h2 (undo h2) h1) ∙ cong (_+++ h1) (undo-inverse h2) ∙ +++-left-id h1

-- testing
p1 : doc [] ≡ doc (ADD "hello" AT zero :: [])
p1 = addP "hello" (zero) []

p0 : doc [] ≡ doc []
p0 = refl

open merging {mergeH}
-- none of these compute with transportRefl, I suspect because they depend on a number which does not compute
_ : merge p0 p1 ≡ (_ , ADD "hello" AT zero :: [] , p1 , refl)
_ = ΣPathP ({!!} , ΣPathP ({!!} , ΣPathP ({!!} , {!!})))
