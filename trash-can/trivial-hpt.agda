{-# OPTIONS --cubical --rewriting #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Int

{-# BUILTIN REWRITE _≡_ #-}

module trivial-hpt where

Unit-is-contr : isContr Unit
Unit-is-contr = tt , λ {tt → refl}

data Maybe (A : Type₀) : Type₀ where
  Nothing : Maybe A
  Just    : A → Maybe A

data Simple (A : Type₀) : Type₀ where
  context : Maybe A → Simple A
  sett    : ∀ a → context Nothing ≡ context (Just a)
  -- apply : (f : A → A) → context (Just a) ≡ context (Just (f a))

Simple-is-contr : {A : Type₀} → isContr (Simple A)
Simple-is-contr {A} = context Nothing , contr
  where
  contr : (x : Simple A) → context Nothing ≡ x
  contr (context Nothing) = refl
  contr (context (Just x)) = sett x
  contr (sett a i) = λ j → sett a (i ∧ j)

Simple≃Unit : {A : Type₀} → Simple A ≃ Unit
Simple≃Unit = Contr→Equiv Simple-is-contr Unit-is-contr

ΩSimple : {A : Type₀} → A → Type₀
ΩSimple {A} a = context Nothing ≡ context (Just a)
-- show that this is *also* contractible and hence there is only one path given the endpoints

path-space-contr : {A : Type₀} → (a : A) → isContr (ΩSimple a)
path-space-contr a = isContr→isContrPath Simple-is-contr (context Nothing) (context (Just a))

path-space-prop : {A : Type₀} → (a : A) → isProp (ΩSimple a)
path-space-prop a = isContr→isProp (path-space-contr a)

only-one : {A : Type₀} {a : A} → (p : ΩSimple a) → p ≡ sett a
only-one {a = a} p = path-space-prop a p (sett a)

general-path-space-prop : {A : Type₀} → {x y : Simple A} (p q : x ≡ y) → p ≡ q
general-path-space-prop {x = x} {y = y} p q = is-prop p q
  where
  is-prop : isProp (x ≡ y)
  is-prop = isContr→isProp (isContr→isContrPath Simple-is-contr x y)

Ja-Ja'-is-comp : {A : Type₀} {a a' : A}
                 → (p : context (Just a) ≡ context (Just a'))
                 → p ≡ (sym (sett a) ∙ sett a')
Ja-Ja'-is-comp {a = a} {a' = a'} p = general-path-space-prop p (sym (sett a) ∙ sett a')

-- use this ↑ lemma to construct:
-- might need J or my own lemma(s)

elim-sett : {A : Type₀} →
            (P : (x y : Simple A) (α : x ≡ y) → Type₀)
            (p : (a : A) → P (context Nothing) (context (Just a)) (sett a))
            (id : P (context Nothing) (context Nothing) refl)
            (comp : (a a' : A) → P (context (Just a)) (context (Just a')) (sym (sett a) ∙ sett a'))
            ----------------------------------------------------------------
            → (x' y' : Simple A) (β : x' ≡ y') → P x' y' β
elim-sett P p _ _ (context Nothing) (context (Just x)) q =
  subst (P (context Nothing) (context (Just x))) (sym (only-one q)) (p x)
-- this symmetry should come "for free" somehow
-- might need a sym (like comp)
elim-sett P p _ _ (context (Just x)) (context Nothing) q = {!!}
elim-sett P _ id _ (context Nothing) (context Nothing) q =
  J (P (context Nothing)) id q
elim-sett P p id comp (context (Just x)) (context (Just y)) q =
  subst (P (context (Just x)) (context (Just y))) (sym (Ja-Ja'-is-comp q)) (comp x y) -- q *must* be composition of two sett's
elim-sett P p id f (context x) (sett a i) q = {!!}
elim-sett P p id f (sett a i) (context x) q = {!!}
elim-sett P p id f (sett a i) (sett a₁ i₁) q = {!!}

-- we want elim-sett P p (context Nothing) (context (Just a)) (sett a) ≡ p a
-- (and this should be the case)

Span : {X : Type₀} → X → X → Type₀
Span {X} y y' = Σ[ x ∈ X ] (x ≡ y) × (x ≡ y')

CoSpan : {X : Type₀} → X → X → Type₀
CoSpan {X} y y' = Σ[ z ∈ X ] (y ≡ z) × (y' ≡ z)

Span-Simple : (A : Type₀) → Simple A → Simple A → Type₀
Span-Simple A sa sa' = Span {X = Simple A} sa sa'

CoSpan-Simple : (A : Type₀) → Simple A → Simple A → Type₀
CoSpan-Simple A sa sa' = CoSpan {X = Simple A} sa sa'

-- Span-Simple is uniquely determined by endpoints (but this relies on simple being contractible)
-- luckily repos should probably be contractible (to the empty repo)
span-Unique : {A : Type₀} {sa sa' : Simple A} → Span sa sa' ≃ ((context Nothing ≡ sa) × (context Nothing ≡ sa'))
span-Unique = Σ-contractFst Simple-is-contr

-- how do we know what to do for base≡base in the circle?
-- ΩS¹ ≃ ℤ !
-- p. 25 Concise course in algtop May (classification of covering spaces of groupoids)
-- 1) characterize path space(s) of simple A
-- 1b) use to define elimination for paths
-- profit?
-- Note: Symmetry has a proof of free groups being "correct" which has to do a similar thing

{- new plan:

            CoSpan a a'
          /      |
      f' /       | p
        /        ↓
Span a a' -----> ?
            f
we can lift f to f' iff f*(π(Span a a')) ⊆ p*(π(CoSpan a a'))
which should always be the case because they are both contractible

appropriate ?
  - needs to be contractible (to be covered by CoSpan)
  - enumerates spans somehow
-}

data Base : Type₀ where
  sett-sett : Base
  sett-refl : Base
  refl-sett : Base
  refl-refl : Base

  -- needs to be contractible to be covered by CoSpan
  ss=rr : sett-sett ≡ refl-refl
  sr=rr : sett-refl ≡ refl-refl
  rs=rr : refl-sett ≡ refl-refl

f : {A : Type₀} {sa sa' : Simple A} → Span-Simple A sa sa' → Base
f {sa = context Nothing} {sa' = context Nothing} s = refl-refl
f {sa = context Nothing} {sa' = context (Just x)} s = refl-sett
f {sa = context (Just x)} {sa' = context Nothing} s = sett-refl
f {sa = context (Just _)} {sa' = context (Just _)} s = refl-refl -- merge conflict?
f {sa = sa} {sa' = sa'} s = {!!} -- the cases where endpoints are along setts

p : {A : Type₀} {sa sa' : Simple A} → CoSpan-Simple A sa sa' → Base
p {sa = context Nothing} {sa' = context Nothing} s = refl-refl
p {sa = context Nothing} {sa' = context (Just x)} s = refl-sett
p {sa = context (Just x)} {sa' = context Nothing} s = sett-refl
p {sa = context (Just x)} {sa' = context (Just y)} s = sett-sett
p {sa = sett a i} {sa' = sett a' j} cs = ss=rr (i ∨ j)
p {sa = sett a i} {sa' = context Nothing} cs = {!!}
p {sa = sett a i} {sa' = context (Just x)} cs = {!!}
p {sa = x} {sa' = y} cs = {!!}

{- yet another "plan":
  a span is half a square, what if we just complete it with ∙∙?
-}

merge : {A : Type₀} {a a' : Simple A} → Span-Simple A a a' → CoSpan-Simple A a a'
merge {a = context Nothing} {a' = context Nothing} (context Nothing , p , q) = context Nothing , refl , refl
merge {a = context Nothing} {a' = context (Just x)} (context Nothing , p , q) = context (Just x) , (sym p) ∙' q , refl
merge {a = context (Just x)} {a' = context Nothing} (context Nothing , p , q) = context (Just x) , refl , (sym q) ∙ p
merge {a = context (Just x)} {a' = context (Just y)} (context Nothing , p , q) = context Nothing , (sym p) , (sym q)
merge (context Nothing , p , q) = {!!} , ({!!} , {!!}) -- coherence issues when a,a' = sett _ i
merge (context (Just x) , p , q) = {!!}
merge (sett a i , p , q) = {!!}

test : Span-Simple Int (context Nothing) (context (Just 0))
test = (context Nothing) , (sett 1) ∙ sym (sett 1) , (sett 0)
-- this does not compute to refl when merging...

foo : CoSpan-Simple Int (context Nothing) (context (Just 0))
foo = merge test

t = fst foo
p' = fst (snd foo)
q' = snd (snd foo)
