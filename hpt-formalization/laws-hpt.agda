{-# OPTIONS --cubical --rewriting #-}
{-
Implementation of the patch theory described in
5. A Patch Theory With laws (Angiuli et al.)

NOTE: compEquiv with swapat is giving some issues after updating to cubical-0.3
      not fixing right now

-}

module laws-hpt where

open import Data.Product
  hiding(Σ-syntax)
open import Data.Product.Properties
open import Data.Fin
  hiding(_≟_)
open import Data.String
  hiding (_<_)
open import Data.Vec
  hiding(map)
open import Data.Vec.Properties
open import Data.Empty
open import Data.Bool
  using(if_then_else_)

open import Cubical.Core.Everything
  hiding (I)
open import Cubical.Foundations.Prelude
  hiding (I)
open import Cubical.Data.Equality
  hiding (I)
open import Cubical.Data.Nat
open import Cubical.Data.Bool
  hiding(_≟_)
open import Cubical.Data.Nat.Order
  hiding(_≟_)
open import Function.Base
open import Relation.Nullary
open import Relation.Binary

open import Cubical.Foundations.Everything
  hiding(_∘_ ; I ; id)
open import Cubical.Foundations.Id
  using(∥_∥)

size : ℕ
size = 8

repoType : Type₀
repoType = Vec String size

_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≢_ x y = x ≡ y → ⊥

sym≢ : ∀ {ℓ} {A : Set ℓ} → {x y : A}
       → x ≢ y → y ≢ x
sym≢ x≢y x≡y = ⊥-elim (x≢y (sym x≡y))

apd : {A : Type₀} {B : A → Type₀} → (f : (a : A) → B a) →
      ∀ {x y : A} → (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
apd f p i = cong f p i


data R : Type₀ where
  -- context (point)
  doc : R
  -- patch (line)
  _↔_AT_ : (s1 s2 : String) (i : Fin size) → (doc ≡ doc)

  --patch laws (squares)
  noop : (s : String) (i : Fin size) → s ↔ s AT i ≡ refl

  indep : (s t u v : String) (i j : Fin size) → (i ≢ j)
          → (s ↔ t AT i) ∙ (u ↔ v AT j) ≡ (u ↔ v AT j) ∙ (s ↔ t AT i)

  -- all proofs of patch laws are equal. This is reuquired for the first attempt at optimization
  trunc : {x y : R} {p q : x ≡ y} {f1 f2 : p ≡ q} → f1 ≡ f2

noop-helper : {s1 s2 : String} {j : Fin size} → s1 ≡ s2
              → (s1 ↔ s2 AT j) ≡ refl
noop-helper {s1} {s2} {j} s1=s2 =
  s1 ↔ s2 AT j ≡⟨ cong (λ s → s1 ↔ s AT j) (sym s1=s2) ⟩ (s1 ↔ s1 AT j) ≡⟨ noop s1 j ⟩ refl ∎

_=?_ : Decidable _≡p_
_=?_ = _≟_

permute : (String × String) → String → String
permute (s1 , s2) s with s =? s1 | s =? s2
...                    | yes _  | _     = s2
...                    | no _   | yes _ = s1
...                    | no _   | no _  = s

permuteId : {s : String} → (t : String) → permute (s , s) t ≡ id t
permuteId {s} t with t =? s | t =? s
...               | yes t=s | yes _   = sym (ptoc t=s)
...               | yes _   | no _    = refl
...               | no t≠s  | yes t=s = ⊥-elim (t≠s t=s)
...               | no _    | no _  = refl

permuteTwice' : {s1 s2 : String} → (s : String)
                → permute (s1 , s2) (permute (s1 , s2) s) ≡ id s
permuteTwice' {s1} {s2} s with s =? s1 | s =? s2
...                       | yes s=s1 | _
                            with s2 =? s1 | s2 =? s2
...                         | yes s2=s1   | _        = ptoc s2=s1 ∙ sym (ptoc s=s1)
...                         | no _        | yes _    = sym (ptoc s=s1)
...                         | no _        | no s2≠s2 = ⊥-elim (s2≠s2 reflp)
permuteTwice' {s1} {s2} s | no _ | yes s=s2
                            with s1 =? s1 | s1 =? s2
...                         | yes _       | _        = sym (ptoc s=s2)
...                         | no s1≠s1    | _        = ⊥-elim (s1≠s1 reflp)
permuteTwice' {s1} {s2} s | no s≠s1 | no s≠s2
                            with s =? s1  | s =? s2
...                         | yes s=s1    | _        =  ⊥-elim (s≠s1 s=s1)
...                         | no _        | yes s=s2 =  ⊥-elim (s≠s2 s=s2)
...                         | no _        | no _     = refl


{-lots of ugly ptocs (ah yes, definitely just the ptocs) here
  ideal solution: an ≟ that returns cubical identity
  → problem for future me
-}

permuteTwice : {s t : String} → (permute (s , t) ∘ permute (s , t)) ≡ id
permuteTwice {s} {t} = funExt permuteTwice'

[]%=id : ∀ {n} {v : Vec String n} {j : Fin n} → v [ j ]%= id ≡ v
[]%=id {n} {x ∷ xs} {zero}  = refl
[]%=id {n} {x ∷ xs} {suc j} = (x ∷ xs) [ suc j ]%= id
                         ≡⟨ refl ⟩ x ∷ updateAt j id xs
                         ≡⟨ cong (λ tail → x ∷ tail) []%=id ⟩ x ∷ xs ∎

[]%=twice : ∀ {n} {A : Type₀} (f : A → A) (v : Vec A n) (i : Fin n)
            → v [ i ]%= f [ i ]%= f ≡ v [ i ]%= f ∘ f
[]%=twice f (x ∷ xs) zero = refl
[]%=twice f (x ∷ xs) (suc i) = cong (λ v → x ∷ v) ([]%=twice f xs i) -- by induction on v → x ∷ v
-- updateAt-compose in Data.Vec.Properties proves the same

swapat : (String × String) → Fin size → repoType ≃ repoType
swapat (s , t) j = permuteAt , permuteAt-is-equiv
  where
  permuteAt : repoType → repoType
  permuteAt v = v [ j ]%= (permute (s , t))

  permuteAtTwice : ∀ v → permuteAt (permuteAt v) ≡ v
  permuteAtTwice v = permuteAt (permuteAt v)
        ≡⟨ []%=twice (permute (s , t)) v j ⟩ v [ j ]%= permute (s , t) ∘ permute (s , t)
        ≡⟨ cong (_[_]%=_ v j) permuteTwice ⟩ v [ j ]%= id
        ≡⟨ []%=id ⟩ v ∎

  permuteAt-is-equiv : isEquiv permuteAt
  permuteAt-is-equiv = isoToIsEquiv (iso permuteAt permuteAt permuteAtTwice permuteAtTwice)

swapatFun : (String × String) → Fin size → repoType → repoType
swapatFun pair j = equivFun (swapat pair j)

swapatPath : (String × String) → Fin size → repoType ≡ repoType
swapatPath pair j = ua (swapat pair j)

{-
This is a direct copy of the proof in Data.Vec.Properties, except with ≡ instead of ≗,
and an explicit vector
-}
updateAt-commutes' : ∀ {n} {A : Type₀} (i j : Fin n) {f g : A → A} → i ≢ j → (v : Vec A n) →
                  (updateAt i f ∘ updateAt j g) v ≡ (updateAt j g ∘ updateAt i f) v
updateAt-commutes' zero    zero    0≠0 (x ∷ xs) = ⊥-elim (0≠0 refl)
updateAt-commutes' zero    (suc j) _   (x ∷ xs) = refl
updateAt-commutes' (suc i) zero    _   (x ∷ xs) = refl
updateAt-commutes' (suc i) (suc j) i≠j (x ∷ xs) =
  cong (x ∷_ ) (updateAt-commutes' i j (i≠j ∘ cong suc) xs)

swapatFun-independent : {s t u v : String} → (i j : Fin size) →
                        i ≢ j → (swapatFun (s , t) i) ∘ (swapatFun (u , v) j)
                              ≡ (swapatFun (u , v) j) ∘ (swapatFun (s , t) i)
swapatFun-independent i j i≠j = funExt (updateAt-commutes' i j i≠j)

swapat-independent : {s t u v : String} → {i j : Fin size} →
                     i ≢ j → compEquiv (swapat (u , v) j) (swapat (s , t) i)
                           ≡ compEquiv (swapat (s , t) i) (swapat (u , v) j)
swapat-independent {s} {t} {u} {v} {i} {j} i≠j = equivEq (swapatFun-independent i j i≠j)

GOAL0 : (s t u v : String) → (i j : Fin size) → (i ≢ j)
        → swapatPath (s , t) i ∙ swapatPath (u , v) j
        ≡ swapatPath (u , v) j ∙ swapatPath (s , t) i
GOAL0 s t u v i j i≠j = swapatPath (s , t) i ∙ swapatPath (u , v) j
                        ≡⟨ refl ⟩ ua p1 ∙ ua p2
                        ≡⟨ sym (uaCompEquiv p1 p2) ⟩ ua (compEquiv p1 p2)
                        ≡⟨ cong ua (swapat-independent (sym≢ i≠j)) ⟩ ua (compEquiv p2 p1)
                        ≡⟨ uaCompEquiv p2 p1 ⟩ ua p2 ∙ ua p1
                        ≡⟨ refl ⟩ swapatPath (u , v) j ∙ swapatPath (s , t) i ∎
      where
        p1 = swapat (s , t) i
        p2 = swapat (u , v) j

swapssId : {s : String} {j : Fin size} → equivFun (swapat (s , s) j) ≡ idfun (repoType)
swapssId {s} {j} = funExt pointwise
  where
    pointwise : (r : repoType) → equivFun (swapat (s , s) j) r ≡ idfun repoType r
    pointwise r = equivFun (swapat (s , s) j) r
                ≡⟨ cong (λ x → r [ j ]%= id x) (funExt permuteId) ⟩ r [ j ]%= id
                ≡⟨ []%=id ⟩ id r ∎

swapatIsId : {s : String} {j : Fin size} → swapat (s , s) j ≡ idEquiv repoType
swapatIsId {s} {j} = equivEq swapssId

GOAL1 : (s : String) → (j : Fin size)
        → swapatPath (s , s) j ≡ refl
GOAL1 s j = cong ua swapatIsId ∙ uaIdEquiv
-- swapat (s , s) j is idEquiv ∙ idEquiv is refl

I : R → Type₀
I doc = repoType
I ((s1 ↔ s2 AT j) i) = swapatPath (s1 , s2) j i
I (noop s j i₁ i₂) = GOAL1 s j i₁ i₂
I (indep s t u v i j i≢j i₁ i₂) = GOAL0 s t u v i j i≢j i₁ i₂
I (trunc i i₁ i₂) = {!!}


{-5.3 a simple optimizer to illustrate the use of patch laws-}

-- Program then prove
-- we write an optimiser that removes noops, then prove it correct separately

opt0 : String → String → Fin size → doc ≡ doc
opt0 s1 s2 i with s1 == s2
...             | true  = refl
...             | false = s1 ↔ s2 AT i

OPTGOAL0 : (s : String) → (j : Fin size) → opt0 s s j ≡ refl
OPTGOAL0 s j with s =? s
...             | yes _  = refl
...             | no s≠s = ⊥-elim (s≠s reflp)

OPTGOAL1 : (s1 s2 s3 s4 : String) → (i j : Fin size) → i ≢ j →
           (opt0 s1 s2 i) ∙ (opt0 s3 s4 j) ≡ (opt0 s3 s4 j) ∙ (opt0 s1 s2 i)
OPTGOAL1 s1 s2 s3 s4 i j i≠j with s1 =? s2
...                          | yes _ with s3 =? s4
...                                    | yes _ = refl
...                                    | no  _ = sym (lUnit s3↔s4) ∙ rUnit s3↔s4
  where s3↔s4 = s3 ↔ s4 AT j
OPTGOAL1 s1 s2 s3 s4 i j i≠j | no _  with s3 =? s4
...                                    | no  _ = indep s1 s2 s3 s4 i j i≠j
...                                    | yes _ = sym (rUnit s1↔s2) ∙ lUnit s1↔s2
  where s1↔s2 = s1 ↔ s2 AT i

opt1 : R → R
opt1 doc = doc
opt1 ((s1 ↔ s2 AT j) i) = opt0 s1 s2 j i
opt1 (noop s j i₁ i₂) = OPTGOAL0 s j i₁ i₂
opt1 (indep s t u v i j i≠j i₁ i₂) = OPTGOAL1 s t u v i j i≠j i₁ i₂
opt1 (trunc i i₁ i₂) = {!!}

CORRECTGOAL0 : (s1 s2 : String) (j : Fin size) (i : Cubical.Foundations.Prelude.I) →
               (s1 ↔ s2 AT j) i ≡ opt1 ((s1 ↔ s2 AT j) i)
CORRECTGOAL0 s1 s2 j i with s1 =? s2
...                       | yes s1=s2 = cong (λ p → p i) (noop-helper (ptoc s1=s2))
...                       | no _      = refl

opt1-correct : (r : R) → r ≡ opt1 r
opt1-correct doc = refl
opt1-correct ((s1 ↔ s2 AT j) i) = CORRECTGOAL0 s1 s2 j {!!}
opt1-correct (noop s i i₁ i₂) = {!!}
opt1-correct (indep s t u v i j i≠j i₁ i₂) = λ i₃ → (OPTGOAL1 s t u v i j i≠j {!!} {!!})
opt1-correct (trunc i i₁ i₂) = {!!}

{-
Attempting the program and prove approach, but running into trouble with e (and also its application)
fibration : (doc ≡ doc) → (B : R → Type₀) → Cubical.Foundations.Prelude.I → Type₀
fibration p B = λ i → B (p i)

e : ∀ {p : doc ≡ doc} → PathP (fibration p (λ x → Σ[ y ∈ R ] y ≡ x)) (doc , refl) (doc , refl)
                        ≡ (Σ[ q ∈ doc ≡ doc ] p ≡ q)
e = {!!}


opt : (x : R) → Σ[ y ∈ R ] y ≡ x
opt doc = (doc , refl)
opt ((s1 ↔ s2 AT j) i) = (transport {!e!}
                                    (if s1 == s2
                                      then (refl , noop s1 j)
                                      else s1 ↔ s2 AT j , refl)) i
opt (noop s i i₁ i₂) = {!!}
opt (indep s t u v i j x i₁ i₂) = {!!}

optimize :(p : doc ≡ doc) → Σ[ q ∈ (doc ≡ doc) ] p ≡ q
optimize p = transport e (apd opt p)
-}

module testing where
  interp : doc ≡ doc → repoType → repoType
  interp p = equivFun (pathToEquiv (cong I p))

  bigBreakfast : repoType
  bigBreakfast = "eggs" ∷
                  ("bacon" ∷
                    ("hashed brown" ∷
                      ("baked beans" ∷
                        ("another hashed brown" ∷
                          ("sausage" ∷
                            ("toast" ∷
                              ("regret" ∷ [])))))))

  dumbPatch : doc ≡ doc
  dumbPatch = op ∙ nop ∙ nop ∙ nop
    where op = "eggs" ↔ "potetsalat" AT (# 0)
          nop = "nop" ↔ "nop" AT (# 4)

  result : repoType
  result = (interp dumbPatch) bigBreakfast
