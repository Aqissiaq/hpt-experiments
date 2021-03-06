{-# OPTIONS --cubical --rewriting #-}
{-
Implementation of the patch theory described in
5. A Patch Theory With laws (Angiuli et al.)

-}

module laws-hpt-noTrunc where

open import Data.Fin
  using(Fin  ; #_ ; zero ; suc)
open import Data.String
  using(String ; _≟_ ; _==_)
open import Data.Vec
  using(Vec ; [] ; _∷_ ; _[_]%=_ ; updateAt)
open import Data.Empty
  using(⊥ ; ⊥-elim)

open import Cubical.Core.Everything
  hiding (I)
open import Cubical.Foundations.Prelude
  renaming (I to Interval)
open import Cubical.Data.Equality
  hiding (I)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
  hiding (I)
open import Cubical.Data.Bool
  hiding(_≟_)
open import Cubical.Data.Nat.Order
  hiding(_≟_)
open import Function.Base
  using(id ; _∘_ )
open import Relation.Nullary
open import Relation.Binary
  using (Decidable)

open import Cubical.Foundations.HLevels

open import path-transport

open import Cubical.Foundations.Everything
  hiding(_∘_ ; I ; id)

-- https://github.com/agda/cubical/blob/9f7f8935dc513679a58fe9c98e07963a185d726e/Cubical/Foundations/Transport.agda
transportComposite : ∀ {ℓ} {A B C : Type ℓ} (p : A ≡ B) (q : B ≡ C) (x : A)
                     → transport (p ∙ q) x ≡ transport q (transport p x)
transportComposite = substComposite (λ D → D)

size : ℕ
size = 8

repoType : Type₀
repoType = Vec String size

isContr→≡ : {A B : Type} → isContr A → isContr B → A ≡ B
isContr→≡ contrA contrB = ua (isoToEquiv (isContr→Iso contrA contrB))

_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≢_ x y = x ≡ y → ⊥

sym≢ : ∀ {ℓ} {A : Set ℓ} → {x y : A}
       → x ≢ y → y ≢ x
sym≢ x≢y x≡y = ⊥-elim (x≢y (sym x≡y))

data R : Type₀ where
  -- context (point)
  doc : R
  -- patch (line)
  _↔_AT_ : (s1 s2 : String) (i : Fin size) → (doc ≡ doc)

  --patch laws (squares)
  noop : (s : String) (i : Fin size) → s ↔ s AT i ≡ refl

  indep : (s t u v : String) (i j : Fin size) → (i ≢ j)
          → (s ↔ t AT i) ∙ (u ↔ v AT j) ≡ (u ↔ v AT j) ∙ (s ↔ t AT i)

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


{-5.3 a simple optimizer to illustrate the use of patch laws-}

-- gives the noop square explicitly
noop-helper : {j : Fin size} {s1 s2 : String} → s1 ≡ s2
              → (s1 ↔ s2 AT j) ≡ refl
noop-helper {j} {s1} {s2} s1=s2 = cong (λ s → s ↔ s2 AT j) (s1=s2) ∙ noop s2 j

result-contractible : {X : Type} → (x : X) → isContr (Σ[ y ∈ X ] y ≡ x)
result-contractible x = (x , refl) , λ (y , p) → ΣPathP (sym p , λ i j → p (~ i ∨ j))

result-contractible' : {X : Type} → (x : X) → isContr (Σ[ y ∈ X ] x ≡ y)
result-contractible' x = (x , refl) , λ (y , p) → ΣPathP (p , (λ i j → p (i ∧ j)))

result-isSet : (x : R) → isSet (Σ[ y ∈ R ] y ≡ x)
result-isSet x = isProp→isSet (isContr→isProp (result-contractible x))

{- failed attempt that shows I *have* to do this by hand
R-contr-elim : {P : R → Type} →
  (∀ x → isContr (P x)) →
  P doc →
  (∀ s1 s2 j i → P ((s1 ↔ s2 AT j) i)) →
  ∀ x → P x
R-contr-elim contr Pdoc Pswap doc = Pdoc
R-contr-elim contr Pdoc Pswap ((s1 ↔ s2 AT j) i) = Pswap s1 s2 j i
R-contr-elim contr Pdoc Pswap (noop s i i₁ i₂) = {!!}
R-contr-elim contr Pdoc Pswap (indep s t u v i j x i₁ i₂) = {!!}
-}

opt : (x : R) → Σ[ y ∈ R ] y ≡ x
opt doc = (doc , refl)
opt x@((s1 ↔ s2 AT j) i) with s1 =? s2
...                       | yes s1=s2 = refl {x = doc} i , λ k → noop-helper {j} (ptoc s1=s2) (~ k) i
...                       | no _ = x , refl
-- these last two *should* be trivial by contractibility
-- but we need endpoints to be *definitionally* equal
opt (noop s j i k) = isOfHLevel→isOfHLevelDep 2 result-isSet
  (doc , refl) (doc , refl) (cong opt (s ↔ s AT j)) (cong opt refl) (noop s j) i k
-- ↑ this is adapted from HITs.SetQuotients.Properties.elim
-- the same approach for indep (correctly) does not pass termination checking
-- (and fuel doesn't help because it there is no reasonable base case)
opt x@(indep s t u v j j' j≠j' i k) = opt-with-fuel 1 x
  where
  opt-with-fuel : ℕ → (x : R) → Σ[ y ∈ R ] y ≡ x
  opt-with-fuel _ doc = opt doc
  opt-with-fuel _ x@((s1 ↔ s2 AT i) i₁) = opt x
  opt-with-fuel _ x@(noop s j i k) = isOfHLevel→isOfHLevelDep 2 result-isSet
    (doc , refl) (doc , refl) (cong opt (s ↔ s AT j)) (cong opt refl) (noop s j) i k
  opt-with-fuel zero (indep s t u v j j' j≠j' i k) = {!!}
  opt-with-fuel (suc n) (indep s t u v j j' j≠j' i k) = isOfHLevel→isOfHLevelDep 2 result-isSet
    (doc , refl) (doc , refl)
    (cong (opt-with-fuel n) ((s ↔ t AT j) ∙ (u ↔ v AT j')))
    (cong (opt-with-fuel n) ((u ↔ v AT j') ∙ (s ↔ t AT j)))
    (indep s t u v j j' j≠j') i k

optimize : (p : doc ≡ doc) → Σ[ q ∈ (doc ≡ doc) ] p ≡ q
optimize p = transport e (cong opt p)
  where
  -- "by rules for path-over-path, Σ-types, constant families and path types"
  -- footnote 6 on p. 9
  e : (PathP (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl) (doc , refl))
      ≡ (Σ[ q ∈ doc ≡ doc ] p ≡ q)
  e = (PathP (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl) (doc , refl))
      ≡⟨ PathP≡Path (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl) (doc , refl) ⟩
        Path (Σ[ y ∈ R ] y ≡ doc) (transport (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl)) (doc , refl)
      ≡⟨ cong (λ x → Path (Σ[ y ∈ R ] y ≡ doc) x (doc , refl)) (ΣPathP (refl , sym (lUnit p))) ⟩
        Path (Σ[ y ∈ R ] y ≡ doc) (doc , p) (doc , refl)
      ≡⟨ sym ΣPath≡PathΣ ⟩
        (Σ[ q ∈ doc ≡ doc ] (PathP (λ i → q i ≡ doc) p refl))
      ≡⟨ Σ-cong-snd (λ q → PathP≡Path (λ i → q i ≡ doc) p refl) ⟩
        (Σ[ q ∈ doc ≡ doc ] (transport (λ i → q i ≡ doc) p) ≡ refl)
      ≡⟨ Σ-cong-snd (λ q → cong (λ x → x ≡ refl) (β-transport q)) ⟩
        (Σ[ q ∈ doc ≡ doc ] (sym q ∙ p) ≡ refl)
      ≡⟨ Σ-cong-snd (λ q → lemma q p) ⟩
        (Σ[ q ∈ doc ≡ doc ] p ≡ q) ∎
    where
    -- lemma 2.11.2 (2) from The Book
    β-transport : (q : doc ≡ doc) → (transport (λ i → q i ≡ doc) p) ≡ sym q ∙ p
    β-transport q = (transport (λ i → q i ≡ doc) p)
      ≡⟨ transport-in-paths (λ x → x) (λ _ → doc) q p ⟩
        sym (cong (λ x → x) q) ∙ p ∙ (cong (λ _ → doc) q)
      ≡⟨ cong₂ {x = q} (λ a b → sym a ∙ p ∙ b) refl refl ⟩ (sym q) ∙ p ∙ refl
      ≡⟨ cong (λ a → sym q ∙ a) (sym (rUnit p)) ⟩ sym q ∙ p ∎


    lemma : {X : Type} {x y : X} →
            (f g : x ≡ y) →
            (sym f ∙ g ≡ refl) ≡ (g ≡ f)
    lemma f g = sym f ∙ g ≡ refl
      ≡⟨ cong (λ x → (sym f ∙ g) ≡ x) (sym (lCancel f)) ⟩
        (sym f) ∙ g ≡ (sym f) ∙ f
      -- this is the key step: the rest is just groupoidLaw shuffling
      ≡⟨ ua (compl≡Equiv f (sym f ∙ g) (sym f ∙ f)) ⟩
        (f ∙ (sym f ∙ g)) ≡ f ∙ (sym f ∙ f)
      ≡⟨ cong₂ (λ a b → a ≡ b) (assoc f (sym f) g) (assoc f (sym f) f) ⟩
        (f ∙ sym f) ∙ g ≡ (f ∙ sym f) ∙ f
      ≡⟨ cong₂ (λ a b → (a ∙ g) ≡ b ∙ f) (rCancel f) (rCancel f) ⟩
        refl ∙ g ≡ refl ∙ f
      ≡⟨ cong₂ (λ a b → a ≡ b) (sym (lUnit g)) (sym (lUnit f)) ⟩
        g ≡ f ∎

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

  nopPatch : doc ≡ doc
  nopPatch = ("nop" ↔ "nop" AT (# 0))

  swapPatch : doc ≡ doc
  swapPatch = "eggs" ↔ "potetsalat" AT (# 0)

  testPatch : doc ≡ doc
  testPatch = nopPatch ∙ swapPatch ∙ nopPatch

  -- works as expected
  resultOp : repoType
  resultOp = interp swapPatch bigBreakfast

  -- works as expected
  resultNop : repoType
  resultNop = interp nopPatch bigBreakfast

  -- gives a HUGE term
  result : repoType
  result = interp testPatch bigBreakfast
