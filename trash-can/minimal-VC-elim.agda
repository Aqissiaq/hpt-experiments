{-# OPTIONS --cubical --rewriting #-}
{-
  Plan:
    - define S¹ as an elementary repo
    - write "my own" elimination rule
    - ???
    - profit?
-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Int
open import Cubical.Data.Bool

module minimal-VC-elim where

0-iden : ∀ z → pos 0 + z ≡ z
0{!!}-iden z = sym (pos0+ z)
{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE +-assoc sucInt+ 0-iden #-}

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

data Circle : Type₀ where
  base : Circle
  loop : base ≡ base

Circle-rec : {ℓ : Level} {B : Type ℓ} →
           (b : B) → (p : b ≡ b) →
           ---------------------
           (Circle → B)
Circle-rec b p base = b
Circle-rec b p (loop i) = p i

Circle-elim : {ℓ : Level} (B : Circle → Type ℓ) →
              (b : B base)
              -- I think this↓ is the cubical version of subst B loop b ≡ b
              (p : PathP (λ i → B (loop i)) b b) →
              --------------------------------
              (r : Circle) → B r
Circle-elim _ b _ base = b
Circle-elim _ _ p (loop i) = p i

helix : Circle → Type₀
helix = Circle-rec Int sucPathInt

data Repo : Type₀ where
  num : Int → Repo
  add : (n m : Int) → num n ≡ num (n + m)
  set : ∀ n → (m : Int) → num n ≡ num m

data Span-HIT : Repo → Repo → Type₀ where
  add-add : (n m k : Int) → Span-HIT (num (n + m)) (num (n + k)) -- p = add n m, q = add n k
  add-set : (n m k : Int) → Span-HIT (num (n + m)) (num k) -- p,q = add n m, set n k
  set-add : (n m k : Int) → Span-HIT (num m) (num (n + k)) -- p,q = set n m, add n k
  set-set : (n m k : Int) → Span-HIT (num m) (num k) -- p,q = set n m, set n k

  set=set : (n n' m : Int) → set-set n m m ≡ set-set n' m m
  -- add=add : (n n' m : Int) → add-add n m m ≡ add-add m n n

Span : {X : Type₀} → X → X → Type₀
Span {X} y y' = Σ[ x ∈ X ] (x ≡ y) × (x ≡ y')


Repo-elim : {ℓ : Level} →
            (B : Repo → Type ℓ)
            (f : (n : Int) → B (num n))
            (p : (n m : Int) → PathP (λ i → B (add n m i)) (f n) (f (n + m)))
            (q : ∀ n → (m : Int) → PathP (λ i → B (set n m i)) (f n) (f m))
           ---------------------------------------------------------------
             → (x : Repo) → B x
Repo-elim _ f _ _ (num x) = f x
Repo-elim _ _ p _ (add n m i) = p n m i
Repo-elim _ _ _ q (set n m i) = q n m i

CoSpan :  Repo → Repo → Type₀
CoSpan y y' = Σ[ z ∈ Repo ] (y ≡ z) × (y' ≡ z)

fixed-y : ∀ {y : Repo} → Repo → Type₀
fixed-y {y} y' = Span y y'

Span-elim : ∀ {y y'} →
           (B : Span y y' → Type₀)
           (f : (x : Repo) → (p : x ≡ y) → (q : x ≡ y') → B (x , p , q)) →
           -----------------------------------------------------------------------------
           (s : Span y y') → B s
Span-elim B f (x , p , q) = f x p q


{- WANT: something like
  B : Span y y' → Type₀
  add-add : (n m b : Int) → B (num b , add b n , add b m)
  add-set : (n m b : Int) → B (num b , add b n , set m)
  set-add : (n m b : Int) → B (num b , set n , add b m)
  set-set : (n m b : Int) → B (num b , set n , set m)
  -------------------------------------------------------
  (s : Span y y') → B s

Problems:
  what to do when base is along a path?
  actually defining this thing lol

baby steps:
  (p : Patch) → B p som bryr seg om patch-typen
-}
Patch : Repo → Repo → Type₀
Patch x y = x ≡ y

Patch-elim : ∀ {x y} →
             (B : Patch x y → Type₀)
             (f : (p : x ≡ y) → B p)
             -------------------------------
             (p : Patch x y) → B p
Patch-elim B f p = f p

data PatchType : Type₀ where
  addP : PatchType
  setP : PatchType

Patch' : Repo → Repo → Type₀
Patch' x y = Pair (Patch x y) PatchType

Patch'-elim : ∀ {x y} →
            (B : Patch' x y → Type₀)
            (f-add : (p : Patch x y) → B (p , addP))
            (f-set : (p : Patch x y) → B (p , setP))
            ------------------------------------------------------
            → (q : Patch' x y ) → B q
Patch'-elim B f-add f-set (p , addP) = f-add p
Patch'-elim B f-add f-set (p , setP) = f-set p

-- simple example that depends on type of patch
is-add : ∀ {n m} → Patch' (num n) (num m) → Bool
is-add = Patch'-elim (λ _ → Bool) (λ _ → true) (λ _ → false)

Span' : Repo → Repo → Type₀
Span' y y' = Σ[ x ∈ Repo ] (Patch' x y) × (Patch' x y')

CoSpan' : Repo → Repo → Type₀
CoSpan' y y' = Σ[ z ∈ Repo ] (Patch' y z) × (Patch' y' z)

Span'-elim : ∀ {y y'} →
               (B : Span' y y' → Type₀)
               (f : (x : Repo) (span : (Patch' x y) × (Patch' x y')) → B (x , span))
               -----------------------------
               → (s : Span' y y') → B s
Span'-elim B f (x , span) = f x span

swapPair : {A : Type₀} {B C : A → Type₀}
           → Σ[ a ∈ A ] B a × C a → Σ[ a ∈ A ] C a × B a
swapPair (a , b , c) = a , c , b

filled : ∀ {y y'} → Span y y' → CoSpan y y' → Type₀
filled (_ , (p , q)) (_ , (p' , q')) = p ∙ p' ≡ q ∙ q'

{-
thoughts from Håkon:
  - the equivalences *do* in fact hold
  - but they are deceptive, 'cause we actually want the info
  - maybe try to define useful elimination rules
        - ask Jonathan, he's struggled w/ this
-}
merge : ∀ {y y'} → Span y y' → CoSpan y y'
merge {y} {y'} = {!!}
