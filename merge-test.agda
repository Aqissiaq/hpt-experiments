{-# OPTIONS --cubical --rewriting #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws

module merge-test where

-- equivalence induction from https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#equivalenceinduction

postulate
  J-≃ : {ℓ ℓ' : Level} →
         (A : (X Y : Type ℓ) → X ≃ Y → Type ℓ') →
         ((X : Type ℓ) → A X X (idEquiv X)) →
         (X Y : Type ℓ) → (e : X ≃ Y) → A X Y e

data Base : Type where
  A : Base
  B : Base

data Repo : Type where
  [_] : Base → Repo
  patch :  [ A ] ≡ [ B ]

postulate
  path-ind :
    {ℓ : Level}
    {a0 : Base}
    (P : {x : Base} → [ a0 ] ≡ [ x ] → Type ℓ)
    → P refl
    → ((p : [ a0 ] ≡ [ A ]) → P p ≃ P (p ∙ patch))
    -------------------------------------------------------------------
    → {b : Base} → (q : [ a0 ] ≡ [ b ]) → P q

  β-refl :
    {ℓ : Level}
    {a0 : Base}
    {P : {x : Base} → [ a0 ] ≡ [ x ] → Type ℓ}
    {r : P refl}
    {e : (p : [ a0 ] ≡ [ A ]) → P p ≃ P (p ∙ patch)} →
    path-ind P r e refl ≡ r

  β-path :
    {ℓ : Level}
    {a0 : Base}
    {P : {x : Base} → [ a0 ] ≡ [ x ] → Type ℓ}
    {r : P refl}
    {e : (p : [ a0 ] ≡ [ A ]) → P p ≃ P (p ∙ patch)}
    {q : [ a0 ] ≡ [ A ]} →
    path-ind P r e (q ∙ patch) ≡ equivFun (e q) (path-ind P r e q)

Span : Base → Base → Type
Span x y = Σ[ z ∈ Base ] ([ z ] ≡ [ x ]) × ([ z ] ≡ [ y ])

Cospan : Base → Base → Type
Cospan x y = Σ[ n ∈ Base ] ([ x ] ≡ [ n ]) × ([ y ] ≡ [ n ])

{-
2. Jeg har en sterk fornemmelse at at induksjonsprinsippet må
brukes i alle fall tre ganger for å definere en funksjon på spans.
Skjematisk burde det se ut slik:
ind (ind (1) (2)) ( … ind  (3) (4) … ) . Hvor 1 er refl–refl caset,
2 er refl–do og 3 er do–refl og 4 er do–do.


litt usikker på do-do-casen, den er mer komplisert enn jeg liker
-}
span-ind :
  {ℓ : Level} →
  {zenith : Base} →
  (P : {x y : Base} → [ zenith ] ≡ [ x ] → [ zenith ] ≡ [ y ] → Type) →
  P refl refl →
  ((p : [ zenith ] ≡ [ A ]) → P refl p ≃ P refl (p ∙ patch)) →
  ((p : [ zenith ] ≡ [ A ]) → P p refl ≃ P (p ∙ patch) refl) →
  ((p : [ zenith ] ≡ [ A ]) (q : [ zenith ] ≡ [ A ]) →
    (P p q ≃ P (p ∙ patch) q)
    ≃ (P p (q ∙ patch) ≃ P (p ∙ patch) (q ∙ patch))) →
  -----------------------------------------------
  {x : Base} → (p : [ zenith ] ≡ [ x ]) → {y : Base} → (q : [ zenith ] ≡ [ y ]) → P p q
span-ind {ℓ} {zenith} P refl-refl refl-patch patch-refl patch-patch =
  path-ind (λ p → ({y : Base} → (q : [ zenith ] ≡ [ y ]) → P p q))
           (path-ind (λ {y} q → P refl q) refl-refl refl-patch)
           λ p → equivImplicitΠCod (equivΠCod λ q → e p q)
  where
  e : (p : [ zenith ] ≡ [ A ]) →
      {y : Base} → (q : [ zenith ] ≡ [ y ]) →
      P p q ≃ P (p ∙ patch) q
  e p = path-ind (λ {y} q → P p q ≃ P (p ∙ patch) q) (patch-refl p) (patch-patch p)

{-
1. Kanskje det hadde gått å definere merge i dette (litt enklere tilfellet):
Repo modell: To tilstander A og B, én path do : [A] = [B].
Merge skal merge do og do til do (altså at kospannet blir B,refl,refl).
-}

-- postulating this is basically like truncating the repo type, I guess
-- maybe it's provable tho
patches-contractible : ∀ x y →
                     isContr ([ x ] ≡ [ y ])
patches-contractible A A = refl , {!!}
patches-contractible A B = patch , {!!}
patches-contractible B A = (sym patch) , {!!}
patches-contractible B B = refl , {!!}

from-Contraction : {X : Type} →
                   isContr X →
                   (x y : X) →
                   x ≡ y
from-Contraction = isContr→isProp
merge : ∀ x y z →
        [ z ] ≡ [ x ] →
        [ z ] ≡ [ y ] →
        Cospan x y
merge x y z left right = span-ind (λ {x'} {y'} _ _ → Cospan x' y')
                                  (z , refl , refl)
                                  (λ p → left-refl p)
                                  (λ q → right-refl q)
                                  {!!}
                         left right
      where
      left-refl : [ z ] ≡ [ A ] → Cospan z A ≃ Cospan z B
      left-refl p = isoToEquiv (iso zA→zB zB→zA sect retr)
        where
        zA→zB : Cospan z A → Cospan z B
        zA→zB (A , _) = B , p ∙ patch , refl
        zA→zB (B , _) = A , p , sym patch

        zB→zA : Cospan z B → Cospan z A
        zB→zA (A , _) = B , p ∙ patch , patch
        zB→zA (B , _) = A , p , refl

        sect : section zA→zB zB→zA
        sect (A , p' , q') = let (_ , p'' , q'') = zA→zB (zB→zA (A , p' , q')) in
          ΣPathP (refl , ≡-× (isContr→isProp (patches-contractible z A) p'' p')
                             (isContr→isProp (patches-contractible B A) q'' q'))
        sect (B , p' , q') = let (_ , p'' , q'') = zA→zB (zB→zA (B , p' , q')) in
          ΣPathP (refl , ≡-× (isContr→isProp (patches-contractible z B) p'' p')
                             (isContr→isProp (patches-contractible B B) refl q'))

        retr : retract zA→zB zB→zA
        retr (A , p' , q') = let (_ , p'' , q'') = zB→zA (zA→zB (A , p' , q')) in
          ΣPathP (refl , ≡-× (isContr→isProp (patches-contractible z A) p'' p')
                             (isContr→isProp (patches-contractible A A) refl q'))
        retr (B , p' , q') = let (_ , p'' , q'') = zB→zA (zA→zB (B , p' , q')) in
          ΣPathP (refl , ≡-× (isContr→isProp (patches-contractible z B) p'' p')
                             (isContr→isProp (patches-contractible A B) patch q'))

      right-refl : [ z ] ≡ [ A ] → Cospan A z ≃ Cospan B z
      right-refl q = isoToEquiv (iso Az→Bz Bz→Az sect retr)
        where
        Az→Bz : Cospan A z → Cospan B z
        Az→Bz (A , _) = A , sym patch , q
        Az→Bz (B , _) = B , refl , q ∙ patch

        Bz→Az : Cospan B z → Cospan A z
        Bz→Az (A , _) = A , refl , q
        Bz→Az (B , _) = B , patch , q ∙ patch

        sect : section Az→Bz Bz→Az
        sect (A , p' , q') = let (_ , p'' , q'') = Az→Bz (Bz→Az (A , p' , q')) in
          ΣPathP (refl , ≡-× (isContr→isProp (patches-contractible B A) p'' p')
                             (isContr→isProp (patches-contractible z A) q q'))
        sect (B , p' , q') = let (_ , p'' , q'') = Az→Bz (Bz→Az (B , p' , q')) in
          ΣPathP (refl , ≡-× (isContr→isProp (patches-contractible B B) p'' p')
                             (isContr→isProp (patches-contractible z B) (q ∙ patch) q'))
        retr : retract Az→Bz Bz→Az
        retr (A , p' , q') = let (_ , p'' , q'') = Bz→Az (Az→Bz (A , p' , q')) in
          ΣPathP (refl , ≡-× (isContr→isProp (patches-contractible A A) p'' p')
                             (isContr→isProp (patches-contractible z A) q q'))
        retr (B , p' , q') = let (_ , p'' , q'') = Bz→Az (Az→Bz (B , p' , q')) in
          ΣPathP (refl , ≡-× (isContr→isProp (patches-contractible A B) p'' p')
                             (isContr→isProp (patches-contractible z B) (q ∙ patch) q'))

      patch-patch : (p q : [ z ] ≡ [ A ]) →
                    (Cospan A A ≃ Cospan B A) ≃ (Cospan A B ≃ Cospan B B)
      patch-patch p q = isoToEquiv (iso {!!} {!!} {!!} {!!})
        where
        ϕ : Cospan A A ≃ Cospan B A → Cospan A B ≃ Cospan B B
        ϕ = EquivJ (λ X e → {!!}) {!!}

      {-
      these are both equivalences IF [ x ] ≡ [ y ] is contractible for each x and y, which is kinda what we're thinking
      -}


{-
commutes : {x y : Base} → Span x y → Cospan x y → Type
commutes (z , p , q) (n , p' , q') = p ∙ p' ≡ q ∙ q'

Cospan-under : {x y : Base} → Span x y → Type
Cospan-under {x} {y} s = Σ[ c ∈ (Cospan x y)] (commutes s c)

refl-patch-merge-equiv : {zenith : Base} →
  (q : [ zenith ] ≡ [ A ]) →
  Cospan-under (zenith , refl , q) ≃
  Cospan-under (zenith , refl , q ∙ patch)
refl-patch-merge-equiv {zenith} q = isoToEquiv (iso expand {!!} {!!} {!!})
  where
  expand : Cospan-under (zenith , refl , q) →
           Cospan-under (zenith , refl , q ∙ patch)
  expand ((n , l , r) , comm) = (B , q ∙ patch , refl) , {!!}
  -- this is incomplete, and probably not an equivalence, but it is the function we want...

patch-refl-merge-equiv : {zenith : Base} →
  (p : [ zenith ] ≡ [ A ]) →
  Cospan-under (zenith , p , refl) ≃
  Cospan-under (zenith , p ∙ patch , refl)
patch-refl-merge-equiv {zenith} p = isoToEquiv (iso expand {!!} {!!} {!!})
  where
  expand : Cospan-under (zenith , p , refl) →
           Cospan-under (zenith , p ∙ patch , refl)
  expand ((n , l , r) , comm) = (B , refl , p ∙ patch) , {!!}
  -- same as above

patch-patch-merge-equiv : {zenith : Base} →
  (p q : [ zenith ] ≡ [ A ]) →
  (Cospan-under (zenith , p , q) ≃
    Cospan-under (zenith , p ∙ patch , q))
  ≃
  (Cospan-under (zenith , p , q ∙ patch) ≃
    Cospan-under (zenith , p ∙ patch , q ∙ patch))
  -- basically, if we know how to expand cospans under (z , p , q), can we do it for (z , p , q∙patch)?
patch-patch-merge-equiv {zenith} p q = isoToEquiv (iso {!!} {!!} {!!} {!!})
  where
  left : Cospan-under (zenith , p , q) ≃
         Cospan-under (zenith , p ∙ patch , q)
       → Cospan-under (zenith , p , q ∙ patch) ≃
         Cospan-under (zenith , p ∙ patch , q ∙ patch)
  left = {!!}
{-
φ : (A ≃ B) → (C ≃ D)
og ψ : (C ≃ D) → (A ≃ B) danner en evivalens om ψ (φ f) x = f x for
alle x:A, og  φ (ψ g) y = y for alle y : C.
-}
merge : {x y : Base} → (s : Span x y) → Cospan-under s
merge (zenith , p , q) = span-ind (λ p' q' → Cospan-under (zenith , (p' , q')))
                                  ((zenith , refl , refl) , refl)
                                  refl-patch-merge-equiv
                                  patch-refl-merge-equiv
                                  patch-patch-merge-equiv
                         p q
-}
