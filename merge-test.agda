{-# OPTIONS --cubical --rewriting #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws

module merge-test where

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
  e : (p : [ zenith ] ≡ [ A ]) → {y : Base} → (q : [ zenith ] ≡ [ y ]) → P p q ≃ P (p ∙ patch) q
  e p = path-ind (λ {y} q → P p q ≃ P (p ∙ patch) q) (patch-refl p) (patch-patch p)

{-
: (p : [ zenith ] ≡ [ A ]) →
({y : Base} (q : [ zenith ] ≡ [ y ]) → P p q) ≃
({y : Base} (q : [ zenith ] ≡ [ y ]) → P (p ∙ patch) q)
1. Kanskje det hadde gått å definere merge i dette (litt enklere tilfellet):
Repo modell: To tilstander A og B, én path do : [A] = [B].
Merge skal merge do og do til do (altså at kospannet blir B,refl,refl).

2. Jeg har en sterk fornemmelse at at induksjonsprinsippet må
brukes i alle fall tre ganger for å definere en funksjon på spans.
Skjematisk burde det se ut slik:
ind (ind (1) (2)) ( … ind  (3) (4) … ) . Hvor 1 er refl–refl caset,
2 er refl–do og 3 er do–refl og 4 er do–do.
-}
