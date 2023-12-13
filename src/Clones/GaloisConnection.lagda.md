---
layout: default
title : "Clones.GaloisConnection module"
date : "2023-10-18"
author: "Gonzalo Zigarán"
---

# Galois Connection


```agda

module Clones.GaloisConnection where

open import Agda.Primitive               using () renaming ( Set to Type )
open import Level                        using ( _⊔_ ; Level ; suc )
open import Data.Nat                     using ( ℕ )
open import Data.Product                 using ( proj₂)
open import Relation.Unary       using ( Pred ; _∈_ )

import Relation.Binary.PropositionalEquality as Eq

open import Overture        using ( _≈_ )

private variable α ρ : Level

```


```agda

open import Clones.Basic using ( FinOps ; FinRels ; FinOp ; FinRel )
open import Clones.Preservation using ( _◃_ )

-- invariantes de un conjunto de operaciones F
invₙ : {A : Type α} {n : ℕ} → Pred (FinOps A) ρ → Pred (FinRel {n = n} A) (α ⊔ ρ)
invₙ F = λ r → ∀ f → f ∈ F → (proj₂ f) ◃ r

inv : {A : Type α} → Pred (FinOps A) ρ → Pred (FinRels A) (α ⊔ ρ)
inv F = λ r → ∀ f → f ∈ F → (proj₂ f) ◃ (proj₂ r)


-- polimorfismos de un conjunto de relaciones R
polₙ : {A : Type α} {n : ℕ} → Pred (FinRels A) ρ → Pred (FinOp {n = n} A) (suc α ⊔ ρ)
polₙ R = λ f → ∀ r → r ∈ R → f ◃ (proj₂ r)

pol : {A : Type α} → Pred (FinRels A) ρ → Pred (FinOps A) (suc α ⊔ ρ)
pol R = λ f → ∀ r → r ∈ R →  (proj₂ f) ◃ (proj₂ r) 

```
