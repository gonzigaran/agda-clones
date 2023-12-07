---
layout: default
title : "Clones.GaloisConnection module"
date : "2023-10-18"
author: "Gonzalo Zigarán"
---

# Clones


```agda

open import Agda.Primitive               using () renaming ( Set to Type )
open import Level                        using ( _⊔_ ; Level ; suc )

module Clones.GaloisConnection (α : Level) (A : Type α) where

open import Data.Nat                     using ( ℕ )
open import Data.Fin                     using ( Fin )
open import Data.Product                 using ( _×_ ; Σ-syntax ; proj₁ ; proj₂ ; _,_ ; ∃ ; ∃-syntax)
open import Relation.Unary       using ( Pred ; _∈_ ; _⊆_ )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Overture        using ( _≈_ ; _⁻¹ ; Op )
open import Base.Relations.Continuous    using ( Rel )

private variable ρ β 𝓧 : Level


-- invariantes de un conjunto de operaciones F
invₙ : {n : ℕ} → Pred (FinOps A) ρ → Pred (FinRel {n = n} A) (α ⊔ ρ)
invₙ F = λ r → ∀ f → f ∈ F → (proj₂ f) ◃ r

inv : Pred (FinOps A) ρ → Pred (FinRels A) (α ⊔ ρ)
inv F = λ r → ∀ f → f ∈ F → (proj₂ f) ◃ (proj₂ r)


-- polimorfismos de un conjunto de relaciones R
polₙ : {n : ℕ} → Pred (FinRels A) ρ → Pred (FinOp {n = n} A) (suc α ⊔ ρ)
polₙ R = λ f → ∀ r → r ∈ R → f ◃ (proj₂ r)

pol : Pred (FinRels A) ρ → Pred (FinOps A) (suc α ⊔ ρ)
pol R = λ f → ∀ r → r ∈ R →  (proj₂ f) ◃ (proj₂ r) 


