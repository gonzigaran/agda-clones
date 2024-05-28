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
open import Data.Fin                     using ( Fin )
open import Data.Product                 using ( proj₂)
open import Relation.Unary       using ( Pred ; _∈_ )

import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_ )

open import Overture        using ( _≈_ )

private variable α ρ : Level

```

A partir de la definición de preserva ◃, podemos definir los operadores que van a ser los que nos den la conexión de Galois. Para un conjunto $F$ de operaciones, todas las relaciones que son preservadas por elementos de $F$, y para un conjunto $R$ de relaciones, todas las operaciones que preservan todas las relaciones de $R$.

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

A partir de las equivalencias de la preservación con ser subuniverso o ser homomorfismo, podemos caracterizar a los operadores $inv_n$ y $pol_n$ de la siguiente manera:

```agda

open import Base.Structures.Products using ( ⨅ )
open import Clones.TermOps  using ( ⟨_,_,_⟩ ; R∅ ; F∅ ; Ops-sig)

-- polₙ≡homos : {A : Type α} {n : ℕ} → (R : Pred (FinRels A) ρ)
--             → polₙ {n = n} R ≈
-- polₙ≡homos = ?

open import Base.Structures.Substructures using ( Subuniverses )

invₙ≡subuniv : {A : Type α} {n : ℕ} → (F : Pred (FinOps A) ρ)
               → invₙ {n = n} F ≈ Subuniverses {𝑨 = ⨅ {ℑ = Fin n } (λ i → ⟨  A , Ops-sig F , R∅ ⟩)}
invₙ≡subuniv = ?


```
