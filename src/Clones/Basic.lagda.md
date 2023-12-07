---
layout: default
title : "Clones.Basic module"
date : "2023-10-18"
author: "Gonzalo Zigarán"
---

# Clones: Basic definitions


```agda
module Clones.Basic where

open import Agda.Primitive               using () renaming ( Set to Type )
open import Level                        using ( _⊔_ ; Level ; suc )
open import Data.Nat                     using ( ℕ )
open import Data.Fin                     using ( Fin )
open import Data.Product                 using ( _×_ ; Σ-syntax ; _,_ )
open import Relation.Unary       using ( Pred ; _∈_ )

private variable α ρ : Level

```

## Operaciones y Relaciones

Para un conjunto $A$ definimos el conjunto de operaciones $n$-arias para un $n ∈ ℕ$ fijo, y luego el conjunto de operaciones de aridad finita.

```agda

open import Overture        using ( Op )
-- Operaciones de aridad finita
FinOp : { n : ℕ } → Type α → Type α
FinOp { n = n } A = Op A (Fin n)

FinOps : Type α → Type α
FinOps A = Σ[ n ∈ ℕ ] (FinOp {n = n} A)

```

De la misma manera, el conjunto de relaciones con elementos de $A$ de aridad para un $n$ fijo, y de relaciones de aridad finita

```agda

open import Base.Relations.Continuous    using ( Rel )
-- Relaciones de aridad finita
FinRel : { n : ℕ } → Type α → Type (suc α)
FinRel { n = n } A  = Rel A (Fin n)

FinRels : Type α → Type (suc α)
FinRels A = Σ[ n ∈ ℕ ] (FinRel {n = n} A)

```

## Clones

Difinimos a un clon de $A$ como un conjunto de operaciones en $A$ que cumple que:

- Contiene todas las proyecciones.
- Es cerrado por composiciones.

```agda
-- Funcion proyeccion, proyecta en la coordenada dada, infiere la aridad
π : {A : Type α} → { n : ℕ } → Fin n → FinOp A
π k = λ x → x k 

-- Definimos propiedades que tiene que cumplir un Clon
containsProjections : {A : Type α} → Pred (FinOps A) ρ → Type ρ
containsProjections F = ∀ (n : ℕ) → ∀ (k : Fin n) → F ( n , π {n = n} k )

containsCompositions : {A : Type α} → Pred (FinOps A) ρ → Type (α ⊔ ρ)
containsCompositions {A = A} F = (n m : ℕ)(f : FinOp {n = m} A )(gs : (Fin m → FinOp {n = n} A))
                                   → F ( m , f )
                                   → (∀ (i : Fin m) → F ( n , gs i ))
                                   → F ( n , λ (xs : (Fin n → A)) → f (λ i → gs i xs) )
-- Definimos Clon
isClon : {A : Type α} → Pred (FinOps A) ρ → Type (α ⊔ ρ)
isClon F = containsProjections F × containsCompositions F

-- Clones : {A : Type α} → Pred (Pred (FinOps A) ρ) (α ⊔ ρ)
-- Clones = λ F → isClon F 

record Clon {A : Type α} : Type (α ⊔ suc ρ) where
  constructor mkclon
  field
    F  : Pred (FinOps A) ρ
    FIsClon : isClon F

```

### Clon generado

A partir de un conjunto $F$ de operaciones en $A$ podemos hablar del clon generado por $F$ como el menor clon que contiene a $F$. Lo denotamos con [$F$].

```agda

-- clon generado
data [_] {A : Type α}(F : Pred (FinOps A) ρ) : Pred (FinOps A) (suc Level.zero ⊔ α ⊔ ρ)
  where
    ops : ∀ {f} → f ∈ F → f ∈ [ F ]
    projections : containsProjections [ F ]
    compositions : containsCompositions [ F ]

GeneratedClonIsClon : {A : Type α} {F : Pred (FinOps A) ρ} → isClon {A = A} [ F ]
GeneratedClonIsClon  = projections , compositions

```
