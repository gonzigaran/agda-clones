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
open import Data.Product                 using ( _×_ ; Σ-syntax ; proj₁ ; proj₂ ; _,_ )
open import Relation.Unary       using ( Pred ; _∈_ )

import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; sym )

private variable α ρ β : Level

```

## Operaciones y Relaciones

Para un conjunto $A$ y un $n ∈ ℕ$, definimos el conjunto de operaciones $n$-arias, y luego el conjunto de operaciones de aridad finita.

```agda

open import Overture        using ( Op )
-- Operaciones de aridad finita
FinOp : { n : ℕ } → Type α → Type α
FinOp { n = n } A = Op A (Fin n)

FinOps : Type α → Type α
FinOps A = Σ[ n ∈ ℕ ] (FinOp {n = n} A)

```

De la misma manera, el conjunto de relaciones con elementos de $A$ de aridad $n$, con $n ∈ ℕ$ fijo, y de relaciones de aridad finita

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

open import Overture        using ( _≈_ )
open import Data.Sum.Base using ( _⊎_ ; inj₁ ; inj₂ )

-- Funcion proyeccion, proyecta en la coordenada dada, infiere la aridad
π : {A : Type α} → { n : ℕ } → Fin n → FinOp A
π k = λ x → x k

Projs : {A : Type α} → Pred (FinOps A) α
Projs ( n , f ) =  Σ[ k ∈ Fin n ] (f ≈ π { n = n } k)

-- Definimos propiedades que tiene que cumplir un Clon
containsProjections : {A : Type α} → Pred (FinOps A) ρ → Type ρ
containsProjections F = ∀ (n : ℕ) → ∀ (k : Fin n) → F ( n , π {n = n} k )

containsCompositions : {A : Type α} → Pred (FinOps A) ρ → Pred (FinOps A) β → Type (α ⊔ ρ ⊔ β)
containsCompositions {A = A} F₁ F₂ = (n m : ℕ)(f : FinOp {n = m} A )(gs : (Fin m → FinOp {n = n} A))
                                   → (F₁ ( m , f )) ⊎ (Projs ( m , f ))
                                   → (∀ (i : Fin m) → F₂ ( n , gs i ))
                                   → F₂ ( n , λ (xs : (Fin n → A)) → f (λ i → gs i xs) )

containsExtensionality : {A : Type α} → Pred (FinOps A) ρ → Type (α ⊔ ρ)
-- containsExtensionality {A = A} F = (( n , f ) : FinOps A ) → Σ[ g ∈ FinOp {n = n} A ] (F ( n , g ) × f ≈ g)  → F ( n , f )
containsExtensionality {A = A} F = (( n , f ) : FinOps A ) → F ( n , f ) → ( g : FinOp {n = n} A ) →  f ≈ g → F ( n , g )
-- Definimos Clon
isClon : {A : Type α} → Pred (FinOps A) ρ → Type (α ⊔ ρ)
isClon F = containsProjections F × containsCompositions F F × containsExtensionality F

-- Clones : {A : Type α} → Pred (Pred (FinOps A) ρ) (α ⊔ ρ)
-- Clones = λ F → isClon F 

record Clon {A : Type α} : Type (α ⊔ suc ρ) where
  constructor mkclon
  field
    F  : Pred (FinOps A) ρ
    FIsClon : isClon F

```

### Clon generado

A partir de un conjunto $F$ de operaciones en $A$ podemos hablar del clon generado por $F$ como el menor clon que contiene a $F$. Lo denotamos con [ $F$ ].

```agda

-- clon generado
data [_] {A : Type α} (F : Pred (FinOps A) ρ) : Pred (FinOps A) (suc Level.zero ⊔ α ⊔ ρ)
  where
    ops : ∀ {f} → f ∈ F → f ∈ [ F ]
    projections : containsProjections [ F ]
    compositions : containsCompositions F [ F ]
    extensionality : containsExtensionality [ F ]

-- GeneratedClonIsClon : {A : Type α} {F : Pred (FinOps A) ρ} → isClon {A = A} [ F ]
-- GeneratedClonIsClon = projections , compositions , extensionality

π1 : {A : Type α} {n : ℕ} (F : Pred (FinOps A) ρ) → ( ℕ.suc n , π {n = ℕ.suc n} Fin.zero ) ∈ [ F ]
π1 {n = n} F = projections (ℕ.suc n) Fin.zero

```
