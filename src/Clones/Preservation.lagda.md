---
layout: default
title : "Clones.Preservation module"
date : "2023-10-18"
author: "Gonzalo Zigarán"
---

# Preservation


```agda

module Clones.Preservation where

open import Agda.Primitive               using () renaming ( Set to Type )
open import Level                        using ( Level )
open import Data.Nat                     using ( ℕ )
open import Data.Fin                     using ( Fin )
open import Data.Product                 using ( _,_ )

import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_ )

private variable α ρ : Level
```

En esta sección vamos a empezar a ver la relación que hay entre el espacio de Operaciones y de Relaciones de un conjunto $A$ dado. Para eso, vamos a definir cuando una operación $f$ preserva una relación $r$ ($f◃r$).
Concretamente, dada una operación $n$-aria $f$ y una relación $k$-aria $r$, decimos que $f$ preserva a $r$ si:
$(a₁₁, a₁₂, ... , a₁ₖ), ... , (aₙ₁, aₙ₂, ... , aₙₖ) ∈ r$ implica que $(f(a₁₁, ..., aₙ₁), ..., f(a₁ₖ, ..., aₙₖ)) ∈ r$.

```agda 

open import Clones.Basic using ( FinOp ; FinRel )

-- Se fija que k vectores de largo n, coordeanada a coordenada, pertenezcan a la relación de aridad k
evalFinRel : {A : Type α } → { k : ℕ } → FinRel { n = k} A  → ( n : ℕ) → (Fin k → Fin n → A) → Type α
evalFinRel r n t = ∀ (j : Fin n) → r λ i → t i j 

-- f preserva la relacion r
_◃_ : {A : Type α} → { n k : ℕ } → FinOp {n = n} A → FinRel {n = k} A → Type α
_◃_ { n = n} f r = ∀ t → evalFinRel r n t → r λ i → f (t i)

```

Definida esta noción, demostramos la conexión entre que $f◃r$, que $r$ sea un subuniverso del álgebra con la función $f$ y que $f$ sea un homomorfismo en el modelo que tiene la relación $r$.

Primero vemos la equivalencia entre que $f◃r$ y que $r$ sea subuniverso de ⟨ $A$ , $f$ ⟩ ᵏ.

```agda
open import Base.Structures.Substructures using ( Subuniverses )
open import Base.Structures.Products using ( ⨅ )
open import Clones.TermOps  using ( ⟨_,_,_⟩ ; R∅ ; F∅ )

preserv-then-r-subuniv : {A : Type α} → ∀ {n k : ℕ} (f : FinOp {n = n} A )  (r : FinRel {n = k} A )
                       → (f ◃ r)
                       ---------
                       → Subuniverses {𝑨 = ⨅ {ℑ = Fin k } (λ i → ⟨  A , (λ g → g ≡ ( n , f )) , R∅ ⟩)} {X = Type ρ} r
preserv-then-r-subuniv f r pfr = {!!}

r-subuniv-then-preserv : {A : Type α} → ∀ {n k : ℕ} (f : FinOp {n = n} A )  (r : FinRel {n = k} A )
                       → Subuniverses {𝑨 = ⨅ {ℑ = Fin k } (λ i → ⟨  A , (λ g → g ≡ ( n , f )) , R∅ ⟩)} {X = Type ρ} r
                       ---------
                       → (f ◃ r)
r-subuniv-then-preserv f r psubr = {!!}

```

A continuación demostramos la equivalencia entre $f◃r$ y que $f$ sea un homomorfismo de  ⟨ $A$ , $r$ ⟩ ⁿ en ⟨ $A$ , $r$ ⟩ .

```agda

open import Base.Structures using ( is-hom-rel )

-- Lema 3 a) sii c)
preserv-then-f-homo : {A : Type α} → ∀ {n k : ℕ} (f : FinOp {n = n} A )  (r : FinRel {n = k} A )
                    → (f ◃ r)
                    ----------
                    → is-hom-rel ( ⨅ {ℑ = Fin n } (λ i → ⟨  A , F∅ , (λ s → s ≡ ( k , r ) ) ⟩ ))  ⟨  A , F∅ , (λ s → s ≡ ( k , r ) ) ⟩ f
preserv-then-f-homo f r pfr = λ ( ( m , s ) , ps ) → λ as → λ i → {!!} 

f-homo-then-preserv : {A : Type α} → ∀ {n k : ℕ} (f : FinOp {n = n} A )  (r : FinRel {n = k} A )
                    → is-hom-rel ( ⨅ {ℑ = Fin n } (λ i → ⟨  A , F∅ , (λ s → s ≡ ( k , r ) ) ⟩ ))  ⟨  A , F∅ , (λ s → s ≡ ( k , r ) ) ⟩ f
                    ---------
                    → (f ◃ r)
f-homo-then-preserv f r pfhomo = λ as → {!!}

```
