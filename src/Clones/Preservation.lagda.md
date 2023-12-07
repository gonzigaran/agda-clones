---
layout: default
title : "Clones.Preservation module"
date : "2023-10-18"
author: "Gonzalo Zigarán"
---

# Preservation


```agda

open import Agda.Primitive               using () renaming ( Set to Type )
open import Level                        using ( _⊔_ ; Level ; suc )

module Clones.Preservation (α : Level) (A : Type α) where

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

-- Se fija que k vectores de largo n, coordeanada a coordenada, pertenezcan a la relación de aridad k
evalFinRel : {A : Type α } → { k : ℕ } → FinRel { n = k} A  → ( n : ℕ) → (Fin k → Fin n → A) → Type α
evalFinRel r n t = ∀ (j : Fin n) → r λ i → t i j 

-- f preserva la relacion r
_◃_ : {A : Type α} → { n k : ℕ } → FinOp {n = n} A → FinRel {n = k} A → Type α
_◃_ { n = n} f r = ∀ t → evalFinRel r n t → r λ i → f (t i)


-- Lema 3 a) sii b)
open import Base.Structures.Substructures using ( Subuniverses )
open import Base.Structures.Products using ( ⨅ )

preserv-then-r-subuniv : {A : Type α} → ∀ {n k : ℕ} (f : FinOp {n} A )  (r : FinRel {k} A )
                       → (f ◃ r)
                       ---------
                       → Subuniverses {𝑨 = ⨅ {ℑ = Fin k } (λ i → ⟨  A , (λ g → g ≡ ( n , f )) , R∅ ⟩)} {X = Type ρ} r
preserv-then-r-subuniv f r pfr = {!!}

r-subuniv-then-preserv : {A : Type α} → ∀ {n k : ℕ} (f : FinOp {n} A )  (r : FinRel {k} A )
                       → Subuniverses {𝑨 = ⨅ {ℑ = Fin k } (λ i → ⟨  A , (λ g → g ≡ ( n , f )) , R∅ ⟩)} {X = Type ρ} r
                       ---------
                       → (f ◃ r)
r-subuniv-then-preserv f r psubr = {!!}


open import Base.Structures using ( is-hom-rel )

-- Lema 3 a) sii c)
preserv-then-f-homo : {A : Type α} → ∀ {n k : ℕ} (f : FinOp {n} A )  (r : FinRel {k} A )
                    → (f ◃ r)
                    ----------
                    → is-hom-rel ( ⨅ {ℑ = Fin n } (λ i → ⟨  A , F∅ , (λ s → s ≡ ( k , r ) ) ⟩ ))  ⟨  A , F∅ , (λ s → s ≡ ( k , r ) ) ⟩ f
preserv-then-f-homo f r pfr = λ ( ( m , s ) , ps ) → λ as → λ i → {!!} 

f-homo-then-preserv : {A : Type α} → ∀ {n k : ℕ} (f : FinOp {n} A )  (r : FinRel {k} A )
                    → is-hom-rel ( ⨅ {ℑ = Fin n } (λ i → ⟨  A , F∅ , (λ s → s ≡ ( k , r ) ) ⟩ ))  ⟨  A , F∅ , (λ s → s ≡ ( k , r ) ) ⟩ f
                    ---------
                    → (f ◃ r)
f-homo-then-preserv f r pfhomo = λ as → {!!}

