---
layout: default
title : "Clones.Basic module"
date : "2023-10-18"
author: "Gonzalo Zigarán"
---

# Clones


```agda

open import Agda.Primitive               using () renaming ( Set to Type )
open import Level                        using ( _⊔_ ; Level ; suc )

module Clones.Basic (α : Level) (A : Type α) where

open import Data.Nat                     using ( ℕ )
open import Data.Fin                     using ( Fin )
open import Data.Product                 using ( Σ-syntax ; proj₁ ; proj₂ ; _,_ ; ∃ ; ∃-syntax)
open import Relation.Unary       using ( Pred ; _∈_ ; _⊆_ )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Overture.Operations          using ( Op )
open import Base.Relations.Continuous    using ( Rel )

private variable ρ β 𝓧 : Level

-- Para subconjuntos
-- Pred : {ρ β : Level} → Type ρ → Type (ρ ⊔ suc β)
-- Pred {β = β} X = X → Type β 
-- The type of operations on A of arity I
-- Op : Type α → Type 𝓥 → Type (α ⊔ 𝓥)
-- Op A I = (I → A) → A

-- Operaciones de aridad finita
FinOp : { n : ℕ} → Type α → Type α
FinOp { n = n } A = Op A (Fin n)

FinOps : Type α → Type α
FinOps A = Σ[ n ∈ ℕ ] (FinOp {n = n} A)

-- Funcion proyeccion, proyecta en la coordenada dada, infiere la aridad
π : { n : ℕ } → Fin n → FinOp A
π k = λ x → x k 

-- Definimos Clones 
containsProjections : Pred (FinOps A) ρ → Type ρ
containsProjections F = ∀ (n : ℕ) → ∀ (k : Fin n) → F ( n , π {n = n} k )

containsCompositions : Pred (FinOps A) ρ → Type (α ⊔ ρ)
containsCompositions F = (n m : ℕ)(f : FinOp {m} A )(gs : (Fin m → FinOp {n} A)) → F ( n , λ xs → f (λ i → gs i xs) )

isClon : Pred (FinOps A) ρ → Type (α ⊔ ρ)
isClon F = containsProjections F → containsCompositions F

Clones : Pred (Pred (FinOps A) ρ) (α ⊔ ρ)
Clones = λ F → isClon F 

record Clon : Type (α ⊔ suc ρ) where
  constructor mkclon
  field
    F  : Pred (FinOps A) ρ
    FIsClon : F ∈ Clones


open import Base.Algebras.Basic using ( Algebra )

-- Algebra : (α : Level) → Type (𝓞 ⊔ 𝓥 ⊔ suc α)
-- Algebra α =  Σ[ A ∈ Type α ]                 -- the domain
--              ∀ (f : ∣ 𝑆 ∣) → Op A (∥ 𝑆 ∥ f)  -- the basic operations

-- Subuniverses : (𝑨 : Algebra α) → Pred (Pred ∣ 𝑨 ∣ β) (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
-- Subuniverses 𝑨 B = (𝑓 : ∣ 𝑆 ∣)(𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) → Im 𝑎 ⊆ B → (𝑓 ̂ 𝑨) 𝑎 ∈ B


-- Relaciones de aridad finita
FinRel : { n : ℕ } → Type α → Type (suc α)
FinRel { n = n } A  = Rel A (Fin n)

FinRels : Type α → Type (suc α)
FinRels A = Σ[ n ∈ ℕ ] (FinRel {n} A)

-- Se fija que k vectores de largo n, coordeanada a coordenada, pertenezcan a la relación de aridad k
evalFinRel : { k : ℕ } → FinRel { n = k} A  → ( n : ℕ) → (Fin k → Fin n → A) → Type α
evalFinRel r n t = ∀ (j : Fin n) → r λ i → t i j 

-- f preserva la relacion r
_◃_ : { n k : ℕ } → FinOp {n = n} A → FinRel {n = k} A → Type α
_◃_ { n = n} f r = ∀ t → evalFinRel r n t → r λ i → f (t i)

-- Lema 3 a) sii b)
open import Base.Subalgebras.Subuniverses using ( Subuniverses )

-- preserv-iff-r-subuniv : ∀ {n k : ℕ} (f : FinOp { n} A) (r : FinRel {k} A)
--      → (f ◃ r)
--   → (f ◃ r) ≡ (r ∈ Subuniverses (A , ))
-- preserv-iff-r-subuniv f r = {!!}





-- invariantes de un conjunto de operaciones F
invₙ : {n : ℕ} → Pred (FinOps A) ρ → Pred (FinRel {n = n} A) (α ⊔ ρ)
invₙ F = λ r → ∀ f → f ∈ F → (proj₂ f) ◃ r

inv : Pred (FinOps A) ρ → Pred (FinRels A) (α ⊔ ρ)
inv F = λ r → ∀ f → f ∈ F → (proj₂ f) ◃ (proj₂ r)
-- inv F {ρ} = Σ[ n ∈ ℕ ] (invₙ {n = n} F {ρ = ρ})


-- polimorfismos de un conjunto de relaciones R
polₙ : {n : ℕ} → Pred (FinRels A) ρ → Pred (FinOp {n = n} A) (suc α ⊔ ρ)
polₙ R = λ f → ∀ r → r ∈ R → f ◃ (proj₂ r)

pol : Pred (FinRels A) ρ → Pred (FinOps A) (suc α ⊔ ρ)
pol R = λ f → ∀ r → r ∈ R →  (proj₂ f) ◃ (proj₂ r) 




-- TyConst : Type α → Type α
-- TyConst A = Op A ⊥

-- propiedad : (a : A) → TyConst A
-- propiedad a _ = a

-- propiedad' : TyConst A → A
-- propiedad' f = f (λ ())

-- compatible-Rel : {I J : ar}{A : Type α} → Op(A) J → Rel A I{ρ} → Type (𝓥 ⊔ α ⊔ ρ)
-- compatible-Rel f R  = ∀ t → eval-Rel R arity[ f ] t → R λ i → f (t i)


-- sucFinOp : FinOp {n = 1} ℕ
-- sucFinOp = λ f → ℕ.suc (f Fin.zero)

-- _^_ : Type α → ℕ → Type α
-- A ^ zero = A
-- A ^ (suc n) = A → A ^ n 

-- FinOp' : Type α → Type α 
-- FinOp' A = Σ[ n ∈ ℕ ] (A ^ n)

-- sucFinOp' : FinOp' ℕ
-- sucFinOp' = 1 ,  ℕ.suc

-- proj' : (n : ℕ) → Fin n → A ^ n
-- proj' zero ()
-- proj' (suc zero) zero = λ a₀ → a₀
-- proj' (suc (suc n)) zero = λ a₀ a₁ → proj' (suc n) zero a₀
-- proj' (suc (suc n)) (suc k) = λ a₀ a₁ → proj' (suc n) k a₁


-- toOp : ∀ n → (A ^ n) → FinOp {n = n} A
-- toOp zero f g = f
-- toOp (suc n) f g = toOp n (f (g zero)) (λ k -> g (suc k))


