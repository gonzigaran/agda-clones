---
layout: default
title : "Clones.Basic module"
date : "2023-10-18"
author: "Gonzalo Zigarán"
---

# Clones


```agda

module Clones.Basic where

open import Agda.Primitive               using () renaming ( Set to Type )
open import Level                        using ( _⊔_ ; Level  )
open import Data.Nat                     using ( ℕ )
open import Data.Fin
open import Data.Product     using ( Σ-syntax )

open import Overture.Operations          using ( Op ; arity[_] )
open import Base.Relations.Continuous    using ( Rel )

private variable α ρ : Level
private variable A : Type α 

-- Operaciones de aridad finita
FinOp : { n : ℕ} → Type α → Type α 
FinOp { n = n } A = Op A (Fin n)

FinOps : Type α → Type α
FinOps A = Σ[ n ∈ ℕ ] (FinOp {n = n} A)

-- Funcion proyeccion, proyecta en la coordenada dada, infiere la aridad
proj : { n : ℕ } → Fin n → FinOp A
proj k = λ x → x k

-- Relaciones de aridad finita
FinRel : { n : ℕ } → Type α → { ρ : Level } → Type (α ⊔ Level.suc ρ)
FinRel { n = n } A { ρ = ρ } = Rel A (Fin n) {ρ}

FinRels : Type α → { ρ : Level } → Type (α ⊔ Level.suc ρ)
FinRels A {ρ} = Σ[ n ∈ ℕ ] (FinRel {n = n} A {ρ = ρ})

-- Se fija que k vectores de largo n, coordeanada a coordenada, pertenezcan a la relación de aridad k
evalFinRel : { k : ℕ } { A : Type α } → FinRel { n = k} A { ρ = ρ } → ( n : ℕ) → (Fin k → Fin n → A) → Type ρ
evalFinRel r n t = ∀ (j : Fin n) → r λ i → t i j 

-- f preserva la relacion r
_◃_ : { n k : ℕ } { A : Type α } → FinOp {n = n} A → FinRel {n = k} A {ρ = ρ} → Type (α ⊔ ρ) 
_◃_ { n = n} f r = ∀ t → evalFinRel r n t → r λ i → f (t i)





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


```
