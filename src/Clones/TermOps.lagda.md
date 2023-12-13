---
layout: default
title : "Clones.TermOps module"
date : "2023-10-18"
author: "Gonzalo Zigarán"
---

# Term Operations


```agda

{-# OPTIONS --allow-unsolved-metas #-}

module Clones.TermOps where

open import Agda.Primitive               using () renaming ( Set to Type )
open import Level                        using ( _⊔_ ; Level ; suc )
open import Data.Fin                     using ( Fin )
open import Data.Product                 using ( Σ-syntax ; proj₁ ; proj₂ ; _,_ )
open import Relation.Unary       using ( Pred  )

import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; sym )
open Eq.≡-Reasoning using ( _≡⟨⟩_ ; step-≡ ; _∎)

open import Overture        using ( _≈_ )

private variable α ρ β : Level

```

Para un álgebra $𝑨$ dada, podemos hablar del Clon de $𝑨$ cómo todas las operaciones que se pueden generar a partir de componer las funciones del álgebra y las proyecciones. Este clon coincide con las *term-operations*, que son todas las operaciones definidas a partir de un término.  


```agda

-- term-operations
open import Clones.Basic using ( FinOps ; FinRels )
open import Base.Structures.Basic using ( signature ; structure )
open signature ; open structure
open import Base.Terms.Basic using ( Term )
open import Base.Structures.Terms using ( _⟦_⟧ )
variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ χ : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁
 
TermOps : (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → Pred (FinOps ( carrier 𝑨 )) _
TermOps 𝑨 ( n , f ) = Σ[ t ∈ Term (Fin n) ] (∀ as → f as ≡ (𝑨 ⟦ t ⟧) as)


```

Lo primero a demostrar es que efectivamente el conjunto de *term-operations* de un álgebra es un Clon. Para ello vamos a utilizar una versión del lema de sustitución. 

```agda

open import Base.Terms.Operations using ( _[_]t ; Substerm )
open import Base.Equality   using ( swelldef )

subst-lemma-t :  { 𝐹 : signature 𝓞₀ 𝓥₀} → swelldef 𝓥₀ α → {I J : Type χ }(r : Term I)(s : Substerm J I )
                 (𝑨 : structure 𝐹 𝑅 {α} {ρ})(as : J → carrier 𝑨)
              →  (𝑨 ⟦ r [ s ]t ⟧) as ≡ (𝑨 ⟦ r ⟧) (λ i → (𝑨 ⟦ s i ⟧) as)
subst-lemma-t _ (Term.ℊ x) s 𝑨 as = refl
subst-lemma-t wd (Term.node f t) s 𝑨 as = wd ((op 𝑨) f)  ( λ j → (𝑨 ⟦ (t j) [ s ]t ⟧) as )
                                             ( λ j → (𝑨 ⟦ t j ⟧) (λ i → (𝑨 ⟦ s i ⟧) as)  )
                                             λ j → subst-lemma-t wd (t j) s 𝑨 as

open import Clones.Basic using ( isClon )

TermOpsIsClon : { 𝐹 : signature 𝓞₀ 𝓥₀} → (∀ ℓ ℓ' → swelldef ℓ ℓ' ) → (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → isClon {A = carrier 𝑨} (TermOps 𝑨)
TermOpsIsClon wd 𝑨 = ( (λ n → λ k → ( Term.ℊ k , λ as →  refl )) ,
                    λ n m → λ f → λ gs → λ tf → λ tgs → ( (proj₁ tf) [ (λ i → proj₁ (tgs i)) ]t , λ as → 
                      f (λ i → gs i as)
                    ≡⟨ proj₂ tf (λ i → gs i as) ⟩
                      (𝑨 ⟦ proj₁ tf ⟧) (λ i → gs i as)
                    ≡⟨ wd _ _ (𝑨 ⟦ proj₁ tf ⟧) (λ z → gs z as) (λ i → (𝑨 ⟦ proj₁ (tgs i)⟧) as) (λ i → proj₂ (tgs i ) as) ⟩
                      (𝑨 ⟦ proj₁ tf ⟧) (λ i → (𝑨 ⟦ proj₁ (tgs i)⟧) as)
                    ≡⟨ sym (subst-lemma-t (wd _ _) (proj₁ tf) (λ i → proj₁ (tgs i)) 𝑨 as) ⟩
                      (𝑨 ⟦ ( (proj₁ tf) [ (λ i → proj₁ (tgs i) ) ]t) ⟧ ) as
                    ∎  ) )
```

En varias ocaciones, a partir de un conjunto de operaciones $F$ y uno de relaciones $R$, vamos a querer hablar de la estructura dada por el conjunto $A$ y con el lenguaje que tiene un símbolo para cada operación en $F$ y un símbolo de relación para cada relación en $R$, interpretados de la manera esperable. Denotaremos con ⟨ $A$, $F$, $R$ ⟩ a dicha estructura.


```agda

-- a partir de un subconjunto, nos generamos una signatura con un símbolo para cada elemento
SubType : {U : Type β} → Pred U ρ → Type (β ⊔ ρ)
SubType {U = U} P = Σ[ a ∈ U ] (P a)

-- signatura para un conjunto de operaciones
Ops-sig : {A : Type α} → Pred (FinOps A) ρ → signature (α ⊔ ρ) Level.zero
Ops-sig F = record {symbol = SubType F ; arity = λ f → Fin (proj₁ (proj₁ f))}

-- signatura para un conjunto de relaciones
Rels-sig : {A : Type α} → Pred (FinRels A) ρ → signature (suc α ⊔ ρ) Level.zero
Rels-sig R = record {symbol = SubType R ; arity = λ r → Fin (proj₁ (proj₁ r))}

-- estructura inducida por F y R
⟨_,_,_⟩ : (A : Type α) → (F : Pred (FinOps A) ρ) → (R : Pred (FinRels A) ρ)
             → structure (Ops-sig {A = A} F) (Rels-sig {A = A} R) {α} {α}
⟨ A , F , R ⟩ = record {carrier = A ; op = λ f → proj₂ (proj₁ f) ; rel = λ r → proj₂ (proj₁ r) }

```

Si $F$∅ es el conjunto vacío de operaciones y $R$∅ el conjunto vacío de relaciones, entones ⟨ $A$, $F$∅, $R$ ⟩ es una estructura relacional y ⟨ $A$, $F$, $R$∅ ⟩ un álgebra. Y como tenemos un álgebra, podemos hablar del clon de las *term-operations*, denotado por Clo[ $A$ , $F$ ].

```agda

data ⊥ { ρ : Level } : Type ρ  where

-- conjunto vacío de relaciones
R∅ : {A : Type α } → Pred (FinRels A) ρ
R∅ r = ⊥

-- conjunto vacío de relaciones
F∅ : {A : Type α } → Pred (FinOps A) ρ
F∅ f = ⊥ 

Clo[_,_] : (A : Type α) → (F : Pred (FinOps A) ρ) →  Pred (FinOps A) (suc Level.zero ⊔ α ⊔ ρ)
Clo[ A , F ] = TermOps ⟨ A , F , R∅ {A = A} ⟩

```

El clon de las *term-operations* dado por Clo[ $A$ , $F$ ] coincide con el clon generado por $F$.

```agda

-- Lema:  [F] = clon(A,F)
open import Clones.Basic using ( [_] )

-- TermOps 𝑨 ( n , f ) = Σ[ t ∈ Term (Fin n) ] (∀ as → f as ≡ (𝑨 ⟦ t ⟧) as)

[F]≡Clo[A,F] : (A : Type α) (F : Pred (FinOps A) ρ)
             → Clo[ A , F ] ≈ [ F ]
[F]≡Clo[A,F] A F = λ ( n , f ) →  {!!}

```
