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
open import Data.Product                 using ( _×_ ; Σ-syntax ; proj₁ ; proj₂ ; _,_ ; ∃ ; ∃-syntax)
open import Relation.Unary       using ( Pred ; _∈_ ; _⊆_ )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Overture        using ( _≈_ ; _⁻¹ ; Op )
open import Base.Relations.Continuous    using ( Rel )

private variable ρ β 𝓧 : Level

-- Para subconjuntos
-- Pred : {ρ β : Level} → Type ρ → Type (ρ ⊔ suc β)
-- Pred {β = β} X = X → Type β 
-- The type of operations on A of arity I
-- Op : Type α → Type 𝓥 → Type (α ⊔ 𝓥)
-- Op A I = (I → A) → A

-- Operaciones de aridad finita
FinOp : { n : ℕ } → Type α → Type α
FinOp { n = n } A = Op A (Fin n)

FinOps : Type α → Type α
FinOps A = Σ[ n ∈ ℕ ] (FinOp {n = n} A)

-- Funcion proyeccion, proyecta en la coordenada dada, infiere la aridad
π : {A : Type α} → { n : ℕ } → Fin n → FinOp A
π k = λ x → x k 

-- Relaciones de aridad finita
FinRel : { n : ℕ } → Type α → Type (suc α)
FinRel { n = n } A  = Rel A (Fin n)

FinRels : Type α → Type (suc α)
FinRels A = Σ[ n ∈ ℕ ] (FinRel {n} A)


-- Definimos Clones 
containsProjections : {A : Type α} → Pred (FinOps A) ρ → Type ρ
containsProjections F = ∀ (n : ℕ) → ∀ (k : Fin n) → F ( n , π {n = n} k )

containsCompositions : {A : Type α} → Pred (FinOps A) ρ → Type (α ⊔ ρ)
containsCompositions {A = A} F = (n m : ℕ)(f : FinOp {m} A )(gs : (Fin m → FinOp {n} A))
                                   → F ( m , f )
                                   → (∀ (i : Fin m) → F ( n , gs i ))
                                   → F ( n , λ (xs : (Fin n → A)) → f (λ i → gs i xs) )

--  λ (i : Fin m) → F ( n , gs i )


isClon : {A : Type α} → Pred (FinOps A) ρ → Type (α ⊔ ρ)
isClon F = containsProjections F × containsCompositions F

-- Clones : {A : Type α} → Pred (Pred (FinOps A) ρ) (α ⊔ ρ)
-- Clones = λ F → isClon F 

record Clon : Type (α ⊔ suc ρ) where
  constructor mkclon
  field
    F  : Pred (FinOps A) ρ
    FIsClon : isClon F


-- data Sg (𝑨 : Algebra α)(X : Pred ∣ 𝑨 ∣ β) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
--   where
--      var : ∀ {v} → v ∈ X → v ∈ Sg 𝑨 X
--      app : ∀ f a → Im a ⊆ Sg 𝑨 X → (f ̂ 𝑨) a ∈ Sg 𝑨 X

-- clon generado
data [_] {A : Type α}(F : Pred (FinOps A) ρ) : Pred (FinOps A) (suc Level.zero ⊔ α ⊔ ρ)
  where
    ops : ∀ {f} → f ∈ F → f ∈ [ F ]
    projections : containsProjections [ F ]
    compositions : containsCompositions [ F ]

GeneratedClonIsClon : {A : Type α} {F : Pred (FinOps A) ρ} → isClon {A = A} [ F ]
GeneratedClonIsClon {A = A} {F = F} = {![ F ].projections!} , {!!}

open import Base.Structures.Basic using ( signature ; structure )
open signature ; open structure

SubType : {U : Type β} → Pred U ρ → Type (β ⊔ ρ)
SubType {U = U} P = Σ[ a ∈ U ] (P a)

Op-sig : {A : Type α} → Pred (FinOps A) ρ → signature (α ⊔ ρ) Level.zero
Op-sig F = record {symbol = SubType F ; arity = λ f → Fin (proj₁ (proj₁ f))}

Rel-sig : {A : Type α} → Pred (FinRels A) ρ → signature (suc α ⊔ ρ) Level.zero
Rel-sig R = record {symbol = SubType R ; arity = λ r → Fin (proj₁ (proj₁ r))}

⟨_,_,_⟩ : (A : Type α) → (F : Pred (FinOps A) ρ) → (R : Pred (FinRels A) ρ)
             → structure (Op-sig {A = A} F) (Rel-sig {A = A} R) {α} {α}
⟨ A , F , R ⟩ = record {carrier = A ; op = λ f → proj₂ (proj₁ f) ; rel = λ r → proj₂ (proj₁ r) }


-- term-operations
open import Overture.Signatures
open import Base.Terms.Basic using ( Term ; 𝑻 ) 
open Term
open import Base.Structures.Terms using ( _⟦_⟧ )
variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ χ : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁
 𝑆 : Signature 𝓞 𝓥
 
TermOps : (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → Pred (FinOps ( carrier 𝑨 )) _
TermOps 𝑨 ( n , f ) = Σ[ t ∈ Term (Fin n) ] (∀ as → f as ≡ (𝑨 ⟦ t ⟧) as)

open import Base.Terms.Operations using ( _[_]t ; Substerm )
open import Base.Equality   using ( swelldef )
open import Function        using ( _∘_ )

subst-lemma-t :  { 𝐹 : signature 𝓞₀ 𝓥₀} → swelldef 𝓥₀ α → {I J : Type χ }(r : Term I)(s : Substerm J I )
                 (𝑨 : structure 𝐹 𝑅 {α} {ρ})(as : J → carrier 𝑨)
              →  (𝑨 ⟦ r [ s ]t ⟧) as ≡ (𝑨 ⟦ r ⟧) (λ i → (𝑨 ⟦ s i ⟧) as)
subst-lemma-t _ (ℊ x) s 𝑨 as = refl
subst-lemma-t wd (node f t) s 𝑨 as = wd ((op 𝑨) f)  ( λ j → (𝑨 ⟦ (t j) [ s ]t ⟧) as )
                                             ( λ j → (𝑨 ⟦ t j ⟧) (λ i → (𝑨 ⟦ s i ⟧) as)  )
                                             λ j → subst-lemma-t wd (t j) s 𝑨 as
                                             

TermOpsIsClon : { 𝐹 : signature 𝓞₀ 𝓥₀} → (∀ ℓ ℓ' → swelldef ℓ ℓ' ) → (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → isClon {A = carrier 𝑨} (TermOps 𝑨)
TermOpsIsClon wd 𝑨 = ( (λ n → λ k → ( ℊ k , λ as →  refl )) ,
                    λ n m → λ f → λ gs → λ tf → λ tgs → ( (proj₁ tf) [ (λ i → proj₁ (tgs i)) ]t , λ as → 
                      f (λ i → gs i as)
                    ≡⟨ proj₂ tf (λ i → gs i as) ⟩
                      (𝑨 ⟦ proj₁ tf ⟧) (λ i → gs i as)
                    ≡⟨ wd _ _ (𝑨 ⟦ proj₁ tf ⟧) (λ z → gs z as) (λ i → (𝑨 ⟦ proj₁ (tgs i)⟧) as) (λ i → proj₂ (tgs i ) as) ⟩
                      (𝑨 ⟦ proj₁ tf ⟧) (λ i → (𝑨 ⟦ proj₁ (tgs i)⟧) as)
                    ≡⟨ sym (subst-lemma-t (wd _ _) (proj₁ tf) (λ i → proj₁ (tgs i)) 𝑨 as) ⟩
                      (𝑨 ⟦ ( (proj₁ tf) [ (λ i → proj₁ (tgs i) ) ]t) ⟧ ) as
                    ∎  ) )


data ⊥ { ρ : Level } : Type ρ  where

R∅ : {A : Type α } → Pred (FinRels A) ρ
R∅ r = ⊥ 

Clo[_,_] : (A : Type α) → (F : Pred (FinOps A) ρ) →  Pred (FinOps A) (suc Level.zero ⊔ α ⊔ ρ)
Clo[ A , F ] = TermOps ⟨ A , F , R∅ {A = A} ⟩

-- Lema:  [F] = clon(A,F)
[F]≡Clo[A,F] : (A : Type α) (F : Pred (FinOps A) ρ)
             → [ F ] ≈ Clo[ A , F ]
[F]≡Clo[A,F] A F = λ ( n , f ) → {!!}


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


-- Lema 3 a) sii c)
preserv-then-f-homo : {A : Type α} → ∀ {n k : ℕ} (f : FinOp {n} A )  (r : FinRel {k} A )
                    → (f ◃ r)
                    ----------
                    → {!!}
preserv-then-f-homo f r pfr = {!!}

f-homo-then-preserv : {A : Type α} → ∀ {n k : ℕ} (f : FinOp {n} A )  (r : FinRel {k} A )
                    → {!!}
                    ---------
                    → (f ◃ r)
f-homo-then-preserv f r pfhomo = {!!}


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
