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
data [_] (F : Pred (FinOps A) ρ) : Pred (FinOps A) (α ⊔ ρ)
  where
    ops : ∀ {f} → f ∈ F → f ∈ [ F ]
    projections : containsProjections [ F ]
    compositions : containsCompositions [ F ]


open import Base.Structures.Basic using ( signature ; structure )
open signature ; open structure

-- record signature (𝓞 𝓥 : Level) : Type (suc (𝓞 ⊔ 𝓥)) where
--   field
--     symbol : Type 𝓞
--     arity : symbol → Type 𝓥

SubType : {U : Type β} → Pred U ρ → Type (β ⊔ ρ)
SubType {U = U} P = Σ[ a ∈ U ] (P a)
--              Σ U P
--              ∃ P

-- dado un conjunto de operaciones, el algebra dada por el conjunto con esas operaciones como tipo
Op-sig : {A : Type α} → Pred (FinOps A) ρ → signature (α ⊔ ρ) Level.zero
Op-sig F = record {symbol = SubType F ; arity = λ f → Fin (proj₁ (proj₁ f))}

Rel-sig : {A : Type α} → Pred (FinRels A) ρ → signature (suc α ⊔ ρ) Level.zero
Rel-sig R = record {symbol = SubType R ; arity = λ r → Fin (proj₁ (proj₁ r))}


-- record structure  (𝐹 : signature 𝓞₀ 𝓥₀)
--                   (𝑅 : signature 𝓞₁ 𝓥₁)
--                   {α ρ : Level} : Type (𝓞₀ ⊔ 𝓥₀ ⊔ 𝓞₁ ⊔ 𝓥₁ ⊔ (suc (α ⊔ ρ)))
--  where
--  field
--   carrier : Type α
--   op   : ∀(f : symbol 𝐹) → Op  carrier (arity 𝐹 f)      -- interpret. of operations
--   rel  : ∀(r : symbol 𝑅) → Rel carrier (arity 𝑅 r) {ρ}  -- interpret. of relations


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


-- TermFromTermOp : (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → ( ( n , f ) : FinOps ( carrier 𝑨 ) ) → TermOps 𝑨 ( n , f )
-- TermFromTermOp 𝑨 ( n , f ) = ( _ , _ ) 

-- fFromTerm : { n : ℕ } → Term (Fin n) → Type α
-- fFromTerm (ℊ x) = _
-- fFromTerm (node f t) = f

-- fFromTermOp : {𝑨 : structure 𝐹 𝑅 {α} {ρ}} → ( ( n , f ) : FinOps ( carrier 𝑨 ) ) → {tp : TermOps 𝑨 ( n , f )}  → Term ( Fin n) 
-- fFromTermOp ( n , f ) { tp = ( t , p ) } = t 

_∘t_ : { I J : Type β } → Term {𝑆 = 𝑆} I → ( I → Term J ) → Term J
(ℊ x) ∘t s = s x
(node f t) ∘t s = node f (λ i → (t i) ∘t s )


⟦∘t⟧≡⟦⟧∘t⟦⟧ : {𝑨 : structure 𝐹 𝑅 {α} {ρ}} { I J : Type β }  {t : Term I} {s : I → Term J} {as : J → carrier 𝑨}
      → (𝑨 ⟦ (t ∘t s) ⟧) as ≡ (𝑨 ⟦ t ⟧) (λ i → (𝑨 ⟦ (s i) ⟧) as) 
⟦∘t⟧≡⟦⟧∘t⟦⟧ {t = ℊ x} = refl
⟦∘t⟧≡⟦⟧∘t⟦⟧ {𝑨 = 𝑨} {t = node f r} {s = s} {as = as} = cong  (op 𝑨 f) {!!}


-- begin
--                                       op 𝑨 f (λ i → (𝑨 ⟦ t i ∘t s ⟧) as) ≡⟨ {!∘t-⟦⟧ {𝑨 = 𝑨} {t = t} {s = s} {as = as}!} ⟩
--                                       {!!}


TermOpsIsClon :  (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → isClon {A = carrier 𝑨} (TermOps 𝑨)
TermOpsIsClon 𝑨 = ( (λ n → λ k → ( ℊ k , λ as →  refl )) ,
                    λ n m → λ f → λ gs → λ ( t , pf ) → λ tgs → ( t ∘t (λ i → proj₁ (tgs i)) , λ as →  {!!}))
-- TermOpsIsClon' 𝑨 = ( (λ n → λ k → ( ℊ k , λ as →  refl )) ,
--                      λ n m → λ f → λ gs → λ ( t , pf ) → λ gts → {!(t ∘t (λ i → proj₁ (gts i)) , ? )!}  )-- {!!} ) -- ( {!!} , λ as → {!!}))

-- ( node {!!} {!!} , {!!} ) ) --{!λ ti → ?!} )

-- TermOpsIsClon : {F : Pred (FinOps A) ρ} → {R : Pred (FinRels A) ρ} → isClon (TermOps ⟨ A , F , R ⟩) 
-- TermOpsIsClon {F = F} {R = R} = ( (λ n → λ k → ( ℊ k , λ as → refl ) ) , λ n m → λ f →  λ gs → ( node (( m ,  f ) , {!!} )  (λ i → node ( (n , gs i) , {!} ) {!!} )  , λ as → {!!} ) )


data ⊥ { ρ : Level } : Type ρ  where

R∅ : {A : Type α } → Pred (FinRels A) ρ
R∅ r = ⊥ 

Clo[_,_] : (A : Type α) → (F : Pred (FinOps A) ρ) →  Pred (FinOps A) _
Clo[ A , F ] = TermOps ⟨ A , F , R∅ {A = A} ⟩

-- Lema:  [F] = clon(A,F)
-- [F]≡


-- Se fija que k vectores de largo n, coordeanada a coordenada, pertenezcan a la relación de aridad k
evalFinRel : { k : ℕ } → FinRel { n = k} A  → ( n : ℕ) → (Fin k → Fin n → A) → Type α
evalFinRel r n t = ∀ (j : Fin n) → r λ i → t i j 

-- f preserva la relacion r
_◃_ : { n k : ℕ } → FinOp {n = n} A → FinRel {n = k} A → Type α
_◃_ { n = n} f r = ∀ t → evalFinRel r n t → r λ i → f (t i)


-- Lema 3 a) sii b)
open import Base.Subalgebras.Subuniverses using ( Subuniverses )

-- Subuniverses : (𝑨 : Algebra α) → Pred (Pred ∣ 𝑨 ∣ β) (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
-- Subuniverses 𝑨 B = (𝑓 : ∣ 𝑆 ∣)(𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) → Im 𝑎 ⊆ B → (𝑓 ̂ 𝑨) 𝑎 ∈ B

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


