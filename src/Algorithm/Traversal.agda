{-# OPTIONS --guardedness #-}

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Fin as Fin
open import Data.List as List
open import Data.List.Membership.Propositional as List using (_∈_)
open import Data.List.Relation.Unary.Any
open import Data.Vec as Vec
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈Vec_)
open import Data.Vec.Relation.Unary.Any
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function.Base

module Algorithm.Traversal
  (A : Set) (eq? : (x y : A) → Dec (x ≡ y))
  (N : Set) where

open import Data.Core A eq? N
open nonEmptyGraph

------------------------------------------------------------------------
-- Traversal algorithms

mutual

  dfs : ∀ {n vs} → List A → Graph n vs → List A
  dfs {zero}  xs g = []
  dfs {suc n} xs g = dfsUtil xs g

  dfsUtil : ∀ {n vs} → List A → Graph (suc n) vs → List A
  dfsUtil []       g = []
  dfsUtil (x ∷ xs) g with findVtx g x
  ... | just i  = x ∷ dfs (gsuc g i List.++ xs) (delVtx g i)
  ... | nothing = dfsUtil xs g

mutual

  bfs : ∀ {n vs} → List A → Graph n vs → List A
  bfs {zero}  xs g = []
  bfs {suc n} xs g = bfsUtil xs g

  bfsUtil : ∀ {n vs} → List A → Graph (suc n) vs → List A
  bfsUtil []       g = []
  bfsUtil (x ∷ xs) g with findVtx g x
  ... | just i  = x ∷ bfs (xs List.++ gsuc g i) (delVtx g i)
  ... | nothing = bfsUtil xs g

------------------------------------------------------------------------
-- Properties

-- define reachability
data _[_↝_] : ∀ {n vs} → Graph n vs → A → A → Set where
  base : ∀ {n vs} → {v : A} → {g : Graph n vs} → v ∈Vec vs → g [ v ↝ v ]
  step : ∀ {n vs} → {u v w : A} → {g : Graph n vs}
         → g [ u ⇀ v ] → g [ v ↝ w ] → g [ u ↝ w ]

↝⇒nonEmpty : ∀ {vs} → {g : Graph zero vs} → {u v : A}
                → g [ u ↝ v ] → ⊥
↝⇒nonEmpty (step _ g[u↝v]) = ↝⇒nonEmpty g[u↝v]

↝⇒∈ : ∀ {n vs} → {g : Graph n vs} → {u v : A}
        → g [ u ↝ v ] → u ∈Vec vs
↝⇒∈ g[u↝v] = {!   !}

-- path properties

path-delete : ∀ {n vs} → {g : Graph (suc n) vs} → {i : Fin (suc n)} → {u v x : A}
    → g [ u ↝ v ] → V g [ i ]= x → g [ x ↝ v ] ⊎ (delVtx g i) [ u ↝ v ]
path-delete = {!   !}

_ : ∀ {n vs} → {g : Graph (suc n) vs} → {i : Fin (suc n)} → {u v : A}
    → V g [ i ]= u → g [ u ↝ v ] → ∃[ w ] w ∈ gsuc g i × (delVtx g i) [ w ↝ v ]
_ = {!   !}

private
  ∈-++ₗ : {B : Set} → {x : B} → {xs ys : List B}
        → x ∈ xs → x ∈ ys List.++ xs
  ∈-++ₗ {B} {x} {xs} {[]}     p = p
  ∈-++ₗ {B} {x} {xs} {y ∷ ys} p = there (∈-++ₗ p)

  ∈-++ᵣ : {B : Set} → {x : B} → {xs ys : List B}
        → x ∈ xs → x ∈ xs List.++ ys
  ∈-++ᵣ (here px) = here px
  ∈-++ᵣ (there p) = there (∈-++ᵣ p)

mutual
  dfs-↝ : ∀ {n vs} → (g : Graph n vs) → (u v : A) → (xs : List A)
          → u ∈ xs → g [ u ↝ v ] → v ∈ dfs xs g
  dfs-↝ {zero} {[]} _ _ _ _ _ g[u↝v] = ⊥-elim (helper (↝⇒∈ g[u↝v]))
    where helper : ∀ {v} → v ∈Vec [] → ⊥
          helper ()
  dfs-↝ {suc n} g u v xs u∈xs g[u↝v] = dfsUtil-↝ g u v xs u∈xs g[u↝v]

  dfsUtil-↝ : ∀ {n vs} → (g : Graph (suc n) vs) → (u v : A) → (xs : List A)
              → u ∈ xs → g [ u ↝ v ] → v ∈ dfsUtil xs g
  dfsUtil-↝ g u v (x ∷ xs) u∈xs g[u↝v] with findVtx g x in eq
  dfsUtil-↝ g u v (x ∷ xs) u∈xs         g[u↝v] | just i with eq? u x
  dfsUtil-↝ g u .u (x ∷ xs) u∈xs (base u∈vs)            | just i | yes u≡x = here u≡x
  dfsUtil-↝ g u  v (x ∷ xs) u∈xs (step g[u⇀w] g[w↝v]) | just i | yes u≡x 
    = {!   !}
  dfsUtil-↝ g u v (x ∷ xs) (here px)    g[u↝v] | just i | no u≢x = ⊥-elim (u≢x px)
  dfsUtil-↝ g u v (x ∷ xs) (there u∈xs) g[u↝v] | just i | no u≢x with path-delete g[u↝v] eq
  dfsUtil-↝ g u v (x ∷ xs) (there u∈xs) g[u↝v] | just i | no u≢x | inj₁ g[x↝v]
    = {!   !}
  dfsUtil-↝ g u v (x ∷ xs) (there u∈xs) g[u↝v] | just i | no u≢x | inj₂ delg[u↝v]
    = there (dfs-↝ (delVtx g i) u v (gsuc g i List.++ xs) (∈-++ₗ u∈xs) delg[u↝v])
  dfsUtil-↝ g u v (x ∷ xs) (here px)    g[u↝v] | nothing
    = ⊥-elim (findVtx-∈ {g = g} (↝⇒∈ g[u↝v]) (trans (cong (findVtx g) px) eq))
  dfsUtil-↝ g u v (x ∷ xs) (there u∈xs) g[u↝v] | nothing 
    = dfsUtil-↝ g u v xs u∈xs g[u↝v]