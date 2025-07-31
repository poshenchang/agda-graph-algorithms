{-# OPTIONS --guardedness #-}

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.List as List
open import Data.List.Membership.Propositional as List using (_∈_)
open import Data.Vec as Vec
open import Data.Fin
open import Data.Maybe
open import Data.Unit
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
  dfs {Nat.zero}  xs       g = []
  dfs {Nat.suc n} xs       g = dfsUtil xs g

  dfsUtil : ∀ {n vs} → List A → Graph (Nat.suc n) vs → List A
  dfsUtil [] g = []
  dfsUtil (x ∷ xs) g with findVtx g x
  ... | just i  = x ∷ dfs (gsuc g i List.++ xs) (delVtx g i)
  ... | nothing = dfsUtil xs g

-- open import Data.Bool

-- merge' : (cmp : A → A → Bool) → List A → List A → List A
-- merge' cmp [] ys = ys
-- merge' cmp xs [] = xs
-- merge' cmp (x ∷ xs) (y ∷ ys) with cmp x y
-- ... | true  = x ∷ merge' cmp xs (y ∷ ys)
-- ... | false = y ∷ merge' cmp (x ∷ xs) ys

mutual

  bfs : ∀ {n vs} → List A → Graph n vs → List A
  bfs {Nat.zero}  xs       g = []
  bfs {Nat.suc n} xs       g = bfsUtil xs g

  bfsUtil : ∀ {n vs} → List A → Graph (Nat.suc n) vs → List A
  bfsUtil [] g = []
  bfsUtil (x ∷ xs) g with findVtx g x
  ... | just i  = x ∷ bfs (xs List.++ gsuc g i) (delVtx g i)
  ... | nothing = bfsUtil xs g

------------------------------------------------------------------------
-- Properties

-- define neighbors
_[_⇀_] : ∀ {n vs} → Graph n vs → A → A → Set
g [ u ⇀ v ] = ∃[ i ] findVtx g u ≡ just i × v ∈ gsuc g i

-- define reachability
data _[_↝_] : ∀ {n vs} → Graph n vs → A → A → Set where
  here : ∀ {n vs} → {v : A} → {g : Graph n vs} → g [ v ↝ v ]
  step : ∀ {n vs} → {u v w : A} → {g : Graph n vs}
         → g [ u ↝ v ] → g [ v ⇀ w ] → g [ u ↝ w ]

-- dfs-↝ : ∀ {n vs} → (g : Graph n vs) → (u v : A)
--          → g [ u ↝ v ] → v ∈ dfs (u ∷ []) g
-- dfs-↝ g u v g[u↝v] = {!   !}