{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc; zero; pred)
open import Data.Fin renaming (_≟_ to _fin≟_)
open import Data.Unit
open import Data.Maybe
open import Data.List as List hiding (findIndex)
open import Data.Vec as Vec
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.All
open import Data.Vec.Relation.Unary.AllPairs.Core
open import Data.Vec.Relation.Unary.Unique.Propositional hiding (_∷_; [])
open import Data.Vec.Relation.Unary.Unique.Setoid as Setoid hiding (_∷_; []; Unique)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function

------------------------------------------------------------------------
-- Definitions

module Data.Core (A : Set) (eq? : (x y : A) → Dec (x ≡ y))
    (N : Set) (Nzero : N) (_+_ : N → N → Set) (_≤_ : N → N → Set) where

-- 'r' for recursive

rremove : ∀ {n} → Vec A (suc n) → Fin (suc n) → Vec A n
rremove         (v ∷ vs)  Fin.zero   = vs
rremove {suc n} (v ∷ vs) (Fin.suc i) = v ∷ rremove vs i

rremove-∉ : ∀ {n} {v : A} {vs : Vec A (suc n)} {i : Fin (suc n)} 
            → All (_≢_ v) vs → All (_≢_ v) (rremove vs i)
rremove-∉         {vs = _ ∷ vs} {i = Fin.zero}  (_   ∷ v∉vs) = v∉vs
rremove-∉ {suc n} {vs = x ∷ vs} {i = Fin.suc i} (v≢x ∷ v∉vs) = v≢x ∷ rremove-∉ v∉vs

mutual
  Graph : (n : ℕ) → (vs : Vec A n) → Set
  Graph 0 [] = ⊤
  Graph (suc n) vs = nonEmptyGraph n vs

  record nonEmptyGraph (n : ℕ) (vs : Vec A (suc n)): Set where
    coinductive
    field
      inEdges  : Fin (suc n) → List (Fin (suc n) × N)
      outEdges : Fin (suc n) → List (Fin (suc n) × N)
      delVtx   : (i : Fin (suc n)) → Graph n (rremove vs i)
      unique-vs : Unique vs

open nonEmptyGraph

------------------------------------------------------------------------
-- Graph operations

-- efficiency of graph operations largely depends on the construction 
-- of the graph

addVtx : ∀ {n vs} (v : A) (g : Graph n vs) (v∉g : All (v ≢_) vs) → Graph (suc n) (v ∷ vs)
addVtx {zero} {[]} v ⊤ _ = ( record
   { inEdges   = const [] ; 
     outEdges  = const [] ; 
     delVtx    = λ {Fin.zero → ⊤} ; 
     unique-vs = [] ∷ [] })
addVtx {suc n} {vs} v g v∉g = g'
  where
    g' : Graph (suc (suc n)) (v ∷ vs)
    inEdges   g'  Fin.zero   = []
    inEdges   g' (Fin.suc i) = List.map (λ {(j , w) → Fin.suc j , w}) (inEdges g i)
    outEdges  g'  Fin.zero   = []
    outEdges  g' (Fin.suc i) = List.map (λ {(j , w) → Fin.suc j , w}) (outEdges g i)
    delVtx    g'  Fin.zero   = g
    delVtx    g' (Fin.suc i) = addVtx v (delVtx g i) (rremove-∉ v∉g)
    unique-vs g'             = v∉g ∷ unique-vs g

addEdge : ∀ {n vs} (i j : Fin n) (w : N) (g : Graph n vs) 
          → Graph n vs
addEdge {zero}  {[]} i j w ⊤ = ⊤
inEdges (addEdge {suc n} {v ∷ vs} i j w g) k with k fin≟ i
... | yes _ = (j , w) ∷ (inEdges g k)
... | no  _ = inEdges g k
outEdges (addEdge {suc n} {v ∷ vs} i j w g) k with k fin≟ j
... | yes _ = (i , w) ∷ outEdges g k
... | no  _ = outEdges g k
delVtx (addEdge {suc n} {v ∷ vs} i j w g) k with k fin≟ i | k fin≟ j 
... | yes _ | _     = delVtx g k
... | no  _ | yes _ = delVtx g k    
delVtx (addEdge {suc n} {v ∷ vs} zero    _       _ _) zero    | no p | no _ = ⊥-elim (p refl)
delVtx (addEdge {suc n} {v ∷ vs} (suc _) zero    _ _) zero    | no _ | no q = ⊥-elim (q refl)
delVtx (addEdge {suc n} {v ∷ vs} (suc i) (suc j) w g) zero    | no _ | no _ = addEdge i j w (delVtx g zero)
delVtx (addEdge {suc n} {v ∷ vs} i       j       w g) (suc k) | no _ | no _ = addEdge (pinch k i) (pinch k j) w (delVtx g (suc k))
unique-vs (addEdge {suc n} {v ∷ vs} i j w g) = unique-vs g

------------------------------------------------------------------------
-- Utility functions

-- Requires decidable equality on A
private
  findIndex : ∀ {n} → (xs : Vec A n) → (x : A) → Maybe (Fin n)
  findIndex [] x = nothing
  findIndex (y ∷ ys) x with eq? x y
  ... | yes _ = just zero
  ... | no  _ = Data.Maybe.map suc (findIndex ys x)

findVtx : ∀ {n vs} → (g : Graph n vs) → A → Maybe (Fin n)
findVtx {vs = vs} g v = findIndex vs v

gsuci : ∀ {n vs} → Graph n vs → Fin n → List (Fin n)
gsuci {suc _} g i = List.map proj₁ (outEdges g i)

gsuc : ∀ {n vs} → Graph n vs → Fin n → List A
gsuc {vs = vs} g i = List.map (λ j → Vec.lookup vs j) (gsuci g i)

