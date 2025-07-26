{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.List
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

------------------------------------------------------------------------
-- Definitions

module Data.Core (A : Set) (eq? : (x y : A) → Dec (x ≡ y))
    (N : Set) (zero : N) (_+_ : N → N → Set) (_≤_ : N → N → Set) where

record Graph : Set where
  coinductive
  field
    findVtx  : A → Bool
    inEdges  : A → List (A × N)
    outEdges : A → List (A × N)
    delVtx   : A → Graph

open Graph

empty : Graph
findVtx  empty _ = false
inEdges  empty _ = []
outEdges empty _ = []
delVtx   empty _ = empty

------------------------------------------------------------------------
-- Graph construction

-- efficiency of graph operations largely depends on the construction 
-- of the graph

addVtx : A → Graph → Maybe Graph
addVtx v g with findVtx g v
... | true  = nothing
... | false = just (addVtxHelper v g)
  where
    addVtxHelper : A → Graph → Graph
    findVtx  (addVtxHelper v g) u with eq? u v 
    ... | yes _ = true
    ... | no  _ = findVtx g u
    inEdges  (addVtxHelper v g) u with eq? u v
    ... | yes _ = []
    ... | no  _ = inEdges g u
    outEdges (addVtxHelper v g) u with eq? u v
    ... | yes _ = []
    ... | no  _ = outEdges g u
    delVtx   (addVtxHelper v g) u with eq? u v
    ... | yes _ = g
    ... | no  _ = addVtxHelper v (delVtx g u)

record Edge : Set where
  field
    src : A
    dst : A
    weight : N

open Edge

addEdge : Edge → Graph → Maybe Graph
addEdge e g with findVtx g (src e) | findVtx g (dst e)
... | false | _     = nothing
... | true  | false = nothing
... | true  | true  = just (addEdgeHelper e g)
  where
    addEdgeHelper : Edge → Graph → Graph
    findVtx  (addEdgeHelper e g) v = findVtx g v
    inEdges  (addEdgeHelper e g) v with eq? v (dst e)
    ... | yes _ = (src e , weight e) ∷ inEdges g v
    ... | no  _ = inEdges g v
    outEdges (addEdgeHelper e g) v with eq? v (src e)
    ... | yes _ = (dst e , weight e) ∷ outEdges g v
    ... | no  _ = outEdges g v
    delVtx   (addEdgeHelper e g) v with eq? v (src e) | eq? v (dst e)
    ... | yes _ | _     = g
    ... | no  _ | yes _ = g
    ... | no  _ | no  _ = addEdgeHelper e (delVtx g v)

-- TODO : complete graphs

-- TODO : complete bipartite graphs

------------------------------------------------------------------------
-- Graph properties

-- isEmpty : Graph → Set

-- isFinite : Graph → Set

