{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.List
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Algorithm (A : Set)
    (N : Set) (zero : N) (_+_ : N → N → Set) (_≤_ : N → N → Set) where

open import Data.Core A N zero _+_ _≤_
open nonEmptyGraph

------------------------------------------------------------------------
-- Graph algorithms

-- TODO : prove that dfs is terminating for finite graphs
-- {-# TERMINATING #-}
-- dfs : List A → Graph → List A
-- dfs []       g = []
-- dfs (v ∷ vs) g with findVtx g v
-- ... | true  = v ∷ dfs (gsuc g v ++ vs) g
-- ... | false = dfs vs g