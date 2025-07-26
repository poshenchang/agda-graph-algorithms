{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.List
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Algorithm (A : Set) (eq? : (x y : A) → Dec (x ≡ y))
    (N : Set) (zero : N) (_+_ : N → N → Set) (_≤_ : N → N → Set) where

open import Data.Core A eq? N zero _+_ _≤_
open Graph

------------------------------------------------------------------------
-- Graph algorithms

dfs : List A → Graph → List A
dfs []       g = []
dfs (v ∷ vs) g with findVtx g v
... | true  = {!   !}
... | false = dfs vs g