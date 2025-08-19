{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Data.VertexSet where

------------------------------------------------------------------------
-- Definitions

data VertexSet (A : Set) : Set where
-- TODO

fromList : ∀ {A} → List A → VertexSet A
fromList xs = {!   !}

size : ∀ {A} → VertexSet A → ℕ
size vs = {!   !}

data _∈S_ {A} : A → VertexSet A → Set where
-- TODO

data _⊆_ {A} : VertexSet A → VertexSet A → Set where
-- TODO

record Sublist {A} (vs : VertexSet A) : Set where
  constructor sublist
  field
    xs  : VertexSet A
    ⊆vs : xs ⊆ vs

del : ∀ {A} → VertexSet A → A → Maybe (VertexSet A)
del vs v = {!   !}

del-decrease : ∀ {A} → (vs : VertexSet A) → (v : A)
             → {vs' : VertexSet A} → del vs v ≡ just vs'
             → size vs' < size vs
del-decrease vs u eq = {!   !}

del-subset : ∀ {A} → (vs : VertexSet A) → (v : A)
           → {vs' : VertexSet A} → del vs v ≡ just vs'
           → vs' ⊆ vs
del-subset vs v eq = {!   !}

size-mono-≤ : ∀ {A} {us vs : VertexSet A} → us ⊆ vs → size us ≤ size vs
size-mono-≤ us⊆vs = {!   !}

⊆-refl : ∀ {A} {vs : VertexSet A} → vs ⊆ vs
⊆-refl = {!   !}

⊆-trans : ∀ {A} {vs₁ vs₂ vs₃ : VertexSet A} → vs₁ ⊆ vs₂ → vs₂ ⊆ vs₃ → vs₁ ⊆ vs₃
⊆-trans ⊆vs₁₂ ⊆vs₂₃ = {!   !}