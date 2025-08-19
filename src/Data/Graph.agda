open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module Data.Graph 
    (V : Set) (Edges : V → List V) where

------------------------------------------------------------------------
-- Definitions

data E : V → V → Set where
  edge : ∀ {u v} → v ∈ Edges u → E u v

data Path : V → V → Set where
  []   : ∀ {v}                        → Path v v
  _▷_ : ∀ {u v w} → Path u v → E v w → Path u w