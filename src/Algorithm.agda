{-# OPTIONS --guardedness #-}

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Nat.Induction renaming (<-wellFounded to ℕ-wf)
open import Data.List as List
open import Data.Vec as Vec
open import Data.Fin
open import Data.Maybe
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Product.Relation.Binary.Lex.Strict
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.On
open import Relation.Nullary
open import Function.Base
open import Induction.WellFounded
open import Level


module Algorithm (A : Set) (eq? : (x y : A) → Dec (x ≡ y))
    (N : Set) (zero : N) (_+_ : N → N → Set) (_≤_ : N → N → Set) where

open import Data.Core A eq? N zero _+_ _≤_
open nonEmptyGraph

------------------------------------------------------------------------
-- Traversal algorithms

record traversal : Set where
  field
    size   : ℕ
    {vs}     : Vec A size
    graph  : Graph size vs
    list   : List A
    result : List A

open traversal

emptyTraversal : traversal
emptyTraversal = record
  { size   = Nat.zero
  ; graph  = tt
  ; list   = []
  ; result = []
  }

private
  trav→pair : traversal → ℕ × ℕ
  trav→pair t = (size t , List.length (list t))

_<trav_ : Rel traversal _
_<trav_ = (×-Lex _≡_ Nat._<_ Nat._<_) on trav→pair

trav-wf : WellFounded _<trav_
trav-wf = wellFounded trav→pair (×-wellFounded ℕ-wf ℕ-wf)

module WFTraversal = Induction.WellFounded.All trav-wf 0ℓ

dfs-step : (t : traversal) → ({u : traversal} → u <trav t → traversal) → traversal
dfs-step record { size = Nat.zero ; graph = _ ; list = _  ; result = _ } _ = emptyTraversal
dfs-step record { size = (suc n)  ; graph = _ ; list = [] ; result = _ } _ = emptyTraversal
dfs-step record { size = (suc n)  ; graph = g ; list = (x ∷ xs) ; result = res } f with findVtx g x 
... | just i  = f {record { size = n ; graph = delVtx g i ; list = gsuc g i List.++ xs ; result = x ∷ res }}
                  (inj₁ (s≤s ≤-refl))
... | nothing = f {record { size = (Nat.suc n) ; graph = g ; list = xs ; result = res }}
                  (inj₂ (refl , s≤s ≤-refl))

dfs-wfRec : traversal → traversal
dfs-wfRec = WFTraversal.wfRec (λ _ → traversal) dfs-step

-- how depth first search would look like without needing to dealing with nasty
-- termination issues
-- dfs : ∀ {n vs} → List A → Graph n vs → List A
-- dfs {Nat.zero} xs       g = []
-- dfs {suc n}    []       g = []
-- dfs {suc n}    (x ∷ xs) g with findVtx g x
-- ... | just i  = x ∷ dfs (gsuc g i List.++ xs) (delVtx g i)
-- ... | nothing = dfs xs g

bfs-step : (t : traversal) → ({u : traversal} → u <trav t → traversal) → traversal
bfs-step record { size = Nat.zero ; graph = _ ; list = _  ; result = _ } _ = emptyTraversal
bfs-step record { size = (suc n)  ; graph = _ ; list = [] ; result = _ } _ = emptyTraversal
bfs-step record { size = (suc n)  ; graph = g ; list = (x ∷ xs) ; result = res } f with findVtx g x 
... | just i  = f {record { size = n ; graph = delVtx g i ; list = xs List.++ gsuc g i ; result = x ∷ res }}
                  (inj₁ (s≤s ≤-refl))
... | nothing = f {record { size = (Nat.suc n) ; graph = g ; list = xs ; result = res }}
                  (inj₂ (refl , s≤s ≤-refl))

bfs-wfRec : traversal → traversal
bfs-wfRec = WFTraversal.wfRec (λ _ → traversal) bfs-step