open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Induction renaming (<-wellFounded to ℕ-wf)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; []; _∷_; _∷ʳ_; ⊆-refl; ⊆-trans)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties using (length-mono-≤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.On using (wellFounded)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function.Base using (_on_)
open import Induction.WellFounded using (WellFounded)
open import Level using (0ℓ)

open import Data.Tree
open import Data.Tree.Properties

module Algorithm.DFSForest
  (V : Set) (Edges : V → List V) where

record State : Set where
    constructor state
    field
      vs    : List V
      stack : List V

state→pair : State → ℕ × ℕ
state→pair (state vs stack) = length vs , length stack

_<S_ : Rel State _
_<S_ = (×-Lex _≡_ _<_ _<_) on state→pair

<S-wf : WellFounded _<S_
<S-wf = wellFounded state→pair (×-wellFounded ℕ-wf ℕ-wf)

module stateTraversal = Induction.WellFounded.All <S-wf 0ℓ

record Sublist {A} (L : List A) : Set where
  constructor sublist
  field
    xs : List A
    ⊆L : xs ⊆ L

del : List V → V → Maybe (List V)
del xs x = {!   !}

del-decrease : ∀ xs x {xs'} → del xs x ≡ just xs'
             → length xs' < length xs
del-decrease eq = {!   !}

del-sublist : ∀ xs x {xs'} → del xs x ≡ just xs'
            → xs' ⊆ xs
del-sublist eq = {!   !}

dfs-forest-util : (s : State) → Forest V × Sublist (State.vs s)
dfs-forest-util = stateTraversal.wfRec
                  (λ s → Forest V × Sublist (State.vs s))
                  dfs-forest-step
  where
    dfs-forest-step : (s : State)
                    → ({s' : State} → s' <S s → Forest V × Sublist (State.vs s'))
                    → Forest V × Sublist (State.vs s)
    dfs-forest-step (state []         stack)       f = [] , sublist [] []
    dfs-forest-step (state vs@(_ ∷ _) [])          f = [] , sublist vs ⊆-refl
    dfs-forest-step (state vs@(_ ∷ _) (v ∷ stack)) f with del vs v in eq
    ... | just vs' = let ts₁ , (sublist vs₁ vs₁⊆vs')
                           = f {state vs' (Edges v)} (inj₁ (del-decrease vs v eq))
                         ts₂ , (sublist vs₂ vs₂⊆vs₁)
                           = f {state vs₁ stack} (inj₁ (≤-trans (s≤s (length-mono-≤ vs₁⊆vs')) (del-decrease vs v eq)))
                     in  node v ts₁ ∷ ts₂ , sublist vs₂ (⊆-trans (⊆-trans vs₂⊆vs₁ vs₁⊆vs') (del-sublist vs v eq))
    ... | nothing  = f {state vs stack} (inj₂ (refl , ≤-refl))

dfs-forest : List V → Forest V
dfs-forest vs = proj₁ (dfs-forest-util (state vs vs))