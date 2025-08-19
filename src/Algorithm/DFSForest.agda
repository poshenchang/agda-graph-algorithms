open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s)
open import Data.Nat.Induction renaming (<-wellFounded to ℕ-wf)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.On using (wellFounded)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Function.Base using (_∘_; _on_)
open import Induction.WellFounded using (WellFounded; WfRec)
open import Level using (0ℓ)

open import Data.Tree
open import Data.Tree.Properties
open import Data.VertexSet

module Algorithm.DFSForest
  (V : Set) (Edges : V → List V)
  (eq? : (x y : V) → Dec (x ≡ y))
  where

open import Data.Graph V Edges

------------------------------------------------------------------------
-- Definitions

_<S_ : Rel (VertexSet V) _
_<S_ = _<_ on size

<S-wf : WellFounded _<S_
<S-wf = wellFounded size ℕ-wf

open Induction.WellFounded.All <S-wf 0ℓ

dff-step : (vs : VertexSet V)
         → ({vs' : VertexSet V} → vs' <S vs → (List V → Forest V × Sublist vs'))
         → (stack : List V) → Forest V × Sublist vs
dff-step vs f []          = [] , sublist vs ⊆-refl
dff-step vs f (v ∷ stack) with del vs v in eq
... | just vs' = let ts₁ , (sublist vs₁ vs₁⊆vs')
                       = f {vs'} (del-decrease vs v eq) (Edges v)
                     ts₂ , (sublist vs₂ vs₂⊆vs₁)
                       = f {vs₁} (≤-trans (s≤s (size-mono-≤ vs₁⊆vs')) (del-decrease vs v eq)) stack
                 in  node v ts₁ ∷ ts₂ , sublist vs₂ (⊆-trans (⊆-trans vs₂⊆vs₁ vs₁⊆vs') (del-subset vs v eq))
... | nothing  = dff-step vs f stack

_≗_ : ∀ {A B : Set} → (A → B) → (A → B) → Set
f ≗ g = ∀ x → f x ≡ g x

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
                 → f ≗ g → f ≡ g

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

dff-step-ext : (vs : VertexSet V)
               {IH IH' : {vs' : VertexSet V} → vs' <S vs → (List V → Forest V × Sublist vs')}
             → (∀ {vs'} vs'<vs → IH {vs'} vs'<vs ≡ IH' {vs'} vs'<vs)
             → dff-step vs IH ≡ dff-step vs IH'
dff-step-ext vs ext = extensionality (dff-step-≗ vs ext)
  where dff-step-≗ : (vs : VertexSet V)
                     {IH IH' : {vs' : VertexSet V} → vs' <S vs → (List V → Forest V × Sublist vs')}
                   → (∀ {vs'} vs'<vs → IH {vs'} vs'<vs ≡ IH' {vs'} vs'<vs)
                   → dff-step vs IH ≗ dff-step vs IH'
        dff-step-≗ vs ext []          = refl
        dff-step-≗ vs ext (v ∷ stack) = {!   !}

dff-util : (vs : VertexSet V) → (stack : List V) → Forest V × Sublist vs
dff-util = wfRec
           (λ vs → List V → Forest V × Sublist vs)
           dff-step

dff : List V → Forest V
dff vs = proj₁ (dff-util (fromList vs) vs)

open Induction.WellFounded.FixPoint <S-wf (λ vs → List V → Forest V × Sublist vs)
                                    dff-step
                                    dff-step-ext

------------------------------------------------------------------------
-- Properties for depth first forest (dff-util)

dff-util-completeness : ∀ {v vs stack} → v ∈S vs → v ∈ stack
                      → v ∈F proj₁ (dff-util vs stack)
dff-util-completeness {v} {vs} {u ∷ stack} v∈vs v∈stack = {!unfold-wfRec   !}

------------------------------------------------------------------------
-- Properties for depth first forest (dff)

dff-completeness : ∀ {v vs} → v ∈ vs → v ∈F dff vs
dff-completeness {v} {vs} v∈vs = {!   !}

dff-soundness : ∀ {v vs} → v ∈F dff vs → v ∈ vs
dff-soundness v∈dff = {!   !}

dff-TreeEdge⇒Edge : ∀ {u v vs} → TreeEdgeF (dff vs) u v → E u v
dff-TreeEdge⇒Edge e = {!   !}


edge-classify : (vs : List V) → {u v : V} → E u v
              → (u∈dff : u ∈F dff vs)
              → (v∈dff : v ∈F dff vs)
              → v∈dff ≼F u∈dff ⊎ descF v∈dff u∈dff
edge-classify vs e u∈dff v∈dff = {!   !}