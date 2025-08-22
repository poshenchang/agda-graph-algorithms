open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Vec using (Vec; []; _∷_; toList; fromList)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈Vec_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Tree
open import Data.Tree.Properties
open import Data.Tree.Operations

module Algorithm.DFSForest
  (V : Set) (Edges : V → List V) where

open import Data.Graph V Edges

------------------------------------------------------------------------
-- Definitions

del : ∀ {n} → Vec V (suc n) → V → Maybe (Vec V n)
del = {!   !}

TreeExt : (t : Tree V) → (v : V) → Set
TreeExt t v = ∃[ u ] (u ∈T t) × (E u v)

data ForestExt : (f : Forest V) → (v : V) → Set where
  leaf   : ∀ {f v} → ∃[ u ] (u ∈F f) × (E u v) → ForestExt f v
  branch : ∀ {f v} → ForestExt f v

record ForestStack (n : ℕ) : Set where
  constructor fStack
  field
    vs    : Vec V n
    ts    : Forest V
    stack : List (∃[ v ] ForestExt ts v)

forest-ext : ∀ (ts : Forest V) (v : V)
             → ForestExt ts v
             → Forest V
forest-ext ts v (leaf (u , u∈ts , e)) = insertF ts u∈ts v
forest-ext ts v branch                = ts ∷ʳ node v []

∈-forest-ext : ∀ (ts : Forest V) (v : V)
               → (ext : ForestExt ts v)
               → v ∈F forest-ext ts v ext
∈-forest-ext ts v (leaf (u , u∈ts , e)) = ∈-insertF u∈ts
∈-forest-ext ts v branch   = helper root
  where helper : ∀ {v : V} {t ts} → v ∈T t → v ∈F (ts ∷ʳ t)
        helper {ts = []}     v∈t = here v∈t
        helper {ts = x ∷ ts} v∈t = there (helper v∈t)

ForestExt-∈ : ∀ {ts u v} (ext : ForestExt ts v)
            → ForestExt ts u
            → ForestExt (forest-ext ts v ext) u
ForestExt-∈ (leaf (w , w∈ts , e)) (leaf (w' , w'∈ts , e'))
  = leaf (w' , insertF-preserves∈ w'∈ts , e')
ForestExt-∈ branch (leaf (w , w∈ts , e)) = leaf (w , helper w∈ts , e)
  where helper : ∀ {v : V} {t ts} → v ∈F ts → v ∈F (ts ∷ʳ t)
        helper (here  v∈t') = here v∈t'
        helper (there v∈ts) = there (helper v∈ts)
ForestExt-∈ _ branch = branch

map-∈ : ∀ {A : Set} → (xs : List A) → List (∃[ x ] x ∈ xs)
map-∈ []       = []
map-∈ (x ∷ xs) = (x , here refl) ∷ map (λ { (y , y∈xs) → (y , there y∈xs) }) (map-∈ xs)

edges-ext : ∀ {ts} (v : V)
          → v ∈F ts
          → List (∃[ u ] ForestExt ts u)
edges-ext v v∈ts = map (λ { (u , u∈E) → u , leaf (v , v∈ts , edge u∈E) }) (map-∈ (Edges v))

dff-step : {n : ℕ}
          → Vec V (suc n) → (ts : Forest V)
          → List (∃[ v ] ForestExt ts v)
          → ForestStack n
dff-step (_ ∷ vs) ts [] = fStack vs ts []
dff-step vs ts ((v , ext) ∷ stack) with del vs v
... | just vs' = fStack vs' (forest-ext ts v ext)
                   (edges-ext v (∈-forest-ext ts v ext) 
                   ++ map (λ { (u , ext') → u , ForestExt-∈ ext ext' }) stack)
... | nothing  = dff-step vs ts stack

dff-rec : {n : ℕ}
        → ForestStack n
        → ForestStack 0
dff-rec {zero}  fstack               = fstack
dff-rec {suc n} (fStack vs ts stack) = dff-rec (dff-step vs ts stack)

dff : (vs : List V) → Forest V
dff vs = ForestStack.ts
         (dff-rec (fStack (fromList vs) [] 
                    (map (λ v → v , branch) vs)))

------------------------------------------------------------------------
-- Depth-First-Forest Properties (dff)

case_of_ : ∀ {A B : Set} → (x : A) → (f : A → B) → B
case x of f = f x

open import Algorithm.TopoSort V Edges

-- uniqueness

dff-uniqueness : ∀ {vs} → Unique (postorderF (dff vs))
dff-uniqueness {vs} = {!   !}

-- completeness

dff-step-completeness : {n : ℕ}
                      → (vs : Vec V (suc n)) → (ts : Forest V)
                      → (stack : List (∃[ v ] ForestExt ts v))
                      → ∀ {v} → v ∈Vec vs
                      → v ∈Vec ForestStack.vs (dff-step vs ts stack)
                        ⊎ v ∈F ForestStack.ts (dff-step vs ts stack)
dff-step-completeness vs ts stack v∈vs = {!   !}

dff-step-preserve-vtx : {n : ℕ}
                      → (vs : Vec V (suc n)) → (ts : Forest V)
                      → (stack : List (∃[ v ] ForestExt ts v))
                      → ∀ {v} → v ∈F ts
                      → v ∈F ForestStack.ts (dff-step vs ts stack)
dff-step-preserve-vtx vs ts stack v∈ts = {!   !}

dff-rec-preserve-vtx : {n : ℕ}
                      → (fstack : ForestStack n)
                      → ∀ {v} → v ∈F ForestStack.ts fstack
                      → v ∈F ForestStack.ts (dff-rec fstack)
dff-rec-preserve-vtx {zero}  fstack v∈ts = v∈ts
dff-rec-preserve-vtx {suc n} (fStack vs ts stack) v∈ts
  = dff-rec-preserve-vtx (dff-step vs ts stack)
    (dff-step-preserve-vtx vs ts stack v∈ts)

dff-rec-completeness : {n : ℕ}
                      → (fstack : ForestStack n)
                      → ∀ {v} → v ∈Vec ForestStack.vs fstack
                      → v ∈F ForestStack.ts (dff-rec fstack)
dff-rec-completeness {suc n} (fStack vs ts stack) v∈vs with dff-step-completeness vs ts stack v∈vs
... | inj₁ v∈vs' = dff-rec-completeness (dff-step vs ts stack) v∈vs'
... | inj₂ v∈ts' = dff-rec-preserve-vtx (fStack vs ts stack) {! v∈ts'  !}

dff-completeness : ∀ {v vs} → v ∈ vs → v ∈F dff vs
dff-completeness v∈vs = {!   !}

--soundness

dff-soundness : ∀ {v vs} → v ∈F dff vs → v ∈ vs
dff-soundness v∈dff = {!   !}

-- edge preserving

PreservesEdges : Forest V → Set
PreservesEdges ts = ∀ {u v} → TreeEdgeF ts u v → E u v

dff-step-TreeEdge⇒Edge : {n : ℕ}
                        → (vs : Vec V (suc n)) → (ts : Forest V)
                        → (stack : List (∃[ v ] ForestExt ts v))
                        → PreservesEdges ts
                        → PreservesEdges (ForestStack.ts (dff-step vs ts stack))
dff-step-TreeEdge⇒Edge (_ ∷ vs) ts [] preserves-ts = preserves-ts
dff-step-TreeEdge⇒Edge vs ts ((v , ext) ∷ stack) preserves-ts te
  = case del vs v of
    λ { (just vs') → dff-step-TreeEdge⇒Edge vs ts stack preserves-ts {!   !}
      ; nothing    → {!   !}
      }

dff-rec-TreeEdge⇒Edge : {n : ℕ}
                        → (fstack : ForestStack n)
                        → PreservesEdges (ForestStack.ts fstack)
                        → PreservesEdges (ForestStack.ts (dff-rec fstack))
dff-rec-TreeEdge⇒Edge {zero}  fstack preserves-ts = preserves-ts
dff-rec-TreeEdge⇒Edge {suc n} (fStack vs ts stack) preserves-ts
  = dff-rec-TreeEdge⇒Edge (dff-step vs ts stack)
    (dff-step-TreeEdge⇒Edge vs ts stack preserves-ts)

dff-TreeEdge⇒Edge : ∀ {vs} → PreservesEdges (dff vs)
dff-TreeEdge⇒Edge {vs}
  = dff-rec-TreeEdge⇒Edge
    (fStack (fromList vs) [] (map (λ v → v , branch) vs))
    λ { () }

-- edge classification

dff-edge-classify : (vs : List V) → {u v : V} → E u v
              → (u∈dff : u ∈F dff vs)
              → (v∈dff : v ∈F dff vs)
              → v∈dff ≼F u∈dff ⊎ descF v∈dff u∈dff
dff-edge-classify vs e u∈dff v∈dff = {!   !}