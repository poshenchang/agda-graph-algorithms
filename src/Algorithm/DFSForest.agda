open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Vec using (Vec; []; _∷_; toList; fromList)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈Vec_)
open import Data.Vec.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Data.Tree
open import Data.Tree.Properties
open import Data.Tree.Operations

module Algorithm.DFSForest
  (V : Set) (Edges : V → List V) where

open import Data.Graph V Edges

------------------------------------------------------------------------
-- Delete function and properties

del : ∀ {n} → Vec V (suc n) → V → Maybe (Vec V n)
del = {!   !}

del-preserve : ∀ {u n} (v : V) (vs : Vec V (suc n)) {vs'}
               → u ∈Vec vs → del vs v ≡ just vs'
               → u ≡ v ⊎ u ∈Vec vs'
del-preserve v vs u∈vs eq = {!   !}

del-exist : ∀ {n} (v : V) (vs : Vec V (suc n)) {vs'}
            → del vs v ≡ just vs' → v ∈Vec vs
del-exist v vs eq = {!   !}

del-inclusion : ∀ {u n} (v : V) (vs : Vec V (suc n)) {vs'}
                → del vs v ≡ just vs'
                → u ∈Vec vs' → u ∈Vec vs
del-inclusion v vs eq u∈vs' = {!   !}

------------------------------------------------------------------------
-- Definitions

-- tree extension

TreeExt : (t : Tree V) → (v : V) → Set
TreeExt t v = ∃[ u ] (u ∈T t) × (E u v)

-- forest extension

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
ForestExt-∈ _ branch = branch
ForestExt-∈ (leaf (w , w∈ts , e)) (leaf (w' , w'∈ts , e'))
  = leaf (w' , insertF-preserves∈ w'∈ts , e')
ForestExt-∈ branch (leaf (w , w∈ts , e)) = leaf (w , helper w∈ts , e)
  where helper : ∀ {v : V} {t ts} → v ∈F ts → v ∈F (ts ∷ʳ t)
        helper (here  v∈t') = here v∈t'
        helper (there v∈ts) = there (helper v∈ts)

forest-ext-retrace : ∀ {u v ts} → (ext : ForestExt ts v)
                     → u ∈F forest-ext ts v ext
                     → u ≡ v ⊎ u ∈F ts
forest-ext-retrace (leaf x) u∈forest-ext = insertF-retrace _ u∈forest-ext
forest-ext-retrace {ts = []}     branch (here root)  = inj₁ refl
forest-ext-retrace {ts = t ∷ ts} branch (here u∈t)   = inj₂ (here u∈t)
forest-ext-retrace {ts = t ∷ ts} branch (there u∈ts) with forest-ext-retrace branch u∈ts
... | inj₁ refl = inj₁ refl
... | inj₂ p    = inj₂ (there p)

map-∈ : ∀ {A : Set} → (xs : List A) → List (∃[ x ] x ∈ xs)
map-∈ []       = []
map-∈ (x ∷ xs) = (x , here refl) ∷ map (λ { (y , y∈xs) → (y , there y∈xs) }) (map-∈ xs)

edges-ext : ∀ {ts} (v : V)
          → v ∈F ts
          → List (∃[ u ] ForestExt ts u)
edges-ext v v∈ts = map (λ { (u , u∈E) → u , leaf (v , v∈ts , edge u∈E) }) (map-∈ (Edges v))

-- depth first forest implementation

dff-step : {n : ℕ}
          → Vec V (suc n) → (ts : Forest V)
          → List (∃[ v ] ForestExt ts v)
          → ForestStack n
dff-step vs ts ((v , ext) ∷ stack) with del vs v
... | just vs' = fStack vs' (forest-ext ts v ext)
                   (edges-ext v (∈-forest-ext ts v ext) 
                   ++ map (λ { (u , ext') → u , ForestExt-∈ ext ext' }) stack)
... | nothing  = dff-step vs ts stack
dff-step (v ∷ vs) ts [] = fStack vs (ts ∷ʳ node v []) []

dff-rec : {n : ℕ}
        → ForestStack n
        → ForestStack 0
dff-rec {zero}  fstack               = fstack
dff-rec {suc n} (fStack vs ts stack) = dff-rec (dff-step vs ts stack)

init-ext : V → ∃[ v ] ForestExt [] v
init-ext v = (v , branch)

dff : (vs : List V) → Forest V
dff vs = ForestStack.ts
         (dff-rec (fStack (fromList vs) [] 
                    (map init-ext vs)))

------------------------------------------------------------------------
-- Auxiliary functions

∈F-∷ʳ : ∀ {A} {u : A} {t ts} → u ∈F ts → u ∈F (ts ∷ʳ t)
∈F-∷ʳ {ts = t' ∷ ts} (here  u∈t') = here u∈t'
∈F-∷ʳ {ts = t' ∷ ts} (there u∈ts) = there (∈F-∷ʳ u∈ts)

∈⇒∈fromList : ∀ {A : Set} {v : A} {vs}
             → v ∈ vs → v ∈Vec fromList vs
∈⇒∈fromList {vs = x ∷ vs} (here  refl) = here refl
∈⇒∈fromList {vs = x ∷ vs} (there v∈vs) = there (∈⇒∈fromList v∈vs)

∈fromList⇒∈ : ∀ {A : Set} {v : A} {vs}
             → v ∈Vec fromList vs → v ∈ vs
∈fromList⇒∈ {vs = x ∷ vs} (here  refl) = here refl
∈fromList⇒∈ {vs = x ∷ vs} (there v∈vs) = there (∈fromList⇒∈ v∈vs)

------------------------------------------------------------------------
-- Depth-First-Forest Properties (dff)

case_of_ : ∀ {A B : Set} → (x : A) → (f : A → B) → B
case x of f = f x

open import Algorithm.TopoSort V Edges

-- uniqueness

dff-uniqueness : ∀ {vs} → Unique vs → Unique (postorderF (dff vs))
dff-uniqueness {vs} unique-vs = {!   !}

-- completeness

forest-ext-preserve-ts : {ts : Forest V} {v : V}
                       → (ext : ForestExt ts v)
                       → ∀ {u} → u ∈F ts
                       → u ∈F forest-ext ts v ext
forest-ext-preserve-ts (leaf (v , v∈ts , e)) u∈ts = insertF-preserves∈ u∈ts
forest-ext-preserve-ts branch                u∈ts = ∈F-∷ʳ u∈ts

dff-step-preserve-ts : {n : ℕ}
                     → (vs : Vec V (suc n)) → (ts : Forest V)
                     → (stack : List (∃[ v ] ForestExt ts v))
                     → ∀ {v} → v ∈F ts
                     → v ∈F ForestStack.ts (dff-step vs ts stack)
dff-step-preserve-ts vs ts ((v , ext) ∷ stack) v∈ts with del vs v
... | just vs' = forest-ext-preserve-ts ext v∈ts
... | nothing  = dff-step-preserve-ts vs ts stack v∈ts
dff-step-preserve-ts (v ∷ vs) ts [] v∈ts = ∈F-∷ʳ v∈ts

dff-step-completeness : {n : ℕ}
                      → (vs : Vec V (suc n)) → (ts : Forest V)
                      → (stack : List (∃[ v ] ForestExt ts v))
                      → ∀ {v} → v ∈Vec vs
                      → v ∈Vec ForestStack.vs (dff-step vs ts stack)
                        ⊎ v ∈F ForestStack.ts (dff-step vs ts stack)
dff-step-completeness vs ts ((v , ext) ∷ stack) v∈vs with del vs v in eq
... | just vs' with del-preserve v vs v∈vs eq
...   | inj₁ refl = inj₂ (∈-forest-ext ts v ext)
...   | inj₂ p    = inj₁ p
dff-step-completeness vs ts ((v , ext) ∷ stack) v∈vs | nothing  = dff-step-completeness vs ts stack v∈vs
dff-step-completeness (v ∷ vs) ts [] (here  refl) = inj₂ (helper root)
  where helper : ∀ {A} {v : A} {t ts} → v ∈T t → v ∈F (ts ∷ʳ t)
        helper {ts = []}     v∈t = here v∈t
        helper {ts = x ∷ ts} v∈t = there (helper v∈t)
dff-step-completeness (v ∷ vs) ts [] (there v∈vs) = inj₁ v∈vs

dff-rec-preserve-ts : {n : ℕ}
                    → (fstack : ForestStack n)
                    → ∀ {v} → v ∈F ForestStack.ts fstack
                    → v ∈F ForestStack.ts (dff-rec fstack)
dff-rec-preserve-ts {zero}  fstack v∈ts = v∈ts
dff-rec-preserve-ts {suc n} (fStack vs ts stack) v∈ts
  = dff-rec-preserve-ts (dff-step vs ts stack)
    (dff-step-preserve-ts vs ts stack v∈ts)

dff-rec-completeness : {n : ℕ}
                     → (fstack : ForestStack n)
                     → ∀ {v} → v ∈Vec ForestStack.vs fstack
                     → v ∈F ForestStack.ts (dff-rec fstack)
dff-rec-completeness {suc n} (fStack vs ts stack) v∈vs with dff-step-completeness vs ts stack v∈vs
... | inj₁ v∈vs' = dff-rec-completeness (dff-step vs ts stack) v∈vs'
... | inj₂ v∈ts' = dff-rec-preserve-ts (dff-step vs ts stack) v∈ts'

dff-completeness : ∀ {v vs} → v ∈ vs → v ∈F dff vs
dff-completeness {vs = vs} v∈vs
  = dff-rec-completeness
    (fStack (fromList vs) [] (map (λ v → v , branch) vs))
    (∈⇒∈fromList v∈vs)

--soundness

dff-step-preserve-vs : {n : ℕ}
                     → (vs : Vec V (suc n)) → (ts : Forest V)
                     → (stack : List (∃[ v ] ForestExt ts v))
                     → ∀ {v} → v ∈Vec ForestStack.vs (dff-step vs ts stack)
                     → v ∈Vec vs
dff-step-preserve-vs vs ts ((v , ext) ∷ stack) v∈dff-step with del vs v in eq
... | just vs' = del-inclusion v vs eq v∈dff-step 
... | nothing  = dff-step-preserve-vs vs ts stack v∈dff-step
dff-step-preserve-vs (v ∷ vs) ts [] v∈dff-step = there v∈dff-step

dff-step-soundness : {n : ℕ}
                   → (vs : Vec V (suc n)) → (ts : Forest V)
                   → (stack : List (∃[ v ] ForestExt ts v))
                   → ∀ {v} → v ∈F ForestStack.ts (dff-step vs ts stack)
                   → v ∈Vec vs ⊎ v ∈F ts
dff-step-soundness vs ts ((v , ext) ∷ stack) v∈dff-step with del vs v in eq
... | nothing  = dff-step-soundness vs ts stack v∈dff-step
... | just vs' with forest-ext-retrace ext v∈dff-step
...   | inj₁ p    = inj₁ (subst (_∈Vec vs) (sym p) (del-exist v vs eq))
...   | inj₂ u∈ts = inj₂ u∈ts
dff-step-soundness (v ∷ vs) ts [] v∈dff-step with ∈F-head v∈dff-step
... | inj₁ p    = inj₂ p
... | inj₂ root = inj₁ (here refl)

dff-rec-soundness : {n : ℕ}
                  → (fstack : ForestStack n)
                  → ∀ {v} → v ∈F ForestStack.ts (dff-rec fstack)
                  → v ∈Vec ForestStack.vs fstack
                    ⊎ v ∈F ForestStack.ts fstack
dff-rec-soundness {zero}  fstack               v∈dff-rec = inj₂ v∈dff-rec
dff-rec-soundness {suc n} (fStack vs ts stack) v∈dff-rec
  with dff-rec-soundness (dff-step vs ts stack) v∈dff-rec
... | inj₁ v∈vs = inj₁ (dff-step-preserve-vs vs ts stack v∈vs)
... | inj₂ v∈ts = dff-step-soundness vs ts stack v∈ts

dff-soundness : ∀ {v vs} → v ∈F dff vs → v ∈ vs
dff-soundness {v} {vs} v∈dff with dff-rec-soundness
                             (fStack (fromList vs) [] (map init-ext vs))
                             v∈dff
... | inj₁ v∈vs = ∈fromList⇒∈ v∈vs
... | inj₂ ()

-- edge preserving

PreservesEdges : Tree V → Set
PreservesEdges t = ∀ {u v} → TreeEdge t u v → E u v

PreservesEdgesF : Forest V → Set
PreservesEdgesF ts = ∀ {u v} → TreeEdgeF ts u v → E u v

mutual

  insertT-preserve-edges : ∀ {t} → PreservesEdges t
                         → ∀ {u v} → (u∈t : u ∈T t) → E u v
                         → PreservesEdges (insertT t u∈t v)
  insertT-preserve-edges {t = node u []} f root e (sub (root ()) (here refl))
  insertT-preserve-edges {t = node u []} f root e (sub (sub te ()) (here refl))
  insertT-preserve-edges {t = node u (t ∷ ts)} f root e (sub te (here refl)) = f (sub te (here refl))
  insertT-preserve-edges {t = node u (t ∷ ts)} f root e (sub te (there x))
    = insertT-preserve-edges
      (λ { (root x)   → f (root (there x))
         ; (sub te x) → f (sub te (there x)) }) root e (sub te x)
  insertT-preserve-edges {t = node u []}       f root e (root (here refl)) = e
  insertT-preserve-edges {t = node u (t ∷ ts)} f root e (root (here refl)) = f (root (here refl))
  insertT-preserve-edges {t = node u (t ∷ ts)} f root e (root (there x))
    = insertT-preserve-edges
      (λ { (root x)   → f (root (there x))
         ; (sub te x) → f (sub te (there x)) }) root e (root x)
  insertT-preserve-edges f (sub u∈ts) e (sub te x)
    = insertF-preserve-edges
      (λ { (t , t∈ts , te) → f (sub te t∈ts) }) u∈ts e (_ , x , te)
  insertT-preserve-edges f (sub (here  root))    e (root (here refl)) = f (root (here refl))
  insertT-preserve-edges f (sub (here  (sub x))) e (root (here refl)) = f (root (here refl))
  insertT-preserve-edges f (sub (here  u∈t))     e (root (there x))   = f (root (there x))
  insertT-preserve-edges f (sub (there u∈ts))    e (root (here refl)) = f (root (here refl))
  insertT-preserve-edges f (sub (there u∈ts))    e (root (there x))
    = insertT-preserve-edges
      (λ { (root x)   → f (root (there x))
         ; (sub te x) → f (sub te (there x)) }) (sub u∈ts) e (root x)

  insertF-preserve-edges : ∀ {ts} → PreservesEdgesF ts
                         → ∀ {u v} → (u∈ts : u ∈F ts) → E u v
                         → PreservesEdgesF (insertF ts u∈ts v)
  insertF-preserve-edges f (here  u∈t)  e (t , here  refl , te)
    = insertT-preserve-edges
      (λ te → f (_ , here refl , te)) u∈t e te
  insertF-preserve-edges f (here  u∈t)  e (t , there t∈ts , te) = f (t , there t∈ts , te)
  insertF-preserve-edges f (there u∈ts) e (t , here  refl , te) = f (t , here  refl , te)
  insertF-preserve-edges f (there u∈ts) e (t , there t∈ts , te)
    = insertF-preserve-edges
      (λ { (t , t∈ts , te) → f (t , there t∈ts , te) }) u∈ts e (t , t∈ts , te)

forest-ext-preserve-edges : ∀ {v ts} ext
                          → PreservesEdgesF ts
                          → PreservesEdgesF (forest-ext ts v ext)
forest-ext-preserve-edges (leaf (t , t∈ts , e)) f = insertF-preserve-edges f t∈ts e
forest-ext-preserve-edges {ts = []}      branch f (.(node _ []) , here refl , root ())
forest-ext-preserve-edges {ts = []}      branch f (.(node _ []) , here refl , sub e ())
forest-ext-preserve-edges {ts = t ∷ ts}  branch f (.t , here refl , e) = f (t , here refl , e)
forest-ext-preserve-edges {ts = t' ∷ ts} branch f (t , there t∈ts , e)
  = forest-ext-preserve-edges branch
    (λ { (t , t∈ts , e) → f (t , there t∈ts , e) }) (t , t∈ts , e)

dff-step-TreeEdge⇒Edge : {n : ℕ}
                        → (vs : Vec V (suc n)) → (ts : Forest V)
                        → (stack : List (∃[ v ] ForestExt ts v))
                        → PreservesEdgesF ts
                        → PreservesEdgesF (ForestStack.ts (dff-step vs ts stack))
dff-step-TreeEdge⇒Edge vs ts ((v , ext) ∷ stack) preserves-ts with del vs v
... | just vs' = forest-ext-preserve-edges ext preserves-ts
... | nothing  = dff-step-TreeEdge⇒Edge vs ts stack preserves-ts
dff-step-TreeEdge⇒Edge (_ ∷ vs) ts [] preserves-ts = helper preserves-ts
  where helper : ∀ {u ts} → PreservesEdgesF ts → PreservesEdgesF (ts ∷ʳ node u [])
        helper {ts = []} f (.(node _ []) , here refl , root ())
        helper {ts = []} f (.(node _ []) , here refl , sub e ())
        helper {ts = t  ∷ ts} f (.t , here refl , e) = f (t , here refl , e)
        helper {ts = t' ∷ ts} f (t , there t∈ts , e)
          = helper (λ { (t , t∈ts , e) → f (t , there t∈ts , e) }) (t , t∈ts , e)

dff-rec-TreeEdge⇒Edge : {n : ℕ}
                        → (fstack : ForestStack n)
                        → PreservesEdgesF (ForestStack.ts fstack)
                        → PreservesEdgesF (ForestStack.ts (dff-rec fstack))
dff-rec-TreeEdge⇒Edge {zero}  fstack preserves-ts = preserves-ts
dff-rec-TreeEdge⇒Edge {suc n} (fStack vs ts stack) preserves-ts
  = dff-rec-TreeEdge⇒Edge (dff-step vs ts stack)
    (dff-step-TreeEdge⇒Edge vs ts stack preserves-ts)

dff-TreeEdge⇒Edge : ∀ {vs} → PreservesEdgesF (dff vs)
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
