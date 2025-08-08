open import Function
open import Data.Nat
open import Data.Product using (Σ; proj₁; proj₂; Σ-syntax)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈Vec_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Binary.PropositionalEquality

module Algorithm.DFS
  (V : Set) (Edges : V → List V) where

------------------------------------------------------------------------
-- Definitions

data E : V → V → Set where
  edge : ∀ {u v} → v ∈ Edges u → E u v

data Path : V → V → Set where
  []   : ∀ {v}                        → Path v v
  _▷_ : ∀ {u v w} → Path u v → E v w → Path u w

Visited : V → Set
Visited src = List (Σ[ v ∈ V ] Path src v)

del : ∀ {n} → Vec V (suc n) → V → Maybe (Vec V n)
del = {!   !}

extendPath : ∀ {u v} → Path u v → Visited u
extendPath p = {!   !}

mutual

  dfs : {n : ℕ} → (src : V) → (ord : Vec V n) 
      → (stack : Visited src) → Visited src
  dfs src []          stack = []
  dfs src ord@(_ ∷ _) stack = dfsUtil src ord stack

  dfsUtil : {n : ℕ} → (src : V) → (ord : Vec V (suc n)) 
          → (stack : Visited src) → Visited src
  dfsUtil _   _   []       = []
  dfsUtil src ord (p ∷ ps) with del ord (proj₁ p)
  ... | just ord' = p ∷ (dfs src ord' (extendPath (proj₂ p) ++ ps))
  ... | nothing   = dfsUtil src ord ps

------------------------------------------------------------------------
-- Lexicographic ordering

-- ordering for list membership proofs
data _≺_ {A : Set} : {x y : A} {xs : List A} → x ∈ xs → y ∈ xs → Set where
  first : ∀ {x y xs} {p : y ∈ xs} → here {x = x} refl ≺ there p
  cons  : ∀ {x y xs} {p : x ∈ xs} {q : y ∈ xs}
          → p ≺ q → (there {x = x} p) ≺ (there q)

-- edge ordering based on their position in the Edges list
data _<E_ : ∀ {u v w} → E u v → E u w → Set where
  order : ∀ {u v w} {e₁ : v ∈ Edges u} {e₂ : w ∈ Edges u} 
          → e₁ ≺ e₂ → edge e₁ <E edge e₂

data _⊏_ : ∀ {u v w} → Path u v → Path u w → Set where
  base : ∀ {u v w} → {p : Path u v}
         → (e : E v w) → p ⊏ (p ▷ e)
  ext  : ∀ {u v w x} → {p : Path u v} → {q : Path u w}
         → (p ⊏ q) → (e : E w x) → p ⊏ (q ▷ e)

-- strong lexicographic ordering on paths
-- intuitively, p <SP q means that all extensions of p
-- are lexicographically less than q
data _<SP_ : ∀ {u v w} → Path u v → Path u w → Set where
  base  : ∀ {u v w x} → {p : Path u v} → (e : E v w) 
          → (f : E v x) → e <E f → (p ▷ e) <SP (p ▷ f)
  stepₗ : ∀ {u v w x} → {p : Path u v} → {q : Path u w} 
          → (p <SP q) → (e : E v x) → (p ▷ e) <SP q
  stepᵣ : ∀ {u v w x} → {p : Path u v} → {q : Path u w} 
          → (p <SP q) → (e : E w x) → p <SP (q ▷ e)

-- lexicographic ordering on paths
data _<P_ : ∀ {u v w} → Path u v → Path u w → Set where
  pref  : ∀ {u v w} → {p : Path u v} → {q : Path u w}
          → p ⊏ q → p <P q
  comp  : ∀ {u v w} → {p : Path u v} → {q : Path u w}
          → p <SP q → p <P q

data _≤P_ : ∀ {u v w} → Path u v → Path u w → Set where
  refl  : ∀ {u v} → {p : Path u v} → p ≤P p
  lt    : ∀ {u v w} → {p : Path u v} → {q : Path u w} 
          → p <P q → p ≤P q

≺-trans : ∀ {A : Set} {x y z : A} {xs : List A}
          → {p : x ∈ xs} → {q : y ∈ xs} → {r : z ∈ xs}
          → p ≺ q → q ≺ r → p ≺ r
≺-trans first      (cons q≺r) = first
≺-trans (cons p≺q) (cons q≺r) = cons (≺-trans p≺q q≺r)

<E-trans : ∀ {u v w x} → {e : E u v} → {f : E u w} 
           → {g : E u x} → e <E f → f <E g → e <E g
<E-trans (order p≺q) (order q≺r) = order (≺-trans p≺q q≺r)

⊏-trans : ∀ {u v w x} → {p : Path u v} → {q : Path u w} 
          → {r : Path u x} → p ⊏ q → q ⊏ r → p ⊏ r
⊏-trans p⊏q (base e)    = ext p⊏q e
⊏-trans p⊏q (ext q⊏r e) = ext (⊏-trans p⊏q q⊏r) e

<SP-trans : ∀ {u v w x} → {p : Path u v} → {q : Path u w} 
            → {r : Path u x} → p <SP q → q <SP r → p <SP r
<SP-trans (base e f e<f) (base .f g f<g) = base e g (<E-trans e<f f<g)
<SP-trans (base e f e<f) (stepₗ q<r .f)  = stepₗ q<r e
<SP-trans (stepᵣ p<q e)  (base f g f<g)  = stepᵣ p<q g
<SP-trans (stepᵣ p<q e)  (stepₗ q<r f)   = <SP-trans p<q q<r
<SP-trans p<q            (stepᵣ q<r g)   = stepᵣ (<SP-trans p<q q<r) g
<SP-trans (stepₗ p<q e)  q<r             = stepₗ (<SP-trans p<q q<r) e

comp-pref⇒comp : ∀ {u v w x} → {p : Path u v} → {q : Path u w}
                  → {r : Path u x} → p <SP q → q ⊏ r → p <SP r
comp-pref⇒comp p<q (base e)    = stepᵣ p<q e
comp-pref⇒comp p<q (ext q⊏r e) = stepᵣ (comp-pref⇒comp p<q q⊏r) e

<P-ext : ∀ {u v w x} → {p : Path u v} → {q : Path u w}
         → p <P q → (e : E w x) → p <P (q ▷ e)
<P-ext (pref p⊏q) e = pref (ext p⊏q e)
<P-ext (comp p<q) e = comp (stepᵣ p<q e)

<P-trans : ∀ {u v w x} → {p : Path u v} → {q : Path u w} 
           → {r : Path u x} → p <P q → q <P r → p <P r
<P-trans (pref p⊏q) (pref q⊏r) = pref (⊏-trans p⊏q q⊏r)
<P-trans (pref (base e))    (comp (base .e f e<f)) = pref (base f)
<P-trans (pref (base e))    (comp (stepₗ q<r .e))  = comp q<r
<P-trans (pref p⊏q)         (comp (stepᵣ q<r f))   = <P-ext (<P-trans (pref p⊏q) (comp q<r)) f
<P-trans (pref (ext p⊏q e)) (comp (base .e f e<f)) = pref (ext p⊏q f)
<P-trans (pref (ext p⊏q e)) (comp (stepₗ q<r .e))  = <P-trans (pref p⊏q) (comp q<r)
<P-trans (comp p<q) (pref q⊏r) = comp (comp-pref⇒comp p<q q⊏r)
<P-trans (comp p<q) (comp q<r) = comp (<SP-trans p<q q<r)

------------------------------------------------------------------------
-- TODO : existence of a "smallest" path among paths between 
--        two vertices

-- TODO : define existence of a path with restriction to a subset
--        of vertices, e.g. a path from u to v that only uses vertices
--        in a given set S ⊆ V

------------------------------------------------------------------------
-- paths output by DFS are lexicographically ordered

-- ascendingly sorted by strict lexicographic order
data SortedByLex : ∀ {u} → Visited u → Set where
  empty     : ∀ {u} → SortedByLex {u} []
  singleton : ∀ {u} {p : Σ[ v ∈ V ] Path u v} → SortedByLex (p ∷ [])
  cons      : ∀ {u} {p q : Σ[ v ∈ V ] Path u v} {ps : Visited u}
              → SortedByLex (p ∷ ps) → ((proj₂ q) <P (proj₂ p))
              → SortedByLex (q ∷ p ∷ ps)

-- ascendingly sorted by strong lexicographic order
data StronglySortedByLex : ∀ {u} → Visited u → Set where
  empty     : ∀ {u} → StronglySortedByLex {u} []
  singleton : ∀ {u} {p : Σ[ v ∈ V ] Path u v} → StronglySortedByLex (p ∷ [])
  cons      : ∀ {u} {p q : Σ[ v ∈ V ] Path u v} {ps : Visited u}
              → StronglySortedByLex (p ∷ ps) → ((proj₂ q) <SP (proj₂ p))
              → StronglySortedByLex (q ∷ p ∷ ps)

StronglySorted⇒Sorted : ∀ {u} → {ps : Visited u} → StronglySortedByLex ps 
                         → SortedByLex ps
StronglySorted⇒Sorted empty             = empty
StronglySorted⇒Sorted singleton         = singleton
StronglySorted⇒Sorted (cons sorted p<q) = cons (StronglySorted⇒Sorted sorted) (comp p<q)

tail-sorted : ∀ {u} → {p : Σ[ v ∈ V ] Path u v} {ps : Visited u}
              → StronglySortedByLex (p ∷ ps) → StronglySortedByLex ps
tail-sorted (singleton {u}) = empty
tail-sorted (cons sorted p<q) = sorted

extendPath-sorted : ∀ {u} → {p : Σ[ v ∈ V ] Path u v} {ps : Visited u}
    → StronglySortedByLex (p ∷ ps) → StronglySortedByLex (extendPath (proj₂ p) ++ ps)
extendPath-sorted sorted = {!   !}

sorted-drop2 : ∀ {u} → {p q : Σ[ v ∈ V ] Path u v} {qs : Visited u}
               → SortedByLex (p ∷ q ∷ qs) → SortedByLex (p ∷ qs)
sorted-drop2 (cons singleton          p<q) = singleton
sorted-drop2 (cons (cons sorted q<q') p<q) = cons sorted (<P-trans p<q q<q')

-- p LB ps means that p is a lower-bound for ps 
-- (assuming that ps is sorted)
data _LB_ : ∀ {u} → (p : Σ[ v ∈ V ] Path u v) → Visited u → Set where
  empty : ∀ {u} {p : Σ[ v ∈ V ] Path u v} → p LB []
  cons  : ∀ {u} {p q : Σ[ v ∈ V ] Path u v} {qs : Visited u}
          → (proj₂ p) <P (proj₂ q) → p LB (q ∷ qs)

LB⇒sorted : ∀ {u} → {p : Σ[ v ∈ V ] Path u v} {ps : Visited u}
             → p LB ps → SortedByLex ps → SortedByLex (p ∷ ps)
LB⇒sorted empty      _      = singleton
LB⇒sorted (cons p<q) sorted = cons sorted p<q

sorted⇒LB : ∀ {u} → {p : Σ[ v ∈ V ] Path u v} {ps : Visited u}
             → SortedByLex (p ∷ ps) → p LB ps
sorted⇒LB singleton         = empty
sorted⇒LB (cons sorted p<q) = cons p<q

extendPath-LB : ∀ {u} → {p : Σ[ v ∈ V ] Path u v} → p LB extendPath (proj₂ p)
extendPath-LB = {!   !}

LB-++ : ∀ {u} → {p : Σ[ v ∈ V ] Path u v} {ps qs : Visited u}
        → p LB ps → p LB qs → p LB (ps ++ qs)
LB-++ empty      lb    = lb
LB-++ (cons p<q) _     = cons p<q

-- the output will be lexicographically larger than the input stack
mutual

  dfs-increasing : ∀ {n} → (src : V) → (ord : Vec V n) 
                   → (ps : Visited src) → (p : Σ[ v ∈ V ] Path src v)
                   → SortedByLex (p ∷ ps)
                   → p LB (dfs src ord ps)
  dfs-increasing src []          ps p sorted = empty
  dfs-increasing src ord@(_ ∷ _) ps p sorted = dfsUtil-increasing src ord ps p sorted

  dfsUtil-increasing : ∀ {n} → (src : V) → (ord : Vec V (suc n)) 
                      → (ps : Visited src) → (p : Σ[ v ∈ V ] Path src v)
                      → SortedByLex (p ∷ ps)
                      → p LB (dfsUtil src ord ps)
  dfsUtil-increasing _   _   []       p _  = empty
  dfsUtil-increasing src ord (q ∷ qs) p sorted@(cons _ p<q) with del ord (proj₁ q)
  ... | just ord' = cons p<q
  ... | nothing   = dfsUtil-increasing src ord qs p (sorted-drop2 sorted)


-- if initial stack is strongly sorted, then the output of dfs will
-- be sorted by lexicographic order
mutual

  dfs-sorted : ∀ {n} → (src : V) → (ord : Vec V n) 
              → (stack : Visited src)
              → StronglySortedByLex stack
              → SortedByLex (dfs src ord stack)
  dfs-sorted src []          stack sorted = empty
  dfs-sorted src ord@(_ ∷ _) stack sorted = dfsUtil-sorted src ord stack sorted

  dfsUtil-sorted : ∀ {n} → (src : V) → (ord : Vec V (suc n))
                  → (stack : Visited src)
                  → StronglySortedByLex stack
                  → SortedByLex (dfsUtil src ord stack)
  dfsUtil-sorted src ord []       sorted = empty
  dfsUtil-sorted src ord (p ∷ ps) sorted with del ord (proj₁ p)
  ... | just ord' = LB⇒sorted 
                    (dfs-increasing src ord' (extendPath (proj₂ p) ++ ps) 
                      p (LB⇒sorted (LB-++ extendPath-LB 
                          (sorted⇒LB (StronglySorted⇒Sorted sorted)))
                        (StronglySorted⇒Sorted (extendPath-sorted sorted))))
                    (dfs-sorted src ord' (extendPath (proj₂ p) ++ ps) 
                      (extendPath-sorted sorted))
  ... | nothing   = dfsUtil-sorted src ord ps (tail-sorted sorted)

-- paths output by DFS are lexicographically minimal
-- (among those with vertices in the order given)
