open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; concat; map; reverse)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈Vec_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (¬_)

module Algorithm.TopoSort
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

record Tree (A : Set) : Set where
  inductive
  constructor node
  field
    value : A
    children : List (Tree A)

Forest : (A : Set) → Set
Forest A = List (Tree A)

-- postorder traversal
mutual

  postorder : ∀ {A} → Tree A → List A
  postorder (node v ts) = concat (postorderList ts)
  
  postorderList : ∀ {A} → Forest A → List (List A)
  postorderList []       = []
  postorderList (t ∷ ts) = postorder t ∷ postorderList ts

data StackElem (src : V) : Set where
  push : Σ[ v ∈ V ] Path src v → StackElem src
  pop  : Σ[ v ∈ V ] Path src v → StackElem src

mutual 

  postorderDFS : {n : ℕ} {src : V} → (ord : Vec V n) 
               → (stack : List (StackElem src)) → Visited src
  postorderDFS []          stack = []
  postorderDFS ord@(_ ∷ _) stack = postorderDFSUtil ord stack

  postorderDFSUtil : {n : ℕ} {src : V} → (ord : Vec V (suc n))
                   → (stack : List (StackElem src)) → Visited src
  postorderDFSUtil _   []       = []
  postorderDFSUtil ord (push p ∷ ps) with del ord (proj₁ p)
  ... | just ord' = postorderDFS ord' (map push (extendPath (proj₂ p)) ++ pop p ∷ ps)
  ... | nothing   = postorderDFSUtil ord ps
  postorderDFSUtil ord (pop p ∷ ps) = p ∷ postorderDFSUtil ord ps

topoSort : {n : ℕ} → (src : V) → (ord : Vec V n) → List V
topoSort src ord = reverse (map proj₁ (postorderDFS ord (push (src , []) ∷ [])))

------------------------------------------------------------------------
-- correctness of topological sort on acyclic graphs

-- notion of a path belonging to a given subset of vertices
data _⊆P_ : ∀ {u v} {n} → (p : Path u v) → (ord : Vec V n) → Set where
  empty  : ∀ {u} {n} {ord : Vec V n} → u ∈Vec ord → ([] {u}) ⊆P ord
  cons   : ∀ {u v w} {n} → {e : E v w} → {ord : Vec V (suc n)} 
           → {p : Path u v} → p ⊆P ord → (p ▷ e) ⊆P ord

Acyclic : ∀ {n} → (ord : Vec V n) → Set
Acyclic ord = ∀ {v} → (p : Path v v) → p ⊆P ord → p ≡ []

-- notion of strict precedence of elements in a list
data _≺_ {A : Set} : {x y : A} {xs : List A} → x ∈ xs → y ∈ xs → Set where
  base : ∀ {x y xs} {p : y ∈ xs} → here {x = x} refl ≺ there p
  step : ∀ {x y xs} {p : x ∈ xs} {q : y ∈ xs}
         → p ≺ q → (there {x = x} p) ≺ (there q)

mutual

  postorderDFS-topo : ∀ {n} {x y : V} → (src : V) → (ord : Vec V n) 
                      → (stack : List (StackElem src)) → Acyclic ord 
                      → (x∈post : x ∈ map proj₁ (postorderDFS ord stack))
                      → (y∈post : y ∈ map proj₁ (postorderDFS ord stack))
                      → Σ[ p ∈ Path x y ] p ⊆P ord → y∈post ≺ x∈post
  postorderDFS-topo src ord stack acyclic x∈post y∈post (p , p⊆ord) = {!   !}

topoSort-correct : ∀ {n} → (src : V) → (ord : Vec V n) → Acyclic ord → {x y : V}
                   → {x∈top : x ∈ topoSort src ord} → {y∈top : y ∈ topoSort src ord}
                   → x∈top ≺ y∈top → ¬ (Σ[ p ∈ Path y x ] p ⊆P ord)
topoSort-correct src ord acyclic x≺y = {!   !}