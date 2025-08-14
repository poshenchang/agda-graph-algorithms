open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; _∷ʳ_; concat; map; reverse)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Relation.Unary.AllPairs.Core
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; _≢_)
open import Relation.Nullary using (¬_)
open import Function.Base

module Algorithm.TopoSort
  (V : Set) (Edges : V → List V) where

------------------------------------------------------------------------
-- Definitions

data E : V → V → Set where
  edge : ∀ {u v} → v ∈ Edges u → E u v

data Path : V → V → Set where
  []   : ∀ {v}                        → Path v v
  _▷_ : ∀ {u v w} → Path u v → E v w → Path u w

record Tree (A : Set) : Set where
  inductive
  constructor node
  field
    label : A
    children : List (Tree A)

Forest : (A : Set) → Set
Forest A = List (Tree A)

-- preorder traversal
mutual

  preorder : ∀ {A} → Tree A → List A
  preorder (node v ts) = v ∷ preorderF ts

  preorderF : ∀ {A} → Forest A → List A
  preorderF []       = []
  preorderF (t ∷ ts) = preorder t ++ preorderF ts

-- postorder traversal
mutual

  postorder : ∀ {A} → Tree A → List A
  postorder (node v ts) = postorderF ts ∷ʳ v

  postorderF : ∀ {A} → Forest A → List A
  postorderF []       = []
  postorderF (t ∷ ts) = postorder t ++ postorderF ts

Traversal : Set
Traversal = List V → Forest V

------------------------------------------------------------------------
-- ordering relations on lists

-- notion of a path belonging to a given subset of vertices
data _⊆P_ : ∀ {u v} → (p : Path u v) → (vs : List V) → Set where
  empty  : ∀ {u} {vs : List V} → u ∈ vs → ([] {u}) ⊆P vs
  cons   : ∀ {u v w} → {e : E v w} → {vs : List V} 
           → {p : Path u v} → p ⊆P vs → (p ▷ e) ⊆P vs

Acyclic : (vs : List V) → Set
Acyclic vs = ∀ {v} → (p : Path v v) → p ⊆P vs → p ≡ []

-- nonstrict precedence of elements in a list
data _≼_ {A : Set} : {x y : A} {xs : List A} → x ∈ xs → y ∈ xs → Set where
  base : ∀ {x y xs} {p : y ∈ x ∷ xs} → here refl ≼ p
  step : ∀ {x y z xs} {p : y ∈ xs} {q : z ∈ xs}
         → p ≼ q → (there {x = x} p) ≼ (there q)

≼-refl : ∀ {A : Set} {x : A} {xs : List A}
         → {x∈xs : x ∈ xs} → x∈xs ≼ x∈xs
≼-refl {x∈xs = here  refl} = base
≼-refl {x∈xs = there x∈xs} = step ≼-refl

_[_≼V_] : ∀ {A : Set} → List A → A → A → Set
xs [ x ≼V y ] = Σ[ x∈xs ∈ (x ∈ xs) ] Σ[ y∈xs ∈ (y ∈ xs) ] (x∈xs ≼ y∈xs)

------------------------------------------------------------------------
-- helper functions for uniqueness

unique-helper : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → All (x ≢_) xs → ⊥
unique-helper (here  refl) (px ∷ all≢x) = px refl
unique-helper (there x∈xs) (px ∷ all≢x) = unique-helper x∈xs all≢x

-- membership in a unique list are propositions (have unique instances)
∈Unique⇒prop : ∀ {A : Set} {x : A} {xs : List A} → Unique xs
              → (x∈xs x∈xs' : x ∈ xs) → x∈xs ≡ x∈xs'
∈Unique⇒prop unique  (here refl)  (here refl)   = refl
∈Unique⇒prop (f ∷ _) (here refl)  (there x∈xs') = ⊥-elim (unique-helper x∈xs' f)
∈Unique⇒prop (f ∷ _) (there x∈xs) (here refl)   = ⊥-elim (unique-helper x∈xs f)
∈Unique⇒prop (_ ∷ unique) (there x∈xs) (there x∈xs')
  = cong there (∈Unique⇒prop unique x∈xs x∈xs')

Unique≼V⇒∀≼ : ∀ {A : Set} {x y : A} {xs : List A}
               → Unique xs → xs [ x ≼V y ]
               → (x∈xs : x ∈ xs) → (y∈xs : y ∈ xs)
               → x∈xs ≼ y∈xs
Unique≼V⇒∀≼ unique (x∈xs' , y∈xs' , x≼y) x∈xs y∈xs
  = subst (_≼ y∈xs) (∈Unique⇒prop unique x∈xs' x∈xs) 
    (subst (x∈xs' ≼_) (∈Unique⇒prop unique y∈xs' y∈xs) x≼y)

------------------------------------------------------------------------
-- helper functions for reverse

reverse-Unique : ∀ {A : Set} {xs : List A} → Unique xs
                 → Unique (reverse xs)
reverse-Unique unique = {!   !}

∈reverse⇒∈ : ∀ {A : Set} {xs : List A} {x : A}
            → x ∈ reverse xs → x ∈ xs
∈reverse⇒∈ x∈xs = {!   !}

reverse-≼V : ∀ {A : Set} {xs : List A} {x y : A}
             → xs [ x ≼V y ] → reverse xs [ y ≼V x ]
reverse-≼V (x∈xs , y∈xs , x≼y) = {!   !}

------------------------------------------------------------------------
-- helper functions for snoc

-- analogous to `here` and `there` for lists, but with snoc
hereʳ : ∀ {A : Set} {x x' : A} {xs : List A}
        → x' ≡ x → x' ∈ xs ∷ʳ x
hereʳ {xs = []}     refl = here refl
hereʳ {xs = x ∷ xs} refl = there (hereʳ refl)

thereʳ : ∀ {A : Set} {x y : A} {xs : List A}
        → y ∈ xs → y ∈ xs ∷ʳ x
thereʳ (here  refl) = here refl
thereʳ (there y∈xs) = there (thereʳ y∈xs)

-- reverse pattern matching
snoc-match : ∀ {A : Set} {x y : A} {xs : List A}
             → x ∈ xs ∷ʳ y → (x ∈ xs) ⊎ (x ≡ y)
snoc-match {xs = []}     (here refl) = inj₂ refl
snoc-match {xs = x ∷ xs} (here refl) = inj₁ (here refl)
snoc-match {xs = x ∷ xs} (there p) with snoc-match p
... | inj₁ q    = inj₁ (there q)
... | inj₂ refl = inj₂ refl

-- concatenation preserves membership
∈-++ᵣ : {B : Set} → {x : B} → {xs ys : List B}
      → x ∈ xs → x ∈ ys ++ xs
∈-++ᵣ {B} {x} {xs} {[]}     p = p
∈-++ᵣ {B} {x} {xs} {y ∷ ys} p = there (∈-++ᵣ p)

∈-++ₗ : {B : Set} → {x : B} → {xs ys : List B}
      → x ∈ xs → x ∈ xs ++ ys
∈-++ₗ (here px) = here px
∈-++ₗ (there p) = there (∈-++ₗ p)

-- concatenation pattern matching
++-match : ∀ {A : Set} {x : A} (xs : List A) {ys : List A}
           → x ∈ xs ++ ys → (x ∈ xs) ⊎ (x ∈ ys)
++-match []     p           = inj₂ p
++-match (x ∷ xs) (here refl) = inj₁ (here refl)
++-match (x ∷ xs) (there p) with ++-match xs p
... | inj₁ q = inj₁ (there q)
... | inj₂ q = inj₂ q

-- analogous to base and step for _≼_ (precedence), but with snoc
baseʳ : ∀ {A : Set} {x y : A} {xs : List A}
        → {p : y ∈ xs ∷ʳ x} → p ≼ hereʳ refl
baseʳ {xs = []}     {p = here refl} = base
baseʳ {xs = x ∷ xs} {p = here refl} = base
baseʳ {xs = x ∷ xs} {p = there q}   = step baseʳ

stepʳ : ∀ {A : Set} {x y z : A} {xs : List A}
        → {p : y ∈ xs} → {q : z ∈ xs} → p ≼ q
        → thereʳ {x = x} p ≼ thereʳ q
stepʳ {p = here refl}           p≼q        = base
stepʳ {p = there p}   {there q} (step p≼q) = step (stepʳ p≼q)

------------------------------------------------------------------------
-- correctness of topological sort on acyclic graphs

module _ (traversal : Traversal)
         (uniqueness : ∀ {vs} → Unique (postorderF (traversal vs)))
         (completeness : ∀ {v vs} → v ∈ vs → v ∈ postorderF (traversal vs))
         (soundness : ∀ {v vs} → v ∈ postorderF (traversal vs) → v ∈ vs)
  where

  -- topological sort
  topoSort : List V → List V
  topoSort = reverse ∘ postorderF ∘ traversal

  mutual

    data _∈T_ : V → Tree V → Set where
      root : ∀ {  v ts}           → v ∈T (node v ts)
      sub  : ∀ {u v ts} → u ∈F ts → u ∈T (node v ts)
    
    data _∈F_ : V → Forest V → Set where
      here  : ∀ {v t ts} → v ∈T t  → v ∈F (t ∷ ts)
      there : ∀ {v t ts} → v ∈F ts → v ∈F (t ∷ ts)
  
  -- precedence relations on trees and forests  
  mutual
    
    data _≼T_ : ∀ {u v t} → u ∈T t → v ∈T t → Set where
      refl : ∀ {v t} {v∈t : v ∈T t} → v∈t ≼T v∈t
      root : ∀ {v t} {v∈t : v ∈T t} → v∈t ≼T root
      sub  : ∀ {u v w ts} {u∈ts : u ∈F ts} {v∈ts : v ∈F ts}
             → u∈ts ≼F v∈ts → _≼T_ {t = node w ts} (sub u∈ts) (sub v∈ts)

    data _≼F_ : ∀ {u v ts} → u ∈F ts → v ∈F ts → Set where
      here  : ∀ {u v t ts} {u∈t : u ∈T t} {v∈t : v ∈T t}
              → u∈t ≼T v∈t → _≼F_ {ts = t ∷ ts} (here u∈t) (here v∈t)
      there : ∀ {u v t ts} {u∈t : u ∈T t} {v∈ts : v ∈F ts}
              → _≼F_ {ts = t ∷ ts} (here u∈t) (there v∈ts)
      step  : ∀ {u v t ts} {u∈ts : u ∈F ts} {v∈ts : v ∈F ts}
              → u∈ts ≼F v∈ts → _≼F_ {ts = t ∷ ts} (there u∈ts) (there v∈ts)

  lemma : (vs : List V) → Acyclic vs
        → {u v : V} → E u v
        → (u∈trav : u ∈F traversal vs) → (v∈trav : v ∈F traversal vs)
        → v∈trav ≼F u∈trav
  lemma vs acyclic e u∈trav v∈trav = {!   !}

  mutual

    ∈T⇒∈postorder : ∀ {u t} → (u∈t : u ∈T t) → u ∈ postorder t
    ∈T⇒∈postorder root       = hereʳ refl
    ∈T⇒∈postorder (sub u∈ts) = thereʳ (∈F⇒∈postorderF u∈ts)

    ∈F⇒∈postorderF : ∀ {u ts} → (u∈ts : u ∈F ts) → u ∈ postorderF ts
    ∈F⇒∈postorderF (here  u∈t)  = ∈-++ₗ (∈T⇒∈postorder u∈t)
    ∈F⇒∈postorderF (there u∈ts) = ∈-++ᵣ (∈F⇒∈postorderF u∈ts)
  
  mutual

    ∈postorder⇒∈T : ∀ {u t} → u ∈ postorder t → u ∈T t
    ∈postorder⇒∈T {t = node v ts} u∈post with snoc-match u∈post
    ... | inj₁ p    = sub (∈postorderF⇒∈F p)
    ... | inj₂ refl = root

    ∈postorderF⇒∈F : ∀ {u ts} → u ∈ postorderF ts → u ∈F ts
    ∈postorderF⇒∈F {ts = t ∷ ts} u∈post with ++-match (postorder t) u∈post
    ... | inj₁ p = here (∈postorder⇒∈T p)
    ... | inj₂ p = there (∈postorderF⇒∈F p)

  mutual

    ≼T⇒≺postorder : ∀ {u v t} → {u∈t : u ∈T t} → {v∈t : v ∈T t}
                     → u∈t ≼T v∈t
                     → ∈T⇒∈postorder u∈t ≼ ∈T⇒∈postorder v∈t
    ≼T⇒≺postorder refl      = ≼-refl
    ≼T⇒≺postorder root      = baseʳ
    ≼T⇒≺postorder (sub u≼v) = stepʳ (≼F⇒≺postorder u≼v)

    ≼F⇒≺postorder : ∀ {u v ts} → {u∈ts : u ∈F ts} → {v∈ts : v ∈F ts}
                     → u∈ts ≼F v∈ts
                     → ∈F⇒∈postorderF u∈ts ≼ ∈F⇒∈postorderF v∈ts
    ≼F⇒≺postorder (here u≼t) = helper (≼T⇒≺postorder u≼t)
      where helper : ∀ {x y xs ys} → {x∈xs : x ∈ xs} → {y∈xs : y ∈ xs}
                    → x∈xs ≼ y∈xs → ∈-++ₗ {ys = ys} x∈xs ≼ ∈-++ₗ y∈xs
            helper base     = base
            helper (step p) = step (helper p)
    ≼F⇒≺postorder there      = helper
      where helper : ∀ {A : Set} {x y : A} {xs ys : List A}
                     → {x∈xs : x ∈ xs} → {y∈ys : y ∈ ys}
                     → ∈-++ₗ x∈xs ≼ ∈-++ᵣ y∈ys
            helper {x∈xs = here  refl} = base
            helper {x∈xs = there x∈xs} = step helper
    ≼F⇒≺postorder (step u≼t) = helper (≼F⇒≺postorder u≼t)
      where helper : ∀ {A : Set} {x y : A} {xs ys : List A}
                     → {x∈xs : x ∈ xs} → {y∈xs : y ∈ xs}
                     → x∈xs ≼ y∈xs → ∈-++ᵣ {ys = ys} x∈xs ≼ ∈-++ᵣ y∈xs
            helper {ys = []}     p = p
            helper {ys = x ∷ ys} p = step (helper p)

  ∈topo⇒∈trav : ∀ {v vs} → v ∈ topoSort vs → v ∈F traversal vs
  ∈topo⇒∈trav = ∈postorderF⇒∈F ∘ ∈reverse⇒∈

  -- correctness of topological sort
  topoSort-correct : (vs : List V) → Acyclic vs
                   → {u v : V} → E u v
                   → (u∈top : u ∈ topoSort vs)
                   → (v∈top : v ∈ topoSort vs)
                   → u∈top ≼ v∈top
  topoSort-correct vs acyclic e u∈top v∈top
    = Unique≼V⇒∀≼ (reverse-Unique uniqueness)
      (reverse-≼V {xs = postorderF (traversal vs)} 
       (∈F⇒∈postorderF (∈topo⇒∈trav v∈top) , ∈F⇒∈postorderF (∈topo⇒∈trav u∈top) , 
        ≼F⇒≺postorder (lemma vs acyclic e (∈topo⇒∈trav u∈top) (∈topo⇒∈trav v∈top))))
      u∈top v∈top