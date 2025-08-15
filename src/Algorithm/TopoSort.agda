open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; _∷ʳ_; concat; map; reverse; foldl)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; _≢_)
open import Relation.Nullary using (¬_)
open import Function.Base

open import Data.Tree
open import Data.Tree.Properties

module Algorithm.TopoSort
  (V : Set) (Edges : V → List V) where

------------------------------------------------------------------------
-- Definitions

data E : V → V → Set where
  edge : ∀ {u v} → v ∈ Edges u → E u v

data Path : V → V → Set where
  []   : ∀ {v}                        → Path v v
  _▷_ : ∀ {u v w} → Path u v → E v w → Path u w

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
  cons   : ∀ {u v w} → {e : E v w} → {p : Path u v}
           → {vs : List V} 
           → w ∈ vs → p ⊆P vs → (p ▷ e) ⊆P vs

⊆P⇒head∈ : ∀ {u v} {p : Path u v} {vs : List V}
            → p ⊆P vs → u ∈ vs
⊆P⇒head∈ (empty u∈vs)  = u∈vs
⊆P⇒head∈ (cons _ p⊆vs) = ⊆P⇒head∈ p⊆vs

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
-- helper functions for revcat

-- reverse = foldl (λ rev x → x ∷ rev) []

revcat : ∀ {A : Set} → List A → List A → List A
revcat xs ys = foldl (λ rev x → x ∷ rev) ys xs

revcat-∈ᵣ : ∀ {A : Set} {x : A} (xs ys : List A)
            → x ∈ ys → x ∈ revcat xs ys
revcat-∈ᵣ []       ys x∈ys = x∈ys
revcat-∈ᵣ (x ∷ xs) ys x∈ys = revcat-∈ᵣ xs (x ∷ ys) (there x∈ys)

revcat-∈ₗ : ∀ {A : Set} {x : A} (xs ys : List A)
            → x ∈ xs → x ∈ revcat xs ys
revcat-∈ₗ (x ∷ xs) ys (here  refl) = revcat-∈ᵣ xs (x ∷ ys) (here refl)
revcat-∈ₗ (x ∷ xs) ys (there x∈xs) = revcat-∈ₗ xs (x ∷ ys) x∈xs

∈revcat-split : ∀ {A : Set} {x : A} (xs ys : List A)
                → x ∈ revcat xs ys → (x ∈ xs) ⊎ (x ∈ ys)
∈revcat-split []       ys x∈rev = inj₂ x∈rev
∈revcat-split (x ∷ xs) ys x∈rev with ∈revcat-split xs (x ∷ ys) x∈rev
... | inj₁ p           = inj₁ (there p)
... | inj₂ (here refl) = inj₁ (here refl)
... | inj₂ (there p)   = inj₂ p

revcat-Unique : ∀ {A : Set} (xs ys : List A) → Unique xs → Unique ys
                → (∀ {x} → x ∈ xs → All (_≢_ x) ys) → Unique (revcat xs ys)
revcat-Unique []       ys unique-xs unique-ys f = unique-ys
revcat-Unique (x ∷ xs) ys (p ∷ unique-xs) unique-ys f
  = revcat-Unique xs (x ∷ ys) unique-xs
                  (f (here refl) ∷ unique-ys)
                  λ q → helper p q ∷ f (there q)
  where helper : ∀ {x y xs} → All (x ≢_) xs → y ∈ xs → y ≢ x
        helper (px ∷ all) (here refl) = px ∘ sym
        helper (px ∷ all) (there y∈xs) = helper all y∈xs

revcat-≼Vᵣ : ∀ {A : Set} {x y : A} (xs ys : List A)
             → ys [ y ≼V x ] → revcat xs ys [ y ≼V x ]
revcat-≼Vᵣ []        ys p = p
revcat-≼Vᵣ (x' ∷ xs) ys (x∈ys , y∈ys , x≼y) 
  = revcat-≼Vᵣ xs (x' ∷ ys) (there x∈ys , there y∈ys , step x≼y)

revcat-≼Vₘ : ∀ {A : Set} {x y : A} (xs ys : List A)
             → y ∈ xs → x ∈ ys → revcat xs ys [ y ≼V x ]
revcat-≼Vₘ (x' ∷ xs) ys (here  refl) x∈ys
  = revcat-≼Vᵣ xs (x' ∷ ys) (here refl , there x∈ys , base)
revcat-≼Vₘ (x' ∷ xs) ys (there y∈xs) x∈ys
  = revcat-≼Vₘ xs (x' ∷ ys) y∈xs (there x∈ys)

revcat-≼Vₗ : ∀ {A : Set} {x y : A} (xs ys : List A)
             → xs [ x ≼V y ] → revcat xs ys [ y ≼V x ]
revcat-≼Vₗ (x' ∷ xs) ys (here  refl , here  refl , x≼y)
  = revcat-≼Vᵣ xs (x' ∷ ys) (here refl , here refl , base)
revcat-≼Vₗ (x' ∷ xs) ys (here  refl , there y∈xs , x≼y)
  = revcat-≼Vₘ xs (x' ∷ ys) y∈xs (here refl)
revcat-≼Vₗ (x' ∷ xs) ys (there x∈xs , there y∈xs , step x≼y)
  = revcat-≼Vₗ xs (x' ∷ ys) (x∈xs , y∈xs , x≼y)

------------------------------------------------------------------------
-- helper functions for reverse

-- Unique (x ∷ xs) = All (_≢ x) xs × Unique xs

reverse-Unique : ∀ {A : Set} {xs : List A} → Unique xs
                 → Unique (reverse xs)
reverse-Unique unique = revcat-Unique _ _ unique [] λ _ → []

∈⇒∈reverse : ∀ {A : Set} {x : A} {xs : List A}
            → x ∈ xs → x ∈ reverse xs
∈⇒∈reverse x∈xs = revcat-∈ₗ _ [] x∈xs

∈reverse⇒∈ : ∀ {A : Set} {xs : List A} {x : A}
            → x ∈ reverse xs → x ∈ xs
∈reverse⇒∈ {xs = xs} x∈rxs with ∈revcat-split xs [] x∈rxs
... | inj₁ p = p

reverse-≼V : ∀ {A : Set} {x y : A} {xs : List A}
             → xs [ x ≼V y ] → reverse xs [ y ≼V x ]
reverse-≼V p = revcat-≼Vₗ _ [] p

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
-- helper functions for concatenation

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

------------------------------------------------------------------------
-- correctness of topological sort on acyclic graphs

module _ (traversal : Traversal)
         (uniqueness : ∀ {vs} → Unique (postorderF (traversal vs)))
         (completeness : ∀ {v vs} → v ∈ vs → v ∈F traversal vs)
         (soundness : ∀ {v vs} → v ∈F traversal vs → v ∈ vs)
         (TreeEdge⇒Edge : ∀ {u v vs} → TreeEdgeF (traversal vs) u v → E u v)
         (edge-classify : (vs : List V) → {u v : V} → E u v
                        → (u∈trav : u ∈F traversal vs)
                        → (v∈trav : v ∈F traversal vs)
                        → v∈trav ≼F u∈trav ⊎ descF v∈trav u∈trav)
  where

  -- topological sort
  topoSort : List V → List V
  topoSort = reverse ∘ postorderF ∘ traversal

  TreePathF⇒Path : ∀ {u v vs} → TreePathF (traversal vs) u v → Path u v
  TreePathF⇒Path (t , t∈ts , [] u∈t) = []
  TreePathF⇒Path (t , t∈ts , (p ▷ e))
    = TreePathF⇒Path (t , t∈ts , p) ▷ TreeEdge⇒Edge (t , t∈ts , e)
  
  TreePathF⇒⊆P : ∀ {u v vs} → (p : TreePathF (traversal vs) u v)
                  → TreePathF⇒Path p ⊆P vs
  TreePathF⇒⊆P (t , t∈ts , [] u∈t) = empty (soundness (∈T⇒∈F u∈t t∈ts))
  TreePathF⇒⊆P (t , t∈ts , (p ▷ e)) 
    = cons (soundness (∈T⇒∈F (TreeEdge⇒dst∈T e) t∈ts)) (TreePathF⇒⊆P (t , t∈ts , p))

  lemma : (vs : List V) → Acyclic vs
        → {u v : V} → E u v
        → (u∈trav : u ∈F traversal vs) → (v∈trav : v ∈F traversal vs)
        → v∈trav ≼F u∈trav
  lemma vs acyclic e u∈trav v∈trav with edge-classify vs e u∈trav v∈trav
  ... | inj₁ p = p
  ... | inj₂ p = ⊥-elim (helper (TreePathF⇒Path (descF⇒TreePathF p)) 
                                (TreePathF⇒⊆P   (descF⇒TreePathF p)) e)
    where helper : ∀ {u v : V} → (p : Path v u) → p ⊆P vs → E u v → ⊥
          helper p p⊆vs e with acyclic (p ▷ e) (cons (⊆P⇒head∈ p⊆vs) p⊆vs)
          ... | ()

  mutual

    ∈T⇒∈postorder : ∀ {A} {u : A} {t} → (u∈t : u ∈T t) → u ∈ postorder t
    ∈T⇒∈postorder root       = hereʳ refl
    ∈T⇒∈postorder (sub u∈ts) = thereʳ (∈F⇒∈postorderF u∈ts)

    ∈F⇒∈postorderF : ∀ {A} {u : A} {ts} → (u∈ts : u ∈F ts) → u ∈ postorderF ts
    ∈F⇒∈postorderF (here  u∈t)  = ∈-++ₗ (∈T⇒∈postorder u∈t)
    ∈F⇒∈postorderF (there u∈ts) = ∈-++ᵣ (∈F⇒∈postorderF u∈ts)
  
  mutual

    ∈postorder⇒∈T : ∀ {A} {u : A} {t} → u ∈ postorder t → u ∈T t
    ∈postorder⇒∈T {t = node v ts} u∈post with snoc-match u∈post
    ... | inj₁ p    = sub (∈postorderF⇒∈F p)
    ... | inj₂ refl = root

    ∈postorderF⇒∈F : ∀ {A} {u : A} {ts} → u ∈ postorderF ts → u ∈F ts
    ∈postorderF⇒∈F {ts = t ∷ ts} u∈post with ++-match (postorder t) u∈post
    ... | inj₁ p = here (∈postorder⇒∈T p)
    ... | inj₂ p = there (∈postorderF⇒∈F p)

  mutual

    ≼T⇒≺postorder : ∀ {A} {u v : A} {t} → {u∈t : u ∈T t} → {v∈t : v ∈T t}
                     → u∈t ≼T v∈t
                     → ∈T⇒∈postorder u∈t ≼ ∈T⇒∈postorder v∈t
    ≼T⇒≺postorder root      = baseʳ
    ≼T⇒≺postorder (sub u≼v) = stepʳ (≼F⇒≺postorder u≼v)

    ≼F⇒≺postorder : ∀ {A} {u v : A} {ts} → {u∈ts : u ∈F ts} → {v∈ts : v ∈F ts}
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