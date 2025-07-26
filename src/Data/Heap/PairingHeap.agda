open import Data.List
open import Data.Sum
open import Data.Product
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Definitions

module PairingHeap 
    (A : Set)
    (_≤_ : A → A → Set)
    (cmp : (x y : A) → x ≤ y ⊎ y ≤ x)
    (≤-refl : {x : A} → x ≤ x)
    (≤-trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z) where

data Heap : Set where
  Empty : Heap
  Node  : A → List Heap → Heap

meld : Heap → Heap → Heap
meld Empty          h                = h
meld h@(Node _ _)   Empty            = h
meld h1@(Node x hs) h2@(Node x' hs') with cmp x x'
... | inj₁ _ = Node x  (h2 ∷ hs)
... | inj₂ _ = Node x' (h1 ∷ hs')

insert : A → Heap → Heap
insert x h = meld (Node x []) h

findMin : Heap → Maybe A
findMin Empty          = nothing
findMin (Node x _)     = just x

private
  mergePairs : List Heap → Heap
  mergePairs []            = Empty
  mergePairs (h ∷ [])      = h
  mergePairs (h ∷ h' ∷ hs) = meld (meld h h') (mergePairs hs)

deleteMin : Heap → Heap
deleteMin Empty          = Empty
deleteMin (Node _ hs)    = mergePairs hs

build : List A → Heap
build []       = Empty
build (x ∷ xs) = insert x (build xs)

------------------------------------------------------------------------
-- Min-heap property

-- the property that some value x is less than or equal to all values in the heap
data _≤H_ : A → Heap → Set where
  triv : ∀ {x} → x ≤H Empty
  cons : ∀ {x y} {hs} → x ≤ y → All (λ h → x ≤H h) hs → x ≤H (Node y hs)
  
-- the property that the root is minimum of all elements
data IsMinHeap : Heap → Set where
  triv : IsMinHeap Empty
  rec  : ∀ {x hs} → x ≤H (Node x hs) → All IsMinHeap hs → IsMinHeap (Node x hs)

mutual
  ≤H-trans : ∀ {x y h} → x ≤ y → y ≤H h → x ≤H h
  ≤H-trans x≤y triv            = triv
  ≤H-trans x≤y (cons y≤z y≤hs) = cons (≤-trans x≤y y≤z) (≤H-trans-list x≤y y≤hs)

  ≤H-trans-list : ∀ {x y hs} → x ≤ y → All (λ h → y ≤H h) hs → All (λ h → x ≤H h) hs
  ≤H-trans-list x≤y []           = []
  ≤H-trans-list x≤y (y≤h ∷ y≤hs) = ≤H-trans x≤y y≤h ∷ ≤H-trans-list x≤y y≤hs

-- meld preserves min-heap property
meld-minHeap : ∀ h₁ h₂ → IsMinHeap h₁ → IsMinHeap h₂ → IsMinHeap (meld h₁ h₂)
meld-minHeap Empty           h₂    _ q = q
meld-minHeap h₁@(Node _ _)   Empty p _ = p
meld-minHeap h₁@(Node x hs₁) h₂@(Node y hs₂) 
             p@(rec x≤h₁@(cons _ x≤hs₁) Phs₁) 
             q@(rec y≤h₂@(cons _ y≤hs₂) Phs₂) with cmp x y
... | inj₁ x≤y = rec (cons ≤-refl (≤H-trans x≤y y≤h₂ ∷ x≤hs₁)) (q ∷ Phs₁)
... | inj₂ y≤x = rec (cons ≤-refl (≤H-trans y≤x x≤h₁ ∷ y≤hs₂)) (p ∷ Phs₂)

-- Insert preserves min-heap property
insert-minHeap : ∀ x h → IsMinHeap h → IsMinHeap (insert x h)
insert-minHeap x h p = meld-minHeap (Node x []) h (rec (cons ≤-refl []) []) p

-- mergePairs preserves min-heap property
mergePairs-minHeap : ∀ hs → All IsMinHeap hs → IsMinHeap (mergePairs hs)
mergePairs-minHeap []            _             = triv
mergePairs-minHeap (h ∷ [])      (p ∷ _)       = p
mergePairs-minHeap (h ∷ h' ∷ hs) (p ∷ p' ∷ ps) = 
  meld-minHeap (meld h h') (mergePairs hs) (meld-minHeap h h' p p') (mergePairs-minHeap hs ps)

-- DeleteMin preserves min-heap property
deleteMin-minHeap : ∀ h → IsMinHeap h → IsMinHeap (deleteMin h)
deleteMin-minHeap Empty       _           = triv
deleteMin-minHeap (Node _ hs) (rec _ phs) = mergePairs-minHeap hs phs

------------------------------------------------------------------------
-- Presence of elements

-- the property that an element is present in a heap
data _∈H_ : A → Heap → Set where
  root : ∀ {x hs} → x ∈H (Node x hs)
  sub  : ∀ {x y hs h} → h ∈ hs → x ∈H h → x ∈H (Node y hs)

meld-∈H : ∀ {x} h₁ h₂ → x ∈H h₁ ⊎ x ∈H h₂ → x ∈H (meld h₁ h₂)
meld-∈H (Node _ _)  Empty         (inj₁ x∈h₁) = x∈h₁
meld-∈H Empty       (Node _ _)    (inj₂ x∈h₂) = x∈h₂
meld-∈H (Node y hs) (Node y' hs') (inj₁ x∈h₁) with cmp y y' | x∈h₁
... | inj₁ y≤y' | root         = root
... | inj₁ y≤y' | sub h∈hs x∈h = sub (there h∈hs) x∈h
... | inj₂ y'≤y | p            = sub (here refl) p
meld-∈H (Node y hs) (Node y' hs') (inj₂ x∈h₂) with cmp y y' | x∈h₂
... | inj₁ y≤y' | p            = sub (here refl) p
... | inj₂ y'≤y | root         = root
... | inj₂ y'≤y | sub h∈hs x∈h = sub (there h∈hs) x∈h

insert-root-∈H : ∀ x h → x ∈H (insert x h)
insert-root-∈H x h = meld-∈H (Node x []) h (inj₁ root)

insert-sub-∈H : ∀ {x} y h → x ∈H h → x ∈H (insert y h)
insert-sub-∈H y h x∈h = meld-∈H (Node y []) h (inj₂ x∈h)

mergePairs-∈H : ∀ {x h} hs → x ∈H h → h ∈ hs → x ∈H (mergePairs hs)
mergePairs-∈H (h ∷ [])      x∈h (here refl)          = x∈h
mergePairs-∈H (h ∷ h' ∷ hs) x∈h (here refl)          = meld-∈H (meld h h') (mergePairs hs) (inj₁ (meld-∈H h h' (inj₁ x∈h)))
mergePairs-∈H (h ∷ h' ∷ hs) x∈h (there (here refl))  = meld-∈H (meld h h') (mergePairs hs) (inj₁ (meld-∈H h h' (inj₂ x∈h)))
mergePairs-∈H (h ∷ h' ∷ hs) x∈h (there (there h∈hs)) = meld-∈H (meld h h') (mergePairs hs) (inj₂ (mergePairs-∈H hs x∈h h∈hs))

deleteMin-∈H : ∀ {x} h → x ∈H h → findMin h ≡ just x ⊎ x ∈H (deleteMin h)
deleteMin-∈H .(Node _ _) root           = inj₁ refl
deleteMin-∈H .(Node _ _) (sub h∈hs x∈h) = inj₂ (mergePairs-∈H _ x∈h h∈hs)

