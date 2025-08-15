open import Data.List using (List; [];  _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (∃-syntax; _×_)

module Data.Tree where

record Tree (A : Set) : Set where
  inductive
  constructor node
  field
    label : A
    children : List (Tree A)

Forest : (A : Set) → Set
Forest A = List (Tree A)

-- membership relations on trees and forests

mutual

  data _∈T_ {A} : A → Tree A → Set where
    root : ∀ {  v ts}           → v ∈T (node v ts)
    sub  : ∀ {u v ts} → u ∈F ts → u ∈T (node v ts)

  data _∈F_ {A} : A → Forest A → Set where
    here  : ∀ {v t ts} → v ∈T t  → v ∈F (t ∷ ts)
    there : ∀ {v t ts} → v ∈F ts → v ∈F (t ∷ ts)

-- descendant relation on trees and forests

mutual

  data desc {A} : ∀ {u v : A} {t} → u ∈T t → v ∈T t → Set where
    root : ∀ {v t} {v∈t : v ∈T t} → desc root v∈t
    sub  : ∀ {u v w ts} {u∈ts : u ∈F ts} {v∈ts : v ∈F ts}
           → descF u∈ts v∈ts → desc {t = node w ts} (sub u∈ts) (sub v∈ts)

  data descF {A} : ∀ {u v : A} {ts} → u ∈F ts → v ∈F ts → Set where
    here  : ∀ {u v t ts} {u∈t : u ∈T t} {v∈t : v ∈T t}
            → desc u∈t v∈t → descF {ts = t ∷ ts} (here u∈t) (here v∈t)
    there : ∀ {u v t ts} {u∈ts : u ∈F ts} {v∈ts : v ∈F ts}
            → descF u∈ts v∈ts → descF {ts = t ∷ ts} (there u∈ts) (there v∈ts)

-- precedence relations on trees and forests

mutual

  data _≼T_ {A} : ∀ {u v : A} {t} → u ∈T t → v ∈T t → Set where
    root : ∀ {v t} {v∈t : v ∈T t} → v∈t ≼T root
    sub  : ∀ {u v w ts} {u∈ts : u ∈F ts} {v∈ts : v ∈F ts}
           → u∈ts ≼F v∈ts → _≼T_ {t = node w ts} (sub u∈ts) (sub v∈ts)

  data _≼F_ {A} : ∀ {u v : A} {ts} → u ∈F ts → v ∈F ts → Set where
    here  : ∀ {u v t ts} {u∈t : u ∈T t} {v∈t : v ∈T t}
            → u∈t ≼T v∈t → _≼F_ {ts = t ∷ ts} (here u∈t) (here v∈t)
    there : ∀ {u v t ts} {u∈t : u ∈T t} {v∈ts : v ∈F ts}
            → _≼F_ {ts = t ∷ ts} (here u∈t) (there v∈ts)
    step  : ∀ {u v t ts} {u∈ts : u ∈F ts} {v∈ts : v ∈F ts}
            → u∈ts ≼F v∈ts → _≼F_ {ts = t ∷ ts} (there u∈ts) (there v∈ts)

-- tree edges/paths

data TreeEdge {A} : Tree A → A → A → Set where
  root : ∀ {u v ts ts'} → (node v ts' ∈ ts)
         → TreeEdge (node u ts) u v
  sub  : ∀ {u v w t ts} → TreeEdge t u v → t ∈ ts
         → TreeEdge (node w ts) u v

TreeEdgeF : ∀ {A} → Forest A → A → A → Set
TreeEdgeF ts u v = ∃[ t ] t ∈ ts × TreeEdge t u v

data TreePath {A} : Tree A → A → A → Set where
  []   : ∀ {v t} → v ∈T t
         → TreePath t v v
  _▷_ : ∀ {u v w t} → TreePath t u v → TreeEdge t v w
         → TreePath t u w

TreePathF : ∀ {A} → Forest A → A → A → Set
TreePathF ts u v = ∃[ t ] t ∈ ts × TreePath t u v
