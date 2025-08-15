open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Tree

module Data.Tree.Properties where

------------------------------------------------------------------------
-- tree membership properties

∈T⇒∈F : ∀ {A} {u : A} {t ts} → u ∈T t → t ∈ ts → u ∈F ts
∈T⇒∈F u∈t (here  refl) = here u∈t
∈T⇒∈F u∈t (there t∈ts) = there (∈T⇒∈F u∈t t∈ts)

∈F⇒∈T : ∀ {A} {u : A} {ts} → u ∈F ts → ∃[ t ] t ∈ ts × u ∈T t
∈F⇒∈T (here  u∈t)  = _ , here refl , u∈t
∈F⇒∈T (there u∈ts) = let t , t∈ts , u∈t = ∈F⇒∈T u∈ts
                      in  t , there t∈ts , u∈t

TreeEdge⇒src∈T : ∀ {A} {t} {u v : A} → TreeEdge t u v → u ∈T t
TreeEdge⇒src∈T (root u∈t)   = root
TreeEdge⇒src∈T (sub e t∈ts) = sub (∈T⇒∈F (TreeEdge⇒src∈T e) t∈ts)

TreeEdge⇒dst∈T : ∀ {A} {t} {u v : A} → TreeEdge t u v → v ∈T t
TreeEdge⇒dst∈T (root u∈t)   = sub (∈T⇒∈F root u∈t)
TreeEdge⇒dst∈T (sub e t∈ts) = sub (∈T⇒∈F (TreeEdge⇒dst∈T e) t∈ts)

_▷ₗ_ : ∀ {A} {u v w : A} {t} → TreeEdge t u v → TreePath t v w
        → TreePath t u w
e ▷ₗ [] v∈t   = [] (TreeEdge⇒src∈T e) ▷ e
e ▷ₗ (p ▷ f) = (e ▷ₗ p) ▷ f

------------------------------------------------------------------------
-- tree path properties

liftTreePath : ∀ {A} {u v w : A} {t ts}
               → TreePath t u v → t ∈ ts → TreePath (node w ts) u v
liftTreePath ([] u∈t) t∈ts = [] (sub (∈T⇒∈F u∈t t∈ts))
liftTreePath (p ▷ e) t∈ts = liftTreePath p t∈ts ▷ sub e t∈ts

TreePathF⇒TreePath : ∀ {A} {u v w : A} {ts}
                      → TreePathF ts u v → TreePath (node w ts) u v
TreePathF⇒TreePath (t , t∈ts , p) = liftTreePath p t∈ts

mutual

  ∈T⇒TreePath : ∀ {A} {u v : A} {ts}
                 → v ∈T (node u ts) → TreePath (node u ts) u v
  ∈T⇒TreePath root       = [] root
  ∈T⇒TreePath (sub v∈ts) = ∈F⇒TreePath v∈ts

  ∈F⇒TreePath : ∀ {A} {u v : A} {ts}
                  → v ∈F ts → TreePath (node u ts) u v
  ∈F⇒TreePath (here  v∈t)  = root (here refl) ▷ₗ liftTreePath (∈T⇒TreePath v∈t) (here refl)
  ∈F⇒TreePath (there v∈ts) = pathHelper (∈F⇒TreePath v∈ts)
    where edgeHelper : ∀ {A} {u v w : A} {t ts} → TreeEdge (node u ts) v w → TreeEdge (node u (t ∷ ts)) v w
          edgeHelper (root p)  = root (there p)
          edgeHelper (sub e p) = sub e (there p)
          pathHelper : ∀ {A} {u v : A} {t ts} → TreePath (node u ts) u v → TreePath (node u (t ∷ ts)) u v
          pathHelper ([] u∈t) = [] root
          pathHelper (p ▷ e) = pathHelper p ▷ edgeHelper e

mutual
    
  desc⇒TreePath : ∀ {A} {u v : A} {t} {u∈t : u ∈T t} {v∈t : v ∈T t}
                   → desc u∈t v∈t → TreePath t u v
  desc⇒TreePath {v∈t = root}     root = [] root
  desc⇒TreePath {v∈t = sub v∈ts} root = ∈F⇒TreePath v∈ts
  desc⇒TreePath (sub p) = TreePathF⇒TreePath (descF⇒TreePathF p)

  descF⇒TreePathF : ∀ {A} {u v : A} {ts} {u∈ts : u ∈F ts} {v∈ts : v ∈F ts}
                   → descF u∈ts v∈ts → TreePathF ts u v
  descF⇒TreePathF (here  p) = _ , here refl , desc⇒TreePath p
  descF⇒TreePathF (there p) = let t , t∈ts , q = descF⇒TreePathF p
                               in  t , (there t∈ts) , q
