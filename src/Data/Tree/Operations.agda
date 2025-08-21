open import Data.List using (List; []; _∷_; _∷ʳ_)

open import Data.Tree

module Data.Tree.Operations where


mutual
  insertT : ∀ {A} {u : A} → (t : Tree A)
             → u ∈T t → A → Tree A
  insertT (node w ts) root       v = node w (ts ∷ʳ (node v []))
  insertT (node w ts) (sub u∈ts) v = node w (insertF ts u∈ts v)

  insertF : ∀ {A} {u : A} → (ts : Forest A)
            → u ∈F ts → A → Forest A
  insertF (t ∷ ts) (here  u∈t)  v = insertT t u∈t v ∷ ts
  insertF (t ∷ ts) (there u∈ts) v = t ∷ (insertF ts u∈ts v)
