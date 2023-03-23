open import Definition.Bool-Relations using (transitive; total)
open import Definition.Bool

module Definition.Tree.BST (A : Set) (_≤A_ : A → A → Bool)
  (≤A-trans : transitive _≤A_)
  (≤A-total : total _≤A_) where 

open import Definition.Bool-Relations _≤A_ hiding (transitive; total)
open import Definition.Equality
open import Definition.Product
open import Definition.Maybe

data BST : A → A → Set where
  leaf : ∀ {l u : A} → l ≤A u ≡ True → BST l u
  node : ∀ {l l′ u u′ : A} (d : A) → BST l′ d → BST d u′ 
    → l ≤A l′ ≡ True → u′ ≤A u ≡ True → BST l u

search : ∀ {l u : A} (d : A) → BST l u → Maybe (Σ A (λ x → (d isoBool x) ≡ True))
search d (leaf _) = nothing
search d (node d′ l r _ _) with keep (d ≤A d′) 
...| True  , p with keep (d′ ≤A d) 
...| True  , p′ = just (d′ , isoBool-intro p p′)
...| False , p′ = search d l 
search d (node d′ l r _ _) | False , p = search d r

