open import Definition.Bool-Relations using (transitive; total)
open import Definition.Bool

module Definition.Tree.BST (A : Set) (_≤A_ : A → A → Bool)
  (≤A-trans : transitive _≤A_)
  (≤A-total : total _≤A_) where 

open import Definition.Bool-Relations _≤A_
open import Definition.Equality
open import Definition.Product
open import Definition.Maybe
open import Definition.Min-Max (_≤A_) (≤A-trans) (≤A-total)

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

dec-lb : ∀ {l u l′ : A} → BST l u → l′ ≤A l ≡ True → BST l′ u
dec-lb (leaf x) p = leaf (≤A-trans p x)
dec-lb (node d l r p1 p2) p = node d l r (≤A-trans p p1) p2

inc-ub : ∀ {l u u′ : A} → BST l u → u ≤A u′ ≡ True → BST l u′
inc-ub (leaf x) p = leaf (≤A-trans x p)
inc-ub (node d l r p1 p2) p = node d l r p1 (≤A-trans p2 p)

insert : ∀ {l u : A} (d : A) → BST l u → BST (min d l) (max d u)
insert d (leaf _) = node d (leaf ≤A-refl) (leaf ≤A-refl) min[a,b]≤a a≤max[a,b]
insert d (node d′ l r p1 p2) with keep (d ≤A d′)
...| True  , p with insert d l
...| l′ rewrite p = node d′ l′ r (min-mono2 p1) (≤A-trans p2 b≤max[a,b])
insert d (node d′ l r p1 p2) | False , p with insert d r 
...| r′ rewrite p = node d′ l r′ (≤A-trans min[a,b]≤b p1) (max-mono2 p2)

remove-min : ∀ {l u : A} → BST l u → Maybe (A × BST l u)
remove-min (leaf p) = nothing
remove-min (node d (leaf pl) (leaf pr) p1 p2) = just (d , (leaf (≤A-trans (≤A-trans (≤A-trans p1 pl) pr) p2)))
remove-min (node d (leaf x) (node d₁ r r₁ x₁ x₂) pl pr) = just (d , (node d₁ r r₁ (≤A-trans (≤A-trans pl x) x₁) (≤A-trans x₂ pr)))
remove-min (node d (node d₁ l l₁ x x₁) r pl pr) with remove-min (node d₁ l l₁ x x₁)
...| nothing = nothing
...| just (a , bt) = just (a , (node d bt r pl pr))
