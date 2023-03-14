{-# OPTIONS --rewriting #-}
open import Definition.Equality
open import Definition.Bool
open import Definition.Nat
open import Definition.Sum
open import Definition.Product

module Definition.Tree.Braun {ℓ} (A : Set ℓ) (_≤A_ : A → A → Bool) where

data Braun-Tree : (n : ℕ) → Set ℓ where
  empty : Braun-Tree 0
  node  : ∀ {m n : ℕ} → A → Braun-Tree m → Braun-Tree n → (m ≡ n) ⨄ (m ≡ suc n)
    → Braun-Tree (suc (m + n))

insert : ∀ {n : ℕ} → A → Braun-Tree n → Braun-Tree (suc n)
insert a empty = node a empty empty (inj₁ refl)
insert a (node {m} {n} a´ l r p) rewrite +comm m n 
  with p            | if (a ≤A a´) then (a , a´) else (a´ , a)
... | inj₁ m≡n      | (a1 , a2) rewrite m≡n = node a1 (insert a2 r) l (inj₂ refl)
... | inj₂ m≡suc[n] | (a1 , a2) = node a1 (insert a2 r) l (inj₁ (sym m≡suc[n]))

lemma : ∀ {mₗ nₗ mᵣ nᵣ : ℕ} 
  → (suc (mₗ + nₗ) ≡ suc (mᵣ + nᵣ)) ⨄ (suc (mₗ + nₗ) ≡ suc (suc (mᵣ + nᵣ)))
  → (suc (mᵣ + nᵣ) ≡ mₗ + nₗ) ⨄ (suc (mᵣ + nᵣ) ≡ suc (mₗ + nₗ))
lemma (inj₁ p) = inj₂ (sym p)
lemma (inj₂ p) = inj₁ (sym (suc-inj p))

siftDown : ∀ {n : ℕ} → A → Braun-Tree (suc n) → Braun-Tree (suc n)
siftDown a (node _ empty empty p) = node a empty empty p
siftDown a (node _ empty (node aᵣ lᵣ rᵣ pᵣ) (inj₁ ()))
siftDown a (node _ empty (node aᵣ lᵣ rᵣ pᵣ) (inj₂ ()))
siftDown a (node _ (node aₗ lₗ rₗ pₗ) empty (inj₂ p)) = 
  if a ≤A aₗ 
  then node a (node aₗ lₗ rₗ pₗ) empty (inj₂ p)
  else node aₗ (siftDown a ((node aₗ lₗ rₗ pₗ))) empty (inj₂ p)
siftDown a (node _ (node aₗ lₗ rₗ pₗ) (node aᵣ lᵣ rᵣ pᵣ) p) = 
  if (a ≤A aₗ ∧ a ≤A aᵣ) 
  then (node a (node aₗ lₗ rₗ pₗ) (node aᵣ lᵣ rᵣ pᵣ) p)
  else (
    if (aₗ ≤A aᵣ) 
    then (node aₗ (siftDown a (node aₗ lₗ rₗ pₗ)) (node aᵣ lᵣ rᵣ pᵣ) p) 
    else (node aᵣ (node aₗ lₗ rₗ pₗ) (siftDown a (node aᵣ lᵣ rᵣ pᵣ)) p)
  )

del : ∀ {n : ℕ} → Braun-Tree (suc n) → Braun-Tree n
del (node a empty empty _) = empty
del (node a empty (node _ _ _ _) p) with p
... | inj₁ ()
... | inj₂ ()
del (node a (node {mₗ} {nₗ} aₗ lₗ rₗ pₗ) empty p) 
  rewrite +0 (suc (mₗ + nₗ)) = (node {mₗ} {nₗ} aₗ lₗ rₗ pₗ)
del (node {m} {n} a 
      (node {mₗ} {nₗ} aₗ lₗ rₗ pₗ) 
      (node {mᵣ} {nᵣ} aᵣ lᵣ rᵣ pᵣ) p) with del (node {mₗ} {nₗ} aₗ lₗ rₗ pₗ)
... | l rewrite +comm (mₗ + nₗ) (suc (mᵣ + nᵣ)) = 
  if (aₗ ≤A aᵣ) 
  then node aₗ (node {mᵣ} {nᵣ} aᵣ lᵣ rᵣ pᵣ) l (lemma {mₗ} {nₗ} {mᵣ} {nᵣ} p)
  else node aᵣ (siftDown aₗ (node {mᵣ} {nᵣ} aᵣ lᵣ rᵣ pᵣ)) l (lemma {mₗ} {nₗ} {mᵣ} {nᵣ} p)

pop : ∀ {n : ℕ} → Braun-Tree (suc n) → A × Braun-Tree n
pop (node a l r p) = (a , del (node a l r p))