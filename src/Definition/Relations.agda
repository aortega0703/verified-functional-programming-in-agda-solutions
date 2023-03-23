open import Definition.Level
module Definition.Relations {ℓ ℓ′ : level} {A : Set ℓ}
  (_≤A_ : A → A → Set ℓ′) where

reflexive : Set (ℓ ⊔ ℓ′)
reflexive = ∀ {a : A} → a ≤A a

transitive : Set (ℓ ⊔ ℓ′)
transitive = ∀ {a b c : A} → a ≤A b → b ≤A c → a ≤A c