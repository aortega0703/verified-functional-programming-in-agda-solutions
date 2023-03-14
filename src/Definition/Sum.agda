open import Level

module Definition.Sum where

data _⨄_ {ℓ ℓ´} (A : Set ℓ) (B : Set ℓ´) : Set (ℓ ⊔ ℓ´) where
  inj₁ : A → A ⨄ B
  inj₂ : B → A ⨄ B