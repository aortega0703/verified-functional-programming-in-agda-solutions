module Definition.Equality where

infix 0 _≡_
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a