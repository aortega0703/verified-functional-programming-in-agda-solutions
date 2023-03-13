module Definition.Maybe where

data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
  just : A → Maybe A
  nothing : Maybe A