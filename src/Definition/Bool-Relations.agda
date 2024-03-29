open import Definition.Bool

module Definition.Bool-Relations {ℓ} {A : Set ℓ}
  (_≤A_ : A → A → Bool) where

open import Definition.Equality
open import Definition.Product

reflexive : Set ℓ
reflexive = ∀ {a : A} → a ≤A a ≡ True

transitive : Set ℓ
transitive = ∀ (a b c : A) → a ≤A b ≡ True → b ≤A c ≡ True → a ≤A c ≡ True

total : Set ℓ
total = ∀ (a b : A) → a ≤A b ≡ False → b ≤A a ≡ True

total-reflexive : total → reflexive
total-reflexive tot {a} with keep (a ≤A a)
...| True ,  p = p
...| False , p = tot _ _ p

_isoBool_ : A → A → Bool
a isoBool b = a ≤A b ∧ b ≤A a

isoBool-intro : ∀ {a b : A} → a ≤A b ≡ True → b ≤A a ≡ True
  → a isoBool b ≡ True
isoBool-intro p1 p2 rewrite p1 | p2 = refl