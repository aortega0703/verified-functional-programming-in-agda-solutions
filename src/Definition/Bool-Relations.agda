open import Definition.Bool

module Definition.Bool-Relations {ℓ} {A : Set ℓ}
  (_≤A_ : A → A → Bool) where

open import Definition.Equality
open import Definition.Product
open import Definition.Relations (λ a b → a ≤A b ≡ True) public
  using (reflexive; transitive)

total : Set ℓ
total = ∀ {a b : A} → a ≤A b ≡ False → b ≤A a ≡ True

total-reflexive : total → reflexive
total-reflexive tot {a} with keep (a ≤A a)
...| True ,  p = p
...| False , p = tot p

_isoBool_ : A → A → Bool
a isoBool b = a ≤A b ∧ b ≤A a

isoBool-intro : ∀ {a b : A} → a ≤A b ≡ True → b ≤A a ≡ True 
  → a isoBool b ≡ True
isoBool-intro p1 p2 rewrite p1 | p2 = refl