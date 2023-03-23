open import Definition.Bool
open import Definition.Bool-Relations
module Definition.Min-Max {A : Set} (_≤A_ : A → A → Bool)
  (≤A-trans : transitive _≤A_)
  (≤A-total : total _≤A_)
  where
open import Definition.Equality
open import Definition.Product

≤A-refl : reflexive _≤A_ 
≤A-refl = total-reflexive _≤A_ ≤A-total

min : A → A → A
min a b = if a ≤A b then a else b

max : A → A → A
max a b = if a ≤A b then b else a

min[a,b]≤a : ∀ {a b : A} → min a b ≤A a ≡ True
min[a,b]≤a {a} {b} with keep (a ≤A b)
...| True  , p rewrite p = ≤A-refl
...| False , p rewrite p = ≤A-total p

min[a,b]≤b : ∀ {a b : A} → min a b ≤A b ≡ True
min[a,b]≤b {a} {b} with keep (a ≤A b)
...| True  , p rewrite p = p
...| False , p rewrite p = ≤A-refl

a≤max[a,b] : ∀ {a b : A} → a ≤A max a b ≡ True
a≤max[a,b] {a} {b} with keep (a ≤A b)
...| True  , p rewrite p = p
...| False , p rewrite p = ≤A-refl

b≤max[a,b] : ∀ {a b : A} → b ≤A max a b ≡ True
b≤max[a,b] {a} {b} with keep (a ≤A b)
...| True  , p rewrite p = ≤A-refl
...| False , p rewrite p = ≤A-total p

min[a,b]≤max[a,b] : ∀ {a b : A} → min a b ≤A max a b ≡ True
min[a,b]≤max[a,b] {a} {b} with keep (a ≤A b)
...| True  , p rewrite p = p
...| False , p rewrite p = ≤A-total p

min-mono1 : ∀ {a b a′ : A} → a ≤A a′ ≡ True → min a b ≤A min a′ b ≡ True
min-mono1 {a} {b} {a′} p with keep (a ≤A b) | keep (a′ ≤A b)
...| True  , p′ | True  , p″ rewrite p′ | p″ = p
...| True  , p′ | False , p″ rewrite p′ | p″ = p′
...| False , p′ | True  , p″ rewrite p′ | p″ = ≤A-trans (≤A-total p′) p
...| False , p′ | False , p″ rewrite p′ | p″ = ≤A-refl

min-mono2 : ∀ {a b b′ : A} → b ≤A b′ ≡ True → min a b ≤A min a b′ ≡ True
min-mono2 {a} {b} {b′} p with keep (a ≤A b) | keep (a ≤A b′)
...| True  , p′ | True  , p″ rewrite p′ | p″ = ≤A-refl
...| True  , p′ | False , p″ rewrite p′ | p″ = ≤A-trans p′ p
...| False , p′ | True  , p″ rewrite p′ | p″ = ≤A-total p′
...| False , p′ | False , p″ rewrite p′ | p″ = p

max-mono1 : ∀ {a b a′ : A} → a ≤A a′ ≡ True → max a b ≤A max a′ b ≡ True
max-mono1 {a} {b} {a′} p with keep (a ≤A b) | keep (a′ ≤A b)
...| True  , p′ | True  , p″ rewrite p′ | p″ = ≤A-refl
...| True  , p′ | False , p″ rewrite p′ | p″ = ≤A-total p″
...| False , p′ | True  , p″ rewrite p′ | p″ = ≤A-trans p p″
...| False , p′ | False , p″ rewrite p′ | p″ = p

max-mono2 : ∀ {a b b′ : A} → b ≤A b′ ≡ True → max a b ≤A max a b′ ≡ True
max-mono2 {a} {b} {b′} p with keep (a ≤A b) | keep (a ≤A b′)
...| True  , p′ | True  , p″ rewrite p′ | p″ = p
...| True  , p′ | False , p″ rewrite p′ | p″ = ≤A-trans p (≤A-total p″)
...| False , p′ | True  , p″ rewrite p′ | p″ = p″
...| False , p′ | False , p″ rewrite p′ | p″ = ≤A-refl