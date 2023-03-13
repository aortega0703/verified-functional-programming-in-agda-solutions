open import Definition.Equality
open import Definition.Bool
open import Definition.Nat
open import Definition.Maybe
open import Definition.Product

module Definition.List where

data List {ℓ} (A : Set ℓ) : Set ℓ where
  [] : List A
  _::_ : (x : A) (xs : List A) → List A

length : ∀ {ℓ} {A : Set ℓ} → List A → ℕ
length [] = 0
length (x :: xs) = suc (length xs)

_++_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) → List A → List B
map f [] = []
map f (x :: xs) = (f x) :: (map f xs)

filter : ∀ {ℓ} {A : Set ℓ} → (A → Bool) → List A → List A
filter f [] = []
filter f (x :: xs) with f x
... | True = x :: filter f xs
... | False = filter f xs

remove : ∀ {ℓ} {A : Set ℓ} → (A → A → Bool) → A → List A → List A
remove eq x xs = filter (λ y → ¬ (eq y x)) xs

_!!_ : ∀ {ℓ} {A : Set ℓ} → List A → ℕ → Maybe A
[] !! n = nothing
(x :: xs) !! zero = just x
(x :: xs) !! suc n = xs !! n

sreverse : ∀ {ℓ} {A : Set ℓ} → List A → List A
sreverse [] = []
sreverse (x :: xs) = (sreverse xs) ++ (x :: [])

reverse´ : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
reverse´ [] ys = ys
reverse´ (x :: xs) ys = reverse´ xs (x :: ys)

reverse : ∀ {ℓ} {A : Set ℓ} → List A → List A
reverse xs = reverse´ xs []

length-++ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) 
  → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x :: xs) ys rewrite length-++ xs ys = refl

++-assoc : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) 
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x :: xs) ys zs rewrite ++-assoc xs ys zs = refl

length-filter : ∀ {ℓ} {A : Set ℓ} (f : A → Bool) (xs : List A)
  → length (filter f xs) ≤ length xs ≡ True
length-filter f [] = refl
length-filter f (x :: xs) with f x 
... | True  = length-filter f xs
... | False = ≤-trans {length (filter f xs)} (length-filter f xs) (≤-suc {length xs})  

filter-idem : ∀ {ℓ} {A : Set ℓ} (f : A → Bool) (xs : List A)
  → filter f (filter f xs) ≡ filter f xs
filter-idem f [] = refl
filter-idem f (x :: xs) with keep (f x)
... | True  , p´ rewrite p´ | p´ | filter-idem f xs = refl
... | False , p´ rewrite p´ | filter-idem f xs = refl

length-reverse´ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → length (reverse´ xs ys) ≡ length xs + length ys
length-reverse´ [] ys = refl
length-reverse´ (x :: xs) ys 
  rewrite 
      length-reverse´ xs (x :: ys) 
    | +suc (length xs) (length ys) = refl

length-reverse : ∀ {ℓ} {A : Set ℓ} (xs : List A) → length (reverse xs) ≡ length xs
length-reverse xs rewrite length-reverse´ xs [] | +0 (length xs) = refl