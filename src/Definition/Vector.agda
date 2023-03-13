open import Definition.Equality
open import Definition.Bool
open import Definition.Nat

module Definition.Vector where

data Vector {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  [] : Vector A 0
  _::_ : {n : ℕ} → A → Vector A n → Vector A (suc n)

_++_ : ∀ {ℓ} {A : Set ℓ} {m n : ℕ} (xs : Vector A m) (ys : Vector A n) 
  → Vector A (m + n)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

head : ∀ {ℓ} {A : Set ℓ} {n : ℕ} (xs : Vector A (suc n)) → A
head (x :: xs) = x

tail : ∀ {ℓ} {A : Set ℓ} {n : ℕ} (xs : Vector A n) → Vector A (pred n)
tail [] = []
tail (x :: xs) = xs

map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {n : ℕ} (f : A → B) (xs : Vector A n)
  → Vector B n
map f [] = []
map f (x :: xs) = (f x) :: (map f xs)

concat : ∀ {ℓ} {A : Set ℓ} {m n : ℕ} → Vector (Vector A n) m 
  → Vector A (m * n)
concat [] = []
concat (x :: xs) = x ++ (concat xs)

nth : ∀ {ℓ} {A : Set ℓ} {m : ℕ} (n : ℕ) (xs : Vector A m) → n < m ≡ True → A
nth zero (x :: xs) n<m = x
nth (suc n) (x :: xs) n<m = nth n xs n<m

repeat : ∀ {ℓ} {A : Set ℓ} (n : ℕ) → A → Vector A n
repeat zero x = []
repeat (suc n) x = x :: repeat n x