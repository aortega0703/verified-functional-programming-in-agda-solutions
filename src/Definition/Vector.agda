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

foldr : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {n : ℕ} 
  → (A → B → B) → B → Vector A n → B
foldr f e [] = e
foldr f e (x :: xs) = f x (foldr f e xs)

zip : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''} → 
      (A → B → C) → {n : ℕ} → Vector A n → Vector B n → Vector C n
zip f [] [] = []
zip f (x :: xs) (y :: ys) = (f x y) :: (zip f xs ys)

concat : ∀ {ℓ} {A : Set ℓ} {m n : ℕ} → Vector (Vector A n) m 
  → Vector A (m * n)
concat [] = []
concat (x :: xs) = x ++ (concat xs)

nth : ∀ {ℓ} {A : Set ℓ} {m : ℕ} (n : ℕ) (xs : Vector A m) → {n < m ≡ True} → A
nth zero (x :: xs) = x
nth (suc n) (x :: xs) {p} = nth n xs {p}

repeat : ∀ {ℓ} {A : Set ℓ} (n : ℕ) → A → Vector A n
repeat zero x = []
repeat (suc n) x = x :: repeat n x

reverse : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vector A n → Vector A n
reverse xs = reverse´ [] xs
  where
    reverse´ : ∀ {ℓ} {A : Set ℓ} {m n : ℕ} → Vector A m → Vector A n → Vector A (m + n)
    reverse´ {_} {_} {m} xs [] rewrite +0 m = xs
    reverse´ {_} {_} {m} {suc n} xs (y :: ys) rewrite +suc m n = 
      reverse´ (y :: xs) ys

downTo : ∀ (n : ℕ) → Vector ℕ n
downTo zero = []
downTo (suc n) = n :: downTo n

upTo : ∀ (n : ℕ) → Vector ℕ n
upTo n = reverse (downTo n)

eye : ∀ (n i v : ℕ) → Vector ℕ n
eye n i v = map (λ j → if i =ℕ j then v else 0) (upTo n)