```agda
module Exercise.Chapter5 where

open import Definition.Equality
open import Definition.Bool
open import Definition.Nat
open import Definition.Vector
open import Definition.List using (List) renaming (_::_ to _::L_; [] to []L)
open import Definition.Product
open import Definition.Maybe
import Definition.Tree.BST
open Definition.Tree.BST ℕ _≤_ ≤-trans ≤-total
  using (BST; leaf; insert; remove-min; remove-max)
```

1. Using the vector type V in a nested fashion, fill in the hole below to define a
type for matrices of natural numbers, where the type lists the dimensions of
the matrix:
```agda
_by_matrix : ℕ → ℕ → Set
m by n matrix = Vector (Vector ℕ n) m
```

2. Define the following basic operations on matrices, using the definition you
propose in the previous problem. You should first figure out the types of the
operations, of course, and then write code for them (possibly using helper
functions).
```agda
zero-matrix : (m n : ℕ) → m by n matrix
zero-matrix m n = repeat m (repeat n 0)

matrix-elt :
    {m n : ℕ} → m by n matrix → (i j : ℕ)
  → {i < m ≡ True} → {j < n ≡ True}
  → ℕ
matrix-elt M i j {p} {q} = nth j (nth i M {p}) {q}

diagonal-matrix : (n v : ℕ) → n by n matrix
diagonal-matrix n v = map (λ x → eye n x v) (upTo n)

identity-matrix : (n : ℕ) → n by n matrix
identity-matrix n = diagonal-matrix n 1

create_empties : {n : ℕ} → n by 0 matrix
create_empties {n = Z} = repeat Z []

transpose : ∀ {m n : ℕ} → m by n matrix → n by m matrix
transpose [] = create_empties
transpose (x :: xs) =
  let xs_trans = transpose xs in
  zip (_::_) x xs_trans

_·_ : ∀ {n : ℕ} → Vector ℕ n → Vector ℕ n → ℕ
[] · [] = 0
(x :: xs) · (y :: ys) = x * y + (xs · ys)

_*matrix_ : ∀ {m n p : ℕ} → m by n matrix → n by p matrix → m by p matrix
_*matrix_ [] N = []
_*matrix_ (m :: ms) N with transpose N
...| Nᵗ = (map (λ x → m · x) Nᵗ) :: (ms *matrix N)
```

3. vector.agda contains functions V-to-L and L-to-V for converting between
vectors and lists. State and prove a theorem expressing the idea that
converting a vector to a list and then back to a vector results in the same
vector.
```agda
vector-to-list : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vector A n → List A
vector-to-list [] = []L
vector-to-list (x :: xs) = x ::L (vector-to-list xs)

list-to-vector : ∀ {ℓ} {A : Set ℓ} → List A → Σ ℕ (λ n → Vector A n)
list-to-vector []L = 0 , []
list-to-vector (x ::L xs) with list-to-vector xs
...| (n , ys) = suc n , (x :: ys)

vector↑↓ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} (xs : Vector A n)
  → list-to-vector (vector-to-list xs) ≡ (n , xs)
vector↑↓ [] = refl
vector↑↓ (x :: xs) rewrite vector↑↓ xs = refl
```

4. Write a function which takes a vector of type V (A × B) n and returns
a pair of vectors, one of type V A n and another of type V B n. This is
similar to the unzip function in Haskell, only with vectors instead of lists.
```agda
unzip : ∀ {ℓ} {A B : Set ℓ} {n : ℕ} → Vector (A × B) n → (Vector A n) × (Vector B n)
unzip [] = [] , []
unzip ((y , z) :: xs) with unzip xs
...| ys , zs = (y :: ys) , (z :: zs)

test : Maybe (ℕ × BST 0 1)
test = remove-max (insert 0 (insert 1 (insert 0 (insert {1} {1} 1 (leaf refl)))))
```