```agda
module Exercise.Chapter5 where

open import Definition.Equality
open import Definition.Bool
open import Definition.Nat
open import Definition.Vector
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

``` 