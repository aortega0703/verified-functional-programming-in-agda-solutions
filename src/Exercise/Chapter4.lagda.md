```agda
open import Definition.Equality
open import Definition.Bool
open import Definition.Nat
open import Definition.List
open import Definition.Product

module Exercise.Chapter4 where
```

1. Which of the following formulas are theorems (i.e., they can be proved)
```agda
repeat : ∀ {ℓ} {A : Set ℓ} → ℕ → A → List A
repeat zero a = []
repeat (suc n) a = a :: repeat n a

c : ∀ {ℓ} {A : Set ℓ} {p : A → Bool} {a : A} (n : ℕ) 
  → p a ≡ False → filter p (repeat n a) ≡ []
c zero pa≡False = refl
c (suc n) pa≡False rewrite pa≡False = c n pa≡False

e : ∀ {ℓ} {A : Set ℓ} (p : A → Bool) (xs ys : List A)
  → filter p (xs ++ ys) ≡ (filter p xs) ++ (filter p ys)
e p [] ys = refl
e p (x :: xs) ys with p x 
... | True  rewrite e p xs ys = refl
... | False rewrite e p xs ys = refl
```

2. Indicate which of the typings listed for each test term would be accepted by
Agda

> a. test = []
> I. test : List ℕ
> III. test : List Bool
> V. test : List Set

> b. test [] = 0
> test (x :: xs) = suc (test xs)
> I. test : ∀ {ℓ} {A : Set ℓ} → List A → ℕ

> c. test f g x = map g (map f x)
> I. ∀ {A B C : Set} → (A → B) → (B → C) → List A → List C
> II. ∀ {ℓ} {A : Set ℓ} → (A → A) → (A → A) → List A → List A
> V. ∀ {B : Set} {A : List B} → (A → B) → (B → B) → List A → List B

3. Define a polymorphic function takeWhile which takes in a predicate on
type A and a list of As, and returns the longest prefix of the list which
satisfies the predicate.
```agda
takeWhile : ∀ {ℓ} {A : Set ℓ} → (A → Bool) → List A → List A
takeWhile p [] = []
takeWhile p (x :: xs) with p x
... | True = x :: takeWhile p xs
... | False = []
```

4. Prove that if value a satisfies predicate p, then takeWhile p (repeat n a)
is equal to repeat n a
```agda
ex4 : ∀ {ℓ} {A : Set ℓ} (p : A → Bool) (a : A) (n : ℕ) 
  → p a ≡ True → takeWhile p (repeat n a) ≡ repeat n a
ex4 p a zero pa = refl
ex4 p a (suc n) pa rewrite pa | ex4 p a n pa = refl
```

5. Define a function take which takes in a natural number n and a list l, and
returns a list of the first n elements of l (in order), or all the elements if n
exceeds the length of the list.
```agda
take : ∀ {ℓ} {A : Set ℓ} → ℕ → List A → List A
take zero xs = []
take (suc n) [] = []
take (suc n) (x :: xs) = x :: take n xs
```

6. list.agda in the IAL already defines a similar function nthTail that re-
turns the part of the list after the first n elements, or the empty list if the list
has fewer than n elements. Prove that appending the result of take with the
result of nthTail for any n (the same value given to both functions) results
in the list again.
```agda
nthTail : ∀ {ℓ} {A : Set ℓ} → ℕ → List A → List A
nthTail zero xs = xs
nthTail (suc n) [] = []
nthTail (suc n) (x :: xs) = nthTail n xs

ex6 : ∀ {ℓ} {A : Set ℓ} (n : ℕ) (xs : List A) → (take n xs) ++ (nthTail n xs) ≡ xs
ex6 zero [] = refl
ex6 zero (x :: xs) = refl
ex6 (suc n) [] = refl
ex6 (suc n) (x :: xs) rewrite ex6 n xs = refl
```