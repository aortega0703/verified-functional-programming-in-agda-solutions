```agda
open import Definition.Equality
open import Definition.Bool
open import Definition.Nat
module Exercise.Chapter3 where
```

1. Pick a theorem from nat-thms.agda, and reprove it yourself.
```agda
*1 : ∀ (n : ℕ) → n * 1 ≡ n
*1 zero = refl
*1 (suc n) rewrite *1 n = refl
```

2. Prove <-trans and <+, but modified to use _>_ instead of _<_
```agda
_>_ : ℕ → ℕ → Bool
zero > zero = False
zero > suc n = False
suc m > zero = True
suc m > suc n = m > n

>-trans : ∀ {m n p : ℕ} → m > n ≡ True → n > p ≡ True → m > p ≡ True
>-trans {suc m} {suc n} {zero} m>n n>p = refl
>-trans {suc m} {suc n} {suc p} m>n n>p = >-trans {m} {n} {p} m>n n>p

+> : ∀ {x y : ℕ} → y =ℕ 0 ≡ False → (x + y) > x ≡ True
+> {zero} {suc y} y≠ℕ0 = refl
+> {suc x} {suc y} y≠ℕ0 = +> {x} {suc y} refl
```

3. What does the following function do?
(a).
```agda
f : ℕ → ℕ
f 0 = 1
f (suc n) = suc n * f n
```
> Computes factorial

(b).
```agda
f´ : ℕ → Bool
f´´ : (n : ℕ) → Bool

f´ 0 = True
f´ suc n = f´´ n

f´´ 0 = False
f´´ suc n = f´ n
```
> Test for even numbers