module Definition.Nat where
open import Definition.Equality
open import Definition.Bool

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

0+ : ∀ (n : ℕ) → 0 + n ≡ n
0+ n = refl

+0 : ∀ (n : ℕ) → n + 0 ≡ n
+0 zero = refl
+0 (suc n) rewrite +0 n = refl

+assoc : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
+assoc zero n p = refl
+assoc (suc m) n p rewrite +assoc m n p = refl

+suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+suc zero n = refl
+suc (suc m) n rewrite +suc m n = refl

+comm : ∀ (m n : ℕ) → m + n ≡ n + m
+comm zero n rewrite 0+ n | +0 n = refl
+comm (suc m) n rewrite +comm m n | +suc n m = refl

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

*distribr : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*distribr zero n p = refl
*distribr (suc m) n p rewrite *distribr m n p = +assoc p (m * p) (n * p)

*0 : ∀ (m : ℕ) → m * 0 ≡ zero
*0 zero = refl
*0 (suc m) rewrite *0 m = refl

*suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*suc zero n = refl
*suc (suc m) n 
  rewrite 
      *suc m n 
    | +assoc n m (m * n) 
    | +comm n m 
    | +assoc m n (m * n) = refl

*comm : ∀ (m n : ℕ) → m * n ≡ n * m
*comm zero n rewrite *0 n = refl
*comm (suc m) n rewrite *suc n m | *comm m n = refl

*assoc : ∀ (m n p : ℕ) → m * (n * p) ≡ (m * n) * p
*assoc zero n p = refl
*assoc (suc m) n p rewrite *distribr n (m * n) p | *assoc m n p = refl

_≤_ : ℕ → ℕ → Bool
zero ≤ zero = True
zero ≤ suc n = True
suc m ≤ zero = False
suc m ≤ suc n = m ≤ n

≤-trans : ∀ {x y z : ℕ} → x ≤ y ≡ True → y ≤ z ≡ True → x ≤ z ≡ True
≤-trans {zero} {zero} {zero} x≤y y≤z = refl
≤-trans {zero} {zero} {suc z} x≤y y≤z = refl
≤-trans {zero} {suc y} {suc z} x≤y y≤z = refl
≤-trans {suc x} {suc y} {suc z} x≤y y≤z = ≤-trans {x} {y} {z} x≤y y≤z

≤-suc : ∀ {x : ℕ} → x ≤ suc x ≡ True
≤-suc {zero} = refl
≤-suc {suc n} = ≤-suc {n}

_<_ : ℕ → ℕ → Bool
zero < zero = False
zero < suc n = True
suc m < zero = False
suc m < suc n = m < n

<-trans : ∀ {x y z : ℕ} → x < y ≡ True → y < z ≡ True → x < z ≡ True
<-trans {zero} {suc y} {suc z} x<y y<z = refl
<-trans {suc x} {suc y} {suc z} x<y y<z = <-trans {x} {y} {z} x<y y<z

_=ℕ_ : ℕ → ℕ → Bool
zero =ℕ zero = True
zero =ℕ suc n = False
suc m =ℕ zero = False
suc m =ℕ suc n = m =ℕ n

=ℕ-refl : ∀ (m : ℕ) → m =ℕ m ≡ True
=ℕ-refl zero = refl
=ℕ-refl (suc m) = =ℕ-refl m

=ℕ-to-≡ : ∀ {x y : ℕ} → x =ℕ y ≡ True → x ≡ y
=ℕ-to-≡ {zero} {zero} x=ℕy = refl
=ℕ-to-≡ {suc x} {suc y} x=ℕy rewrite =ℕ-to-≡ {x} {y} x=ℕy = refl

=ℕ-from-≡ : ∀ {x y : ℕ} → x ≡ y → x =ℕ y ≡ True
=ℕ-from-≡ {x} {y} x≡y rewrite x≡y = =ℕ-refl y 