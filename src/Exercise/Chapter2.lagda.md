```
module Exercise.Chapter2 where

open import Definition.Bool
open import Definition.Equality
```

1. Pick a theorem from bool-thms.agda or bool-thms2.agda, and reprove
it yourself.
```agda
∧-elim1 : ∀ {b1 b2 : Bool} → b1 ∧ b2 ≡ True → b1 ≡ True
∧-elim1 {True} {True} b1∧b2 = refl
∧-elim1 {True} {False} ()
```

2. Think of a theorem about the boolean operations that is missing from the
IAL (i.e., from bool-thms.agda and bool-thms2.agda), and prove it.
```agda
em⇒nne : ∀ {b : Bool} → b ∨ ¬ b ≡ True → (¬ ¬ b ≡ b)
em⇒nne {True} em = refl
em⇒nne {False} em = refl
```

3. Which of the following formulas could be proved by refl (there may be
several correct answers)?
(a) tt ≡ tt
  Yes
(b) ff ≡ ff
  Yes
(c) ff ≡ tt
  No
(d) ff && ff ≡ ˜ tt
  Yes
(e) tt && x ≡ x, where x is a variable of type B
  Yes
(f) x && tt ≡ x, where x is a variable of type B
  Yes