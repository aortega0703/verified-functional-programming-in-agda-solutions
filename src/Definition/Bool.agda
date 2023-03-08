module Definition.Bool where

data Bool : Set where
  True False : Bool

infix 7 ¬_
infixl 6 _xor_ _nand_ _⇒_
infixr 6 _∧_
infixr 5 _∨_
infixr 4 _⇔_

_nand_ : Bool → Bool → Bool
True nand True = False
True nand False = True
False nand True = True
False nand False = True

¬_ : Bool → Bool
¬ b = b nand b

_∧_ : Bool → Bool → Bool
a ∧ b = ¬ (a nand b)

_∨_ : Bool → Bool → Bool
a ∨ b = ¬ (¬ a ∧ ¬ b)

_⇔_ : Bool → Bool → Bool
a ⇔ b = (a ∧ b) ∨ (¬ a ∧ ¬ b)

_xor_ : Bool → Bool → Bool
a xor b = ¬ (a ⇔ b)

_⇒_ : Bool → Bool → Bool
a ⇒ b = ¬ a ∨ b

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if True then x else y = x
if False then x else y = y