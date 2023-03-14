open import Definition.Level
open import Definition.Equality

module Definition.Product where

data Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  _,_ : (a : A) → (b : B a) → Σ A B

_×_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ x → B)

⟨_,_⟩ : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄}
         {A : Set ℓ₁}{B : Set ℓ₂}
         {C : Set ℓ₃}{D : Set ℓ₄}
       → (A → C)
       → (B → D)
       → (A × B → C × D)
⟨ f , g ⟩ (a , b) = f a , g b

fst : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A × B → A
fst (a , b) = a

snd : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A × B → B
snd (a , b) = b

keep : ∀{ℓ}{A : Set ℓ} → (x : A) → Σ A (λ y → x ≡ y)
keep x = ( x , refl )