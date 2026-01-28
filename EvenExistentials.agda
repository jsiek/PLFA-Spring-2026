open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Product using (Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

-- The inductive definition from the "Relations" lecture
data Even : ℕ → Set where
  even-0 : Even 0
  even-+2 : (n : ℕ) → Even n → Even (2 + n)

-- Our new definition using existentials
Ev : ℕ → Set
Ev n = ∃[ m ] (2 * m ≡ n)

-- The two definitions are equivalent
Ev→Even : ∀ n → Ev n → Even n
Ev→Even n ⟨ zero , refl ⟩ = even-0
Ev→Even n ⟨ suc m , 2m=n ⟩ rewrite +-identityʳ m | +-comm m (suc m) | sym 2m=n =
  even-+2 _ (Ev→Even _ ⟨ m , cong (m +_) (+-identityʳ m) ⟩)

Even→Ev : ∀ n → Even n → Ev n
Even→Ev n even-0 = ⟨ 0 , refl ⟩
Even→Ev 2+n (even-+2 n even)
  with Even→Ev n even
... | ⟨ m , 2m=n ⟩ = ⟨ suc m , cong suc m+[1+m]=1+n ⟩
  where
  m+[1+m]=1+n : m + suc (m + 0) ≡ suc n
  m+[1+m]=1+n rewrite +-suc m (m + 0) | 2m=n = refl
