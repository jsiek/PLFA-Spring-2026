```
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation using (contradiction)
```

# Quantifiers

## Universal quantification

As we have seen, universal quantification ("for all") is represented
using dependent function types.

We use (eliminate) a dependent function simply by applying it.

```
postulate Human : Set
postulate Mortal : Human → Set
postulate Socrates : Human
-- postulate all-Humans-mortal : (p : Human) → Mortal p
-- Alternatively
postulate all-Humans-mortal : ∀ p → Mortal p

socrates-is-mortal : Mortal Socrates
socrates-is-mortal = all-Humans-mortal Socrates
```

We can prove a universally quantified formula by writing a function of
the appropriate type.

```
*-0ʳ : ∀ (n : ℕ) → n * 0 ≡ 0
*-0ʳ n rewrite *-comm n 0 = refl
```

As another example, let's prove that universals distribute with disjunction.

```
∀-dist-⊎ : ∀ {P : Set} {Q R : P → Set}
    → (∀ x → Q x) ⊎ (∀ x → R x)
      ------------------------------
    → (∀ x → Q x ⊎ R x)
∀-dist-⊎ (inj₁ ∀x→Qx) x = let Qx = ∀x→Qx x in inj₁ Qx
∀-dist-⊎ (inj₂ ∀x→Rx) x = let Rx = ∀x→Rx x in inj₂ Rx
```

## Existential quantification

Existential quantification is represented using dependent product types.
In a dependent product type, the type of the second part can refer to
the first part.

Normal product type:

   A × B

Dependent product type:

  Σ[ x ∈ A ] B x

The values of dependent product types are good old pairs: ⟨ v₁ , v₂ ⟩
where v₁ : A and v₂ : B v₁.

∃ x. P x

Σ[ x ∈ ℕ ] P x

To express "there exists", the witness of the existential is the first
part of the pair. The type of the second part of the pair is some
formula involving the first part, and the value in the second part of
the pair is a proof of that formula.

```
open import Data.Product using (Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
```

The following example implements a disjoint union type `A or B` using
a dependent pair.
The first part is a tag, false or true, that says whether the payload
(the second part) has type `A` or type `B`.

```
open import Data.Bool using (Bool; true; false)

select : (A : Set) → (B : Set) → Bool → Set
select A B false = A
select A B true = B

_or_ : Set → Set → Set
A or B = Σ[ flag ∈ Bool ] select A B flag

forty-two : ℕ or (ℕ → ℕ)
forty-two = ⟨ false , 42 ⟩

inc : ℕ or (ℕ → ℕ)
inc = ⟨ true , suc ⟩

inject₁ : ∀{A B : Set} → A → A or B
inject₁ a = ⟨ false , a ⟩

inject₂ : ∀{A B : Set} → B → A or B
inject₂ b = ⟨ true , b ⟩

case : ∀{A B C : Set} → A or B → (A → C) → (B → C) → C
case ⟨ false , a ⟩ ac bc = ac a
case ⟨ true , b ⟩ ac bc = bc b

_ : 42 ≡ case forty-two (λ n → n) (λ f → f 0)
_ = refl

_ : 1 ≡ case inc (λ n → n) (λ f → f 0)
_ = refl
```

Let's reason about currying: A × B → C ⇔ A → B → C

Σ[ x ∈ A ] B x → C ⇔ (x : A) → B x → C

```
∀∃-currying1 : ∀ {A : Set} {B : A → Set} {C : Set}
  → ((x : A) → B x → C)
    ------------------------
  → (Σ[ x ∈ A ] B x) → C
∀∃-currying1 f ⟨ x , y ⟩ = f x y

∀∃-currying2 : ∀ {A : Set} {B : A → Set} {C : Set}
  → ((Σ[ x ∈ A ] B x) → C)
    ---------------------------
  → ((x : A) → B x → C)
∀∃-currying2 f x Bx = f ⟨ x , Bx ⟩
```

Let's look at another example of defining the "devides evenly"
relation using existentials.

Recall the following definition using an inductive datatype and addition:

```
data _div_ : ℕ → ℕ → Set where
  div-refl : (m : ℕ) → m ≢ 0 → m div m
  div-step : (n m : ℕ) → m div n → m div (m + n)

-- Alternatively:
-- open import lecture-notes-Relations using (_div_; div-refl; div-step)
```

An alternative way to state that a number evenly divides another
number is using multiplication instead of repeated addition.
We shall prove that if `m div n`, then there exists some number `k`
such that `k * m ≡ n`.

To express "there exists some number `k` such that `k * m ≡ n`",
we can use the following dependent produce type

    Σ[ k ∈ ℕ ] k * m ≡ n (or equivalently, ∃[ k ] k * m ≡ n)

where `k` is a name for the first part of the pair, `ℕ` is it's type,
and `k * m ≡ n` is the type for the second part of the pair.

We prove that the two definitions are equivalent.

```
_div′_ : ℕ → ℕ → Set
m div′ n = m ≢ 0 × ∃[ k ] (k ≢ 0 × k * m ≡ n)

m-div-k*m : ∀ (k m : ℕ) → m ≢ 0 → k ≢ 0 → m div (k * m)
m-div-k*m zero m m≠0 k≠0 = contradiction refl k≠0
m-div-k*m (suc zero) m m≠0 k≠0 rewrite +-identityʳ m = div-refl m m≠0
m-div-k*m (2+ k) m m≠0 k≠0 =
  let iH = m-div-k*m (suc k) m m≠0 (λ ()) in
  div-step _ m iH

div′→div : ∀ (m n : ℕ) → m div′ n → m div n
div′→div m n ⟨ n≠0 , ⟨ zero , ⟨ k≠0 , k*m=n ⟩ ⟩ ⟩ = contradiction refl k≠0
div′→div m n ⟨ n≠0 , ⟨ suc k , ⟨ k≠0 , k*m=n ⟩ ⟩ ⟩ rewrite sym k*m=n =
  -- nts m div ((1 + k) * m)
  -- prove lemma: ∀ k. m div k * m
  m-div-k*m (suc k) m n≠0 (λ ())

div→div′ : ∀ (m n : ℕ) → m div n → m div′ n
div→div′ m n (div-refl .m m≠0) = ⟨ m≠0 , ⟨ 1 , ⟨ (λ ()) , +-identityʳ m ⟩ ⟩ ⟩
-- the dot is for inaccessible pattern
div→div′ m m+n (div-step n m mdivn)
  with div→div′ m n mdivn
... | ⟨ m≠0 , ⟨ k , ⟨ k≠0 , k*m=n ⟩ ⟩ ⟩ = ⟨ m≠0 , ⟨ suc k , ⟨ (λ ()) , cong (m +_) k*m=n ⟩ ⟩ ⟩

infix 0 _⇔_

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

div⇔div′ : ∀ {m n} → m div n ⇔ m div′ n
div⇔div′ {m} {n} = record {
    to   = div→div′ m n ;
    from = div′→div m n
  }
```


# Decidable

An alternative way to represent a relation is Agda is with the relation's
characteristic function. That is, a function that takes the two elements and
returns true or false, depending on whether the elements are in the relation.

```
less-eq : ℕ → ℕ → Bool
less-eq zero    n       = true
less-eq (suc m) zero    = false
less-eq (suc m) (suc n) = less-eq m n

_ : less-eq 3 5 ≡ true
_ = refl
```

Such a function also serves as a decision procedure. However, for some
relations it is difficult or even impossible to come up with such a function.

Sometimes it's nice to be able to link your decision procedure to the relation
defined by a data type, thereby building the correctness of your decision
procedure into its type. The `Dec` type includes both the true or false
(whether the relation holds for the input) *and* a proof that it holds or
that its negation holds.

```
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (_≤_)

less-eq? : (m n : ℕ) → Dec (m ≤ n)
less-eq? m n = {!!}

minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m
```
