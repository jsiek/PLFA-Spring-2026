```
module lecture-notes-Equality where
```

```
open import Data.Nat
open import Data.Nat.Properties
open import lecture-notes-Relations
```

# Equality

`≡` is just a relation defined as a data type, as in the above examples.

It has one constructor named `refl` that says anything is equal to
itself.

## `≡` is an equivalence relation and a congruence

```
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
```

Example of `refl`:

```
0≡0+0 : 0 ≡ 0 + 0
0≡0+0 = refl
```

Example of `sym`:

```
0+0≡0 : 0 + 0 ≡ 0
0+0≡0 = sym 0≡0+0
```

Example of `cong`:

```
0+0≡0+0+0 : 0 + 0 ≡ 0 + (0 + 0)
0+0≡0+0+0 = cong (λ □ → 0 + □) 0≡0+0
```

Example of `trans`:

```
0≡0+0+0 : 0 ≡ 0 + 0 + 0
0≡0+0+0 = trans 0≡0+0 0+0≡0+0+0
```

## `subst`

  Example:

```
open import Relation.Binary.PropositionalEquality using (subst)

even-dub' : (n m : ℕ) → m + m ≡ n → Even n
even-dub' n m eq = subst (λ □ → Even □) eq (even-dub m)
```

## Chains of equations

```
open Relation.Binary.PropositionalEquality.≡-Reasoning
```

```
_ : 0 ≡ 0 + 0 + 0
_ =
  begin
  0            ≡⟨ 0≡0+0 ⟩
  0 + 0        ≡⟨ 0+0≡0+0+0 ⟩
  0 + 0 + 0
  ∎
```

## Rewriting

  Revisiting the proof of `even-dub'`, using `rewrite`
  instead of `subst`.

```
even-dub'' : (n m : ℕ) → m + m ≡ n → Even n
even-dub'' n m eq rewrite (sym eq) = even-dub m
```


# Isomorphism

Two types `A` and `B` are *isomorphic* if there exist a pair of
functions that map back and forth between the two types, and doing a
round trip starting from either `A` or `B` brings you back to where
you started, that is, composing the two functions in either order is
the identity function.

```
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
```

## Example: products are commutative upto isomorphism.

(Note that we're using implicit parameters for the first time.)

```
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

×-comm : ∀{A B : Set} → A × B ≃ B × A
×-comm =
  record {
    to = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ } ;
    from = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ } ;
    from∘to = λ { ⟨ x , y ⟩ → refl }  ;
    to∘from = λ { ⟨ x , y ⟩ → refl } }
```

## Example: `((A → B) × (A → B) ≃ ((A × Bool) → B))`

Two functions can always be merged into a single function
with an extra Boolean parameter. The proof of this isomorphism
requires the principle of extensionality.

```
open import Data.Bool using (Bool; true; false)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

_ : ∀{A B : Set} → ((A → B) × (A → B) ≃ ((A × Bool) → B))
_ = record {
      to = λ { fg ⟨ a , true ⟩ → proj₁ fg a ;
               fg ⟨ a , false ⟩ → proj₂ fg a };
      from = λ h → ⟨ (λ a → h ⟨ a , true ⟩) , (λ a → h ⟨ a , false ⟩) ⟩ ;
      from∘to = λ fg → refl ;
      to∘from = λ h → extensionality λ { ⟨ a , true ⟩ → refl ; ⟨ a , false ⟩ → refl } }
```

## Example: ℕ is isomorphic to the even numbers.

Here is another definition of the even numbers.

```
data IsEven : ℕ → Set where
  is-even : ∀ n m → n ≡ m + m → IsEven n
```

We define the type `Evens` as a wrapper around the even numbers
that combines the number with a proof that it is even.

```
data Evens : Set where
  even : (n : ℕ) → (IsEven n) → Evens
```

We convert from natural numbers to evens by multiplying by 2.  Going
the other way, it is tempting to divide by 2 using the operator
`⌊_/2⌋`. However, a simpler approach is to recognize that a value of
`Evens` carries with it a witness `m` that is half of `n`, so we can
just return `m`.

```
ℕ≃Evens : ℕ ≃ Evens
ℕ≃Evens =
  record {
    to = λ n → even (n + n) (is-even (n + n) n refl) ;
    from = λ { (even n (is-even n m refl)) → m } ;
    from∘to = λ x → refl ;
    to∘from = λ { (even n (is-even n m refl)) → refl } }
```

