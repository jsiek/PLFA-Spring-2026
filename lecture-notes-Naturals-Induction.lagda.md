```
module lecture-notes-Naturals-Induction where
```

# Naturals

Concepts: datatype definitions, constructors, `Set`.

```
data Nat : Set where
  zero : Nat
  suc : Nat → Nat
```

Here are some natural numbers:

```
one = suc zero
two = suc (suc zero)
```

The main way to eliminate a datatype in Agda is to define a function
on it. Often, the function is recursive.

```
add : Nat → Nat → Nat
add zero n = n
add (suc m) n = suc (add m n)
```

```
three = add two one
```

To talk about equality we import Agda's `≡` operator.

```
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

To prove that something is equal to itself, use `refl`.

```
_ : add two one ≡ suc (suc (suc zero))
_ = refl
```

The Agda standard library defines a data type for natural numbers, named
`ℕ`, just like the definition above.

```
open import Data.Nat
```

Let's define another recursive function that you may be familiar with,
the sum of the numbers up to a given number `n`.

```
gauss : ℕ → ℕ
gauss zero = 0
gauss (suc n) = suc n + gauss n
```

## Proofs about all the naturals numbers

To prove something about all the natural numbers,
such as 

    x + y + x ≡ 2 * x + y

for all x and y, your plan A should be to try and prove
it using the laws of algebra, which are provided in the Agda
standard library.

```
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
```

The Agda standard library module
[Data.Nat.Properties](https://agda.github.io/agda-stdlib/v2.3/Data.Nat.Properties.html)
includes proofs for many of the laws of algebra for natural numbers.
Some of those laws refer to names, such as `RightIdentity`, that are
defined in the module 
[Algebra.Definitions](https://agda.github.io/agda-stdlib/v2.3/Algebra.Definitions.html).

```
_ : (x : ℕ) → (y : ℕ) → x + y + x ≡ 2 * x + y
_ = λ x y → 
  begin
    (x + y) + x
  ≡⟨ +-assoc x y x ⟩
    x + (y + x)
  ≡⟨ cong (λ □ → x + □) (+-comm y x) ⟩
    x + (x + y)
  ≡⟨ sym (+-assoc x x y) ⟩
    (x + x) + y
  ≡⟨ cong (λ □ → (x + □) + y) (sym (+-identityʳ x)) ⟩
    (x + (x + zero)) + y
  ≡⟨ refl ⟩
    2 * x + y
  ∎
```

If the equation only involves simple reasoning about addition and
multiplication, you can instead use Agda's automatic solver.

```
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

_ : (x : ℕ) → (y : ℕ) → x + y + x ≡ 2 * x + y
_ = solve 2 (λ x y → x :+ y :+ x := con 2 :* x :+ y) refl
```

The recipe for using the solver is that the first argument is the
number of variables mentioned in the equation, the second argument is
a function of those variables that produces an encoding of the
equation. Put a colon in front of each `+` and `*` and replace `≡` with
`:=`.  Also, put `con` in front of each constant, e.g., change `2` to
`con 2`. The third argument has something to do with how to prove the
leftover equations that the solver couldn't prove. Usually `refl`
works. If it doesn't, good luck to you!


# Induction

If you don't see a way to prove something about all the natural
numbers using the laws of algebra, then your plan B should be to use
induction.

Such situations often arise when you need to prove something about a
function that you have defined. For example, consider the following
silly example of a recursive function that doubles its input.

```
dub : ℕ → ℕ
dub 0 = 0
dub (suc n) = suc (suc (dub n))
```

We prove that `dub` is correct by induction. That is, we write a
recursive function that takes an integer and returns a proof that

    dub n ≡ n + n

The easiest part of a proof-by-induction is the base case, that is,
for zero. If you have trouble with the base case, there's a good
chance that what you're trying to prove is actually false.

The high-point of a proof-by-induction is the use of the induction
hypothesis (IH), that is, when we make a recursive call. Sometimes we
need to do some reasoning before using the induction hypothesis and
sometimes we do some reasoning afterwards.

```
dub-correct : (n : ℕ) → dub n ≡ n + n
dub-correct zero = refl
dub-correct (suc n) =
  let IH = dub-correct n in
  begin
    suc (suc (dub n))
  ≡⟨ cong (λ □ → suc (suc □)) IH ⟩
    suc (suc (n + n))
  ≡⟨ cong suc (sym (+-suc n n)) ⟩
    suc (n + suc n)
  ∎
```

As a second example, let's prove the formula of Gauss for the sum of
the first `n` natural numbers. Division on natural numbers can be a
bit awkward to work with, so we'll instead multiply the left-hand side
by `2`.

```
gauss-formula : (n : ℕ) → 2 * gauss n ≡ n * suc n
gauss-formula zero = refl
gauss-formula (suc n) =
  let IH : 2 * gauss n ≡ n * suc n
      IH = gauss-formula n in
  begin
    2 * gauss (suc n)
  ≡⟨ refl ⟩
    2 * (suc n + gauss n)
  ≡⟨ *-distribˡ-+ 2 (suc n) (gauss n) ⟩
    2 * (suc n) + 2 * gauss n
  ≡⟨ cong (λ □ → 2 * (suc n) + □) IH ⟩
    2 * (suc n) + n * (suc n)
  ≡⟨ EQ n ⟩
    (suc n) * suc (suc n)
  ∎
  where
  EQ = solve 1 (λ n → (con 2 :* (con 1 :+ n)) :+ (n :* (con 1 :+ n))
         := (con 1 :+ n) :* (con 1 :+ (con 1 :+ n))) refl
```

* The base case is trivial, indeed `2 * 0 ≡ 0 * suc 0`.

* For the induction step, we need to show that

        2 * gauss (suc n) ≡ (suc n) * suc (suc n)

    In the above chain of equations, we expand the
    definition for `gauss (suc n)`, distribute the multiplication
    by `2`, and then apply the induction hypothesis,
    which states that `2 * gauss n ≡ n * suc n`.
    The last step is some simple reasoning about addition and
    multiplication, which is handled by Agda's automatic solver.


