```
module lecture-notes-Lists where
```

```
open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
```

# Lists

Agda provides Lisp-style lists, with nil and cons, spelled `[]` and `_∷_`.
For example:

```
open import Data.List using (List; []; _∷_; map; unzip)

_ : List ℕ
_ = 1 ∷ 2 ∷ []
```

Agda provides lots of standard functions on lists, such as append
(`_++_`), `map`, `foldr`, `foldl`, `zip`, `unzip`, `reverse`,
`splitAt`, and many more. The Agda standard library also provides many
theorems about these functions.  We shall study some examples that use
some of these functions and theorems.

Consider the operation that rotates the elements of a list to the left
by `k` positions, with wrap-around. For example,

    rotate (1 ∷ 2 ∷ 3 ∷ []) 2 ≡ (3 ∷ 1 ∷ 2 ∷ [])

One clever way to rotate a list is to split it into two parts, reverse
each part, append them, and then reverse again.

```
open import Data.List using (reverse; splitAt; _++_)

rotate : ∀ {A : Set} → List A → ℕ → List A
rotate xs k
    with splitAt k xs
... | ⟨ ls , rs ⟩ =
    let ls' = reverse ls in
    let rs' = reverse rs in
    reverse (ls' ++ rs')
```

Here are a few examples of `rotate` in action.

```
_ : rotate (1 ∷ 2 ∷ 3 ∷ []) 1 ≡ (2 ∷ 3 ∷ 1 ∷ [])
_ = refl

_ : rotate (1 ∷ 2 ∷ 3 ∷ []) 2 ≡ (3 ∷ 1 ∷ 2 ∷ [])
_ = refl

_ : rotate (1 ∷ 2 ∷ 3 ∷ []) 3 ≡ (1 ∷ 2 ∷ 3 ∷ [])
_ = refl
```

One way to think about `rotate` is in terms of swapping the part of
the list at the front with the rest of the list at the back. In the
following, the first three elements, `a , b , c`, are moved to the
back, swapping places with the `d , e`.

    rotate ([ a , b , c ] ++ [ d , e ]) 3
          ≡ [ d , e ] ++ [ a , b , c ]

With this view in mind, we prove that `rotate` is correct using some
equations from the Agda standard library about `reverse` and `append`.

```
open import Data.List.Properties using (reverse-++; reverse-involutive)

rotate-correct : ∀ {A : Set} {xs ys zs : List A} {k : ℕ}
   → splitAt k xs ≡ ⟨ ys , zs ⟩
   → rotate xs k ≡ zs ++ ys
rotate-correct {A}{xs}{ys}{zs} sk rewrite sk =
  begin
     reverse (reverse ys ++ reverse zs)   ≡⟨ cong reverse (sym (reverse-++ zs ys)) ⟩
     reverse (reverse (zs ++ ys))         ≡⟨ reverse-involutive (zs ++ ys) ⟩
     zs ++ ys
  ∎
```

Next consider a simplified version of the `map-compose` theorem from
the standard library. It says that mapping functions `f` then `g` over
a list is equivalent to mapping the composition `g ∘ f` over the list.

```
open import Function using (_∘_)

map-compose : ∀{A B C : Set}{g : B → C} {f : A → B}
              → (xs : List A)
              → map (g ∘ f) xs ≡ map g (map f xs)
map-compose []       = refl
map-compose (x ∷ xs) = cong (_ ∷_) (map-compose xs)
```

There are many more operations and theorems in the works of Richard
Bird concerning the interactions between lists, functions, pairs, and
sums. In the following we will introduce a couple of these operations
and prove some theorems about them.  To begin, we define the fork (`▵`)
and cross (`⊗`) functions.

```
_▵_ : ∀{A B C : Set} → (A → B) → (A → C) → A → B × C
(f ▵ g) a = ⟨ (f a) , (g a) ⟩

_⊗_ : ∀{A B C D : Set} → (A → B) → (C → D) → A × C → B × D
(f ⊗ g) ⟨ a , c ⟩ = ⟨ f a , g c ⟩
```

Recall that `unzip` converts a list of pairs `xs` into a pair of
lists.  One way to implement `unzip` is to 1) `map` the `proj₁`
function over `xs`, 2) `map` the `proj₂` over `xs` and 3) pair the two
resulting lists. This can be expressed using fork in the following
way.

```
unzip-slow : {A B : Set} → List (A × B) → List A × List B
unzip-slow xs = ((map proj₁) ▵ (map proj₂)) xs
```

This implementation of `unzip` is obviously correct but not very
efficient because it makes two passes over the list of pairs. The real
implementation is more clever and makes only a single pass over the
list of pairs, as shown below. (The `unzip` in the Agda standard
library is equivalent to the following `unzip-fast`, but it is
implemented in terms of a more general function named `unzipWith`.)

```
unzip-fast : {A B : Set} → List (A × B) → List A × List B
unzip-fast [] = ⟨ [] , [] ⟩
unzip-fast (⟨ a , b ⟩ ∷ xs) =
  let ⟨ as , bs ⟩ = unzip-fast xs in
  ⟨ a ∷ as , b ∷ bs ⟩
```

The fast and slow versions of `unzip` are equivalent, which is
straightforward to prove by induction on the input list `xs`.

```
unzip≡▵map : ∀{A B : Set}
           → (xs : List (A × B))
           → unzip xs ≡ ((map proj₁) ▵ (map proj₂)) xs
unzip≡▵map {A} {B} [] =  begin
  unzip []                    ≡⟨⟩
  ⟨ [] , [] ⟩                 ≡⟨⟩
  (map proj₁ ▵ map proj₂) []  ∎
unzip≡▵map {A} {B} (⟨ a , b ⟩ ∷ xs) =              begin
  unzip (⟨ a , b ⟩ ∷ xs)                           ≡⟨⟩
  ⟨ a ∷ proj₁ (unzip xs) , b ∷ proj₂ (unzip xs) ⟩  ≡⟨ cong₂ ⟨_,_⟩ IH1 IH2 ⟩
  ⟨ a ∷ map proj₁ xs , b ∷ map proj₂ xs ⟩          ≡⟨⟩
  (map proj₁ ▵ map proj₂) (⟨ a , b ⟩ ∷ xs)
  ∎
  where
  IH = unzip≡▵map xs
  IH1 = cong (λ □ → a ∷ (proj₁ □)) IH
  IH2 = cong (λ □ → b ∷ (proj₂ □)) IH
```

The cross of `map f` and `map g` commutes with `unzip` in the
following sense, which we prove with a direct equational proof.
(No induction needed.)

```
⊗-distrib-unzip : ∀{A B C D} {f : A → B} {g : C → D}
    → (xs : List (A × C))
    → (map f ⊗ map g) (unzip xs) ≡ unzip (map (f ⊗ g) xs)
⊗-distrib-unzip {A}{B}{C}{D}{f}{g} xs =                        begin
  (map f ⊗ map g) (unzip xs)                                   ≡⟨ cong (map f ⊗ map g) (unzip≡▵map xs) ⟩
  (map f ⊗ map g) (((map proj₁) ▵ (map proj₂)) xs)             ≡⟨⟩
  ⟨ (map f ∘ map proj₁) xs , (map g ∘ map proj₂) xs ⟩          ≡⟨ cong₂ ⟨_,_⟩ (sym (map-compose xs)) (sym (map-compose xs)) ⟩
  ⟨ map (f ∘ proj₁) xs , map (g ∘ proj₂) xs ⟩                  ≡⟨⟩
  ⟨ map (proj₁ ∘ (f ⊗ g)) xs , map (proj₂ ∘ (f ⊗ g)) xs ⟩      ≡⟨ cong₂ ⟨_,_⟩ (map-compose xs) (map-compose xs) ⟩ 
  ⟨ map proj₁ (map (f ⊗ g) xs) , map proj₂ (map (f ⊗ g) xs) ⟩  ≡⟨⟩ 
  (map proj₁ ▵ map proj₂) (map (f ⊗ g) xs)                     ≡⟨ sym (unzip≡▵map (map (f ⊗ g) xs)) ⟩ 
  unzip (map (f ⊗ g) xs)                                       ∎
```
The above proof proceeds as follows.
1. Apply `unzip≡▵map` to replace `unzip` with a fork and two maps.
2. To get `xs` next to the maps, we unfold the definition of fork .
3. To fuse `f` and `proj₁` on the  left and `g` and `proj₂` on the right,
   we apply `map-compose` in reverse.
4. Use the definition of cross to change `f ∘ proj₁` into
   `proj₁ ∘ (f ⊗ g)`, and similarly for `g ∘ proj₂`.
5. Apply `map-compose`, separating `proj₁` from `f ⊗ g` on the
   left and `proj₂` from `f ⊗ g` on the right.
6. Apply `unzip≡▵map` a second time, in reverse,
   to replace the fork and two maps with `unzip`.

