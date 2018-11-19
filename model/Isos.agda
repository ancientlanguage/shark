module Isos where

open import Agda.Builtin.Nat using () renaming (Nat to ℕ; zero to Z; suc to S)
open import Agda.Builtin.Equality

_∘_ : {A B C : Set} (g : B → C) (f : A → B) → (A → C)
(g ∘ f) x = g (f x)

data _+_ (A B : Set) : Set where
  inl : (a : A) → A + B
  inr : (b : B) → A + B
infixr 6 _+_

data _×_ (A B : Set) : Set where
  pair : (a : A) → (b : B) → A × B

data 𝕍 (A : Set) : ℕ → Set where
  nil : 𝕍 A Z
  cons : (a : A) → (n : ℕ) → 𝕍 A n → 𝕍 A (S n)

record Iso (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    idA : (a : A) → from (to a) ≡ a
    idB : (b : B) → to (from b) ≡ b

module General where
  compose : (A B C : Set) → Iso A B → Iso B C → Iso A C
  compose A B C
    record { to = a→b ; from = b→a ; idA = idA-AB ; idB = idB-AB }
    record { to = b→c ; from = c→b ; idA = idB-BC ; idB = idC-BC }
    =
    record { to = a→c ; from = c→a ; idA = idA-AC ; idB = idC-AC }
    where
    a→c : A → C
    a→c a = b→c (a→b a)

    c→a : C → A
    c→a c = b→a (c→b c)

    idA-AC : (a : A) → c→a (a→c a) ≡ a
    idA-AC a rewrite idB-BC (a→b a) = idA-AB a

    idC-AC : (c : C) → a→c (c→a c) ≡ c
    idC-AC c rewrite idB-AB (c→b c) = idC-BC c

  swap : (A B : Set) → Iso A B → Iso B A
  swap A B
    record { to = to ; from = from ; idA = idA ; idB = idB }
    =
    record { to = from ; from = to ; idA = idB ; idB = idA }

module SumIso where
  over-inl : (A B C : Set) → Iso A B → Iso (A + C) (B + C)
  over-inl A B C
    record { to = a→b ; from = b→a ; idA = idA-AB ; idB = idB-AB }
    =
    record { to = to ; from = from ; idA = idA ; idB = idB }
    where
    to : (x : A + C) → B + C
    to (inl a) = inl (a→b a)
    to (inr c) = inr c

    from : (x : B + C) → A + C
    from (inl b) = inl (b→a b)
    from (inr c) = inr c

    idA : (x : A + C) → from (to x) ≡ x
    idA (inl a) rewrite idA-AB a = refl
    idA (inr c) = refl

    idB : (x : B + C) → to (from x) ≡ x
    idB (inl b) rewrite idB-AB b = refl
    idB (inr c) = refl

  over-inr : (A B C : Set) → Iso A B → Iso (C + A) (C + B)
  over-inr A B C
    record { to = a→b ; from = b→a ; idA = idA-AB ; idB = idB-AB }
    =
    record { to = to ; from = from ; idA = idA ; idB = idB }
    where
    to : (x : C + A) → C + B
    to (inl c) = inl c
    to (inr a) = inr (a→b a)

    from : (x : C + B) → C + A
    from (inl c) = inl c
    from (inr b) = inr (b→a b)

    idA : (x : C + A) → from (to x) ≡ x
    idA (inl c) = refl
    idA (inr a) rewrite idA-AB a = refl

    idB : (x : C + B) → to (from x) ≡ x
    idB (inl c) = refl
    idB (inr b) rewrite idB-AB b = refl
  
module PairIso where
  over-fst : (A B C : Set) → Iso A B → Iso (A × C) (B × C)
  over-fst A B C
    record { to = a→b ; from = b→a ; idA = idA-AB ; idB = idB-AB }
    =
    record { to = to ; from = from ; idA = idA ; idB = idB }
    where
    to : (x : A × C) → B × C
    to (pair a b) = pair (a→b a) b

    from : (x : B × C) → A × C
    from (pair a b) = pair (b→a a) b

    idA : (x : A × C) → from (to x) ≡ x
    idA (pair a c) rewrite idA-AB a = refl

    idB : (x : B × C) → to (from x) ≡ x
    idB (pair b c) rewrite idB-AB b = refl

  over-snd : (A B C : Set) → Iso A B → Iso (C × A) (C × B)
  over-snd A B C
    record { to = a→b ; from = b→a ; idA = idA-AB ; idB = idB-AB }
    =
    record { to = to ; from = from ; idA = idA ; idB = idB }
    where
    to : (x : C × A) → C × B
    to (pair a b) = pair a (a→b b)

    from : (x : C × B) → C × A
    from (pair a b) = pair a (b→a b)

    idA : (x : C × A) → from (to x) ≡ x
    idA (pair c a) rewrite idA-AB a = refl

    idB : (x : C × B) → to (from x) ≡ x
    idB (pair c b) rewrite idB-AB b = refl

module Vec where
  map : (A B : Set) → (A → B) → (n : ℕ) → 𝕍 A n → 𝕍 B n
  map A B f .0 nil = nil
  map A B f .(S n) (cons a n x) = cons (f a) n (map A B f n x)

  module Props where
    map-id : (A : Set) (f : A → A) (f-id : (a : A) → f a ≡ a) (n : ℕ) (x : 𝕍 A n) → map A A f n x ≡ x
    map-id A f f-id .0 nil = refl
    map-id A f f-id .(S n) (cons a n x) rewrite f-id a | map-id A f f-id n x = refl

    map-compose : (A B C : Set) (f : A → B) (g : B → C) (n : ℕ) (x : 𝕍 A n) → map B C g n (map A B f n x) ≡ map A C (g ∘ f) n x
    map-compose A B C f g .0 nil = refl
    map-compose A B C f g .(S n) (cons a n x) rewrite map-compose A B C f g n x = refl

module VecIso where
  each : (A B : Set) → Iso A B → (n : ℕ) → Iso (𝕍 A n) (𝕍 B n)
  each A B
    record { to = a→b ; from = b→a ; idA = idA-AB ; idB = idB-AB }
    n
    =
    record { to = to ; from = from ; idA = idA ; idB = idB }
    where
    to : (x : 𝕍 A n) → 𝕍 B n
    to = Vec.map A B a→b n

    from : (x : 𝕍 B n) → 𝕍 A n
    from = Vec.map B A b→a n

    idA : (x : 𝕍 A n) → from (to x) ≡ x
    idA nil = refl
    idA (cons a n x) rewrite idA-AB a | Vec.Props.map-compose A B A a→b b→a n x | Vec.Props.map-id A (b→a ∘ a→b) idA-AB n x = refl

    idB : (x : 𝕍 B n) → to (from x) ≡ x
    idB nil = refl
    idB (cons b n x) rewrite idB-AB b | Vec.Props.map-compose B A B b→a a→b n x | Vec.Props.map-id B (a→b ∘ b→a) idB-AB n x = refl
