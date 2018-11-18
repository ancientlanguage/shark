module Isos where

open import Agda.Builtin.Nat using () renaming (Nat to ℕ; zero to Z; suc to S)
open import Agda.Builtin.Equality

data 𝕍 (A : Set) : ℕ → Set where
  nil : 𝕍 A Z
  cons : (a : A) → (n : ℕ) → 𝕍 A n → 𝕍 A (S n)

data _+_ (A B : Set) : Set where
  inl : (a : A) → A + B
  inr : (b : B) → A + B
infixr 6 _+_

data _*_ (A B : Set) : Set where
  pair : (a : A) → (b : B) → A * B

record Iso (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    idA : (a : A) → from (to a) ≡ a
    idB : (b : B) → to (from b) ≡ b

module Isos where
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
