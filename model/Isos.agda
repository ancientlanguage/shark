module Isos where

open import Agda.Builtin.Nat using () renaming (Nat to ℕ; zero to Z; suc to S)
open import Agda.Builtin.Equality

_∘_ : {A B C : Set} (g : B → C) (f : A → B) → (A → C)
(g ∘ f) x = g (f x)

cong : {A B : Set} (f : A → B) (x y : A) (p : x ≡ y) → f x ≡ f y
cong _ _ _ refl = refl

data 𝟘 : Set where

record 𝟙 : Set where
  constructor <>

data R+ : (nl nr n : ℕ) → Set where
  rz : R+ Z Z Z
  rsl : (nl nr n : ℕ) (r : R+ nl nr n) → R+ (S nl) nr (S n)
  rsr : (nl nr n : ℕ) (r : R+ nl nr n) → R+ nl (S nr) (S n)

module Nat where
  injs : (m n : ℕ) (p : S m ≡ S n) → m ≡ n
  injs m n refl = refl

module NatSum where
  zerol : (nr n : ℕ) (r : R+ Z nr n) → nr ≡ n
  zerol Z Z rz = refl
  zerol (S nr) (S n) (rsr .0 .nr .n r) = cong S nr n (zerol nr n r)

  zeror : (nl n : ℕ) (r : R+ nl Z n) → nl ≡ n
  zeror .0 .0 rz = refl
  zeror .(S nl) .(S n) (rsl nl .0 n r) = cong S nl n (zeror nl n r)

  sum-zerol : (nl nr : ℕ) (r : R+ nl nr Z) → nl ≡ Z
  sum-zerol .0 .0 rz = refl

  sum-zeror : (nl nr : ℕ) (r : R+ nl nr Z) → nr ≡ Z
  sum-zeror .0 .0 rz = refl

  module NatPlus where
    open import Agda.Builtin.Nat using () renaming (_+_ to _+ₙ_)
    swaps : (nl nr n : ℕ) (p : S nl +ₙ nr ≡ n) → nl +ₙ S nr ≡ n
    swaps Z nr n p = p
    swaps (S nl) nr (S n) p = cong S (nl +ₙ S nr) n (swaps nl nr n (Nat.injs (S (nl +ₙ nr)) n p))

    matches : (nl nr n : ℕ) (r : R+ nl nr n) → nl +ₙ nr ≡ n
    matches .0 .0 .0 rz = refl
    matches .(S nl) nr .(S n) (rsl nl .nr n r) = cong S (nl +ₙ nr) n (matches nl nr n r)
    matches nl .(S nr) .(S n) (rsr .nl nr n r) = swaps nl nr (S n) (cong S (nl +ₙ nr) n (matches nl nr n r))

data _+_ (A B : Set) : Set where
  inl : (a : A) → A + B
  inr : (b : B) → A + B
infixr 6 _+_

data _×_ (A B : Set) : Set where
  pair : (a : A) (b : B) → A × B

data 𝕃 (A : Set) : Set where
  nil : 𝕃 A
  cons : (a : A) (x : 𝕃 A) → 𝕃 A

data 𝕍 (A : Set) : ℕ → Set where
  nil : 𝕍 A Z
  cons : (a : A) (n : ℕ) (v : 𝕍 A n) → 𝕍 A (S n)

data 𝕍+ (A B : Set) : (nl nr n : ℕ) → Set where
  nil : 𝕍+ A B Z Z Z
  consl : (a : A) (nl nr n : ℕ) (v : 𝕍+ A B nl nr n) → 𝕍+ A B (S nl) nr (S n)
  consr : (b : B) (nl nr n : ℕ) (v : 𝕍+ A B nl nr n) → 𝕍+ A B nl (S nr) (S n)

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

record 𝕍R (A : Set) : Set where
  field
    len : ℕ
    vec : 𝕍 A len

record 𝕍+R (A B : Set) : Set where
  field
    lenl lenr len : ℕ
    vec : 𝕍+ A B lenl lenr len

module Vec+ where
  plus-rel : (A B : Set) (nl nr n : ℕ) → 𝕍+ A B nl nr n → R+ nl nr n
  plus-rel A B .0 .0 .0 nil = rz
  plus-rel A B .(S nl) nr .(S n) (consl a nl .nr n v) = rsl nl nr n (plus-rel A B nl nr n v)
  plus-rel A B nl .(S nr) .(S n) (consr b .nl nr n v) = rsr nl nr n (plus-rel A B nl nr n v)

module ListVec {A : Set} where
  index-cons : A → 𝕍R A → 𝕍R A
  index-cons a record { len = len ; vec = vec } = record { len = S len ; vec = cons a _ vec }

  index : 𝕃 A → 𝕍R A
  index nil = record { len = Z ; vec = nil }
  index (cons a x) = index-cons a (index x)

  forget-cons : A → 𝕃 A → 𝕃 A
  forget-cons a x = cons a x

  forget : 𝕍R A → 𝕃 A
  forget record { len = .0 ; vec = nil } = nil
  forget record { len = .(S n) ; vec = (cons a n vec) } = forget-cons a (forget record { len = _ ; vec = vec })

  iso : Iso (𝕃 A) (𝕍R A)
  iso = record { to = index ; from = forget ; idA = idA ; idB = idB }
    where
    idA : (x : 𝕃 A) → forget (index x) ≡ x
    idA nil = refl
    idA (cons a x) = cong (cons a) _ _ (idA x)

    idB : (x : 𝕍R A) → index (forget x) ≡ x
    idB record { len = .0 ; vec = nil } = refl
    idB record { len = .(S n) ; vec = (cons a n vec) } rewrite idB record { len = n ; vec = vec } = refl

module VecSum (A B : Set) where
  index-consl : A → 𝕍+R A B → 𝕍+R A B
  index-consl a record { lenl = lenl ; lenr = lenr ; len = len ; vec = vec } = record { lenl = _ ; lenr = _ ; len = _ ; vec = consl a _ _ _ vec }

  index-consr : B → 𝕍+R A B → 𝕍+R A B
  index-consr b record { lenl = lenl ; lenr = lenr ; len = len ; vec = vec } = record { lenl = _ ; lenr = _ ; len = _ ; vec = consr b _ _ _ vec }

  index : 𝕍R (A + B) → 𝕍+R A B
  index record { len = .0 ; vec = nil } = record { lenl = Z ; lenr = Z ; len = Z ; vec = nil }
  index record { len = .(S n) ; vec = (cons (inl a) n vec) } = index-consl a (index record { len = _ ; vec = vec })
  index record { len = .(S n) ; vec = (cons (inr b) n vec) } = index-consr b (index record { len = _ ; vec = vec })

  forget-cons : (A + B) → 𝕍R (A + B) → 𝕍R (A + B)
  forget-cons x record { len = len ; vec = vec } = record { len = _ ; vec = cons x _ vec }

  forget : 𝕍+R A B → 𝕍R (A + B)
  forget record { lenl = .0 ; lenr = .0 ; len = .0 ; vec = nil } = record { len = _ ; vec = nil }
  forget record { lenl = .(S nl) ; lenr = lenr ; len = .(S n) ; vec = (consl a nl .lenr n vec) } = forget-cons (inl a) (forget record { lenl = _ ; lenr = _ ; len = _ ; vec = vec})
  forget record { lenl = lenl ; lenr = .(S nr) ; len = .(S n) ; vec = (consr b .lenl nr n vec) } = forget-cons (inr b) (forget record { lenl = _ ; lenr = _ ; len = _ ; vec = vec})

  iso : Iso (𝕍R (A + B)) (𝕍+R A B)
  iso = record { to = index ; from = forget ; idA = idA ; idB = idB }
    where
    idA : (a : 𝕍R (A + B)) → forget (index a) ≡ a
    idA record { len = .0 ; vec = nil } = refl
    idA record { len = .(S n) ; vec = (cons (inl a) n vec) } rewrite idA record { len = _ ; vec = vec } = refl
    idA record { len = .(S n) ; vec = (cons (inr b) n vec) } rewrite idA record { len = _ ; vec = vec } = refl

    idB : (b : 𝕍+R A B) → index (forget b) ≡ b
    idB record { lenl = .0 ; lenr = .0 ; len = .0 ; vec = nil } = refl
    idB record { lenl = .(S nl) ; lenr = lenr ; len = .(S n) ; vec = (consl a nl .lenr n vec) } rewrite idB record { lenl = _ ; lenr = _ ; len = _ ; vec = vec } = refl
    idB record { lenl = lenl ; lenr = .(S nr) ; len = .(S n) ; vec = (consr b .lenl nr n vec) } rewrite idB record { lenl = _ ; lenr = _ ; len = _ ; vec = vec } = refl

record 𝕍𝕊 (A B : Set) : Set where
  field
    lenl lenr len : ℕ
    lefts : 𝕍 A lenl
    rights : 𝕍 B lenr
    choices : 𝕍+ 𝟙 𝟙 lenl lenr len

module VecSplit (A B : Set) where
  split-consl : A → 𝕍𝕊 A B → 𝕍𝕊 A B
  split-consl a record { lenl = lenl ; lenr = lenr ; len = len ; lefts = lefts ; rights = rights ; choices = choices } =
    record
      { lenl = _
      ; lenr = _
      ; len = _
      ; lefts = cons a _ lefts
      ; rights = rights
      ; choices = consl _ _ _ _ choices
      }

  split-consr : B → 𝕍𝕊 A B → 𝕍𝕊 A B
  split-consr b record { lenl = lenl ; lenr = lenr ; len = len ; lefts = lefts ; rights = rights ; choices = choices } =
    record
      { lenl = _
      ; lenr = _
      ; len = _
      ; lefts = lefts
      ; rights = cons b _ rights
      ; choices = consr _ _ _ _ choices
      }

  split : 𝕍+R A B → 𝕍𝕊 A B
  split record { lenl = .0 ; lenr = .0 ; len = .0 ; vec = nil } =
    record
      { lenl = _
      ; lenr = _
      ; len = _
      ; lefts = nil
      ; rights = nil
      ; choices = nil
      }
  split record { lenl = .(S nl) ; lenr = lenr ; len = .(S n) ; vec = (consl a nl .lenr n vec) } = split-consl a (split record { lenl = _ ; lenr = _ ; len = _ ; vec = vec})
  split record { lenl = lenl ; lenr = .(S nr) ; len = .(S n) ; vec = (consr b .lenl nr n vec) } = split-consr b (split record { lenl = _ ; lenr = _ ; len = _ ; vec = vec})

  join-consl : A → 𝕍+R A B → 𝕍+R A B
  join-consl a record { lenl = lenl ; lenr = lenr ; len = len ; vec = vec } = record { lenl = _ ; lenr = _ ; len = _ ; vec = consl a _ _ _ vec }

  join-consr : B → 𝕍+R A B → 𝕍+R A B
  join-consr b record { lenl = lenl ; lenr = lenr ; len = len ; vec = vec } = record { lenl = _ ; lenr = _ ; len = _ ; vec = consr b _ _ _ vec }

  join : 𝕍𝕊 A B → 𝕍+R A B
  join record { lenl = .0 ; lenr = .0 ; len = .0 ; lefts = lefts ; rights = rights ; choices = nil } = record { lenl = _ ; lenr = _ ; len = _ ; vec = nil }
  join record { lenl = .(S nl) ; lenr = lenr ; len = .(S n) ; lefts = (cons a .nl lefts) ; rights = rights ; choices = (consl <> nl .lenr n choices) } =
    join-consl a (join record { lenl = _ ; lenr = _ ; len = _ ; lefts = lefts ; rights = rights ; choices = choices } )
  join record { lenl = lenl ; lenr = .(S nr) ; len = .(S n) ; lefts = lefts ; rights = (cons b .nr rights) ; choices = (consr <> .lenl nr n choices) } =
    join-consr b (join record { lenl = _ ; lenr = _ ; len = _ ; lefts = lefts ; rights = rights ; choices = choices })

  iso : Iso (𝕍+R A B) (𝕍𝕊 A B)
  iso = record { to = split ; from = join ; idA = idA ; idB = idB }
    where
    idA : (a : 𝕍+R A B) → join (split a) ≡ a
    idA record { lenl = .0 ; lenr = .0 ; len = .0 ; vec = nil } = refl
    idA record { lenl = .(S nl) ; lenr = lenr ; len = .(S n) ; vec = (consl a nl .lenr n vec) } rewrite idA record { lenl = _ ; lenr = _ ; len = _ ; vec = vec } = refl
    idA record { lenl = lenl ; lenr = .(S nr) ; len = .(S n) ; vec = (consr b .lenl nr n vec) } rewrite idA record { lenl = _ ; lenr = _ ; len = _ ; vec = vec } = refl

    idB : (b : 𝕍𝕊 A B) → split (join b) ≡ b
    idB record { lenl = .0 ; lenr = .0 ; len = .0 ; lefts = nil ; rights = nil ; choices = nil } = refl
    idB record { lenl = .(S nl) ; lenr = lenr ; len = .(S n) ; lefts = (cons a₁ .nl lefts) ; rights = rights ; choices = (consl a nl .lenr n choices) }
      rewrite idB record { lenl = _ ; lenr = _ ; len = _ ; lefts = lefts ; rights = rights ; choices = choices } = refl
    idB record { lenl = lenl ; lenr = .(S nr) ; len = .(S n) ; lefts = lefts ; rights = (cons a .nr rights) ; choices = (consr b .lenl nr n choices) }
      rewrite idB record { lenl = _ ; lenr = _ ; len = _ ; lefts = lefts ; rights = rights ; choices = choices } = refl
