module Isos where

open import Agda.Builtin.Nat using () renaming (Nat to ℕ; zero to Z; suc to S)
open import Agda.Builtin.Equality using (_≡_; refl)

_∘_ : {A B C : Set} (g : B → C) (f : A → B) → (A → C)
g ∘ f = λ x → g (f x)

module Eq where
  cong : {A B : Set} (f : A → B) (x y : A) (p : x ≡ y) → f x ≡ f y
  cong _ _ _ refl = refl

  sym : {A : Set} (x y : A) (p : x ≡ y) → y ≡ x
  sym _ _ refl = refl

data 𝟘 : Set where

record 𝟙 : Set where
  constructor <>

-- a sum relation between two natural numbers
data R+ : (nl nr n : ℕ) → Set where
  rz : R+ Z Z Z
  rsl : (nl nr n : ℕ) (r : R+ nl nr n) → R+ (S nl) nr (S n)
  rsr : (nl nr n : ℕ) (r : R+ nl nr n) → R+ nl (S nr) (S n)

module Nat where
  -- injectivity of successor
  injs : (m n : ℕ) (p : S m ≡ S n) → m ≡ n
  injs m n refl = refl

module NatSum where
  -- when left is zero, then right equals the sum
  zerol : (nr n : ℕ) (r : R+ Z nr n) → nr ≡ n
  zerol Z Z rz = refl
  zerol (S nr) (S n) (rsr .0 .nr .n r) = Eq.cong S nr n (zerol nr n r)

  -- when right is zero, then left equals the sum
  zeror : (nl n : ℕ) (r : R+ nl Z n) → nl ≡ n
  zeror .0 .0 rz = refl
  zeror .(S nl) .(S n) (rsl nl .0 n r) = Eq.cong S nl n (zeror nl n r)

  -- when sum is zero, then left is zero
  sum-zerol : (nl nr : ℕ) (r : R+ nl nr Z) → nl ≡ Z
  sum-zerol .0 .0 rz = refl

  -- when sum is zero, then right is zero
  sum-zeror : (nl nr : ℕ) (r : R+ nl nr Z) → nr ≡ Z
  sum-zeror .0 .0 rz = refl

  module NatPlus where
    open import Agda.Builtin.Nat using () renaming (_+_ to _+ₙ_)

    -- swap the place of the successor from the right side to the left side of the plus expression
    swaps : (nl nr n : ℕ) (p : S nl +ₙ nr ≡ n) → nl +ₙ S nr ≡ n
    swaps Z nr n p = p
    swaps (S nl) nr (S n) p = Eq.cong S _ _ (swaps _ _ _ (Nat.injs _ _ p))

    -- create an equality from a sum relation
    matches : (nl nr n : ℕ) (r : R+ nl nr n) → nl +ₙ nr ≡ n
    matches .0 .0 .0 rz = refl
    matches .(S nl) nr .(S n) (rsl nl .nr n r) = Eq.cong S _ _ (matches _ _ _ r)
    matches nl .(S nr) .(S n) (rsr .nl nr n r) = swaps _ _ (S n) (Eq.cong S _ _ (matches _ _ _ r))

data _+_ (A B : Set) : Set where
  inl : (a : A) → A + B
  inr : (b : B) → A + B
infixr 6 _+_

data _×_ (A B : Set) : Set where
  pair : (a : A) (b : B) → A × B

-- list
data 𝕃 (A : Set) : Set where
  nil : 𝕃 A
  cons : (a : A) (x : 𝕃 A) → 𝕃 A

-- vector; lists indexed by length
data 𝕍 (A : Set) : ℕ → Set where
  nil : 𝕍 A Z
  cons : (a : A) (n : ℕ) (v : 𝕍 A n) → 𝕍 A (S n)

-- vector of sums; vectors indexed by count of each choice
data 𝕍+ (A B : Set) : (nl nr n : ℕ) → Set where
  nil : 𝕍+ A B Z Z Z
  consl : (a : A) (nl nr n : ℕ) (v : 𝕍+ A B nl nr n) → 𝕍+ A B (S nl) nr (S n)
  consr : (b : B) (nl nr n : ℕ) (v : 𝕍+ A B nl nr n) → 𝕍+ A B nl (S nr) (S n)

-- bijection/isomorphism with no structure
record Iso (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    idA : (a : A) → from (to a) ≡ a
    idB : (b : B) → to (from b) ≡ b

module Equiv where
  id : (A : Set) → Iso A A
  id A = record { to = λ a → a ; from = λ a → a ; idA = λ a → refl ; idB = λ b → refl }

  sym : (A B : Set) → Iso A B → Iso B A
  sym A B
    record { to = to ; from = from ; idA = idA ; idB = idB }
    =
    record { to = from ; from = to ; idA = idB ; idB = idA }

  trans : (A B C : Set) → Iso A B → Iso B C → Iso A C
  trans A B C
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

module SumIso where
  over-inl : (A B : Set) (i : Iso A B) (C : Set) → Iso (A + C) (B + C)
  over-inl A B
    record { to = a→b ; from = b→a ; idA = idA-AB ; idB = idB-AB }
    C
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

  over-inr : (A B : Set) (i : Iso A B) (C : Set) → Iso (C + A) (C + B)
  over-inr A B
    record { to = a→b ; from = b→a ; idA = idA-AB ; idB = idB-AB }
    C
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
  over-fst : (A B : Set) (i : Iso A B) (C : Set) → Iso (A × C) (B × C)
  over-fst A B
    record { to = a→b ; from = b→a ; idA = idA-AB ; idB = idB-AB }
    C
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

  over-snd : (A B : Set) (i : Iso A B) (C : Set) → Iso (C × A) (C × B)
  over-snd A B
    record { to = a→b ; from = b→a ; idA = idA-AB ; idB = idB-AB }
    C
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

module List where
  map : (A B : Set) (f : A → B) (x : 𝕃 A) → 𝕃 B
  map A B f nil = nil
  map A B f (cons a x) = cons (f a) (map A B f x)

  module Map where
    id : (A : Set) (f : A → A) (f-id : (a : A) → f a ≡ a) (x : 𝕃 A) → map A A f x ≡ x
    id A f f-id nil = refl
    id A f f-id (cons a x) rewrite f-id a | id A f f-id x = refl

    compose : (A B C : Set) (f : A → B) (g : B → C) (x : 𝕃 A) → map B C g (map A B f x) ≡ map A C (g ∘ f) x
    compose A B C f g nil = refl
    compose A B C f g (cons a x) rewrite compose A B C f g x = refl

module ListIso where
  each : (A B : Set) (i : Iso A B) → Iso (𝕃 A) (𝕃 B)
  each A B
    record { to = a→b ; from = b→a ; idA = idA-AB ; idB = idB-AB }
    =
    record { to = to ; from = from ; idA = idA ; idB = idB }
    where
    to : (x : 𝕃 A) → 𝕃 B
    to = List.map A B a→b

    from : (x : 𝕃 B) → 𝕃 A
    from = List.map B A b→a

    idA : (x : 𝕃 A) → from (to x) ≡ x
    idA nil = refl
    idA (cons a x) rewrite idA-AB a | List.Map.compose A B A a→b b→a x | List.Map.id A (b→a ∘ a→b) idA-AB x = refl

    idB : (x : 𝕃 B) → to (from x) ≡ x
    idB nil = refl
    idB (cons b x) rewrite idB-AB b | List.Map.compose B A B b→a a→b x | List.Map.id B (a→b ∘ b→a) idB-AB x = refl

module Vec where
  map : (A B : Set) (f : A → B) (n : ℕ) (v : 𝕍 A n) → 𝕍 B n
  map A B f .0 nil = nil
  map A B f .(S n) (cons a n x) = cons (f a) n (map A B f n x)

  module Map where
    id : (A : Set) (f : A → A) (f-id : (a : A) → f a ≡ a) (n : ℕ) (x : 𝕍 A n) → map A A f n x ≡ x
    id A f f-id .0 nil = refl
    id A f f-id .(S n) (cons a n x) rewrite f-id a | id A f f-id n x = refl

    compose : (A B C : Set) (f : A → B) (g : B → C) (n : ℕ) (x : 𝕍 A n) → map B C g n (map A B f n x) ≡ map A C (g ∘ f) n x
    compose A B C f g .0 nil = refl
    compose A B C f g .(S n) (cons a n x) rewrite compose A B C f g n x = refl

module VecIso where
  each : (A B : Set) (i : Iso A B) (n : ℕ) → Iso (𝕍 A n) (𝕍 B n)
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
    idA (cons a n x) rewrite idA-AB a | Vec.Map.compose A B A a→b b→a n x | Vec.Map.id A (b→a ∘ a→b) idA-AB n x = refl

    idB : (x : 𝕍 B n) → to (from x) ≡ x
    idB nil = refl
    idB (cons b n x) rewrite idB-AB b | Vec.Map.compose B A B b→a a→b n x | Vec.Map.id B (a→b ∘ b→a) idB-AB n x = refl

-- vector packaged in a record
record 𝕍R (A : Set) : Set where
  field
    len : ℕ
    vec : 𝕍 A len

-- vector choice packaged in a record
record 𝕍+R (A B : Set) : Set where
  field
    lenl lenr len : ℕ
    vec : 𝕍+ A B lenl lenr len

module Vec+ where
  -- extract the sum relation between the indexes of the vector of sums
  plus-rel : (A B : Set) (nl nr n : ℕ) → 𝕍+ A B nl nr n → R+ nl nr n
  plus-rel A B .0 .0 .0 nil = rz
  plus-rel A B .(S nl) nr .(S n) (consl a nl .nr n v) = rsl nl nr n (plus-rel A B nl nr n v)
  plus-rel A B nl .(S nr) .(S n) (consr b .nl nr n v) = rsr nl nr n (plus-rel A B nl nr n v)

-- bijection between list and vector
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
    idA (cons a x) = Eq.cong (cons a) _ _ (idA x)

    idB : (x : 𝕍R A) → index (forget x) ≡ x
    idB record { len = .0 ; vec = nil } = refl
    idB record { len = .(S n) ; vec = (cons a n vec) } rewrite idB record { len = n ; vec = vec } = refl

-- bijection between a plain vector with a sum parameter and vector of sums
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

-- vector of sums split into separate vectors for left elements, right elements, and a vector of the order in which to join the elements
record 𝕍𝕊 (A B : Set) : Set where
  field
    lenl lenr len : ℕ
    lefts : 𝕍 A lenl
    rights : 𝕍 B lenr
    choices : 𝕍+ 𝟙 𝟙 lenl lenr len

-- bijection between vector of sums and vector split
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

module _ (A B : Set) where
  data 𝕍R+ : (nl nr n : ℕ) → Set where
    vr+ : (nl nr n : ℕ) (r : R+ nl nr n) (as : 𝕍 A nl) (bs : 𝕍 B nr) → 𝕍R+ nl nr n

  -- represent a vector of sums as two separate vectors of each type and a sum relation to express the way to combine the elements into a single list
  record 𝕍R+R : Set where
    field
      lenl lenr len : ℕ
      rel : R+ lenl lenr len
      lefts : 𝕍 A lenl
      rights : 𝕍 B lenr

-- bijection between lists of sums and an alternate representation for a split-sum vector which uses the sum relation instead of a list of choices
module VecSumR (A B : Set) where

  index-consl : A → 𝕍R+R A B → 𝕍R+R A B
  index-consl a record { lenl = lenl ; lenr = lenr ; len = len ; rel = rel ; lefts = lefts ; rights = rights } =
    record
      { lenl = _
      ; lenr = _
      ; len = _
      ; rel = rsl _ _ _ rel
      ; lefts = cons a _ lefts
      ; rights = rights
      }

  index-consr : B → 𝕍R+R A B → 𝕍R+R A B
  index-consr b record { lenl = lenl ; lenr = lenr ; len = len ; rel = rel ; lefts = lefts ; rights = rights } =
    record
      { lenl = _
      ; lenr = _
      ; len = _
      ; rel = rsr _ _ _ rel
      ; lefts = lefts
      ; rights = cons b _ rights
      }

  index : (x : 𝕃 (A + B)) → 𝕍R+R A B
  index nil = record
                { lenl = _
                ; lenr = _
                ; len = Z
                ; rel = rz
                ; lefts = nil
                ; rights = nil
                }
  index (cons (inl a) x) = index-consl a (index x)
  index (cons (inr b) x) = index-consr b (index x)

  forget : 𝕍R+R A B → 𝕃 (A + B)
  forget record { lenl = .0 ; lenr = .0 ; len = .0 ; rel = rz ; lefts = nil ; rights = nil } = nil
  forget record { lenl = .(S nl) ; lenr = lenr ; len = .(S n) ; rel = (rsl nl .lenr n rel) ; lefts = (cons a .nl lefts) ; rights = rights }
    = cons (inl a) (forget record { lenl = _ ; lenr = _ ; len = _ ; rel = rel ; lefts = lefts ; rights = rights }) 
  forget record { lenl = lenl ; lenr = .(S nr) ; len = .(S n) ; rel = (rsr .lenl nr n rel) ; lefts = lefts ; rights = (cons b .nr rights) }
    = cons (inr b) (forget record { lenl = _ ; lenr = _ ; len = _ ; rel = rel ; lefts = lefts ; rights = rights })

  iso : Iso (𝕃 (A + B)) (𝕍R+R A B)
  iso = record { to = index ; from = forget ; idA = idA ; idB = idB }
    where
    idA : (a : 𝕃 (A + B)) → forget (index a) ≡ a
    idA nil = refl
    idA (cons (inl a) as) rewrite idA as = refl
    idA (cons (inr b) as) rewrite idA as = refl

    idB : (b : 𝕍R+R A B) → index (forget b) ≡ b
    idB record { lenl = .0 ; lenr = .0 ; len = .0 ; rel = rz ; lefts = nil ; rights = nil } = refl
    idB record { lenl = .(S nl) ; lenr = lenr ; len = .(S n) ; rel = (rsl nl .lenr n rel) ; lefts = (cons a .nl lefts) ; rights = rights }
      rewrite idB record { lenl = _ ; lenr = _ ; len = _ ; rel = rel ; lefts = lefts ; rights = rights } = refl
    idB record { lenl = lenl ; lenr = .(S nr) ; len = .(S n) ; rel = (rsr .lenl nr n rel) ; lefts = lefts ; rights = (cons a .nr rights) }
      rewrite idB record { lenl = _ ; lenr = _ ; len = _ ; rel = rel ; lefts = lefts ; rights = rights } = refl

module VecSumROver (A B : Set) (isoAB : Iso A B) (C : Set) where
  left : Iso (𝕍R+R A C) (𝕍R+R B C)
  left = final
    where
    isoAC-BC : Iso (A + C) (B + C)
    isoAC-BC = SumIso.over-inl _ _ isoAB _

    listIso : Iso (𝕃 (A + C)) (𝕃 (B + C))
    listIso = ListIso.each _ _ isoAC-BC

    rightIso : Iso (𝕃 (B + C)) (𝕍R+R B C)
    rightIso = VecSumR.iso B C

    leftIso : Iso (𝕍R+R A C) (𝕃 (A + C))
    leftIso = Equiv.sym _ _ (VecSumR.iso A C)

    midleft : Iso (𝕍R+R A C) (𝕃 (B + C))
    midleft = Equiv.trans _ _ _ leftIso listIso

    final : Iso (𝕍R+R A C) (𝕍R+R B C)
    final = Equiv.trans _ _ _ midleft rightIso

  right : Iso (𝕍R+R C A) (𝕍R+R C B)
  right = final
    where
    isoSum : Iso (C + A) (C + B)
    isoSum = SumIso.over-inr _ _ isoAB _

    listIso : Iso (𝕃 (C + A)) (𝕃 (C + B))
    listIso = ListIso.each _ _ isoSum

    rightIso : Iso (𝕃 (C + B)) (𝕍R+R C B)
    rightIso = VecSumR.iso C B

    leftIso : Iso (𝕍R+R C A) (𝕃 (C + A))
    leftIso = Equiv.sym _ _ (VecSumR.iso C A)

    midleft : Iso (𝕍R+R C A) (𝕃 (C + B))
    midleft = Equiv.trans _ _ _ leftIso listIso

    final : Iso (𝕍R+R C A) (𝕍R+R C B)
    final = Equiv.trans _ _ _ midleft rightIso


record 𝕃+ (A : Set) : Set where
  field
    first : A
    rest : 𝕃 A

record 𝔾R (A B : Set) : Set where
  field
    initial : 𝕃 B
    core : 𝕃 (𝕃+ A × 𝕃+ B)
    final : 𝕃 A

module GroupAdjacent (A B : Set) where

  group-consl : A → 𝔾R A B → 𝔾R A B
  group-consl a record { initial = nil ; core = nil ; final = final }
    = record { initial = nil ; core = nil ; final = cons a final }
  group-consl a record { initial = nil ; core = (cons (pair record { first = a2 ; rest = as } bs) core) ; final = final }
    = record { initial = nil ; core = cons (pair record { first = a ; rest = cons a2 as } bs) core ; final = final }
  group-consl a record { initial = cons b initial ; core = core ; final = final }
    = record { initial = nil ; core = cons (pair record { first = a ; rest = nil } record { first = b ; rest = initial }) core ; final = final }

  group-consr : B → 𝔾R A B → 𝔾R A B
  group-consr b record { initial = initial ; core = core ; final = final } = record { initial = cons b initial ; core = core ; final = final }

  group : 𝕃 (A + B) → 𝔾R A B
  group nil = record { initial = nil ; core = nil ; final = nil }
  group (cons (inl a) x) = group-consl a (group x)
  group (cons (inr b) x) = group-consr b (group x)

  flatten-cons : (A + B) → 𝕃 (A + B) → 𝕃 (A + B)
  flatten-cons x xs = cons x xs

  flatten-core3 : 𝕃 B → 𝕃 (A + B) → 𝕃 (A + B)
  flatten-core3 nil xs = xs
  flatten-core3 (cons b bs) xs = flatten-cons (inr b) (flatten-core3 bs xs)

  flatten-core2 : 𝕃 A → 𝕃+ B → 𝕃 (A + B) → 𝕃 (A + B)
  flatten-core2 nil record { first = b ; rest = rest } xs = flatten-cons (inr b) (flatten-core3 rest xs)
  flatten-core2 (cons a as) bs xs = flatten-cons (inl a) (flatten-core2 as bs xs)

  flatten-core : (𝕃+ A × 𝕃+ B) → 𝕃 (A + B) → 𝕃 (A + B)
  flatten-core (pair record { first = a ; rest = rest } bs) xs = flatten-cons (inl a) (flatten-core2 rest bs xs) 

  flatten : 𝔾R A B → 𝕃 (A + B)
  flatten record { initial = nil ; core = nil ; final = nil } = nil
  flatten record { initial = nil ; core = nil ; final = (cons a final) } = flatten-cons (inl a) (flatten record { initial = nil ; core = nil ; final = final })
  flatten record { initial = nil ; core = (cons x core) ; final = final } = flatten-core x (flatten record { initial = nil ; core = core ; final = final })
  flatten record { initial = (cons b initial) ; core = core ; final = final } = flatten-cons (inr b) (flatten record { initial = initial ; core = core ; final = final})

  iso : Iso (𝕃 (A + B)) (𝔾R A B)
  iso = record { to = group ; from = flatten ; idA = idA ; idB = idB }
    where
    aux2 : (bs : 𝕃 B) (core : 𝕃 (𝕃+ A × 𝕃+ B)) (final : 𝕃 A) → flatten-core3 bs (flatten (record { initial = nil ; core = core ; final = final })) ≡ flatten (record { initial = bs ; core = core ; final = final })
    aux2 nil core final = refl
    aux2 (cons a bs) core final = Eq.cong (cons (inr a)) _ _ (aux2 bs core final)

    aux1 : (a : A) (xs : 𝕃 (A + B)) (g : 𝔾R A B) (p : flatten g ≡ xs) → flatten (group-consl a g) ≡ cons (inl a) xs
    aux1 a xs record { initial = nil ; core = nil ; final = final } p = Eq.cong (cons (inl a)) _ _ p
    aux1 a xs record { initial = nil ; core = (cons (pair record { first = a2 ; rest = as } bs) core) ; final = final } p = Eq.cong (cons (inl a)) _ _ p
    aux1 a xs record { initial = (cons b nil) ; core = core ; final = final } p = Eq.cong (cons (inl a)) _ _ p
    aux1 a xs record { initial = (cons b (cons a₁ bs)) ; core = core ; final = final } p rewrite aux2 bs core final | p = refl

    idA : (xs : 𝕃 (A + B)) → flatten (group xs) ≡ xs
    idA nil = refl
    idA (cons (inl a) xs) = aux1 a xs (group xs) (idA xs)
    idA (cons (inr b) xs) rewrite idA xs = refl

    auxb1 : (b : B) (bs : 𝕃 B) (core : 𝕃 (𝕃+ A × 𝕃+ B))
          (final : 𝕃 A) →
        group
        (flatten (record { initial = nil ; core = core ; final = final }))
        ≡ record { initial = nil ; core = core ; final = final } →
        group-consr b
        (group
         (flatten-core3 bs
          (flatten
           (record { initial = nil ; core = core ; final = final }))))
        ≡ record { initial = cons b bs ; core = core ; final = final }
    auxb1 b nil core final p = Eq.cong (group-consr b) _ _ p
    auxb1 b (cons b2 bs) core final p = Eq.cong (group-consr b) _ _ (auxb1 b2 bs core final p)

    auxb2 : (a : A) (as : 𝕃 A) (b : 𝕃+ B)
          (core : 𝕃 (𝕃+ A × 𝕃+ B)) (final : 𝕃 A) →
        group
        (flatten (record { initial = nil ; core = core ; final = final }))
        ≡ record { initial = nil ; core = core ; final = final } →
        group-consl a
        (group
         (flatten-core2 as b
          (flatten
           (record { initial = nil ; core = core ; final = final }))))
        ≡
        record
        { initial = nil
        ; core = cons (pair (record { first = a ; rest = as }) b) core
        ; final = final
        }
    auxb2 a nil record { first = b ; rest = bs } core final p = Eq.cong (group-consl a) _ _ (auxb1 b bs core final p)
    auxb2 a (cons a2 as) b core final p = Eq.cong (group-consl a) _ _ (auxb2 a2 as b core final p)

    idB : (g : 𝔾R A B) → group (flatten g) ≡ g
    idB record { initial = nil ; core = nil ; final = nil } = refl
    idB record { initial = nil ; core = nil ; final = (cons a final) } rewrite idB record { initial = nil ; core = nil ; final = final } = refl
    idB record { initial = nil ; core = (cons (pair record { first = a ; rest = nil } record { first = b ; rest = bs }) core) ; final = final } = 
      Eq.cong (group-consl a) _ _ (auxb1 b bs core final (idB record { initial = nil ; core = core ; final = final }))
    idB record { initial = nil ; core = (cons (pair record { first = a ; rest = (cons a2 as) } b) core) ; final = final } =
      Eq.cong (group-consl a) _ _ (auxb2 a2 as b core final (idB record { initial = nil ; core = core ; final = final }))
    idB record { initial = (cons a initial) ; core = core ; final = final } rewrite idB record { initial = initial ; core = core ; final = final } = refl
