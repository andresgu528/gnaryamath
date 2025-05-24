{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

option function boundaries ≔ implicit
option type boundaries ≔ implicit

{` Chapter 1 - Type theory `}

{` 1.2 Function types `}


{` 1.3 Universes and families `}


{` 1.4 Dependent function types (Π-types) `}

`Function
def id (A : Type) : A → A ≔ x ↦ x

`Function
def swap (A B C : Type) : (A → B → C) → (B → A → C) ≔ g b a ↦ g a b


{` 1.5 Product types `}

`Type
def CartesianProduct (A B : Type) : Type ≔ sig ( pr₁ : A, pr₂ : B )

notation 2 CartesianProduct_notation : A "×" B ≔ CartesianProduct A B

`Type
def 𝟙 : Type ≔ data [ ★. ]

`Functon
def rec_× (A B C : Type) : (A → B → C) → A × B → C
  ≔ g x ↦ g (x .pr₁) (x .pr₂)

`Function
def rec_1 (C : Type) : C → 𝟙 → C ≔ c ↦ [ ★. ↦ c ]
`Function
def uniq_× (A B : Type) (x : A × B) : Id (A × B) (x .pr₁, x .pr₂) x ≔ refl x

`Function
def ind_× (A B : Type) (C : A × B → Type)
  : ((x : A) (y : B) → C (x, y)) → (x : A × B) → C x
  ≔ g z ↦ g (z .pr₁) (z .pr₂)

`Function
def ind_1 (C : 𝟙 → Type) : C ★. → (x : 𝟙) → C x ≔ c ↦ [ ★. ↦ c ]

`Proof / Function
def uniq_1 (x : 𝟙) : Id 𝟙 x ★. ≔ match x [ ★. ↦ refl (★. : 𝟙) ]


{` 1.6 Dependent pair types (Σ-types) `}

`Type
def Σ (A : Type) (B : A → Type) : Type ≔ sig ( pr₁ : A, pr₂ : B pr₁ )

`Type
def alt.CartesianProduct (A B : Type) : Type ≔ Σ A (x ↦ B)

notation 2 alt.CartesianProduct_notation : A "×Σ" B
  ≔ alt.CartesianProduct A B

`Function
def rec_Σ (A : Type) (B : A → Type) (C : Type)
  : ((x : A) → B x → C) → Σ A B → C
  ≔ g z ↦ g (z .pr₁) (z .pr₂)

`Function
def ind_Σ (A : Type) (B : A → Type) (C : Σ A B → Type)
  : ((a : A) (b : B a) → C (a, b)) → (p : Σ A B) → C p
  ≔ g z ↦ g (z .pr₁) (z .pr₂)

`Function
def ac (A B : Type) (R : A → B → Type)
  : ((x : A) → Σ B (y ↦ R x y)) → (Σ (A → B) (f ↦ (x : A) → R x (f x)))
  ≔ g ↦ (x ↦ g x .pr₁, x ↦ g x .pr₂)

`Type
def Magma : Type ≔ sig ( A : Type, m : A → A → A )

`Type
def PointedMagma : Type ≔ sig ( A : Type, m : A → A → A, e : A )


{` 1.7 Coproduct types `}

`Type
def Coproduct (A B : Type) : Type ≔ data [ inl. (_ : A) | inr. (_ : B) ]

notation 2 Coproduct_notation : A "＋" B ≔ Coproduct A B

`Type
def 𝟘 : Type ≔ data []

`Function
def rec_＋ (A B C : Type) : (A → C) → (B → C) → A ＋ B → C ≔ g0 g1 ↦ [
| inl. a ↦ g0 a
| inr. b ↦ g1 b]

`Function
def rec_𝟘 (C : Type) : 𝟘 → C ≔ [ ]

`Function
def ind_＋ (A B : Type) (C : A ＋ B → Type)
  : ((a : A) → C (inl. a)) → ((b : B) → C (inr. b)) → (x : A ＋ B) → C x
  ≔ g0 g1 ↦ [ inl. a ↦ g0 a | inr. b ↦ g1 b ]

`Function
def ind_𝟘 (C : 𝟘 → Type) : (z : 𝟘) → C z ≔ [ ]


{` 1.8 The type of booleans `}

`Type
def 𝟚 : Type ≔ data [ 0₂. | 1₂. ]
`Function
def rec_2 (C : Type) : C → C → 𝟚 → C ≔ c0 c1 ↦ [ 0₂. ↦ c0 | 1₂. ↦ c1 ]

`Function
def ind_2 (C : 𝟚 → Type) : C 0₂. → C 1₂. → (x : 𝟚) → C x ≔ c0 c1 ↦ [
| 0₂. ↦ c0
| 1₂. ↦ c1]

`Proof
def unnamed.1_8_1 (x : 𝟚) : (Id 𝟚 x 0₂.) ＋ (Id 𝟚 x 1₂.) ≔ match x [
| 0₂. ↦ inl. (refl (0₂. : 𝟚))
| 1₂. ↦ inr. (refl (1₂. : 𝟚))]


{` 1.9 The natural numbers `}

`Type
def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

`Function
def double : ℕ → ℕ ≔ [ zero. ↦ zero. | suc. n ↦ suc. (suc. (double n)) ]

`Function
def add : ℕ → ℕ → ℕ ≔ [ zero. ↦ n ↦ n | suc. m ↦ n ↦ suc. (add m n) ]

notation 2 add_notation : m "+" n ≔ add m n

`Function
def rec_ℕ (C : Type) : C → (ℕ → C → C) → ℕ → C ≔ c0 cs ↦ [
| zero. ↦ c0
| suc. n ↦ cs n (rec_ℕ C c0 cs n)]

`Function
def ind_ℕ (C : ℕ → Type)
  : C zero. → ((n : ℕ) → C n → C (suc. n)) → (n : ℕ) → C n
  ≔ c0 cs ↦ [ zero. ↦ c0 | suc. n ↦ cs n (ind_ℕ C c0 cs n) ]

`Proof
def assoc (i j k : ℕ) : Id ℕ (i + (j + k)) ((i + j) + k) ≔ match i [
| zero. ↦ refl (j + k)
| suc. i ↦ refl ((n ↦ suc. n) : ℕ → ℕ) (assoc i j k)]


{` 1.11 Propositions as types `}

`Type
def ¬ : Type → Type ≔ A ↦ A → 𝟘

`Proof
def unnamed.1_11_1 (A B : Type) : (¬ A) × (¬ B) → ¬ (A ＋ B) ≔ z ↦ [
| inl. a ↦ z .pr₁ a
| inr. b ↦ z .pr₂ b]

`Proof
def unnamed.1_11_2 (A : Type) (P Q : A → Type)
  : ((x : A) → (P x × Q x)) → ((x : A) → P x) × ((x : A) → Q x)
  ≔ p ↦ (x ↦ p x .pr₁, x ↦ p x .pr₂)

`Type
def leq : ℕ → ℕ → Type ≔ n m ↦ Σ ℕ (k ↦ Id ℕ (n + k) m)

notation 2 leq_notation : m "≤" n ≔ leq m n

`Type
def lt : ℕ → ℕ → Type ≔ n m ↦ Σ ℕ (k ↦ Id ℕ (n + suc. k) m)

notation 2 lt_notation : m "<" n ≔ lt m n

`Type
def Semigroup : Type ≔ sig (
  A : Type,
  m : A → A → A,
  assoc : (x y z : A) → Id A (m x (m y z)) (m (m x y) z) )

`Type
def unnamed.1_11_3 (A : Type) (a b : A) : Type ≔ (P : A → Type) → P a → P b

`Proof
def unnamed.1_11_4 : ¬ 𝟘 ≔ [ ]


{` 1.12 Identity types `}

`Proof / Function
def IndiscernibilityOfIdenticals (A : Type) (C : A → Type) (x y : A)
  : Id A x y → C x → C y
  ≔ p ↦ refl C p .trr

`Proof
def IndiscernibilityOfIdenticals_eq (A : Type) (C : A → Type) (x : A)
  : Id (C x → C x) (IndiscernibilityOfIdenticals A C x x (refl x)) (id (C x))
  ≔ c0 c1 c2 ↦ (C x)⁽ᵉᵉ⁾ (refl (C x) .liftr c0) (refl c1) .trr c2

{` 1.12.1 Path induction `}

`Proof / Function
def Ind_Id (A : Type) (C : (x y : A) → Id A x y → Type)
  : ((x : A) → C x x (refl x)) → (x y : A) (p : Id A x y) → C x y p
  ≔ c x y p ↦
  let a2 : Id A x y ≔ A⁽ᵉᵉ⁾ (refl x) p .trr (refl x) in
  let b2 : A⁽ᵉᵉ⁾ (refl x) a2 (refl x) p
    ≔ sym (A⁽ᵉᵉ⁾ (refl x) p .liftr (refl x)) in
  refl (C x) a2 b2 .trr (c x)

`Proof
def Ind_Id_eq (A : Type) (C : (x y : A) → Id A x y → Type)
  (c : (x : A) → C x x (refl x)) (x : A)
  : Id (C x x (refl x)) (Ind_Id A C c x x (refl x)) (c x)
  ≔
  let a02 : Id A x x ≔ A⁽ᵉᵉ⁾ (refl x) (refl x) .trr (refl x) in
  let lifta02 : A⁽ᵉᵉ⁾ (refl x) (refl x) (refl x) a02
    ≔ A⁽ᵉᵉ⁾ (refl x) (refl x) .liftr (refl x) in
  let a22 : A⁽ᵉᵉ⁾ a02 (refl x) (refl x) (refl x)
    ≔ A⁽ᵉᵉᵉ⁾ lifta02 x⁽ᵉᵉ⁾ x⁽ᵉᵉ⁾ x⁽ᵉᵉ⁾ .trr x⁽ᵉᵉ⁾ in
  let b02 : A⁽ᵉᵉ⁾ (refl x) a02 (refl x) (refl x) ≔ sym lifta02 in
  let lifta22 : A⁽ᵉᵉᵉ⁾ lifta02 x⁽ᵉᵉ⁾ x⁽ᵉᵉ⁾ x⁽ᵉᵉ⁾ x⁽ᵉᵉ⁾ a22
    ≔ A⁽ᵉᵉᵉ⁾ lifta02 x⁽ᵉᵉ⁾ x⁽ᵉᵉ⁾ x⁽ᵉᵉ⁾ .liftr x⁽ᵉᵉ⁾ in
  let b22 : A⁽ᵉᵉᵉ⁾ x⁽ᵉᵉ⁾ a22 b02 x⁽ᵉᵉ⁾ x⁽ᵉᵉ⁾ x⁽ᵉᵉ⁾ ≔ lifta22⁽³¹²⁾ in
  let c01 : C x x (refl x) ≔ refl (C x) a02 b02 .trr (c x) in
  let c02 : Id (C x) a02 b02 (c x) c01 ≔ refl (C x) a02 b02 .liftr (c x) in
  (C x)⁽ᵉᵉ⁾ a22 b22 c02 (refl (c x)) .trr (refl (c x))

`Proof / Function
def Ind'_Id (A : Type) (a : A) (C : (x : A) → Id A a x → Type)
  : C a (refl a) → (x : A) (p : Id A a x) → C x p
  ≔ c x p ↦
  let a2 : Id A a x ≔ A⁽ᵉᵉ⁾ (refl a) p .trr (refl a) in
  let b2 : A⁽ᵉᵉ⁾ (refl a) a2 (refl a) p
    ≔ sym (A⁽ᵉᵉ⁾ (refl a) p .liftr (refl a)) in
  refl C a2 b2 .trr c

`Proof
def Ind'_Id_eq (A : Type) (a : A) (C : (x : A) → Id A a x → Type)
  (c : C a (refl a))
  : Id (C a (refl a)) (Ind'_Id A a C c a (refl a)) c
  ≔
  let a02 : Id A a a ≔ A⁽ᵉᵉ⁾ (refl a) (refl a) .trr (refl a) in
  let lifta02 : A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) a02
    ≔ A⁽ᵉᵉ⁾ (refl a) (refl a) .liftr (refl a) in
  let a22 : A⁽ᵉᵉ⁾ a02 (refl a) (refl a) (refl a)
    ≔ A⁽ᵉᵉᵉ⁾ lifta02 a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ .trr a⁽ᵉᵉ⁾ in
  let b02 : A⁽ᵉᵉ⁾ (refl a) a02 (refl a) (refl a) ≔ sym lifta02 in
  let lifta22 : A⁽ᵉᵉᵉ⁾ lifta02 a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ a22
    ≔ A⁽ᵉᵉᵉ⁾ lifta02 a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ .liftr a⁽ᵉᵉ⁾ in
  let b22 : A⁽ᵉᵉᵉ⁾ a⁽ᵉᵉ⁾ a22 b02 a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ ≔ lifta22⁽³¹²⁾ in
  let c01 : C a (refl a) ≔ refl C a02 b02 .trr c in
  let c02 : Id C a02 b02 c c01 ≔ refl C a02 b02 .liftr c in
  C⁽ᵉᵉ⁾ a22 b22 c02 (refl c) .trr (refl c)

{` 1.12.2 Equivalence of path induction and based path induction `}

`Proof
def unnamed.1_12_1_1
  : let Ind'_Id_statement
      ≔ ((A : Type) (a : A) (C : (x : A) → Id A a x → Type) → C a (refl a) →
         (x : A) → (p : Id A a x)
         → C x p) in
    let Ind'_Id_eq_statement : Ind'_Id_statement → Type
      ≔ Ind'_Id ↦
        (A : Type) (a : A) (C : (x : A) → Id A a x → Type) (c : C a (refl a))
        → Id (C a (refl a)) (Ind'_Id A a C c a (refl a)) c in
    let Ind_Id_statement
      ≔ (A : Type) (C : (x y : A) → Id A x y → Type) →
        ((x : A) → C x x (refl x)) → (x y : A) (p : Id A x y)
        → C x y p in
    let Ind_Id_eq_statement : Ind_Id_statement → Type
      ≔ Ind_Id ↦
        (A : Type) (C : (x y : A) → Id A x y → Type)
        (c : (x : A) → C x x (refl x)) (x : A)
        → Id (C x x (refl x)) (Ind_Id A C c x x (refl x)) (c x) in
    (Σ Ind'_Id_statement Ind'_Id_eq_statement)
    → Σ Ind_Id_statement Ind_Id_eq_statement
  ≔ Ind' ↦
  let Ind'_Id ≔ Ind' .pr₁ in
  let Ind'_Id_eq ≔ Ind' .pr₂ in
  (A C c x y p ↦ Ind'_Id A x (C x) (c x) y p,
   A C c x ↦ Ind'_Id_eq A x (C x) (c x))

`Proof
def unnamed.1_12_1_2
  : let Ind_Id_statement
      ≔ (A : Type) (C : (x y : A) → Id A x y → Type) →
        ((x : A) → C x x (refl x)) → (x y : A) (p : Id A x y)
        → C x y p in
    let Ind_Id_eq_statement : Ind_Id_statement → Type
      ≔ Ind_Id ↦
        (A : Type) (C : (x y : A) → Id A x y → Type)
        (c : (x : A) → C x x (refl x)) (x : A)
        → Id (C x x (refl x)) (Ind_Id A C c x x (refl x)) (c x) in
    let Ind'_Id_statement
      ≔ (A : Type) (a : A) (C : (x : A) → Id A a x → Type) → C a (refl a) →
        (x : A) → (p : Id A a x)
        → C x p in
    let Ind'_Id_eq_statement : Ind'_Id_statement → Type
      ≔ Ind'_Id ↦
        (A : Type) (a : A) (C : (x : A) → Id A a x → Type) (c : C a (refl a))
        → Id (C a (refl a)) (Ind'_Id A a C c a (refl a)) c in
    (Σ Ind_Id_statement Ind_Id_eq_statement)
    → Σ Ind'_Id_statement Ind'_Id_eq_statement
  ≔ Ind ↦
  let Ind_Id ≔ Ind .pr₁ in
  let Ind_Id_eq ≔ Ind .pr₂ in
  (A a C c x p ↦
     let D : (x y : A) → (Id A x y) → Type
       ≔ x y p ↦ (C : (z : A) → Id A x z → Type) → C x (refl x) → C y p in
     let d : (x : A) → D x x (refl x) ≔ x _ c ↦ c in
     let f : (x y : A) (p : Id A x y) → D x y p ≔ Ind_Id A D d in
     f a x p C c,
   A a C c ↦
     let D : (x y : A) → (Id A x y) → Type
       ≔ x y p ↦ (C : (z : A) → Id A x z → Type) → C x (refl x) → C y p in
     let d : (x : A) → D x x (refl x) ≔ x _ c ↦ c in
     (Ind_Id_eq A D d a) (refl C) (refl c))

{` 1.12.3 Disequality `}

`Type
def neq (A : Type) (x y : A) : Type ≔ ¬ (Id A x y)
