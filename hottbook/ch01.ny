{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}


{` Chapter 1 - Type theory `}

{` 1.2 Function types `}

`Function types are primitive in Narya

`Type
def function : Type → Type → Type ≔ A B ↦ A → B

`Function
def apply_function (A B : Type) : (A → B) → A → B ≔ f a ↦ f a

`Computation proof
def uniq_function (A B : Type) (f : A → B) : Id (A → B) f (x ↦ f x) ≔ refl f


{` 1.3 Universes and families `}

`For the moment, Narya uses Type:Type

`Type
def universe : Type ≔ Type

`Type
def FamilyOfTypes (A : Type) : Type ≔ A → Type

`Function
def ConstantTypeFamily (A : Type) : Type → A → Type ≔ B x ↦ B


{` 1.4 Dependent function types (Π-types) `}

`In the Narya primitives it also holds that function types are a particular case of dependent function types 

`Computation proof
def unnamed.1_4_1 (A B : Type) : Id Type (Π A (x ↦ B)) (A → B) ≔ refl (A → B)

`Function
def apply_Π (A : Type) (B : A → Type) : ((x : A) → B x) → (a : A) → B a
  ≔ f a ↦ f a

`Computation proof
def uniq_Π (A : Type) (B : A → Type) (f : (x : A) → B x)
  : Id ((x : A) → B x) f (x ↦ f x)
  ≔ refl f

`Function
def id (A : Type) : A → A ≔ x ↦ x

`Function
def swap (A B C : Type) : (A → B → C) → (B → A → C) ≔ g b a ↦ g a b


{` 1.5 Product types `}

`Type
def CartesianProduct (A B : Type) : Type ≔ sig ( pr1 : A, pr2 : B )

notation(2) A "×" B ≔ CartesianProduct A B

`Type
def 𝟙 : Type ≔ sig ()

`Definition
def ★ : 𝟙 ≔ ()

`Computation proofs
def pr1_comput (A B : Type) (a : A) (b : B) : Id A (((a, b) : A × B) .pr1) a
  ≔ refl a
def pr2_comput (A B : Type) (a : A) (b : B) : Id B (((a, b) : A × B) .pr2) b
  ≔ refl b

`Function
def rec_× (A B C : Type) : (A → B → C) → A × B → C
  ≔ g z ↦ g (z .pr1) (z .pr2)
`Computation proof
def rec_×_comput (A B C : Type) (g : A → B → C) (a : A) (b : B)
  : Id C (rec_× A B C g (a, b)) (g a b)
  ≔ refl (g a b)

`Function
def rec_1 (C : Type) : C → 𝟙 → C ≔ c _ ↦ c
`Computation proof
def rec_1_comput (C : Type) (c : C) : Id C (rec_1 C c ★) c ≔ refl c

`Computation proof
def uniq_× (A B : Type) (x : A × B) : Id (A × B) (x .pr1, x .pr2) x ≔ refl x

`Function
def ind_× (A B : Type) (C : A × B → Type)
  : ((x : A) (y : B) → C (x, y)) → (x : A × B) → C x
  ≔ g x ↦ g (x .pr1) (x .pr2)
`Computation proof
def ind_×_comput (A B : Type) (C : A × B → Type)
  (g : (x : A) (y : B) → C (x, y)) (x : A) (y : B)
  : Id (C (x, y)) (ind_× A B C g (x, y)) (g x y)
  ≔ refl (g x y)

`Function
def ind_1 (C : 𝟙 → Type) : C ★ → (x : 𝟙) → C x ≔ c _ ↦ c
`Computation proof
def ind_1_comput (C : 𝟙 → Type) (c : C ★) : Id (C ★) (ind_1 C c ★) c ≔ refl c

`Computation proof
def uniq_1 (x : 𝟙) : Id 𝟙 x ★ ≔ refl ★

{` 1.6 Dependent pair types (Σ-types) `}

`Type
def Σ (A : Type) (B : A → Type) : Type ≔ sig ( pr1 : A, pr2 : B pr1 )

`Type
def altCartesianProduct (A B : Type) : Type ≔ Σ A (_ ↦ B)
notation(2) A "alt×" B ≔ altCartesianProduct A B

`Function
def rec_Σ (A : Type) (B : A → Type) (C : Type)
  : ((x : A) → B x → C) → Σ A B → C
  ≔ g z ↦ g (z .pr1) (z .pr2)
`Computation proof
def rec_Σ_comput (A : Type) (B : A → Type) (C : Type) (g : (x : A) → B x → C)
  (a : A) (b : B a)
  : Id C (rec_Σ A B C g (a, b)) (g a b)
  ≔ refl (g a b)

`Computation proofs
def pr1d_comput (A : Type) (B : A → Type) (a : A) (b : B a)
  : Id A (((a, b) : Σ A B) .pr1) a
  ≔ refl a
def pr2d_comput (A : Type) (B : A → Type) (a : A) (b : B a)
  : Id (B a) (((a, b) : Σ A B) .pr2) b
  ≔ refl b

`Function
def ind_Σ (A : Type) (B : A → Type) (C : Σ A B → Type)
  : ((a : A) (b : B a) → C (a, b)) → (p : Σ A B) → C p
  ≔ g p ↦ g (p .pr1) (p .pr2)
`Computation proof
def ind_Σ_comput (A : Type) (B : A → Type) (C : Σ A B → Type)
  (g : (a : A) (b : B a) → C (a, b)) (a : A) (b : B a)
  : Id (C (a, b)) (ind_Σ A B C g (a, b)) (g a b)
  ≔ refl (g a b)

`Function
def ac (A B : Type) (R : A → B → Type)
  : ((x : A) → Σ B (y ↦ R x y)) → (Σ (A → B) (f ↦ (x : A) → R x (f x)))
  ≔ g ↦ (x ↦ g x .pr1, x ↦ g x .pr2)

`Type
def Magma : Type ≔ sig ( A : Type, m : A → A → A )

`Type
def PointedMagma : Type ≔ sig ( A : Type, m : A → A → A, e : A )


{` 1.7 Coproduct types `}

`Type
def Coproduct (A B : Type) : Type ≔ data [ inl. (_ : A) | inr. (_ : B) ]
notation(2) A "＋" B ≔ Coproduct A B

`Type
def 𝟘 : Type ≔ data []

`Function
def rec_＋ (A B C : Type) : (A → C) → (B → C) → A ＋ B → C ≔ g0 g1 ↦ [
| inl. a ↦ g0 a
| inr. b ↦ g1 b]
`Computation proofs
def rec_＋_comput1 (A B C : Type) (g0 : A → C) (g1 : B → C) (a : A)
  : Id C (rec_＋ A B C g0 g1 (inl. a)) (g0 a)
  ≔ refl (g0 a)
def rec_＋_comput2 (A B C : Type) (g0 : A → C) (g1 : B → C) (b : B)
  : Id C (rec_＋ A B C g0 g1 (inr. b)) (g1 b)
  ≔ refl (g1 b)

`Function
def rec_𝟘 (C : Type) : 𝟘 → C ≔ [ ]

`Function
def ind_＋ (A B : Type) (C : A ＋ B → Type)
  : ((a : A) → C (inl. a)) → ((b : B) → C (inr. b)) → (x : A ＋ B) → C x
  ≔ g0 g1 ↦ [ inl. a ↦ g0 a | inr. b ↦ g1 b ]
`Computation proofs
def ind_＋_comput1 (A B : Type) (C : A ＋ B → Type) (g0 : (a : A) → C (inl. a))
  (g1 : (b : B) → C (inr. b)) (a : A)
  : Id (C (inl. a)) (ind_＋ A B C g0 g1 (inl. a)) (g0 a)
  ≔ refl (g0 a)
def ind_＋_comput2 (A B : Type) (C : A ＋ B → Type) (g0 : (a : A) → C (inl. a))
  (g1 : (b : B) → C (inr. b)) (b : B)
  : Id (C (inr. b)) (ind_＋ A B C g0 g1 (inr. b)) (g1 b)
  ≔ refl (g1 b)

`Function
def ind_𝟘 (C : 𝟘 → Type) : (z : 𝟘) → C z ≔ [ ]


{` 1.8 The type of booleans `}

`Type
def 𝟚 : Type ≔ data [ 0₂. | 1₂. ]
`Function
def rec_2 (C : Type) : C → C → 𝟚 → C ≔ c0 c1 ↦ [ 0₂. ↦ c0 | 1₂. ↦ c1 ]
`Computation rules
def rec_2_comput1 (C : Type) (c0 c1 : C) : Id C (rec_2 C c0 c1 0₂.) c0
  ≔ refl c0
def rec_2_comput2 (C : Type) (c0 c1 : C) : Id C (rec_2 C c0 c1 1₂.) c1
  ≔ refl c1

`Function
def ind_2 (C : 𝟚 → Type) : C 0₂. → C 1₂. → (x : 𝟚) → C x ≔ c0 c1 ↦ [
| 0₂. ↦ c0
| 1₂. ↦ c1]
`Computation rules
def ind_2_comput1 (C : 𝟚 → Type) (c0 : C 0₂.) (c1 : C 1₂.)
  : Id (C 0₂.) (ind_2 C c0 c1 0₂.) c0
  ≔ refl c0
def ind_2_comput2 (C : 𝟚 → Type) (c0 : C 0₂.) (c1 : C 1₂.)
  : Id (C 1₂.) (ind_2 C c0 c1 1₂.) c1
  ≔ refl c1

`Proof
def uniq_2 (x : 𝟚) : (Id 𝟚 x 0₂.) ＋ (Id 𝟚 x 1₂.) ≔ match x [
| 0₂. ↦ inl. (refl (0₂. : 𝟚))
| 1₂. ↦ inr. (refl (1₂. : 𝟚))]

`Type
def unnamed.1_8_1 (A B : Type) : 𝟚 → Type ≔ [ 0₂. ↦ A | 1₂. ↦ B ]

`Type
def altCoproduct (A B : Type) : Type ≔ Σ 𝟚 (rec_2 Type A B)
notation(2) A "alt＋" B ≔ altCoproduct A B

`Definition
def altinl (A B : Type) (a : A) : A alt＋ B ≔ (0₂., a)
def altinr (A B : Type) (b : B) : A alt＋ B ≔ (1₂., b)
 
`Type
def alt2CartesianProduct (A B : Type) : Type ≔ Π 𝟚 (rec_2 Type A B)
notation(2) A "alt2×" B ≔ alt2CartesianProduct A B

`Definition
def alt2pair (A B : Type) : A → B → A alt2× B ≔ a b ↦ [ 0₂. ↦ a | 1₂. ↦ b ]

`Functions
def alt2pr1 (A B : Type) (p : A alt2× B) : A ≔ p 0₂.
def alt2pr2 (A B : Type) (p : A alt2× B) : B ≔ p 1₂.


{` 1.9 The natural numbers `}

`Type
def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

`Function
def rec_ℕ (C : Type) : C → (ℕ → C → C) → ℕ → C ≔ c0 cs ↦ [
| zero. ↦ c0
| suc. n ↦ cs n (rec_ℕ C c0 cs n)]
`Computation proofs
def rec_ℕ_comput1 (C : Type) (c0 : C) (cs : ℕ → C → C)
  : Id C (rec_ℕ C c0 cs 0) c0
  ≔ refl c0
def rec_ℕ_comput2 (C : Type) (c0 : C) (cs : ℕ → C → C) (n : ℕ)
  : Id C (rec_ℕ C c0 cs (suc. n)) (cs n (rec_ℕ C c0 cs n))
  ≔ refl (cs n (rec_ℕ C c0 cs n))

`Function
def double : ℕ → ℕ ≔ [ zero. ↦ 0 | suc. n ↦ suc. (suc. (double n)) ]

`Function
def add : ℕ → ℕ → ℕ ≔ [ zero. ↦ n ↦ n | suc. m ↦ n ↦ suc. (add m n) ]
notation(2) m "+" n ≔ add m n

`Computation proof
def unnamed.1_9_1 : Id ℕ (add 2 2) 4 ≔ refl (4 : ℕ)

`Function
def ind_ℕ (C : ℕ → Type)
  : C zero. → ((n : ℕ) → C n → C (suc. n)) → (n : ℕ) → C n
  ≔ c0 cs ↦ [ zero. ↦ c0 | suc. n ↦ cs n (ind_ℕ C c0 cs n) ]
`Computation proofs
def ind_ℕ_comput1 (C : ℕ → Type) (c0 : C 0) (cs : (n : ℕ) → C n → C (suc. n))
  : Id (C 0) (ind_ℕ C c0 cs 0) c0
  ≔ refl c0
def ind_ℕ_comput2 (C : ℕ → Type) (c0 : C 0) (cs : (n : ℕ) → C n → C (suc. n))
  (n : ℕ)
  : Id (C (suc. n)) (ind_ℕ C c0 cs (suc. n)) (cs n (ind_ℕ C c0 cs n))
  ≔ refl (cs n (ind_ℕ C c0 cs n))

`Proof
def assoc (i j k : ℕ) : Id ℕ (i + (j + k)) ((i + j) + k) ≔ match i [
| zero. ↦ refl (j + k)
| suc. i ↦ suc. (assoc i j k)]


{` 1.10 Pattern matching and recursion `}

`In Narya we do everything by pattern matching.


{` 1.11 Propositions as types `}

`Type
def ¬ : Type → Type ≔ A ↦ A → 𝟘

`Proof
def unnamed.1_11_1 (A B : Type) : (¬ A) × (¬ B) → ¬ (A ＋ B) ≔ z ↦ [
| inl. a ↦ z .pr1 a
| inr. b ↦ z .pr2 b]

`Proof
def unnamed.1_11_2 (A : Type) (P Q : A → Type)
  : ((x : A) → (P x × Q x)) → ((x : A) → P x) × ((x : A) → Q x)
  ≔ p ↦ (x ↦ p x .pr1, x ↦ p x .pr2)

`Type
def leq : ℕ → ℕ → Type ≔ n m ↦ Σ ℕ (k ↦ Id ℕ (n + k) m)

notation(2) m "≤" n ≔ leq m n

`Type
def lt : ℕ → ℕ → Type ≔ n m ↦ Σ ℕ (k ↦ Id ℕ (n + suc. k) m)

notation(2) m "<" n ≔ lt m n

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
def IndiscernibilityOfIdenticals_computId (A : Type) (C : A → Type) (x : A)
  : Id (C x → C x) (IndiscernibilityOfIdenticals A C x x (refl x)) (id (C x))
  ≔ c ⤇ (C x)⁽ᵉᵉ⁾ (refl (C x) .liftr c.0) (refl c.1) .trr c.2

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
def Ind_Id_comput (A : Type) (C : (x y : A) → Id A x y → Type)
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
def Ind'_Id_comput (A : Type) (a : A) (C : (x : A) → Id A a x → Type)
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
    let Ind'_Id_comput_statement : Ind'_Id_statement → Type
      ≔ Ind'_Id ↦
        (A : Type) (a : A) (C : (x : A) → Id A a x → Type) (c : C a (refl a))
        → Id (C a (refl a)) (Ind'_Id A a C c a (refl a)) c in
    let Ind_Id_statement
      ≔ (A : Type) (C : (x y : A) → Id A x y → Type) →
        ((x : A) → C x x (refl x)) → (x y : A) (p : Id A x y)
        → C x y p in
    let Ind_Id_comput_statement : Ind_Id_statement → Type
      ≔ Ind_Id ↦
        (A : Type) (C : (x y : A) → Id A x y → Type)
        (c : (x : A) → C x x (refl x)) (x : A)
        → Id (C x x (refl x)) (Ind_Id A C c x x (refl x)) (c x) in
    (Σ Ind'_Id_statement Ind'_Id_comput_statement)
    → Σ Ind_Id_statement Ind_Id_comput_statement
  ≔ Ind' ↦
  let Ind'_Id ≔ Ind' .pr1 in
  let Ind'_Id_comput ≔ Ind' .pr2 in
  (A C c x y p ↦ Ind'_Id A x (C x) (c x) y p,
   A C c x ↦ Ind'_Id_comput A x (C x) (c x))

`Proof
def unnamed.1_12_1_2
  : let Ind_Id_statement
      ≔ (A : Type) (C : (x y : A) → Id A x y → Type) →
        ((x : A) → C x x (refl x)) → (x y : A) (p : Id A x y)
        → C x y p in
    let Ind_Id_comput_statement : Ind_Id_statement → Type
      ≔ Ind_Id ↦
        (A : Type) (C : (x y : A) → Id A x y → Type)
        (c : (x : A) → C x x (refl x)) (x : A)
        → Id (C x x (refl x)) (Ind_Id A C c x x (refl x)) (c x) in
    let Ind'_Id_statement
      ≔ (A : Type) (a : A) (C : (x : A) → Id A a x → Type) → C a (refl a) →
        (x : A) → (p : Id A a x)
        → C x p in
    let Ind'_Id_comput_statement : Ind'_Id_statement → Type
      ≔ Ind'_Id ↦
        (A : Type) (a : A) (C : (x : A) → Id A a x → Type) (c : C a (refl a))
        → Id (C a (refl a)) (Ind'_Id A a C c a (refl a)) c in
    (Σ Ind_Id_statement Ind_Id_comput_statement)
    → Σ Ind'_Id_statement Ind'_Id_comput_statement
  ≔ Ind ↦
  let Ind_Id ≔ Ind .pr1 in
  let Ind_Id_comput ≔ Ind .pr2 in
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
     (Ind_Id_comput A D d a) (refl C) (refl c))

{` 1.12.3 Disequality `}

`Type
def neq (A : Type) (x y : A) : Type ≔ ¬ (Id A x y)
