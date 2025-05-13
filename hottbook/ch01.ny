{` Chapter 1 - Type theory `}

{` 1.2 Function types `}


{` 1.3 Universes and families `}

`def Fin : ℕ → Type ≔ ?


{` 1.4 Dependent function types (Π-types) `}

`def fmax (n : ℕ) : Fin (ℕ.plus n 1) := ?

`Function definition
def id (A : Type) : A → A ≔ x ↦ x

`Function definition
def swap (A B C : Type) : (A → B → C) → (B → A → C) ≔ g b a ↦ g a b


{` 1.5 Product types `}

`Type definition
def CartesianProduct (A B : Type) : Type ≔ sig ( pr₁ : A, pr₂ : B )

notation 2 CartesianProduct_notation : A "×" B ≔ CartesianProduct A B

`Type definition
def 𝟙 : Type ≔ data [ ★. ]

`Functon definition
def rec_× (A B C : Type) : (A → B → C) → A × B → C
  ≔ g x ↦ g (x .pr₁) (x .pr₂)

`Function definition
def rec_1 (C : Type) : C → 𝟙 → C ≔ c ↦ [ ★. ↦ c ]
`Function definition
def uniq_× (A B : Type) (x : A × B) : Id (A × B) (x .pr₁, x .pr₂) x ≔ refl x

`Function definition
def ind_× (A B : Type) (C : A × B → Type)
  : ((x : A) (y : B) → C (x, y)) → (x : A × B) → C x
  ≔ g z ↦ g (z .pr₁) (z .pr₂)

`Function definition
def ind_1 (C : 𝟙 → Type) : C ★. → (x : 𝟙) → C x ≔ c ↦ [ ★. ↦ c ]

`Function definition
def uniq_1 (x : 𝟙) : Id 𝟙 x ★. ≔ match x [ ★. ↦ refl (★. : 𝟙) ]


{` 1.6 Dependent pair types (Σ-types) `}

`Type definition
def Σ (A : Type) (B : A → Type) : Type ≔ sig ( pr₁ : A, pr₂ : B pr₁ )

`Type definition
def alt.CartesianProduct (A B : Type) : Type ≔ Σ A (x ↦ B)

notation 2 alt.CartesianProduct_notation : A "×Σ" B
  ≔ alt.CartesianProduct A B

`Function definition
def rec_Σ (A : Type) (B : A → Type) (C : Type)
  : ((x : A) → B x → C) → Σ A B → C
  ≔ g z ↦ g (z .pr₁) (z .pr₂)

`Function definition
def ind_Σ (A : Type) (B : A → Type) (C : Σ A B → Type)
  : ((a : A) (b : B a) → C (a, b)) → (p : Σ A B) → C p
  ≔ g z ↦ g (z .pr₁) (z .pr₂)

`Function definition
def ac (A B : Type) (R : A → B → Type)
  : ((x : A) → Σ B (y ↦ R x y)) → (Σ (A → B) (f ↦ (x : A) → R x (f x)))
  ≔ g ↦ (x ↦ g x .pr₁, x ↦ g x .pr₂)

`Type definition
def Magma : Type ≔ sig ( A : Type, m : A → A → A )

`Type definition
def PointedMagma : Type ≔ sig ( A : Type, m : A → A → A, e : A )


{` 1.7 Coproduct types `}

`Type definition
def Coproduct (A B : Type) : Type ≔ data [ inl. (_ : A) | inr. (_ : B) ]

notation 2 Coproduct_notation : A "＋" B ≔ Coproduct A B

`Type definition
def 𝟘 : Type ≔ data []

`Function definition
def rec_＋ (A B C : Type) : (A → C) → (B → C) → A ＋ B → C ≔ g0 g1 ↦ [
| inl. a ↦ g0 a
| inr. b ↦ g1 b]

`Function definition
def rec_𝟘 (C : Type) : 𝟘 → C ≔ [ ]

`Function definition
def ind_＋ (A B : Type) (C : A ＋ B → Type)
  : ((a : A) → C (inl. a)) → ((b : B) → C (inr. b)) → (x : A ＋ B) → C x
  ≔ g0 g1 ↦ [ inl. a ↦ g0 a | inr. b ↦ g1 b ]

`Function definition
def ind_𝟘 (C : 𝟘 → Type) : (z : 𝟘) → C z ≔ [ ]


{` 1.8 The type of booleans `}

`Type definition
def 𝟚 : Type ≔ data [ 0₂. | 1₂. ]
`Function definition
def rec_2 (C : Type) : C → C → 𝟚 → C ≔ c0 c1 ↦ [ 0₂. ↦ c0 | 1₂. ↦ c1 ]

`Function definition
def ind_2 (C : 𝟚 → Type) : C 0₂. → C 1₂. → (x : 𝟚) → C x ≔ c0 c1 ↦ [
| 0₂. ↦ c0
| 1₂. ↦ c1]

`Proof
def unnamed.1_8_1 (x : 𝟚) : (Id 𝟚 x 0₂.) ＋ (Id 𝟚 x 1₂.) ≔ match x [
| 0₂. ↦ inl. (refl (0₂. : 𝟚))
| 1₂. ↦ inr. (refl (1₂. : 𝟚))]


{` 1.9 The natural numbers `}

`Type definition
def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

`Function definition
def double : ℕ → ℕ ≔ [ zero. ↦ zero. | suc. n ↦ suc. (suc. (double n)) ]

`Function definition
def add : ℕ → ℕ → ℕ ≔ [ zero. ↦ n ↦ n | suc. m ↦ n ↦ suc. (add m n) ]

notation 2 add_notation : m "+" n ≔ add m n

`Function definition
def rec_ℕ (C : Type) : C → (ℕ → C → C) → ℕ → C ≔ c0 cs ↦ [
| zero. ↦ c0
| suc. n ↦ cs n (rec_ℕ C c0 cs n)]

`Function definition
def ind_ℕ (C : ℕ → Type)
  : C zero. → ((n : ℕ) → C n → C (suc. n)) → (n : ℕ) → C n
  ≔ c0 cs ↦ [ zero. ↦ c0 | suc. n ↦ cs n (ind_ℕ C c0 cs n) ]

`Proof
def assoc (i j k : ℕ) : Id ℕ (i + (j + k)) ((i + j) + k) ≔ match i [
| zero. ↦ refl (j + k)
| suc. i ↦
    refl ((n ↦ suc. n) : ℕ → ℕ) (i + (j + k)) ((i + j) + k) (assoc i j k)]


{` 1.11 Propositions as types `}

`Type definition
def ¬ : Type → Type ≔ A ↦ A → 𝟘

`Proof
def unnamed.1_11_1 (A B : Type) : (¬ A) × (¬ B) → ¬ (A ＋ B) ≔ z ↦ [
| inl. a ↦ z .pr₁ a
| inr. b ↦ z .pr₂ b]

`Proof
def unnamed.1_11_2 (A : Type) (P Q : A → Type)
  : ((x : A) → (P x × Q x)) → ((x : A) → P x) × ((x : A) → Q x)
  ≔ p ↦ (x ↦ p x .pr₁, x ↦ p x .pr₂)

`Type definition
def leq : ℕ → ℕ → Type ≔ n m ↦ Σ ℕ (k ↦ Id ℕ (n + k) m)

notation 2 leq_notation : m "≤" n ≔ leq m n

`Type definition
def lt : ℕ → ℕ → Type ≔ n m ↦ Σ ℕ (k ↦ Id ℕ (n + suc. k) m)

notation 2 lt_notation : m "<" n ≔ lt m n

`Type definition
def Semigroup : Type ≔ sig (
  A : Type,
  m : A → A → A,
  assoc : (x y z : A) → Id A (m x (m y z)) (m (m x y) z) )

`Type definition
def unnamed.1_11_3 (A : Type) (a b : A) : Type ≔ (P : A → Type) → P a → P b

`Proof
def unnamed.1_11_4 : ¬ 𝟘 ≔ [ ]


{` 1.12 Identity types `}

`Type definition
def isFibrant (A : Type) : Type ≔ codata [
| x .trr.e : A.0 → A.1
| x .trl.e : A.1 → A.0
| x .liftr.e : (a₀ : A.0) → A.2 a₀ (x.2 .trr.1 a₀)
| x .liftl.e : (a₁ : A.1) → A.2 (x.2 .trl.1 a₁) a₁
| x .id.e : (a₀ : A.0) → (a₁ : A.1) → isFibrant (A.2 a₀ a₁) ]

`Type definition
def Fib : Type ≔ sig ( t : Type, f : isFibrant t )

`Proof
def 𝕗Id (A : Fib) (x y : A .t) : isFibrant (Id A .t x y) ≔ refl A .f .id x y

`Type definition
def Id𝕗 (A : Fib) (x y : A .t) : Fib ≔ (Id (A .t) x y, 𝕗Id A x y)

`Proof / Function definition
def IndiscernibilityOfIdenticals (A : Type) (C : A → Fib) (x y : A)
  : Id A x y → C x .t → C y .t
  ≔ p ↦ refl C x y p .f .trr

`Proof
def IndiscernibilityOfIdenticals_eq (A : Type) (C : A → Fib) (x : A)
  : Id (C x .t → C x .t) (IndiscernibilityOfIdenticals A C x x (refl x))
      (id (C x .t))
  ≔ c0 c1 c2 ↦
    (C x .f)⁽ᵉᵉ⁾
    .id.1 c0 (refl (C x .f) .trr c0) (refl (C x .f) .liftr c0) c1 c1
      (refl c1)
    .trr c2

{` 1.12.1 Path induction `}

`Proof / Function definition
def Ind_Id (A : Fib) (C : (x y : A .t) → Id (A .t) x y → Fib)
  : ((x : A .t) → C x x (refl x) .t) → (x y : A .t) (p : Id (A .t) x y)
    → C x y p .t
  ≔ c x y p ↦
  let idfib_2 ≔ (A .f)⁽ᵉᵉ⁾ .id.2 x x (refl x) x y p in
  let y2 ≔ idfib_2 .trr.1 (refl x) in
  let p2 ≔ sym (idfib_2 .liftr.1 (refl x)) in
  let Cfib ≔ refl (C x) x y y2 (refl x) p p2 .f in
  Cfib .trr (c x)

`Proof
def Ind_Id_eq (A : Fib) (C : (x y : A .t) → Id (A .t) x y → Fib)
  (c : (x : A .t) → C x x (refl x) .t) (x : A .t)
  : Id (C x x (refl x) .t) (Ind_Id A C c x x (refl x)) (c x)
  ≔
  let idfib_2 ≔ (A .f)⁽ᵉᵉ⁾ .id.2 x x (refl x) x x (refl x) in
  let y2 ≔ idfib_2 .trr (refl x) in
  let p2 ≔ sym (idfib_2 .liftr (refl x)) in
  let Cfib ≔ refl (C x) x x y2 (refl x) (refl x) p2 .f in
  let J ≔ Ind_Id A C c x x (refl x) in
  let idfib2_3
    ≔ (A .f)⁽ᵉᵉᵉ⁾
        .id.2 x x (refl x) x x y2 (refl x) (refl x) p2 x x (refl x) x x
          (refl x) (refl x) (refl x) x⁽ᵉᵉ⁾
        .id.2 (refl x) (refl x) x⁽ᵉᵉ⁾ (refl x) (refl x) x⁽ᵉᵉ⁾ in
  (C x)⁽ᵉᵉ⁾ x x y2 x x (refl x) (refl x) (refl x) (idfib2_3 .trr.1 x⁽ᵉᵉ⁾)
      (refl x) (refl x) p2 (refl x) (refl x) x⁽ᵉᵉ⁾ x⁽ᵉᵉ⁾ x⁽ᵉᵉ⁾
      (idfib2_3 .liftr x⁽ᵉᵉ⁾)⁽³¹²⁾
    .f
    .id.1 (c x) J (Cfib .liftr (c x)) (c x) (c x) (refl (c x))
    .trr (refl (c x))

`Proof
def Ind'_Id (A : Fib) (a : A .t) (C : (x : A .t) → Id (A .t) a x → Fib)
  : C a (refl a) .t → (x : A .t) (p : Id (A .t) a x) → C x p .t
  ≔ c x p ↦
  let idfib_2 ≔ A⁽ᵉᵉ⁾ .f .id.2 a a (refl a) a x p in
  let x2 ≔ idfib_2 .trr (refl a) in
  let p2 ≔ sym (idfib_2 .liftr (refl a)) in
  refl C a x x2 (refl a) p p2 .f .trr c

`Proof
def Ind'_Id_eq (A : Fib) (a : A .t) (C : (x : A .t) → Id (A .t) a x → Fib)
  (c : C a (refl a) .t)
  : Id (C a (refl a) .t) (Ind'_Id A a C c a (refl a)) c
  ≔
  let idfib_2 ≔ A⁽ᵉᵉ⁾ .f .id.2 a a (refl a) a a (refl a) in
  let x2 ≔ idfib_2 .trr (refl a) in
  let p2 ≔ sym (idfib_2 .liftr (refl a)) in
  let Cfib ≔ refl C a a x2 (refl a) (refl a) p2 .f in
  let idfib2_3
    ≔ (A .f)⁽ᵉᵉᵉ⁾
        .id.2 a a (refl a) a a x2 (refl a) (refl a) p2 a a (refl a) a a
          (refl a) (refl a) (refl a) a⁽ᵉᵉ⁾
        .id.2 (refl a) (refl a) a⁽ᵉᵉ⁾ (refl a) (refl a) a⁽ᵉᵉ⁾ in
  C⁽ᵉᵉ⁾ a a x2 a a (refl a) (refl a) (refl a) (idfib2_3 .trr a⁽ᵉᵉ⁾) (refl a)
      (refl a) p2 (refl a) (refl a) a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾
      (idfib2_3 .liftr a⁽ᵉᵉ⁾)⁽³¹²⁾
    .f
    .id.1 c (Cfib .trr c) (Cfib .liftr c) c c (refl c)
    .trr (refl c)

{` 1.12.2 Equivalence of path induction and based path induction `}

`Proof
def unnamed.1_12_1_1
  : let Ind'_Id_statement
      ≔ ((A : Fib) (a : A .t) (C : (x : A .t) → Id (A .t) a x → Fib) →
         C a (refl a) .t → (x : A .t) → (p : Id (A .t) a x)
         → C x p .t) in
    let Ind_Id_statement
      ≔ (A : Fib) (C : (x y : A .t) → Id (A .t) x y → Fib) →
        ((x : A .t) → C x x (refl x) .t) → (x y : A .t) (p : Id (A .t) x y)
        → C x y p .t in
    Ind'_Id_statement → Ind_Id_statement
  ≔ Ind'_Id A C c x y p ↦ Ind'_Id A x (C x) (c x) y p

{`
`Nothing is gained from this proof, since it is way easier to prove Ind'_Id_statement directly, as done in Ind'_Id_eq. Still, the true reason that I'm skipping it is because I don't know if it is possible to prove this using universes, since I'm not sure if we can prove that universes are fibrant.
`Proof
def unnamed.1_12_1_2
  : let Ind_Id_statement
      ≔ (A : Fib) (C : (x y : A .t) → Id (A .t) x y → Fib) →
        ((x : A .t) → C x x (refl x) .t) → (x y : A .t) (p : Id (A .t) x y)
        → C x y p .t in
    let Ind'_Id_statement
      ≔ (A : Fib) (a : A .t) (C : (x : A .t) → Id (A .t) a x → Fib) →
        C a (refl a) .t → (x : A .t) → (p : Id (A .t) a x)
        → C x p .t in
    Ind_Id_statement → Ind'_Id_statement
  ≔ Ind_Id A a C c x p ↦
  let D : (x y : A .t) → (Id (A .t) x y) → Fib ≔ x y p ↦ (
    (C : (z : A .t) → Id (A .t) x z → Fib) → C x (refl x) .t → C y p .t,
    ?) in
  let d : (x : A .t) → D x x (refl x) .t ≔ x C c ↦ c in
  let f : (x y : A .t) (p : Id (A .t) x y) → D x y p .t ≔ Ind_Id A D d in
  f a x p C c
`}
`Nevertheless, it is possible to prove it without using universes, but using the fibrancy of function types and sigma types, which is quite involved. Here I will then develop that required theory.

section eq ≔

  def eq (A : Type) (a : A) : A → Type ≔ data [ rfl. : eq A a a ]

  def cat (A : Type) (x y z : A) (u : eq A x y) (v : eq A y z) : eq A x z
    ≔ match v [ rfl. ↦ u ]

  def cat3 (A : Type) (x y z w : A) (p : eq A x y) (q : eq A y z)
    (r : eq A z w)
    : eq A x w
    ≔ match q, r [ rfl., rfl. ↦ p ]

  def idl (A : Type) (a0 a1 : A) (a2 : eq A a0 a1)
    : eq (eq A a0 a1) (cat A a0 a0 a1 rfl. a2) a2
    ≔ match a2 [ rfl. ↦ rfl. ]

  def inv (A : Type) (a0 a1 : A) (a2 : eq A a0 a1) : eq A a1 a0 ≔ match a2 [
  | rfl. ↦ rfl.]

  def ap (A B : Type) (f : A → B) (a0 a1 : A) (a2 : eq A a0 a1)
    : eq B (f a0) (f a1)
    ≔ match a2 [ rfl. ↦ rfl. ]

  def ap_ap (A B C : Type) (f : A → B) (g : B → C) (a0 a1 : A)
    (a2 : eq A a0 a1)
    : eq (eq C (g (f a0)) (g (f a1)))
        (ap B C g (f a0) (f a1) (ap A B f a0 a1 a2))
        (ap A C (x ↦ g (f x)) a0 a1 a2)
    ≔ match a2 [ rfl. ↦ rfl. ]

  def trr (A : Type) (P : A → Type) (a0 a1 : A) (a2 : eq A a0 a1) (p : P a0)
    : P a1
    ≔ match a2 [ rfl. ↦ p ]

  def trr2 (A : Type) (B : Type) (P : A → B → Type) (a0 a1 : A)
    (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p : P a0 b0)
    : P a1 b1
    ≔ match a2, b2 [ rfl., rfl. ↦ p ]

  def trl2 (A : Type) (B : Type) (P : A → B → Type) (a0 a1 : A)
    (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p : P a1 b1)
    : P a0 b0
    ≔ match a2, b2 [ rfl., rfl. ↦ p ]

  def trr2_ap (A B : Type) (P : A → B → Type) (C D : Type) (Q : C → D → Type)
    (f : A → C) (g : B → D) (h : (x : A) (y : B) → P x y → Q (f x) (g y))
    (a0 a1 : A) (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p : P a0 b0)
    : eq (Q (f a1) (g b1)) (h a1 b1 (trr2 A B P a0 a1 a2 b0 b1 b2 p))
        (trr2 C D Q (f a0) (f a1) (ap A C f a0 a1 a2) (g b0) (g b1)
           (ap B D g b0 b1 b2) (h a0 b0 p))
    ≔ match a2, b2 [ rfl., rfl. ↦ rfl. ]

  def unwhiskerR (A : Type) (a0 a1 a2 : A) (a01 a01' : eq A a0 a1)
    (a12 : eq A a1 a2)
    (a02 : eq (eq A a0 a2) (cat A a0 a1 a2 a01 a12) (cat A a0 a1 a2 a01' a12))
    : eq (eq A a0 a1) a01 a01'
    ≔ match a12 [ rfl. ↦ a02 ]

end

def eq ≔ eq.eq

section sq ≔

  def sq (A : Type) (a00 : A)
    : (a01 : A) (a02 : eq A a00 a01) (a10 a11 : A) (a12 : eq A a10 a11)
      (a20 : eq A a00 a10) (a21 : eq A a01 a11)
      → Type
    ≔ data [
  | rfl. : sq A a00 a00 rfl. a00 a00 rfl. rfl. rfl. ]

  def hrfl (A : Type) (a0 a1 : A) (a2 : eq A a0 a1)
    : sq A a0 a0 rfl. a1 a1 rfl. a2 a2
    ≔ match a2 [ rfl. ↦ rfl. ]

  def nat_toid (A : Type) (f : A → A) (p : (x : A) → eq A (f x) x)
    (a0 a1 : A) (a2 : eq A a0 a1)
    : sq A (f a0) (f a1) (eq.ap A A f a0 a1 a2) a0 a1 a2 (p a0) (p a1)
    ≔ match a2 [ rfl. ↦ hrfl A (f a0) a0 (p a0) ]

  def ap (A B : Type) (f : A → B) (a00 a01 : A) (a02 : eq A a00 a01)
    (a10 a11 : A) (a12 : eq A a10 a11) (a20 : eq A a00 a10)
    (a21 : eq A a01 a11) (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
    : sq B (f a00) (f a01) (eq.ap A B f a00 a01 a02) (f a10) (f a11)
        (eq.ap A B f a10 a11 a12) (eq.ap A B f a00 a10 a20)
        (eq.ap A B f a01 a11 a21)
    ≔ match a22 [ rfl. ↦ rfl. ]

  def act02 (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A)
    (a12 : eq A a10 a11) (a20 : eq A a00 a10) (a21 : eq A a01 a11)
    (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21) (a02' : eq A a00 a01)
    (p : eq (eq A a00 a01) a02 a02')
    : sq A a00 a01 a02' a10 a11 a12 a20 a21
    ≔ match p [ rfl. ↦ a22 ]

  def act20 (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A)
    (a12 : eq A a10 a11) (a20 : eq A a00 a10) (a21 : eq A a01 a11)
    (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21) (a20' : eq A a00 a10)
    (p : eq (eq A a00 a10) a20 a20')
    : sq A a00 a01 a02 a10 a11 a12 a20' a21
    ≔ match p [ rfl. ↦ a22 ]

  def to_cat (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A)
    (a12 : eq A a10 a11) (a20 : eq A a00 a10) (a21 : eq A a01 a11)
    (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
    : eq (eq A a00 a11) (eq.cat A a00 a01 a11 a02 a21)
        (eq.cat A a00 a10 a11 a20 a12)
    ≔ match a22 [ rfl. ↦ rfl. ]

  def to_cat3 (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A)
    (a12 : eq A a10 a11) (a20 : eq A a00 a10) (a21 : eq A a01 a11)
    (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
    : eq (eq A a10 a11) a12
        (eq.cat3 A a10 a00 a01 a11 (eq.inv A a00 a10 a20) a02 a21)
    ≔ match a22 [ rfl. ↦ rfl. ]

  def all_rfl_21 (A : Type) (a : A) (a2 : eq A a a)
    (a22 : sq A a a rfl. a a rfl. rfl. a2)
    : eq (eq A a a) a2 rfl.
    ≔ eq.cat (eq A a a) a2 (eq.cat A a a a rfl. a2) rfl.
        (eq.inv (eq A a a) (eq.cat A a a a rfl. a2) a2 (eq.idl A a a a2))
        (to_cat A a a rfl. a a rfl. rfl. a2 a22)

  def unact21 (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A)
    (a12 : eq A a10 a11) (a20 : eq A a00 a10) (a21 : eq A a01 a11)
    (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21) (a21' : eq A a01 a11)
    (a22' : sq A a00 a01 a02 a10 a11 a12 a20 a21')
    : eq (eq A a01 a11) a21 a21'
    ≔ match a22 [
  | rfl. ↦ eq.inv (eq A a00 a00) a21' rfl. (all_rfl_21 A a00 a21' a22')]

  def cancel_12_eq_21 (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a11 : A)
    (a12 : eq A a01 a11) (a20 : eq A a00 a01)
    (a22 : sq A a00 a01 a02 a01 a11 a12 a20 a12)
    : eq (eq A a00 a01) a02 a20
    ≔ eq.unwhiskerR A a00 a01 a11 a02 a20 a12
        (to_cat A a00 a01 a02 a01 a11 a12 a20 a12 a22)

end

def selfnat (A : Type) (f : A → A) (H : (x : A) → eq A (f x) x) (a : A)
  : eq (eq A (f (f a)) (f a)) (eq.ap A A f (f a) a (H a)) (H (f a))
  ≔ sq.cancel_12_eq_21 A (f (f a)) (f a) (eq.ap A A f (f a) a (H a)) a (H a)
      (H (f a)) (sq.nat_toid A f H (f a) a (H a))

def eqv (A B : Type) : Type ≔ sig (
  to : A → B,
  fro : B → A,
  fro_to : (a : A) → eq A (fro (to a)) a,
  to_fro : (b : B) → eq B (to (fro b)) b,
  to_fro_to : (a : A)
              → eq (eq B (to (fro (to a))) (to a))
                  (eq.ap A B to (fro (to a)) a (fro_to a)) (to_fro (to a)) )

notation 1 eqv : A "≅" B ≔ eqv A B

def fro_to_fro (A B : Type) (e : A ≅ B) (y : B)
  : eq (eq A (e .fro (e .to (e .fro y))) (e .fro y))
      (eq.ap B A (e .fro) (e .to (e .fro y)) y (e .to_fro y))
      (e .fro_to (e .fro y))
  ≔
  let f ≔ e .to in
  let g ≔ e .fro in
  let ap_f ≔ eq.ap A B f in
  let ap_g ≔ eq.ap B A g in
  let fg : B → B ≔ x ↦ e .to (e .fro x) in
  let ap_fg ≔ eq.ap B B fg in
  let gf : A → A ≔ x ↦ e .fro (e .to x) in
  let ap_gf ≔ eq.ap A A gf in
  let gfg : B → A ≔ x ↦ e .fro (e .to (e .fro x)) in
  let ap_gfg ≔ eq.ap B A gfg in
  let fgfg : B → B ≔ x ↦ e .to (e .fro (e .to (e .fro x))) in
  let gfgfg : B → A ≔ x ↦ e .fro (e .to (e .fro (e .to (e .fro x)))) in
  let η ≔ e .fro_to in
  let ε ≔ e .to_fro in
  sq.unact21 A (gfgfg y) (gfg y)
    (eq.ap A A gf (gfg y) (g y) (ap_g (fg y) y (ε y))) (gfg y) (g y)
    (ap_g (fg y) y (ε y)) (η (gfg y)) (ap_g (fg y) y (ε y))
    (sq.act20 A (gfgfg y) (gfg y)
       (eq.ap A A gf (gfg y) (g y) (ap_g (fg y) y (ε y))) (gfg y) (g y)
       (ap_g (fg y) y (ε y)) (ap_g (fgfg y) (fg y) (ε (fg y)))
       (ap_g (fg y) y (ε y))
       (sq.act02 A (gfgfg y) (gfg y)
          (ap_g (fgfg y) (fg y) (ap_fg (fg y) y (ε y))) (gfg y) (g y)
          (ap_g (fg y) y (ε y)) (ap_g (fgfg y) (fg y) (ε (fg y)))
          (ap_g (fg y) y (ε y))
          (sq.ap B A g (fgfg y) (fg y) (ap_fg (fg y) y (ε y)) (fg y) y (ε y)
             (ε (fg y)) (ε y) (sq.nat_toid B fg ε (fg y) y (ε y)))
          (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
          (eq.cat (eq A (gfgfg y) (gfg y))
             (ap_g (fgfg y) (fg y) (ap_fg (fg y) y (ε y)))
             (ap_gfg (fg y) y (ε y))
             (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
             (eq.ap_ap B B A fg g (fg y) y (ε y))
             (eq.inv (eq A (gfgfg y) (gfg y))
                (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
                (ap_gfg (fg y) y (ε y)) (eq.ap_ap B A A g gf (fg y) y (ε y)))))
       (η (gfg y))
       (eq.cat3 (eq A (gfgfg y) (gfg y)) (ap_g (fgfg y) (fg y) (ε (fg y)))
          (ap_g (fgfg y) (fg y) (ap_f (gfg y) (g y) (η (g y))))
          (eq.ap A A gf (gfg y) (g y) (η (g y))) (η (gfg y))
          (eq.inv (eq A (gfgfg y) (gfg y))
             (ap_g (fgfg y) (fg y) (ap_f (gfg y) (g y) (η (g y))))
             (ap_g (fgfg y) (fg y) (ε (fg y)))
             (eq.ap (eq B (fgfg y) (fg y)) (eq A (gfgfg y) (gfg y))
                (ap_g (fgfg y) (fg y)) (ap_f (gfg y) (g y) (η (g y)))
                (ε (fg y)) (e .to_fro_to (g y))))
          (eq.ap_ap A B A f g (gfg y) (g y) (η (g y))) (selfnat A gf η (g y))))
    (η (g y)) (sq.nat_toid A gf η (gfg y) (g y) (ap_g (fg y) y (ε y)))

def adjointify (A B : Type) (f : A → B) (g : B → A)
  (η : (a : A) → eq A (g (f a)) a) (ε : (b : B) → eq B (f (g b)) b)
  : A ≅ B
  ≔
  let ap_f ≔ eq.ap A B f in
  let ap_g ≔ eq.ap B A g in
  let fg : B → B ≔ x ↦ f (g x) in
  let ap_fg ≔ eq.ap B B fg in
  let gf : A → A ≔ x ↦ g (f x) in
  let ap_gf ≔ eq.ap A A gf in
  let fgf : A → B ≔ x ↦ f (g (f x)) in
  let ap_fgf ≔ eq.ap A B fgf in
  let gfg : B → A ≔ x ↦ g (f (g x)) in
  let ap_gfg ≔ eq.ap B A gfg in
  let gfgf : A → A ≔ x ↦ g (f (g (f x))) in
  let fgfg : B → B ≔ x ↦ f (g (f (g x))) in
  let fgfgf : A → B ≔ x ↦ f (g (f (g (f x)))) in
  let gfgfg : B → A ≔ x ↦ g (f (g (f (g x)))) in
  (to ≔ f,
   fro ≔ g,
   fro_to ≔ η,
   to_fro ≔ b ↦
     eq.cat3 B (fg b) (fgfg b) (fg b) b (eq.inv B (fgfg b) (fg b) (ε (fg b)))
       (ap_f (gfg b) (g b) (η (g b))) (ε b),
   to_fro_to ≔ a ↦
     sq.to_cat3 B (fgfgf a) (fgf a) (ap_f (gfgf a) (gf a) (η (gf a))) (fgf a)
       (f a) (ap_f (gf a) a (η a)) (ε (fgf a)) (ε (f a))
       (sq.act02 B (fgfgf a) (fgf a)
          (ap_fg (fgf a) (f a) (ap_f (gf a) a (η a))) (fgf a) (f a)
          (ap_f (gf a) a (η a)) (ε (fgf a)) (ε (f a))
          (sq.nat_toid B fg ε (fgf a) (f a) (ap_f (gf a) a (η a)))
          (ap_f (gfgf a) (gf a) (η (gf a)))
          (eq.cat3 (eq B (fgfgf a) (fgf a))
             (ap_fg (fgf a) (f a) (ap_f (gf a) a (η a)))
             (ap_fgf (gf a) a (η a))
             (ap_f (gfgf a) (gf a) (ap_gf (gf a) a (η a)))
             (ap_f (gfgf a) (gf a) (η (gf a)))
             (eq.ap_ap A B B f fg (gf a) a (η a))
             (eq.inv (eq B (fgfgf a) (fgf a))
                (ap_f (gfgf a) (gf a) (ap_gf (gf a) a (η a)))
                (ap_fgf (gf a) a (η a)) (eq.ap_ap A A B gf f (gf a) a (η a)))
             (eq.ap (eq A (gfgf a) (gf a)) (eq B (fgfgf a) (fgf a))
                (ap_f (gfgf a) (gf a)) (ap_gf (gf a) a (η a)) (η (gf a))
                (selfnat A gf η a)))))

{` An Id of equalities induces an equality involving transport `}
def Id_eq (A0 A1 : Type) (A2 : Id Type A0 A1) (a00 : A0) (a01 : A1)
  (a02 : A2 a00 a01) (a10 : A0) (a11 : A1) (a12 : A2 a10 a11)
  (a20 : eq A0 a00 a10) (a21 : eq A1 a01 a11)
  (a22 : Id eq A0 A1 A2 a00 a01 a02 a10 a11 a12 a20 a21)
  : eq (A2 a10 a11)
      (eq.trr2 A0 A1 (x y ↦ A2 x y) a00 a10 a20 a01 a11 a21 a02) a12
  ≔ match a22 [ rfl. ⤇ rfl. ]

{` An Id of equivalences induces an equivalence on Ids. `}
def Id_eqv (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : Type)
  (B1 : Type) (B2 : Id Type B0 B1) (e0 : A0 ≅ B0) (e1 : A1 ≅ B1)
  (e2 : Id eqv A0 A1 A2 B0 B1 B2 e0 e1) (b0 : B0) (b1 : B1)
  : A2 (e0 .fro b0) (e1 .fro b1) ≅ B2 b0 b1
  ≔
  let f0 ≔ e0 .to in
  let g0 ≔ e0 .fro in
  let ap_g0 ≔ eq.ap B0 A0 g0 in
  let fg0 : B0 → B0 ≔ x ↦ f0 (g0 x) in
  let gfg0 : B0 → A0 ≔ x ↦ g0 (f0 (g0 x)) in
  let ε0 ≔ e0 .to_fro in
  let η0 ≔ e0 .fro_to in
  let f1 ≔ e1 .to in
  let g1 ≔ e1 .fro in
  let ap_g1 ≔ eq.ap B1 A1 g1 in
  let fg1 : B1 → B1 ≔ x ↦ f1 (g1 x) in
  let gfg1 : B1 → A1 ≔ x ↦ g1 (f1 (g1 x)) in
  let ε1 ≔ e1 .to_fro in
  let η1 ≔ e1 .fro_to in
  let f2 ≔ e2 .to in
  let g2 ≔ e2 .fro in
  let η2 ≔ e2 .fro_to in
  let ε2 ≔ e2 .to_fro in
  adjointify (A2 (g0 b0) (g1 b1)) (B2 b0 b1)
    (a2 ↦
     eq.trr2 B0 B1 (b0 b1 ↦ B2 b0 b1) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1 (ε1 b1)
       (f2 (g0 b0) (g1 b1) a2)) (b2 ↦ g2 b0 b1 b2)
    (a2 ↦
     eq.cat (A2 (g0 b0) (g1 b1))
       (g2 b0 b1
          (eq.trr2 B0 B1 (x y ↦ B2 x y) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1
             (ε1 b1) (f2 (g0 b0) (g1 b1) a2)))
       (eq.trr2 A0 A1 (x y ↦ A2 x y) (gfg0 b0) (g0 b0)
          (ap_g0 (fg0 b0) b0 (ε0 b0)) (gfg1 b1) (g1 b1)
          (ap_g1 (fg1 b1) b1 (ε1 b1))
          (g2 (f0 (g0 b0)) (f1 (g1 b1)) (f2 (g0 b0) (g1 b1) a2))) a2
       (eq.trr2_ap B0 B1 (x y ↦ B2 x y) A0 A1 (x y ↦ A2 x y) g0 g1
          (x0 x1 x2 ↦ g2 x0 x1 x2) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1 (ε1 b1)
          (f2 (g0 b0) (g1 b1) a2))
       (Id_eq A0 A1 A2 (gfg0 b0) (gfg1 b1)
          (g2 (f0 (g0 b0)) (f1 (g1 b1)) (f2 (g0 b0) (g1 b1) a2)) (g0 b0)
          (g1 b1) a2 (ap_g0 (fg0 b0) b0 (ε0 b0)) (ap_g1 (fg1 b1) b1 (ε1 b1))
          (eq.trl2 (eq A0 (gfg0 b0) (g0 b0)) (eq A1 (gfg1 b1) (g1 b1))
             (u v ↦
              Id eq A0 A1 A2 (g0 (f0 (g0 b0))) (g1 (f1 (g1 b1)))
                (g2 (f0 (g0 b0)) (f1 (g1 b1)) (f2 (g0 b0) (g1 b1) a2))
                (g0 b0) (g1 b1) a2 u v) (ap_g0 (fg0 b0) b0 (ε0 b0))
             (η0 (g0 b0)) (fro_to_fro A0 B0 e0 b0)
             (ap_g1 (fg1 b1) b1 (ε1 b1)) (η1 (g1 b1))
             (fro_to_fro A1 B1 e1 b1) (η2 (g0 b0) (g1 b1) a2))))
    (b2 ↦
     Id_eq B0 B1 B2 (fg0 b0) (fg1 b1) (f2 (g0 b0) (g1 b1) (g2 b0 b1 b2)) b0
       b1 b2 (ε0 b0) (ε1 b1) (ε2 b0 b1 b2))

{` Fibrancy transports across equivalences. `}
def 𝕗eqv (A B : Type) (e : A ≅ B) (𝕗A : isFibrant A) : isFibrant B ≔ [
| .trr.e ↦ b0 ↦ e.1 .to (𝕗A.2 .trr (e.0 .fro b0))
| .trl.e ↦ b1 ↦ e.0 .to (𝕗A.2 .trl (e.1 .fro b1))
| .liftr.e ↦ b0 ↦
    eq.trr B.0 (b ↦ B.2 b (e.1 .to (𝕗A.2 .trr (e.0 .fro b0))))
      (e.0 .to (e.0 .fro b0)) b0 (e.0 .to_fro b0)
      (e.2 .to (e.0 .fro b0) (𝕗A.2 .trr.1 (e.0 .fro b0))
         (𝕗A.2 .liftr (e.0 .fro b0)))
| .liftl.e ↦ b1 ↦
    eq.trr B.1 (b ↦ B.2 (e.0 .to (𝕗A.2 .trl (e.1 .fro b1))) b)
      (e.1 .to (e.1 .fro b1)) b1 (e.1 .to_fro b1)
      (e.2 .to (𝕗A.2 .trl.1 (e.1 .fro b1)) (e.1 .fro b1)
         (𝕗A.2 .liftl (e.1 .fro b1)))
| .id.e ↦ b0 b1 ↦
    𝕗eqv (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
      (Id_eqv A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1)
      (𝕗A.2 .id (e.0 .fro b0) (e.1 .fro b1))]

def id_Σ_iso (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type)
  (B2 : Id Π A0 A1 A2 (_ ↦ Type) (_ ↦ Type) (_ ⤇ refl Type) B0 B1) (a0 : A0)
  (a1 : A1) (b0 : B0 a0) (b1 : B1 a1)
  : Σ (A2 a0 a1) (a2 ↦ B2 a0 a1 a2 b0 b1)
    ≅ Id Σ A0 A1 A2 B0 B1 B2 (a0, b0) (a1, b1)
  ≔ (
  to ≔ u ↦ (u .pr₁, u .pr₂),
  fro ≔ v ↦ (v .pr₁, v .pr₂),
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗Σ (A : Type) (B : A → Type) (𝕗A : isFibrant A)
  (𝕗B : (x : A) → isFibrant (B x))
  : isFibrant (Σ A B)
  ≔ [
| .trr.e ↦ u0 ↦ (
    𝕗A.2 .trr (u0 .pr₁),
    𝕗B.2 (u0 .pr₁) (𝕗A.2 .trr.1 (u0 .pr₁)) (𝕗A.2 .liftr (u0 .pr₁))
      .trr (u0 .pr₂))
| .trl.e ↦ u1 ↦ (
    𝕗A.2 .trl (u1 .pr₁),
    𝕗B.2 (𝕗A.2 .trl.1 (u1 .pr₁)) (u1 .pr₁) (𝕗A.2 .liftl (u1 .pr₁))
      .trl (u1 .pr₂))
| .liftr.e ↦ u0 ↦ (
    𝕗A.2 .liftr (u0 .pr₁),
    𝕗B.2 (u0 .pr₁) (𝕗A.2 .trr.1 (u0 .pr₁)) (𝕗A.2 .liftr (u0 .pr₁))
      .liftr (u0 .pr₂))
| .liftl.e ↦ u1 ↦ (
    𝕗A.2 .liftl (u1 .pr₁),
    𝕗B.2 (𝕗A.2 .trl.1 (u1 .pr₁)) (u1 .pr₁) (𝕗A.2 .liftl (u1 .pr₁))
      .liftl (u1 .pr₂))
| .id.e ↦ u0 u1 ↦
    𝕗eqv
      (Σ (A.2 (u0 .pr₁) (u1 .pr₁))
         (a2 ↦ B.2 (u0 .pr₁) (u1 .pr₁) a2 (u0 .pr₂) (u1 .pr₂)))
      (Id Σ A.0 A.1 A.2 B.0 B.1 B.2 u0 u1)
      (id_Σ_iso A.0 A.1 A.2 B.0 B.1 B.2 (u0 .pr₁) (u1 .pr₁) (u0 .pr₂)
         (u1 .pr₂))
      (𝕗Σ (A.2 (u0 .pr₁) (u1 .pr₁))
         (a2 ↦ B.2 (u0 .pr₁) (u1 .pr₁) a2 (u0 .pr₂) (u1 .pr₂))
         (𝕗A.2 .id (u0 .pr₁) (u1 .pr₁))
         (a2 ↦ 𝕗B.2 (u0 .pr₁) (u1 .pr₁) a2 .id (u0 .pr₂) (u1 .pr₂)))]

{` Fibrant Σ-types `}
def Σ𝕗 (A : Fib) (B : A .t → Fib) : Fib ≔ (
  t ≔ Σ (A .t) (a ↦ B a .t),
  f ≔ 𝕗Σ (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

def id_Π_iso (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type)
  (B2 : Id Π A0 A1 A2 (_ ↦ Type) (_ ↦ Type) (_ ⤇ refl Type) B0 B1)
  (f0 : (a0 : A0) → B0 a0) (f1 : (a1 : A1) → B1 a1)
  : ((a0 : A0) (a1 : A1) (a2 : A2 a0 a1) → B2 a0 a1 a2 (f0 a0) (f1 a1))
    ≅ Id Π A0 A1 A2 B0 B1 B2 f0 f1
  ≔ (
  to ≔ f ↦ a ⤇ f a.0 a.1 a.2,
  fro ≔ g ↦ a0 a1 a2 ↦ g a0 a1 a2,
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗Π (A : Type) (B : A → Type) (𝕗A : isFibrant A)
  (𝕗B : (x : A) → isFibrant (B x))
  : isFibrant ((x : A) → B x)
  ≔ [
| .trr.e ↦ f0 a1 ↦
    𝕗B.2 (𝕗A.2 .trl.1 a1) a1 (𝕗A.2 .liftl a1) .trr (f0 (𝕗A.2 .trl a1))
| .trl.e ↦ f1 a0 ↦
    𝕗B.2 a0 (𝕗A.2 .trr.1 a0) (𝕗A.2 .liftr a0) .trl (f1 (𝕗A.2 .trr a0))
| .liftr.e ↦ f0 ↦ a ⤇
    refl 𝕗B.2 a.0 (𝕗A.2 .trl.1 a.1)
        (𝕗A.2⁽ᵉ¹⁾
         .id.1 a.0 a.1 a.2 (𝕗A.2 .trl.1 a.1) a.1 (𝕗A.2 .liftl.1 a.1)
         .trl.1 (refl a.1)) a.1 a.1 (refl a.1) a.2 (𝕗A.2 .liftl.1 a.1)
        (sym
           (sym (refl 𝕗A.2)
            .id.1 a.0 a.1 a.2 (𝕗A.2 .trl.1 a.1) a.1 (𝕗A.2 .liftl a.1)
            .liftl (refl a.1)))
      .id.1 (f0 a.0) (f0 (𝕗A.2 .trl.1 a.1))
        (refl f0 a.0 (𝕗A.2 .trl.1 a.1)
           (𝕗A.2⁽ᵉ¹⁾
            .id.1 a.0 a.1 a.2 (𝕗A.2 .trl.1 a.1) a.1 (𝕗A.2 .liftl a.1)
            .trl (refl a.1)))
        (𝕗B.2 (𝕗A.2 .trl.1 a.1) a.1 (𝕗A.2 .liftl.1 a.1)
         .trr.1 (f0 (𝕗A.2 .trl.1 a.1)))
        (𝕗B.2 (𝕗A.2 .trl.1 a.1) a.1 (𝕗A.2 .liftl.1 a.1)
         .trr.1 (f0 (𝕗A.2 .trl.1 a.1)))
        (refl
           (𝕗B.2 (𝕗A.2 .trl.1 a.1) a.1 (𝕗A.2 .liftl a.1)
            .trr (f0 (𝕗A.2 .trl a.1))))
      .trl
        (𝕗B.2 (𝕗A.2 .trl.1 a.1) a.1 (𝕗A.2 .liftl a.1)
         .liftr (f0 (𝕗A.2 .trl a.1)))
| .liftl.e ↦ f1 ↦ a ⤇
    refl 𝕗B.2 a.0 a.0 (refl a.0) a.1 (𝕗A.2 .trr.1 a.0)
        (𝕗A.2⁽ᵉ¹⁾
         .id.1 a.0 a.1 a.2 a.0 (𝕗A.2 .trr.1 a.0) (𝕗A.2 .liftr.1 a.0)
         .trr.1 (refl a.0)) a.2 (𝕗A.2 .liftr.1 a.0)
        (sym
           (sym (refl 𝕗A.2)
            .id.1 a.0 a.1 a.2 a.0 (𝕗A.2 .trr.1 a.0) (𝕗A.2 .liftr a.0)
            .liftr (refl a.0)))
      .id.1
        (𝕗B.2 a.0 (𝕗A.2 .trr.1 a.0) (𝕗A.2 .liftr.1 a.0)
         .trl.1 (f1 (𝕗A.2 .trr.1 a.0)))
        (𝕗B.2 a.0 (𝕗A.2 .trr.1 a.0) (𝕗A.2 .liftr.1 a.0)
         .trl.1 (f1 (𝕗A.2 .trr.1 a.0)))
        (refl
           (𝕗B.2 a.0 (𝕗A.2 .trr.1 a.0) (𝕗A.2 .liftr a.0)
            .trl (f1 (𝕗A.2 .trr a.0)))) (f1 a.1) (f1 (𝕗A.2 .trr.1 a.0))
        (refl f1 a.1 (𝕗A.2 .trr.1 a.0)
           (𝕗A.2⁽ᵉ¹⁾
            .id.1 a.0 a.1 a.2 a.0 (𝕗A.2 .trr.1 a.0) (𝕗A.2 .liftr a.0)
            .trr (refl a.0)))
      .trl
        (𝕗B.2 a.0 (𝕗A.2 .trr.1 a.0) (𝕗A.2 .liftr a.0)
         .liftl (f1 (𝕗A.2 .trr a.0)))
| .id.e ↦ f0 f1 ↦
    𝕗eqv
      ((a0 : A.0) (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a0 a1 a2 (f0 a0) (f1 a1))
      (Id Π A.0 A.1 A.2 B.0 B.1 B.2 f0 f1)
      (id_Π_iso A.0 A.1 A.2 B.0 B.1 B.2 f0 f1)
      (𝕗Π A.0
         (a0 ↦ (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a0 a1 a2 (f0 a0) (f1 a1))
         𝕗A.0
         (a0 ↦
          𝕗Π A.1 (a1 ↦ (a2 : A.2 a0 a1) → B.2 a0 a1 a2 (f0 a0) (f1 a1)) 𝕗A.1
            (a1 ↦
             𝕗Π (A.2 a0 a1) (a2 ↦ B.2 a0 a1 a2 (f0 a0) (f1 a1))
               (𝕗A.2 .id a0 a1) (a2 ↦ 𝕗B.2 a0 a1 a2 .id (f0 a0) (f1 a1)))))]

{` Fibrant Π-types `}
def Π𝕗 (A : Fib) (B : A .t → Fib) : Fib ≔ (
  t ≔ (a : A .t) → B a .t,
  f ≔ 𝕗Π (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

`Proof
def unnamed.1_12_1_2
  : let Ind_Id_statement
      ≔ (A : Fib) (C : (x y : A .t) → Id (A .t) x y → Fib) →
        ((x : A .t) → C x x (refl x) .t) → (x y : A .t) (p : Id (A .t) x y)
        → C x y p .t in
    let Ind'_Id_statement
      ≔ (A : Fib) (a : A .t) (C : (x : A .t) → Id (A .t) a x → Fib) →
        C a (refl a) .t → (x : A .t) → (p : Id (A .t) a x)
        → C x p .t in
    Ind_Id_statement → Ind'_Id_statement
  ≔ Ind_Id A a C c x p ↦
  let transp
    : (A : Fib) (P : A .t → Fib) (x y : A .t) → Id (A .t) x y → P x .t
      → P y .t
    ≔ A P ↦ Ind_Id A (x y _ ↦ Π𝕗 (P x) (_ ↦ P y)) (x ↦ id (P x .t)) in
  let sigcontr : Id (Σ (A .t) (x ↦ Id (A .t) a x)) (a, refl a) (x, p)
    ≔ Ind_Id A (a x p ↦ Id𝕗 (Σ𝕗 A (z ↦ Id𝕗 A a z)) (a, refl a) (x, p))
        (a ↦ refl ((a, refl a) : (Σ (A .t) (z ↦ Id (A .t) a z)))) a x p in
  transp (Σ𝕗 A (x ↦ Id𝕗 A a x)) (z ↦ C (z .pr₁) (z .pr₂)) (a, refl a) (x, p)
    sigcontr c
