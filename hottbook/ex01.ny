{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "ch01"
  | union (only notations.«_ × _»,
           only rec_×,
           only rec_×_comput,
           only Σ,
           only rec_Σ,
           only rec_Σ_comput,
           only ind_×,
           only ind_×_comput,
           only ind_Σ,
           only ind_Σ_comput,
           only 𝟚,
           only rec_2,
           only ind_2,
           only notations.«_ alt＋ _»,
           only altinl,
           only altinr,
           only notations.«_ alt2× _»,
           only alt2pair,
           only ℕ,
           only ind_ℕ,
           only add,
           only notations.«_ + _»)

{` Chapter 1 - Type theory - Exercises `}

{` Exercise 1.1 `}

def exe1_1_1_composite (A B C : Type) : (A → B) → (B → C) → A → C
  ≔ f g x ↦ g (f x)

def exe1_1_2 (A B C D : Type) (f : A → B) (g : B → C) (h : C → D)
  : Id (A → D) (exe1_1_1_composite A C D (exe1_1_1_composite A B C f g) h)
      (exe1_1_1_composite A B D f (exe1_1_1_composite B C D g h))
  ≔ refl (exe1_1_1_composite A C D (exe1_1_1_composite A B C f g) h)

{` Exercise 1.2 `}

def exe1_2_1 (A B C : Type) : (A → B → C) → A × B → C ≔ rec_× A B C

def exe1_2_1_comput (A B C : Type) (g : A → B → C) (a : A) (b : B)
  : Id C (exe1_2_1 A B C g (a, b)) (g a b)
  ≔ rec_×_comput A B C g a b

def exe1_2_2 (A : Type) (B : A → Type) (C : Type)
  : ((a : A) → B a → C) → Σ A B → C
  ≔ rec_Σ A B C

def exe1_2_2_comput (A : Type) (B : A → Type) (C : Type)
  (g : (a : A) → B a → C) (a : A) (b : B a)
  : Id C (exe1_2_2 A B C g (a, b)) (g a b)
  ≔ rec_Σ_comput A B C g a b

{` Exercise 1.3 `}

def exe1_3_1 (A B : Type) (C : A × B → Type)
  : ((x : A) (y : B) → C (x, y)) → (x : A × B) → C x
  ≔ ind_× A B C

def exe1_3_1_comput (A B : Type) (C : A × B → Type)
  (g : (a : A) (b : B) → C (a, b)) (a : A) (b : B)
  : Id (C (a, b)) (exe1_3_1 A B C g (a, b)) (g a b)
  ≔ ind_×_comput A B C g a b

def exe1_3_2_uniq_Σ (A : Type) (B : A → Type) (C : Σ A B → Type) (x : Σ A B)
  : Id (Σ A B) (x .pr1, x .pr2) x
  ≔ refl x

def exe1_3_3 (A : Type) (B : A → Type) (C : Σ A B → Type)
  : ((a : A) (b : B a) → C (a, b)) → (p : Σ A B) → C p
  ≔ ind_Σ A B C

def exe1_3_3_comput (A : Type) (B : A → Type) (C : Σ A B → Type)
  (g : (a : A) (b : B a) → C (a, b)) (a : A) (b : B a)
  : Id (C (a, b)) (exe1_3_3 A B C g (a, b)) (g a b)
  ≔ ind_Σ_comput A B C g a b

{` Exercise 1.4 `}

def iter (C : Type) : C → (C → C) → ℕ → C ≔ c0 cs ↦ [
| zero. ↦ c0
| suc. n ↦ cs (iter C c0 cs n)]

def exe1_4 (C : Type) : C → (ℕ → C → C) → ℕ → C ≔ c0 cs n ↦
  let f : (ℕ × C) → (ℕ × C) ≔ z ↦ (suc. (z .pr1), cs (z .pr1) (z .pr2)) in
  iter (ℕ × C) (0, c0) f n .pr2

def exe1_4_comput1 (C : Type) (c0 : C) (cs : ℕ → C → C)
  : Id C (exe1_4 C c0 cs 0) c0
  ≔ refl c0
def exe1_4_comput2 (C : Type) (c0 : C) (cs : ℕ → C → C) (n : ℕ)
  : Id C (exe1_4 C c0 cs (suc. n)) (cs n (exe1_4 C c0 cs n))
  ≔
  let f : (ℕ × C) → (ℕ × C) ≔ z ↦ (suc. (z .pr1), cs (z .pr1) (z .pr2)) in
  let rec g : (n : ℕ) → Id ℕ (iter (ℕ × C) (0, c0) f n .pr1) n ≔ [
  | zero. ↦ refl (0 : ℕ)
  | suc. k ↦ refl ((k ↦ suc. k) : ℕ → ℕ) (g k)] in
  let h : ℕ → C ≔ k ↦ cs k (exe1_4 C c0 cs n) in
  refl h (g n)

{` Exercise 1.5 `}

def ind_alt＋ (A B : Type) (C : A alt＋ B → Type)
  : ((a : A) → C (altinl A B a)) → ((b : B) → C (altinr A B b)) →
    (x : A alt＋ B)
    → C x
  ≔ g0 g1 x ↦
  let g : (x : 𝟚) (y : rec_2 Type A B x) → C (x, y) ≔ [
  | 0₂. ↦ a ↦ g0 a
  | 1₂. ↦ b ↦ g1 b] in
  g (x .pr1) (x .pr2)

def int_alt＋comput1 (A B : Type) (C : A alt＋ B → Type)
  (g0 : (a : A) → C (altinl A B a)) (g1 : (b : B) → C (altinr A B b)) (a : A)
  : Id (C (altinl A B a)) (ind_alt＋ A B C g0 g1 (altinl A B a)) (g0 a)
  ≔ refl (g0 a)
def int_alt＋comput2 (A B : Type) (C : A alt＋ B → Type)
  (g0 : (a : A) → C (altinl A B a)) (g1 : (b : B) → C (altinr A B b)) (b : B)
  : Id (C (altinr A B b)) (ind_alt＋ A B C g0 g1 (altinr A B b)) (g1 b)
  ≔ refl (g1 b)

{` Exercise 1.6 `}

def exe1_6_funext (A : Type) (B : A → Type) (f g : (a : A) → B a)
  : ((a : A) → Id (B a) (f a) (g a)) → Id ((a : A) → B a) f g
  ≔ h ↦ x ⤇ B⁽ᵉᵉ⁾ (refl x.2) (refl (f x.0)) (h x.1) .trr (refl f x.2)

def exe1_6_funext_computId (A : Type) (B : A → Type) (f : (a : A) → B a)
  : Id (Id ((a : A) → B a) f f) (exe1_6_funext A B f f (a ↦ refl (f a)))
      (refl f)
  ≔ a ⤇
  let b202
    : B⁽ᵉᵉ⁾ (refl a.20) (refl (f a.00)) (refl (f a.10)) (refl f a.20)
        (B⁽ᵉᵉ⁾ a.20⁽¹ᵉ⁾ (refl (f a.00)) (refl (f a.10)) .trr (refl f a.20))
    ≔ B⁽ᵉᵉ⁾ (refl a.20) (refl (f a.00)) (refl (f a.10)) .liftr (refl f a.20)
    in
  refl (B⁽ᵉᵉ⁾ a.22) (refl (refl f a.02)) (refl (refl f a.12)) b202
      (refl (refl f a.21))
    .trr (f⁽ᵉᵉ⁾ a.22)

def exe1_6_concat (A : Type) (a0 a1 a2 : A)
  : Id A a0 a1 → Id A a1 a2 → Id A a0 a2
  ≔ a01 a12 ↦ A⁽ᵉᵉ⁾ (refl a0) a12 .trr a01

def ind_alt2× (A B : Type) (C : A alt2× B → Type)
  : ((x : A) (y : B) → C (alt2pair A B x y)) → (x : A alt2× B) → C x
  ≔ g x ↦
  let lemma1
    : (y : 𝟚) → Id (rec_2 Type A B y) (alt2pair A B (x 0₂.) (x 1₂.) y) (x y)
    ≔ ind_2
        (y ↦ Id (rec_2 Type A B y) (alt2pair A B (x 0₂.) (x 1₂.) y) (x y))
        (refl (x 0₂.)) (refl (x 1₂.)) in
  let lemma2 : Id (A alt2× B) (alt2pair A B (x 0₂.) (x 1₂.)) x
    ≔ exe1_6_funext 𝟚 (rec_2 Type A B) (alt2pair A B (x 0₂.) (x 1₂.)) x
        lemma1 in
  refl C lemma2 .trr (g (x 0₂.) (x 1₂.))

def ind_alt2×_computId (A B : Type) (C : A alt2× B → Type)
  (g : (a : A) (b : B) → C (alt2pair A B a b)) (a : A) (b : B)
  : Id (C (alt2pair A B a b)) (ind_alt2× A B C g (alt2pair A B a b)) (g a b)
  ≔
  let lemma1
    : (y : 𝟚)
      → Id (rec_2 Type A B y) (alt2pair A B a b y) (alt2pair A B a b y)
    ≔ ind_2
        (y ↦ Id (rec_2 Type A B y) (alt2pair A B a b y) (alt2pair A B a b y))
        (refl a) (refl b) in
  let lemma1refl1
    : (y : 𝟚)
      → Id (Id (rec_2 Type A B y) (alt2pair A B a b y) (alt2pair A B a b y))
          (lemma1 y) (refl (alt2pair A B a b y)) ≔ [
  | 0₂. ↦ a⁽ᵉᵉ⁾
  | 1₂. ↦ b⁽ᵉᵉ⁾] in
  let lemma1refl2
    : Id
        ((y : 𝟚)
         → Id (rec_2 Type A B y) (alt2pair A B a b y) (alt2pair A B a b y))
        lemma1 (y ↦ refl (alt2pair A B a b y))
    ≔ exe1_6_funext 𝟚
        (y ↦ Id (rec_2 Type A B y) (alt2pair A B a b y) (alt2pair A B a b y))
        lemma1 (y ↦ refl (alt2pair A B a b y)) lemma1refl1 in
  let lemma2 : Id (A alt2× B) (alt2pair A B a b) (alt2pair A B a b)
    ≔ exe1_6_funext 𝟚 (rec_2 Type A B) (alt2pair A B a b) (alt2pair A B a b)
        lemma1 in
  let lemma2refl1
    : Id (Id (A alt2× B) (alt2pair A B a b) (alt2pair A B a b)) lemma2
        (exe1_6_funext 𝟚 (rec_2 Type A B) (alt2pair A B a b)
           (alt2pair A B a b) (y ↦ refl (alt2pair A B a b y)))
    ≔ refl
        (exe1_6_funext 𝟚 (rec_2 Type A B) (alt2pair A B a b)
           (alt2pair A B a b)) lemma1refl2 in
  let lemma2refl2
    : Id (Id (A alt2× B) (alt2pair A B a b) (alt2pair A B a b))
        (exe1_6_funext 𝟚 (rec_2 Type A B) (alt2pair A B a b)
           (alt2pair A B a b) (y ↦ refl (alt2pair A B a b y)))
        (refl (alt2pair A B a b))
    ≔ exe1_6_funext_computId 𝟚 (rec_2 Type A B) (alt2pair A B a b) in
  let lemma2refl
    : Id (Id (A alt2× B) (alt2pair A B a b) (alt2pair A B a b)) lemma2
        (refl (alt2pair A B a b))
    ≔ exe1_6_concat (Id (A alt2× B) (alt2pair A B a b) (alt2pair A B a b))
        lemma2
        (exe1_6_funext 𝟚 (rec_2 Type A B) (alt2pair A B a b)
           (alt2pair A B a b) (y ↦ refl (alt2pair A B a b y)))
        (refl (alt2pair A B a b)) lemma2refl1 lemma2refl2 in
  let ind_alt2×Idf
    : Id (A alt2× B) (alt2pair A B a b) (alt2pair A B a b)
      → C (alt2pair A B a b)
    ≔ z ↦ refl C z .trr (g a b) in
  (C (alt2pair A B a b))⁽ᵉᵉ⁾ (refl ind_alt2×Idf lemma2refl)
      (refl (C (alt2pair A B a b)) .liftr (g a b))
    .trl (refl (refl (C (alt2pair A B a b)) .trr (g a b)))

{` Exercise 1.7 `}

def exe1_7
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
  let contract_Σ
    : (A : Type) (a0 a1 : A) (a2 : Id A a0 a1)
      → Id (Σ A (a ↦ Id A a0 a)) (a0, refl a0) (a1, a2)
    ≔ A ↦
      Ind_Id A (a0 a1 a2 ↦ Id (Σ A (a ↦ Id A a0 a)) (a0, refl a0) (a1, a2))
        (a ↦ refl ((a, refl a) : Σ A (a' ↦ Id A a a'))) in
  let contract_Σ_computId
    : (A : Type) (a : A)
      → Id (Id (Σ A (a' ↦ Id A a a')) (a, refl a) (a, refl a))
          (contract_Σ A a a (refl a))
          (refl ((a, refl a) : Σ A (a' ↦ Id A a a')))
    ≔ A ↦
      Ind_Id_comput A
        (a0 a1 a2 ↦ Id (Σ A (a ↦ Id A a0 a)) (a0, refl a0) (a1, a2))
        (a ↦ refl ((a, refl a) : Σ A (a' ↦ Id A a a'))) in
  let transp
    : (A : Type) (B : A → Type) (a0 a1 : A) → Id A a0 a1 → B a0 → B a1
    ≔ A B ↦ Ind_Id A (a0 a1 a2 ↦ B a0 → B a1) (a b ↦ b) in
  let transp_computId
    : (A : Type) (B : A → Type) (a : A)
      → Id (B a → B a) (transp A B a a (refl a)) (b ↦ b)
    ≔ A B ↦ Ind_Id_comput A (a0 a1 a2 ↦ B a0 → B a1) (a b ↦ b) in
  let concat
    : (A : Type) (a0 a1 a2 : A) → Id A a0 a1 → Id A a1 a2 → Id A a0 a2
    ≔ A a0 a1 a2 a01 ↦
      Ind_Id A (a'0 a'1 a'2 ↦ Id A a'1 a2 → Id A a'0 a2) (a p ↦ p) a0 a1 a01
    in
  let Ind'_Id
    : (A : Type) (a : A) (C : (x : A) → Id A a x → Type) → C a (refl a) →
      (x : A) → (p : Id A a x)
      → C x p
    ≔ A a C c x p ↦
      transp (Σ A (z ↦ Id A a z)) (z ↦ C (z .pr1) (z .pr2)) (a, refl a)
        (x, p) (contract_Σ A a x p) c in
  (Ind'_Id,
   A a C c ↦
     concat (C a (refl a)) (Ind'_Id A a C c a (refl a))
       (transp (Σ A (z ↦ Id A a z)) (z ↦ C (z .pr1) (z .pr2)) (a, refl a)
          (a, refl a) (refl ((a, refl a) : Σ A (a' ↦ Id A a a'))) c) c
       (refl
          (transp (Σ A (z ↦ Id A a z)) (z ↦ C (z .pr1) (z .pr2)) (a, refl a)
             (a, refl a)) (contract_Σ_computId A a) (refl c))
       (transp_computId (Σ A (z ↦ Id A a z)) (z ↦ C (z .pr1) (z .pr2))
          (a, refl a) (refl c)))

{` Exercise 1.8 `}

def mult : ℕ → ℕ → ℕ ≔ [ zero. ↦ n ↦ zero. | suc. m ↦ n ↦ add n (mult m n) ]

def exp : ℕ → ℕ → ℕ ≔ m ↦ [ zero. ↦ 1 | suc. n ↦ mult m (exp m n) ]

`There are multiple different conventions on what to call a semiring. I will use here the most specific one
def isSemiring (X : Type) (a : X → X → X) (z : X) (m : X → X → X) (u : X)
  : Type
  ≔ sig (
  a_assoc : (x y z : X) → Id X (a x (a y z)) (a (a x y) z),
  a_lz : (x : X) → Id X (a z x) x,
  a_rz : (x : X) → Id X (a x z) x,
  comm_a : (x y : X) → Id X (a x y) (a y x),
  m_assoc : (x y z : X) → Id X (m x (m y z)) (m (m x y) z),
  m_lu : (x : X) → Id X (m u x) x,
  m_ru : (x : X) → Id X (m x u) x,
  m_lz : (x : X) → Id X (m z x) z,
  m_rz : (x : X) → Id X (m x z) z,
  dist_l : (x y z : X) → Id X (m x (a y z)) (a (m x y) (m x z)),
  dist_r : (x y z : X) → Id X (m (a x y) z) (a (m x z) (m y z)) )

def ℕ_Semiring : isSemiring ℕ add 0 mult 1 ≔ (
  a_assoc ≔
    ind_ℕ (x ↦ (y z : ℕ) → Id ℕ (x + (y + z)) ((x + y) + z))
      (y z ↦ refl (y + z)) (_ cx y z ↦ suc. (cx y z)),
  a_lz ≔ x ↦ refl x,
  a_rz ≔ ind_ℕ (x ↦ Id ℕ (x + 0) x) 0 (_ cx ↦ suc. cx),
  comm_a ≔ ?,
  m_assoc ≔ ?,
  m_lu ≔ ?,
  m_ru ≔ ?,
  m_lz ≔ ?,
  m_rz ≔ ?,
  dist_l ≔ ?,
  dist_r ≔ ?) 
