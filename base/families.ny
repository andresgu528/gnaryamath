{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

option function boundaries ≔ implicit
option type boundaries ≔ implicit

def IdF_1 (A : Type) (B : A → Type) (a0 a1 : A) (a2 : Id A a0 a1)
  : Id Type (B a0) (B a1)
  ≔ refl B a2

def IdF_0 (A : Type) (B : A → Type) (a0 a1 : A) (a2 : Id A a0 a1) (b0 : B a0)
  (b1 : B a1)
  : Type
  ≔ Id B a2 b0 b1

def Id2F_2 (A : Type) (B : A → Type) (a00 a01 : A) (a02 : Id A a00 a01)
  (a10 a11 : A) (a12 : Id A a10 a11) (a20 : Id A a00 a10)
  (a21 : Id A a01 a11) (a22 : A⁽ᵉᵉ⁾ a02 a12 a20 a21)
  : Type⁽ᵉᵉ⁾ (Id B a02) (Id B a12) (Id B a20) (Id B a21)
  ≔ B⁽ᵉᵉ⁾ a22

def Id2F_1 (A : Type) (B : A → Type) (a00 a01 : A) (a02 : Id A a00 a01)
  (a10 a11 : A) (a12 : Id A a10 a11) (a20 : Id A a00 a10)
  (a21 : Id A a01 a11) (a22 : A⁽ᵉᵉ⁾ a02 a12 a20 a21) (b00 : B a00)
  (b01 : B a01) (b02 : Id B a02 b00 b01) (b10 : B a10) (b11 : B a11)
  (b12 : Id B a12 b10 b11)
  : Id Type (Id B a20 b00 b10) (Id B a21 b01 b11)
  ≔ B⁽ᵉᵉ⁾ a22 b02 b12

def Id2F_0 (A : Type) (B : A → Type) (a00 a01 : A) (a02 : Id A a00 a01)
  (a10 a11 : A) (a12 : Id A a10 a11) (a20 : Id A a00 a10)
  (a21 : Id A a01 a11) (a22 : A⁽ᵉᵉ⁾ a02 a12 a20 a21) (b00 : B a00)
  (b01 : B a01) (b02 : Id B a02 b00 b01) (b10 : B a10) (b11 : B a11)
  (b12 : Id B a12 b10 b11) (b20 : Id B a20 b00 b10) (b21 : Id B a21 b01 b11)
  : Type
  ≔ B⁽ᵉᵉ⁾ a22 b02 b12 b20 b21

`Families of two types

def IdF2_1 (A : Type) (B : A → Type) (C : (a : A) → B a → Type) (a0 a1 : A)
  (a2 : Id A a0 a1) (b0 : B a0) (b1 : B a1) (b2 : Id B a2 b0 b1)
  : Id Type (C a0 b0) (C a1 b1)
  ≔ refl C a2 b2

def IdF2_0 (A : Type) (B : A → Type) (C : (a : A) → B a → Type) (a0 a1 : A)
  (a2 : Id A a0 a1) (b0 : B a0) (b1 : B a1) (b2 : Id B a2 b0 b1)
  : C a0 b0 → C a1 b1 → Type
  ≔ c0 c1 ↦ refl C a2 b2 c0 ?

def Id2F2_2 (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  (a00 a01 : A) (a02 : Id A a00 a01) (a10 a11 : A) (a12 : Id A a10 a11)
  (a20 : Id A a00 a10) (a21 : Id A a01 a11) (b00 : B a00)
  (a22 : A⁽ᵉᵉ⁾ a02 a12 a20 a21) (b01 : B a01) (b02 : Id B a02 b00 b01)
  (b10 : B a10) (b11 : B a11) (b12 : Id B a12 b10 b11)
  (b20 : Id B a20 b00 b10) (b21 : Id B a21 b01 b11)
  (b22 : B⁽ᵉᵉ⁾ a22 b02 b12 b20 b21)
  : Type⁽ᵉᵉ⁾ (Id C a02 b02) (Id C a12 b12) (Id C a20 b20) (Id C a21 b21)
  ≔ C⁽ᵉᵉ⁾ a22 b22

def Id2F2_1 (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  (a00 a01 : A) (a02 : Id A a00 a01) (a10 a11 : A) (a12 : Id A a10 a11)
  (a20 : Id A a00 a10) (a21 : Id A a01 a11) (b00 : B a00)
  (a22 : A⁽ᵉᵉ⁾ a02 a12 a20 a21) (b01 : B a01) (b02 : Id B a02 b00 b01)
  (b10 : B a10) (b11 : B a11) (b12 : Id B a12 b10 b11)
  (b20 : Id B a20 b00 b10) (b21 : Id B a21 b01 b11)
  (b22 : B⁽ᵉᵉ⁾ a22 b02 b12 b20 b21) (c00 : C a00 b00) (c01 : C a01 b01)
  (c02 : Id C a02 b02 c00 c01) (c10 : C a10 b10) (c11 : C a11 b11)
  (c12 : Id C a12 b12 c10 c11)
  : Id Type (Id C a20 b20 c00 c10) (Id C a21 b21 c01 c11)
  ≔ C⁽ᵉᵉ⁾ a22 b22 c02 c12

def Id2F2_0 (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  (a00 a01 : A) (a02 : Id A a00 a01) (a10 a11 : A) (a12 : Id A a10 a11)
  (a20 : Id A a00 a10) (a21 : Id A a01 a11) (b00 : B a00)
  (a22 : A⁽ᵉᵉ⁾ a02 a12 a20 a21) (b01 : B a01) (b02 : Id B a02 b00 b01)
  (b10 : B a10) (b11 : B a11) (b12 : Id B a12 b10 b11)
  (b20 : Id B a20 b00 b10) (b21 : Id B a21 b01 b11)
  (b22 : B⁽ᵉᵉ⁾ a22 b02 b12 b20 b21) (c00 : C a00 b00) (c01 : C a01 b01)
  (c02 : Id C a02 b02 c00 c01) (c10 : C a10 b10) (c11 : C a11 b11)
  (c12 : Id C a12 b12 c10 c11) (c20 : Id C a20 b20 c00 c10)
  (c21 : Id C a21 b21 c01 c11)
  : Type
  ≔ C⁽ᵉᵉ⁾ a22 b22 c02 c12 c20 c21

`fibrancy

def trrF (A : Type) (B : A → Type) (a0 a1 : A) (a2 : Id A a0 a1)
  : B a0 → B a1
  ≔ b0 ↦ refl B a2 .trr b0

def trlF (A : Type) (B : A → Type) (a0 a1 : A) (a2 : Id A a0 a1)
  : B a1 → B a0
  ≔ b1 ↦ refl B a2 .trl b1

def liftrF (A : Type) (B : A → Type) (a0 a1 : A) (a2 : Id A a0 a1)
  (b0 : B a0)
  : Id B a2 b0 (refl B a2 .trr b0)
  ≔ refl B a2 .liftr b0

def liftlF (A : Type) (B : A → Type) (a0 a1 : A) (a2 : Id A a0 a1)
  (b1 : B a1)
  : Id B a2 (refl B a2 .trl b1) b1
  ≔ refl B a2 .liftl b1
