{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

option function boundaries ≔ implicit
option type boundaries ≔ implicit

`Function
def Idfd (A0 A1 : Type) : Id Type A0 A1 → A0 → A1 → Type
  ≔ A2 a0 a1 ↦ A2 a0 a1


`Function
def Idt (A : Type) : Id Type A A ≔ refl A

`Function
def Idf (A : Type) : A → A → Type ≔ a0 a1 ↦ Id A a0 a1


`Proof / Function
def Idt2d_1 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a00 : A00) (a01 : A01)
  (a02 : A02 a00 a01) (a10 : A10) (a11 : A11) (a12 : A12 a10 a11)
  : Id Type (A20 a00 a10) (A21 a01 a11)
  ≔ A22 a02 a12

`Proof / Function
def Idt2d_2 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a00 : A00) (a10 : A10)
  (a20 : A20 a00 a10) (a01 : A01) (a11 : A11) (a21 : A21 a01 a11)
  : Id Type (A02 a00 a01) (A12 a10 a11)
  ≔ sym A22 a20 a21

def Idf2d_1 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a00 : A00) (a01 : A01)
  (a02 : A02 a00 a01) (a10 : A10) (a11 : A11) (a12 : A12 a10 a11)
  : (A20 a00 a10) → (A21 a01 a11) → Type
  ≔ a20 a21 ↦ A22 a02 a12 a20 a21

def Idf2d_2 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a00 : A00) (a10 : A10)
  (a20 : A20 a00 a10) (a01 : A01) (a11 : A11) (a21 : A21 a01 a11)
  : (A02 a00 a01) → (A12 a10 a11) → Type
  ≔ a02 a12 ↦ sym A22 a20 a21 a02 a12


`Proof / Function
def Idt2 (A : Type) (a00 a01 : A) (a02 : Id A a00 a01) (a10 a11 : A)
  (a12 : Id A a10 a11)
  : Id Type (Id A a00 a10) (Id A a01 a11)
  ≔ A⁽ᵉᵉ⁾ a02 a12

`Proof / Function
def Idf2 (A : Type) (a00 a01 : A) (a02 : Id A a00 a01) (a10 a11 : A)
  (a12 : Id A a10 a11)
  : Id A a00 a10 → Id A a01 a11 → Type
  ≔ a20 a21 ↦ A⁽ᵉᵉ⁾ a02 a12 a20 a21
