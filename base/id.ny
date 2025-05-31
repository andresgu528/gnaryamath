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
def Id2d_1_1 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a00 : A00) (a01 : A01)
  (a02 : A02 a00 a01) (a10 : A10) (a11 : A11) (a12 : A12 a10 a11)
  : Id Type (A20 a00 a10) (A21 a01 a11)
  ≔ A22 a02 a12

`Proof / Function
def Id2d_1_2 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a00 : A00) (a10 : A10)
  (a20 : A20 a00 a10) (a01 : A01) (a11 : A11) (a21 : A21 a01 a11)
  : Id Type (A02 a00 a01) (A12 a10 a11)
  ≔ sym A22 a20 a21

def Id2d_0_1 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a00 : A00) (a01 : A01)
  (a02 : A02 a00 a01) (a10 : A10) (a11 : A11) (a12 : A12 a10 a11)
  : (A20 a00 a10) → (A21 a01 a11) → Type
  ≔ a20 a21 ↦ A22 a02 a12 a20 a21

def Id2d_0_2 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
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


`Test
def cube (A : Type) (a000 a001 : A) (a002 : Id A a000 a001) (a010 a011 : A)
  (a012 : Id A a010 a011) (a020 : Id A a000 a010) (a021 : Id A a001 a011)
  (a022 : A⁽ᵉᵉ⁾ a002 a012 a020 a021) (a100 a101 : A) (a102 : Id A a100 a101)
  (a110 a111 : A) (a112 : Id A a110 a111) (a120 : Id A a100 a110)
  (a121 : Id A a101 a111) (a122 : A⁽ᵉᵉ⁾ a102 a112 a120 a121)
  (a200 : Id A a000 a100) (a201 : Id A a001 a101)
  (a202 : A⁽ᵉᵉ⁾ a002 a102 a200 a201) (a210 : Id A a010 a110)
  (a211 : Id A a011 a111) (a212 : A⁽ᵉᵉ⁾ a012 a112 a210 a211)
  (a220 : A⁽ᵉᵉ⁾ a020 a120 a200 a210) (a221 : A⁽ᵉᵉ⁾ a021 a121 a201 a211)
  (a222 : A⁽ᵉᵉᵉ⁾ a022 a122 a202 a212 a220 a221)
  : A⁽ᵉᵉᵉ⁾ a022 a122 a202 a212 a220 a221
  ≔ ?


option function boundaries ≔ explicit
option type boundaries ≔ explicit

`Test
def cube (A : Type) (a000 a001 : A) (a002 : Id A a000 a001) (a010 a011 : A)
  (a012 : Id A a010 a011) (a020 : Id A a000 a010) (a021 : Id A a001 a011)
  (a022 : A⁽ᵉᵉ⁾ a000 a001 a002 a010 a011 a012 a020 a021) (a100 a101 : A)
  (a102 : Id A a100 a101) (a110 a111 : A) (a112 : Id A a110 a111)
  (a120 : Id A a100 a110) (a121 : Id A a101 a111)
  (a122 : A⁽ᵉᵉ⁾ a100 a101 a102 a110 a111 a112 a120 a121)
  (a200 : Id A a000 a100) (a201 : Id A a001 a101)
  (a202 : A⁽ᵉᵉ⁾ a000 a001 a002 a100 a101 a102 a200 a201)
  (a210 : Id A a010 a110) (a211 : Id A a011 a111)
  (a212 : A⁽ᵉᵉ⁾ a010 a011 a012 a110 a111 a112 a210 a211)
  (a220 : A⁽ᵉᵉ⁾ a000 a010 a020 a100 a110 a120 a200 a210)
  (a221 : A⁽ᵉᵉ⁾ a001 a011 a021 a101 a111 a121 a201 a211)
  (a222 : A⁽ᵉᵉᵉ⁾ a000 a001 a002 a010 a011 a012 a020 a021 a022 a100 a101 a102
            a110 a111 a112 a120 a121 a122 a200 a201 a202 a210 a211 a212 a220
            a221)
  : ?
  ≔ ?
