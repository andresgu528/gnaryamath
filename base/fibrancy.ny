{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

option function boundaries ≔ implicit
option type boundaries ≔ implicit

`Proof / Function
def trrd (A0 A1 : Type) : Id Type A0 A1 → A0 → A1 ≔ A2 ↦ A2 .trr

`Proof / Function
def trld (A0 A1 : Type) : Id Type A0 A1 → A1 → A0 ≔ A2 ↦ A2 .trl

`Function
def liftrd (A0 A1 : Type) (A2 : Id Type A0 A1) (a0 : A0) : A2 a0 (A2 .trr a0)
  ≔ A2 .liftr a0

`Function
def liftld (A0 A1 : Type) (A2 : Id Type A0 A1) (a1 : A1) : A2 (A2 .trl a1) a1
  ≔ A2 .liftl a1


`Function
def trr (A : Type) : A → A ≔ refl A .trr

def trl (A : Type) : A → A ≔ refl A .trl

`Function
def liftr (A : Type) (a : A) : Id A a (refl A .trr a) ≔ refl A .liftr a

`Function
def liftl (A : Type) (a : A) : Id A (refl A .trl a) a ≔ refl A .liftl a


`Function
def trr2d_1 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a00 : A00) (a01 : A01)
  : A02 a00 a01 → A12 (A20 .trr a00) (A21 .trr a01)
  ≔ a02 ↦ A22 .trr.1 a02

`Function
def trr2d_2 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a00 : A00) (a10 : A10)
  : A20 a00 a10 → A21 (A02 .trr a00) (A12 .trr a10)
  ≔ a20 ↦ A22 .trr.2 a20

`Function
def trl2d_1 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a10 : A10) (a11 : A11)
  : A12 a10 a11 → A02 (A20 .trl a10) (A21 .trl a11)
  ≔ a12 ↦ A22 .trl.1 a12

`Function
def trl2d_2 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a01 : A01) (a11 : A11)
  : A21 a01 a11 → A20 (A02 .trl a01) (A12 .trl a11)
  ≔ a21 ↦ A22 .trl.2 a21

`Function
def liftr2d_1 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a00 : A00) (a01 : A01)
  (a02 : A02 a00 a01)
  : A22 a02 (A22 .trr.1 a02) (A20 .liftr a00) (A21 .liftr a01)
  ≔ A22 .liftr.1 a02

`Function
def liftr2d_2 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a00 : A00) (a10 : A10)
  (a20 : A20 a00 a10)
  : sym A22 a20 (A22 .trr.2 a20) (A02 .liftr a00) (A12 .liftr a10)
  ≔ A22 .liftr.2 a20

`Function
def liftl2d_1 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a10 : A10) (a11 : A11)
  (a12 : A12 a10 a11)
  : A22 (A22 .trl.1 a12) a12 (A20 .liftl a10) (A21 .liftl a11)
  ≔ A22 .liftl.1 a12

`Function
def liftl2d_2 (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21) (a01 : A01) (a11 : A11)
  (a21 : A21 a01 a11)
  : sym A22 (A22 .trl.2 a21) a21 (A02 .liftl a01) (A12 .liftl a11)
  ≔ A22 .liftl.2 a21


`Proof / Function
def trr2 (A : Type) (a0 a1 : A) (a2 : Id A a0 a1)
  : Id A (refl A .trr a0) (refl A .trr a1)
  ≔ A⁽ᵉᵉ⁾ .trr.1 a2

`Proof / Function
def trl2 (A : Type) (a0 a1 : A) (a2 : Id A a0 a1)
  : Id A (refl A .trl a0) (refl A .trl a1)
  ≔ A⁽ᵉᵉ⁾ .trl.1 a2

`Function
def liftr2 (A : Type) (a0 a1 : A) (a2 : Id A a0 a1)
  : A⁽ᵉᵉ⁾ a2 (A⁽ᵉᵉ⁾ .trr.1 a2) (refl A .liftr a0) (refl A .liftr a1)
  ≔ A⁽ᵉᵉ⁾ .liftr.1 a2

`Function
def liftl2 (A : Type) (a0 a1 : A) (a2 : Id A a0 a1)
  : A⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .trl.1 a2) a2 (refl A .liftl a0) (refl A .liftl a1)
  ≔ A⁽ᵉᵉ⁾ .liftl.1 a2
