{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

option function boundaries ≔ implicit
option type boundaries ≔ implicit

import "sigma"

`The convention here is wanted_given

`Proof / Function
def fill2_21_021220 (A : Type) (a00 a01 : A) (a02 : Id A a00 a01)
  (a10 a11 : A) (a12 : Id A a10 a11) (a20 : Id A a00 a10)
  : Id A a01 a11
  ≔ A⁽ᵉᵉ⁾ a02 a12 .trr a20

`Proof / Function
def fill2_22_022021 (A : Type) (a00 a01 : A) (a02 : Id A a00 a01) (a10 : A)
  (a11 : A) (a20 : Id A a00 a10) (a21 : Id A a01 a11)
  : A⁽ᵉᵉ⁾ a02 (A⁽ᵉᵉ⁾ a20 a21 .trr a02) a20 a21
  ≔ sym (A⁽ᵉᵉ⁾ a20 a21 .liftr a02)

`Proof / Function
def fill2_1222_022021 (A : Type) (a00 a01 : A) (a02 : Id A a00 a01) (a10 : A)
  (a11 : A) (a20 : Id A a00 a10) (a21 : Id A a01 a11)
  : Σ (Id A a10 a11) (a12 ↦ A⁽ᵉᵉ⁾ a02 a12 a20 a21)
  ≔ (A⁽ᵉᵉ⁾ a20 a21 .trr a02, sym (A⁽ᵉᵉ⁾ a20 a21 .liftr a02))
