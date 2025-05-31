{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

option function boundaries ≔ implicit
option type boundaries ≔ implicit

{` Chapter 1 - Type theory - Exercises `}

{` Exercise 1.1 `}

def exe1_1_1_composite (A B C : Type) : (A → B) → (B → C) → A → C
  ≔ f g x ↦ g (f x)

def exe1_1_2 (A B C D : Type) (f : A → B) (g : B → C) (h : C → D)
  : Id (A → D) (exe1_1_1_composite A C D (exe1_1_1_composite A B C f g) h)
      (exe1_1_1_composite A B D f (exe1_1_1_composite B C D g h))
  ≔ refl (exe1_1_1_composite A C D (exe1_1_1_composite A B C f g) h)
