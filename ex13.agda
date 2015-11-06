module ex13 where

open import BCoPL.EvalRefML3
open import BCoPL.Show.EvalRefML3

q141 : ● ⊱ ("@l" , i (+ 2)) ╱ ● ⊱ ("x" , ℓ "@l") ⊢ ! (var "x") ⊕ i (+ 3) ⇓ i (+ 5) ╱ ● ⊱ ("@l" , i (+ 2))
q141 = E-Plus (E-Deref (E-Var refl) refl) E-Int (B-Plus refl)
{-
@l = 2 / x = @l |- ((! x) + 3) evalto 5 / @l = 2 by E-Plus {
  @l = 2 / x = @l |- (! x) evalto 2 / @l = 2 by E-Deref {
    @l = 2 / x = @l |- x evalto @l / @l = 2 by E-Var {};
  };
  @l = 2 / x = @l |- 3 evalto 3 / @l = 2 by E-Int {};
  2 plus 3 is 5 by B-Plus {};
};
-}

