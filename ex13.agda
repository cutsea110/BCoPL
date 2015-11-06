module ex13 where

open import BCoPL.EvalRefML3
open import BCoPL.Show.EvalRefML3

q141 : ● ⊱ ("@l" , i (+ 2)) ╱ ● ⊱ ("x" , ℓ "@l") ⊢ ! (var "x") ⊕ i (+ 3) ⇓ i (+ 5) ╱ ● ⊱ ("@l" , i (+ 2))
q141 = E-Plus (E-Deref (E-Var refl) refl)
              E-Int
              (B-Plus refl)
{-
@l = 2 / x = @l |- ((! x) + 3) evalto 5 / @l = 2 by E-Plus {
  @l = 2 / x = @l |- (! x) evalto 2 / @l = 2 by E-Deref {
    @l = 2 / x = @l |- x evalto @l / @l = 2 by E-Var {};
  };
  @l = 2 / x = @l |- 3 evalto 3 / @l = 2 by E-Int {};
  2 plus 3 is 5 by B-Plus {};
};
-}

q142 : ● ⊱ ("@l" , i (+ 2)) ╱ ● ⊱ ("x" , ℓ "@l") ⊢ var "x" ≔ ! (var "x") ⊕ i (+ 1) ⇓ i (+ 3) ╱ ● ⊱ ("@l" , i (+ 3))
q142 = E-Assign (E-Var refl)
                (E-Plus (E-Deref (E-Var refl) refl)
                        E-Int
                        (B-Plus refl))
                refl
{-
@l = 2 / x = @l |- (x := ((! x) + 1)) evalto 3 / @l = 3 by E-Assign {
  @l = 2 / x = @l |- x evalto @l / @l = 2 by E-Var {};
  @l = 2 / x = @l |- ((! x) + 1) evalto 3 / @l = 2 by E-Plus {
    @l = 2 / x = @l |- (! x) evalto 2 / @l = 2 by E-Deref {
      @l = 2 / x = @l |- x evalto @l / @l = 2 by E-Var {};
    };
    @l = 2 / x = @l |- 1 evalto 1 / @l = 2 by E-Int {};
    2 plus 1 is 3 by B-Plus {};
  };
};
-}

q143 : ● ╱ ● ⊢ ℓet "r" ≔ ref (b true) ιn ! (var "r") ⇓ b true ╱ ● ⊱ ("@l" , b true)
q143 = E-Let (E-Ref E-Bool refl)
             (E-Deref (E-Var refl) refl)
{-
|- let r = (ref true) in (! r) evalto true / @l = true by E-Let {
  |- (ref true) evalto @l / @l = true by E-Ref {
    |- true evalto true by E-Bool {};
  };
  @l = true / r = @l |- (! r) evalto true / @l = true by E-Deref {
    @l = true / r = @l |- r evalto @l / @l = true by E-Var {};
  };
};
-}

q144 : ● ╱ ● ⊢ ℓet "incr" ≔ fun "x" ⇒ (var "x" ≔ ! (var "x") ⊕ i (+ 1)) ιn
                 ℓet "x" ≔ ref (i (+ 0)) ιn
                 ℓet "z" ≔ app (var "incr") (var "x") ιn
                 ! (var "x") ⇓ i (+ 1) ╱ ● ⊱ ("@l" , i (+ 1))
q144 = E-Let E-Fun (E-Let (E-Ref {l = "@l"} E-Int refl)
                          (E-Let (E-App (E-Var refl)
                                        (E-Var refl)
                                        (E-Assign (E-Var refl)
                                                  (E-Plus (E-Deref (E-Var refl) refl) E-Int (B-Plus refl))
                                                  refl))
                                 (E-Deref (E-Var refl) refl)))
{-

-}


