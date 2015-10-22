module ex4 where

open import Data.Empty using (⊥)

open import BCoPL.EvalML2
open import BCoPL.Show.EvalML2
open import Relation.Binary.PropositionalEquality as PropEq

-- excercise 4.1
ex-4-1-1 : ● ⊱ ("x" , i (+ 3)) ⊱ ("y" , i (+ 2)) ⊢ var "x" ⇓ i (+ 3)
ex-4-1-1 = E-Var2 x≢y E-Var1
  where
    x≢y : "x" ≡ "y" → ⊥
    x≢y ()
{-
x = 3,y = 2 |- x evalto 3 by E-Var2 {
  x = 3 |- x evalto 3 by E-Var1 {};
};
-}

ex-4-1-2 : ● ⊱ ("x" , b true) ⊱ ("y" , i (+ 4)) ⊢ if var "x" then var "y" ⊕ i (+ 1) else var "y" ⊝ i (+ 1) ⇓ i (+ 5)
ex-4-1-2 = E-IfT (E-Var2 x≢y E-Var1) (E-Plus E-Var1 E-Int (B-Plus refl))
  where
    x≢y : "x" ≡ "y" → ⊥
    x≢y ()
{-
x = true,y = 4 |- if x then (y + 1) else (y - 1) evalto 5 by E-IfT {
  x = true,y = 4 |- x evalto true by E-Var2 {
    x = true |- x evalto true by E-Var1 {};
  };
  x = true,y = 4 |- (y + 1) evalto 5 by E-Plus {
    x = true,y = 4 |- y evalto 4 by E-Var1 {};
    x = true,y = 4 |- 1 evalto 1 by E-Int {};
    4 plus 1 is 5 by B-Plus {};
  };
};
-}
ex-4-1-3 : ● ⊢ ℓet "x" ≔ i (+ 1) ⊕ i (+ 2) ιn var "x" ⊛ i (+ 4) ⇓ i (+ 12)
ex-4-1-3 = E-Let (E-Plus E-Int E-Int (B-Plus refl))
                 (E-Times E-Var1 E-Int (B-Times refl))
{-
|- let x = (1 + 2) in (x * 4) evalto 12 by E-Let {
  |- (1 + 2) evalto 3 by E-Plus {
    |- 1 evalto 1 by E-Int {};
    |- 2 evalto 2 by E-Int {};
    1 plus 2 is 3 by B-Plus {};
  };
  x = 3 |- (x * 4) evalto 12 by E-Times {
    x = 3 |- x evalto 3 by E-Var1 {};
    x = 3 |- 4 evalto 4 by E-Int {};
    3 times 4 is 12 by B-Times {};
  };
};
-}

ex-4-1-4 : ● ⊢ ℓet "x" ≔ i (+ 3) ⊛ i (+ 3) ιn ℓet "y" ≔ i (+ 4) ⊛ var "x" ιn var "x" ⊕ var "y" ⇓ i (+ 45)
ex-4-1-4 = E-Let (E-Times E-Int E-Int (B-Times refl))
                 (E-Let (E-Times E-Int E-Var1 (B-Times refl))
                        (E-Plus (E-Var2 x≢y E-Var1) E-Var1 (B-Plus refl)))
  where
    x≢y : "x" ≡ "y" → ⊥
    x≢y ()
{-
|- let x = (3 * 3) in let y = (4 * x) in (x + y) evalto 45 by E-Let {
  |- (3 * 3) evalto 9 by E-Times {
    |- 3 evalto 3 by E-Int {};
    |- 3 evalto 3 by E-Int {};
    3 times 3 is 9 by B-Times {};
  };
  x = 9 |- let y = (4 * x) in (x + y) evalto 45 by E-Let {
    x = 9 |- (4 * x) evalto 36 by E-Times {
      x = 9 |- 4 evalto 4 by E-Int {};
      x = 9 |- x evalto 9 by E-Var1 {};
      4 times 9 is 36 by B-Times {};
    };
    x = 9,y = 36 |- (x + y) evalto 45 by E-Plus {
      x = 9,y = 36 |- x evalto 9 by E-Var2 {
        x = 9 |- x evalto 9 by E-Var1 {};
      };
      x = 9,y = 36 |- y evalto 36 by E-Var1 {};
      9 plus 36 is 45 by B-Plus {};
    };
  };
};
-}

ex-4-1-5 : ● ⊱ ("x" , i (+ 3)) ⊢ ℓet "x" ≔ var "x" ⊛ i (+ 2) ιn var "x" ⊕ var "x" ⇓ i (+ 12)
ex-4-1-5 = E-Let (E-Times E-Var1 E-Int (B-Times refl))
                 (E-Plus E-Var1 E-Var1 (B-Plus refl))
{-
x = 3 |- let x = (x * 2) in (x + x) evalto 12 by E-Let {
  x = 3 |- (x * 2) evalto 6 by E-Times {
    x = 3 |- x evalto 3 by E-Var1 {};
    x = 3 |- 2 evalto 2 by E-Int {};
    3 times 2 is 6 by B-Times {};
  };
  x = 3,x = 6 |- (x + x) evalto 12 by E-Plus {
    x = 3,x = 6 |- x evalto 6 by E-Var1 {};
    x = 3,x = 6 |- x evalto 6 by E-Var1 {};
    6 plus 6 is 12 by B-Plus {};
  };
};
-}

Q39 : ● ⊢ ℓet "x" ≔ ℓet "y" ≔ i (+ 3) ⊝ i (+ 2) ιn var "y" ⊛ var "y" ιn ℓet "y" ≔ i (+ 4) ιn var "x" ⊕ var "y" ⇓ i (+ 5)
Q39 = E-Let (E-Let (E-Minus E-Int E-Int (B-Minus refl))
                   (E-Times E-Var1 E-Var1 (B-Times refl)))
            (E-Let E-Int 
                   (E-Plus (E-Var2 x≢y E-Var1) E-Var1 (B-Plus refl)))
  where
    x≢y : "x" ≡ "y" → ⊥
    x≢y ()
{-
|- let x = let y = (3 - 2) in (y * y) in let y = 4 in (x + y) evalto 5 by E-Let {
  |- let y = (3 - 2) in (y * y) evalto 1 by E-Let {
    |- (3 - 2) evalto 1 by E-Minus {
      |- 3 evalto 3 by E-Int {};
      |- 2 evalto 2 by E-Int {};
      3 minus 2 is 1 by B-Minus {};
    };
    y = 1 |- (y * y) evalto 1 by E-Times {
      y = 1 |- y evalto 1 by E-Var1 {};
      y = 1 |- y evalto 1 by E-Var1 {};
      1 times 1 is 1 by B-Times {};
    };
  };
  x = 1 |- let y = 4 in (x + y) evalto 5 by E-Let {
    x = 1 |- 4 evalto 4 by E-Int {};
    x = 1,y = 4 |- (x + y) evalto 5 by E-Plus {
      x = 1,y = 4 |- x evalto 1 by E-Var2 {
        x = 1 |- x evalto 1 by E-Var1 {};
      };
      x = 1,y = 4 |- y evalto 4 by E-Var1 {};
      1 plus 4 is 5 by B-Plus {};
    };
  };
};
-}
