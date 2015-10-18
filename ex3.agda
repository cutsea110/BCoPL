module ex3 where

open import BCoPL.EvalML1
open import BCoPL.Show.EvalML1

-- excercise 3.1
ex-3-1-1 : i (+ 3) ⊕ i (+ 5) ⇓ i (+ 8)
ex-3-1-1 = E-Plus E-Int E-Int (B-Plus refl)
{-
(3 + 5) evalto 8 by E-Plus {
  3 evalto 3 by E-Int {};
  5 evalto 5 by E-Int {};
  3 plus 5 is 8 by B-Plus {};
};
-}

ex-3-1-2 : i (+ 8) ⊝ i (+ 2) ⊝ i (+ 3) ⇓ i (+ 3)
ex-3-1-2 = E-Minus (E-Minus E-Int E-Int (B-Minus refl)) E-Int (B-Minus refl)
{-
((8 - 2) - 3) evalto 3 by E-Minus {
  (8 - 2) evalto 6 by E-Minus {
    8 evalto 8 by E-Int {};
    2 evalto 2 by E-Int {};
    8 minus 2 is 6 by B-Minus {};
  };
  3 evalto 3 by E-Int {};
  6 minus 3 is 3 by B-Minus {};
};
-}
ex-3-1-3 : (i (+ 4) ⊕ i (+ 5)) ⊛ (i (+ 1) ⊝ i (+ 10)) ⇓ i (-[1+ 80 ])
ex-3-1-3 = E-Times (E-Plus E-Int E-Int (B-Plus refl)) (E-Minus E-Int E-Int (B-Minus refl)) (B-Times refl)
{-
((4 + 5) * (1 - 10)) evalto -81 by E-Times {
  (4 + 5) evalto 9 by E-Plus {
    4 evalto 4 by E-Int {};
    5 evalto 5 by E-Int {};
    4 plus 5 is 9 by B-Plus {};
  };
  (1 - 10) evalto -9 by E-Minus {
    1 evalto 1 by E-Int {};
    10 evalto 10 by E-Int {};
    1 minus 10 is -9 by B-Minus {};
  };
  9 times -9 is -81 by B-Times {};
};
-}

ex-3-1-4 : if i (+ 4) ≺ i (+ 5) then i (+ 2) ⊕ i (+ 3) else i (+ 8) ⊛ i (+ 8) ⇓ i (+ 5)
ex-3-1-4 = E-IfT (E-Lt E-Int E-Int (B-Lt refl)) (E-Plus E-Int E-Int (B-Plus refl))
{-
if (4 < 5) then (2 + 3) else (8 * 8) evalto 5 by E-IfT {
  (4 < 5) evalto true by E-Lt {
    4 evalto 4 by E-Int {};
    5 evalto 5 by E-Int {};
    4 less than 5 is true by B-Lt {};
  };
  (2 + 3) evalto 5 by E-Plus {
    2 evalto 2 by E-Int {};
    3 evalto 3 by E-Int {};
    2 plus 3 is 5 by B-Plus {};
  };
};
-}

ex-3-1-5 : i (+ 3) ⊕ (if i (-[1+ 22 ]) ≺ i (-[1+ 1 ]) ⊛ i (+ 8) then i (+ 8) else i (+ 2) ⊕ i (+ 4)) ⇓ i (+ 11)
ex-3-1-5 = E-Plus E-Int (E-IfT (E-Lt E-Int (E-Times E-Int E-Int (B-Times refl)) (B-Lt refl)) E-Int) (B-Plus refl)
{-
(3 + if (-23 < (-2 * 8)) then 8 else (2 + 4)) evalto 11 by E-Plus {
  3 evalto 3 by E-Int {};
  if (-23 < (-2 * 8)) then 8 else (2 + 4) evalto 8 by E-IfT {
    (-23 < (-2 * 8)) evalto true by E-Lt {
      -23 evalto -23 by E-Int {};
      (-2 * 8) evalto -16 by E-Times {
        -2 evalto -2 by E-Int {};
        8 evalto 8 by E-Int {};
        -2 times 8 is -16 by B-Times {};
      };
      -23 less than -16 is true by B-Lt {};
    };
    8 evalto 8 by E-Int {};
  };
  3 plus 8 is 11 by B-Plus {};
};
-}

ex-3-1-6 : i (+ 3) ⊕ (if i (-[1+ 22 ]) ≺ i (-[1+ 1 ]) ⊛ i (+ 8) then i (+ 8) else i (+ 2)) ⊕ i (+ 4) ⇓ i (+ 15)
ex-3-1-6 = E-Plus (E-Plus E-Int (E-IfT (E-Lt E-Int (E-Times E-Int E-Int (B-Times refl)) (B-Lt refl)) E-Int) (B-Plus refl)) E-Int (B-Plus refl)
{-
((3 + if (-23 < (-2 * 8)) then 8 else 2) + 4) evalto 15 by E-Plus {
  (3 + if (-23 < (-2 * 8)) then 8 else 2) evalto 11 by E-Plus {
    3 evalto 3 by E-Int {};
    if (-23 < (-2 * 8)) then 8 else 2 evalto 8 by E-IfT {
      (-23 < (-2 * 8)) evalto true by E-Lt {
        -23 evalto -23 by E-Int {};
        (-2 * 8) evalto -16 by E-Times {
          -2 evalto -2 by E-Int {};
          8 evalto 8 by E-Int {};
          -2 times 8 is -16 by B-Times {};
        };
        -23 less than -16 is true by B-Lt {};
      };
      8 evalto 8 by E-Int {};
    };
    3 plus 8 is 11 by B-Plus {};
  };
  4 evalto 4 by E-Int {};
  11 plus 4 is 15 by B-Plus {};
};
-}
