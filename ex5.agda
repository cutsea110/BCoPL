module ex5 where

open import Data.Empty using (⊥)

open import BCoPL.EvalML3
open import BCoPL.Show.EvalML3
open import Relation.Binary.PropositionalEquality as PropEq

q40 : ● ⊢ fun "x" ⇒ var "x" ⊕ i (+ 1) ⇓ ⟨ ● ⟩[fun "x" ⇒ var "x" ⊕ i (+ 1)]
q40 = E-Fun
{-
|- fun x -> (x + 1) evalto ()[fun x -> (x + 1)] by E-Fun {};
-}

q41 : ● ⊢ ℓet "y" ≔ i (+ 2) ιn fun "x" ⇒ var "x" ⊕ var "y" ⇓ ⟨ ● ⊱ ("y" , i (+ 2)) ⟩[fun "x" ⇒ var "x" ⊕ var "y"]
q41 = E-Let E-Int E-Fun
{-
|- let y = 2 in fun x -> (x + y) evalto (y = 2)[fun x -> (x + y)] by E-Let {
  |- 2 evalto 2 by E-Int {};
  y = 2 |- fun x -> (x + y) evalto (y = 2)[fun x -> (x + y)] by E-Fun {};
};
-}

ex-5-1-1 : ● ⊢ ℓet "sq" ≔ fun "x" ⇒ var "x" ⊛ var "x" ιn app (var "sq") (i (+ 3)) ⊕ app (var "sq") (i (+ 4)) ⇓ i (+ 25)
ex-5-1-1 = E-Let E-Fun
                 (E-Plus (E-App E-Var1 E-Int (E-Times E-Var1 E-Var1 (B-Times refl)))
                         (E-App E-Var1 E-Int (E-Times E-Var1 E-Var1 (B-Times refl))) (B-Plus refl))
{-
|- let sq = fun x -> (x * x) in (sq 3 + sq 4) evalto 25 by E-Let {
  |- fun x -> (x * x) evalto ()[fun x -> (x * x)] by E-Fun {};
  sq = ()[fun x -> (x * x)] |- (sq 3 + sq 4) evalto 25 by E-Plus {
  sq = ()[fun x -> (x * x)] |- sq 3 evalto 9 by E-App {
      sq = ()[fun x -> (x * x)] |- sq evalto ()[fun x -> (x * x)] by E-Var1 {};
      sq = ()[fun x -> (x * x)] |- 3 evalto 3 by E-Int {};
      x = 3 |- (x * x) evalto 9 by E-Times {
        x = 3 |- x evalto 3 by E-Var1 {};
        x = 3 |- x evalto 3 by E-Var1 {};
        3 times 3 is 9 by B-Times {};
      };
    };
    sq = ()[fun x -> (x * x)] |- sq 4 evalto 16 by E-App {
      sq = ()[fun x -> (x * x)] |- sq evalto ()[fun x -> (x * x)] by E-Var1 {};
      sq = ()[fun x -> (x * x)] |- 4 evalto 4 by E-Int {};
      x = 4 |- (x * x) evalto 16 by E-Times {
        x = 4 |- x evalto 4 by E-Var1 {};
        x = 4 |- x evalto 4 by E-Var1 {};
        4 times 4 is 16 by B-Times {};
      };
    };
    9 plus 16 is 25 by B-Plus {};
  };
};
-}

ex-5-1-2 : ● ⊢ ℓet "sm" ≔ fun "f" ⇒ app (var "f") (i (+ 3)) ⊕ app (var "f") (i (+ 4)) ιn app (var "sm") (fun "x" ⇒ var "x" ⊛ var "x") ⇓ i (+ 25)
ex-5-1-2 = E-Let E-Fun
                 (E-App E-Var1
                        E-Fun
                        (E-Plus (E-App E-Var1 E-Int (E-Times E-Var1 E-Var1 (B-Times refl)))
                                (E-App E-Var1 E-Int (E-Times E-Var1 E-Var1 (B-Times refl))) (B-Plus refl)))

{-
|- let sm = (fun f -> (f 3 + f 4)) in sm (fun x -> (x * x)) evalto 25 by E-Let {
  |- (fun f -> (f 3 + f 4)) evalto ()[fun f -> (f 3 + f 4)] by E-Fun {};
  sm = ()[fun f -> (f 3 + f 4)] |- sm (fun x -> (x * x)) evalto 25 by E-App {
    sm = ()[fun f -> (f 3 + f 4)] |- sm evalto ()[fun f -> (f 3 + f 4)] by E-Var1 {};
    sm = ()[fun f -> (f 3 + f 4)] |- (fun x -> (x * x)) evalto (sm = ()[fun f -> (f 3 + f 4)])[fun x -> (x * x)] by E-Fun {};
    f = (sm = ()[fun f -> (f 3 + f 4)])[fun x -> (x * x)] |- (f 3 + f 4) evalto 25 by E-Plus {
      f = (sm = ()[fun f -> (f 3 + f 4)])[fun x -> (x * x)] |- f 3 evalto 9 by E-App {
        f = (sm = ()[fun f -> (f 3 + f 4)])[fun x -> (x * x)] |- f evalto (sm = ()[fun f -> (f 3 + f 4)])[fun x -> (x * x)] by E-Var1 {};
        f = (sm = ()[fun f -> (f 3 + f 4)])[fun x -> (x * x)] |- 3 evalto 3 by E-Int {};
        sm = ()[fun f -> (f 3 + f 4)],x = 3 |- (x * x) evalto 9 by E-Times {
          sm = ()[fun f -> (f 3 + f 4)],x = 3 |- x evalto 3 by E-Var1 {};
          sm = ()[fun f -> (f 3 + f 4)],x = 3 |- x evalto 3 by E-Var1 {};
          3 times 3 is 9 by B-Times {};
        };
      };
      f = (sm = ()[fun f -> (f 3 + f 4)])[fun x -> (x * x)] |- f 4 evalto 16 by E-App {
        f = (sm = ()[fun f -> (f 3 + f 4)])[fun x -> (x * x)] |- f evalto (sm = ()[fun f -> (f 3 + f 4)])[fun x -> (x * x)] by E-Var1 {};
        f = (sm = ()[fun f -> (f 3 + f 4)])[fun x -> (x * x)] |- 4 evalto 4 by E-Int {};
        sm = ()[fun f -> (f 3 + f 4)],x = 4 |- (x * x) evalto 16 by E-Times {
          sm = ()[fun f -> (f 3 + f 4)],x = 4 |- x evalto 4 by E-Var1 {};
          sm = ()[fun f -> (f 3 + f 4)],x = 4 |- x evalto 4 by E-Var1 {};
          4 times 4 is 16 by B-Times {};
        };
      };
      9 plus 16 is 25 by B-Plus {};
    };
  };
};
-}

q44 : ● ⊢ ℓet "max" ≔ fun "x" ⇒ fun "y" ⇒ if var "x" ≺ var "y" then var "y" else var "x" ιn app (app (var "max") (i (+ 3))) (i (+ 5)) ⇓ i (+ 5)
q44 = E-Let E-Fun
            (E-App (E-App E-Var1 E-Int E-Fun)
                   E-Int
                   (E-IfT (E-Lt (E-Var2 x≢y E-Var1) E-Var1 (B-Lt refl)) E-Var1))
  where
    x≢y : "x" ≡ "y" → ⊥
    x≢y ()

{-
|- let max = (fun x -> (fun y -> if (x < y) then y else x)) in max 3 5 evalto 5 by E-Let {
  |- (fun x -> (fun y -> if (x < y) then y else x)) evalto ()[fun x -> (fun y -> if (x < y) then y else x)] by E-Fun {};
  max = ()[fun x -> (fun y -> if (x < y) then y else x)] |- max 3 5 evalto 5 by E-App {
    max = ()[fun x -> (fun y -> if (x < y) then y else x)] |- max 3 evalto (x = 3)[fun y -> if (x < y) then y else x] by E-App {
      max = ()[fun x -> (fun y -> if (x < y) then y else x)] |- max evalto ()[fun x -> (fun y -> if (x < y) then y else x)] by E-Var1 {};
      max = ()[fun x -> (fun y -> if (x < y) then y else x)] |- 3 evalto 3 by E-Int {};
      x = 3 |- (fun y -> if (x < y) then y else x) evalto (x = 3)[fun y -> if (x < y) then y else x] by E-Fun {};
    };
    max = ()[fun x -> (fun y -> if (x < y) then y else x)] |- 5 evalto 5 by E-Int {};
    x = 3,y = 5 |- if (x < y) then y else x evalto 5 by E-IfT {
      x = 3,y = 5 |- (x < y) evalto true by E-Lt {
        x = 3,y = 5 |- x evalto 3 by E-Var2 {
          x = 3 |- x evalto 3 by E-Var1 {};
        };
        x = 3,y = 5 |- y evalto 5 by E-Var1 {};
        3 less than 5 is true by B-Lt {};
      };
      x = 3,y = 5 |- y evalto 5 by E-Var1 {};
    };
  };
};
-}

q45 : ● ⊢ ℓet "a" ≔ i (+ 3) ιn ℓet "f" ≔ fun "y" ⇒ var "y" ⊛ var "a" ιn ℓet "a" ≔ i (+ 5) ιn app (var "f") (i (+ 4)) ⇓ i (+ 12)
q45 = E-Let E-Int
            (E-Let E-Fun
                   (E-Let E-Int
                          (E-App (E-Var2 f≢a E-Var1)
                                 E-Int
                                 (E-Times E-Var1 (E-Var2 a≢y E-Var1) (B-Times refl)))))
  where
    f≢a : "f" ≡ "a" → ⊥
    f≢a ()
    a≢y : "a" ≡ "y" → ⊥
    a≢y ()

{-
|- let a = 3 in let f = (fun y -> (y * a)) in let a = 5 in f 4 evalto 12 by E-Let {
  |- 3 evalto 3 by E-Int {};
  a = 3 |- let f = (fun y -> (y * a)) in let a = 5 in f 4 evalto 12 by E-Let {
    a = 3 |- (fun y -> (y * a)) evalto (a = 3)[fun y -> (y * a)] by E-Fun {};
    a = 3,f = (a = 3)[fun y -> (y * a)] |- let a = 5 in f 4 evalto 12 by E-Let {
      a = 3,f = (a = 3)[fun y -> (y * a)] |- 5 evalto 5 by E-Int {};
      a = 3,f = (a = 3)[fun y -> (y * a)],a = 5 |- f 4 evalto 12 by E-App {
        a = 3,f = (a = 3)[fun y -> (y * a)],a = 5 |- f evalto (a = 3)[fun y -> (y * a)] by E-Var2 {
          a = 3,f = (a = 3)[fun y -> (y * a)] |- f evalto (a = 3)[fun y -> (y * a)] by E-Var1 {};
        };
        a = 3,f = (a = 3)[fun y -> (y * a)],a = 5 |- 4 evalto 4 by E-Int {};
        a = 3,y = 4 |- (y * a) evalto 12 by E-Times {
          a = 3,y = 4 |- y evalto 4 by E-Var1 {};
          a = 3,y = 4 |- a evalto 3 by E-Var2 {
            a = 3 |- a evalto 3 by E-Var1 {};
          };
          4 times 3 is 12 by B-Times {};
        };
      };
    };
  };
};
-}

ex-5-1-3 : ● ⊢ ℓet "twice" ≔ fun "f" ⇒ fun "x" ⇒ app (var "f") (app (var "f") (var "x"))
                ιn app (app (var "twice") (fun "x" ⇒ var "x" ⊛ var "x")) (i (+ 2)) ⇓ i (+ 16)
ex-5-1-3 = E-Let E-Fun
                 (E-App (E-App E-Var1 E-Fun E-Fun)
                        E-Int
                        (E-App (E-Var2 f≢x E-Var1)
                               (E-App (E-Var2 f≢x E-Var1)
                                      E-Var1
                                      (E-Times E-Var1 E-Var1 (B-Times refl)))
                               (E-Times E-Var1 E-Var1 (B-Times refl))))
  where
    f≢x : "f" ≡ "x" → ⊥
    f≢x ()
{-
|- let twice = (fun f -> (fun x -> f(f(x)))) in twice((fun x -> (x * x)))(2) evalto 16 by E-Let {
  |- (fun f -> (fun x -> f(f(x)))) evalto ()[fun f -> (fun x -> f(f(x)))] by E-Fun {};
  twice = ()[fun f -> (fun x -> f(f(x)))] |- twice((fun x -> (x * x)))(2) evalto 16 by E-App {
    twice = ()[fun f -> (fun x -> f(f(x)))] |- twice((fun x -> (x * x))) evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-App {
      twice = ()[fun f -> (fun x -> f(f(x)))] |- twice evalto ()[fun f -> (fun x -> f(f(x)))] by E-Var1 {};
      twice = ()[fun f -> (fun x -> f(f(x)))] |- (fun x -> (x * x)) evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Fun {};
      f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- (fun x -> f(f(x))) evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-Fun {};
    };
    twice = ()[fun f -> (fun x -> f(f(x)))] |- 2 evalto 2 by E-Int {};
    f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 2 |- f(f(x)) evalto 16 by E-App {
      f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 2 |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var2 {
        f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var1 {};
      };
      f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 2 |- f(x) evalto 4 by E-App {
        f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 2 |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var2 {
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var1 {};
        };
        f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 2 |- x evalto 2 by E-Var1 {};
        twice = ()[fun f -> (fun x -> f(f(x)))],x = 2 |- (x * x) evalto 4 by E-Times {
          twice = ()[fun f -> (fun x -> f(f(x)))],x = 2 |- x evalto 2 by E-Var1 {};
          twice = ()[fun f -> (fun x -> f(f(x)))],x = 2 |- x evalto 2 by E-Var1 {};
          2 times 2 is 4 by B-Times {};
        };
      };
      twice = ()[fun f -> (fun x -> f(f(x)))],x = 4 |- (x * x) evalto 16 by E-Times {
        twice = ()[fun f -> (fun x -> f(f(x)))],x = 4 |- x evalto 4 by E-Var1 {};
        twice = ()[fun f -> (fun x -> f(f(x)))],x = 4 |- x evalto 4 by E-Var1 {};
        4 times 4 is 16 by B-Times {};
      };
    };
  };
};
-}

q47 : ● ⊢ ℓet "twice" ≔ fun "f" ⇒ fun "x" ⇒ app (var "f") (app (var "f") (var "x")) ιn
           app (app (app (var "twice") (var "twice")) (fun "x" ⇒ var "x" ⊛ var "x")) (i (+ 2)) ⇓ i (+ 65536)
q47 = E-Let E-Fun
            (E-App (E-App (E-App E-Var1 E-Var1 E-Fun)
                          E-Fun
                          (E-App (E-Var2 f≢x E-Var1)
                                 (E-App (E-Var2 f≢x E-Var1)
                                        E-Var1
                                        E-Fun)
                                 E-Fun))
                   E-Int
                   (E-App (E-Var2 f≢x E-Var1)
                          (E-App (E-Var2 f≢x E-Var1)
                                 E-Var1
                                 (E-App (E-Var2 f≢x E-Var1)
                                        (E-App (E-Var2 f≢x E-Var1)
                                               E-Var1
                                               (E-Times E-Var1 E-Var1 (B-Times refl)))
                                        (E-Times E-Var1 E-Var1 (B-Times refl))))
                          (E-App (E-Var2 f≢x E-Var1)
                                 (E-App (E-Var2 f≢x E-Var1)
                                        E-Var1
                                        (E-Times E-Var1 E-Var1 (B-Times refl)))
                                 (E-Times E-Var1 E-Var1 (B-Times refl)))))
  where
    f≢x : "f" ≡ "x" → ⊥
    f≢x ()
{-
|- let twice = (fun f -> (fun x -> f(f(x)))) in twice(twice)((fun x -> (x * x)))(2) evalto 65536 by E-Let {
  |- (fun f -> (fun x -> f(f(x)))) evalto ()[fun f -> (fun x -> f(f(x)))] by E-Fun {};
  twice = ()[fun f -> (fun x -> f(f(x)))] |- twice(twice)((fun x -> (x * x)))(2) evalto 65536 by E-App {
    twice = ()[fun f -> (fun x -> f(f(x)))] |- twice(twice)((fun x -> (x * x))) evalto (f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))])[fun x -> f(f(x))] by E-App {
      twice = ()[fun f -> (fun x -> f(f(x)))] |- twice(twice) evalto (f = ()[fun f -> (fun x -> f(f(x)))])[fun x -> f(f(x))] by E-App {
        twice = ()[fun f -> (fun x -> f(f(x)))] |- twice evalto ()[fun f -> (fun x -> f(f(x)))] by E-Var1 {};
        twice = ()[fun f -> (fun x -> f(f(x)))] |- twice evalto ()[fun f -> (fun x -> f(f(x)))] by E-Var1 {};
        f = ()[fun f -> (fun x -> f(f(x)))] |- (fun x -> f(f(x))) evalto (f = ()[fun f -> (fun x -> f(f(x)))])[fun x -> f(f(x))] by E-Fun {};
      };
      twice = ()[fun f -> (fun x -> f(f(x)))] |- (fun x -> (x * x)) evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Fun {};
      f = ()[fun f -> (fun x -> f(f(x)))],x = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f(f(x)) evalto (f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))])[fun x -> f(f(x))] by E-App {
        f = ()[fun f -> (fun x -> f(f(x)))],x = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto ()[fun f -> (fun x -> f(f(x)))] by E-Var2 {
          f = ()[fun f -> (fun x -> f(f(x)))] |- f evalto ()[fun f -> (fun x -> f(f(x)))] by E-Var1 {};
        };
        f = ()[fun f -> (fun x -> f(f(x)))],x = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f(x) evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-App {
          f = ()[fun f -> (fun x -> f(f(x)))],x = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto ()[fun f -> (fun x -> f(f(x)))] by E-Var2 {
            f = ()[fun f -> (fun x -> f(f(x)))] |- f evalto ()[fun f -> (fun x -> f(f(x)))] by E-Var1 {};
          };
          f = ()[fun f -> (fun x -> f(f(x)))],x = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- x evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var1 {};
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- (fun x -> f(f(x))) evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-Fun {};
        };
        f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] |- (fun x -> f(f(x))) evalto (f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))])[fun x -> f(f(x))] by E-Fun {};
      };
    };
    twice = ()[fun f -> (fun x -> f(f(x)))] |- 2 evalto 2 by E-Int {};
    f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))],x = 2 |- f(f(x)) evalto 65536 by E-App {
      f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))],x = 2 |- f evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-Var2 {
        f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] |- f evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-Var1 {};
      };
      f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))],x = 2 |- f(x) evalto 16 by E-App {
        f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))],x = 2 |- f evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-Var2 {
          f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] |- f evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-Var1 {};
        };
        f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))],x = 2 |- x evalto 2 by E-Var1 {};
        f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 2 |- f(f(x)) evalto 16 by E-App {
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 2 |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var2 {
            f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var1 {};
          };
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 2 |- f(x) evalto 4 by E-App {
            f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 2 |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var2 {
              f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var1 {};
            };
            f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 2 |- x evalto 2 by E-Var1 {};
            twice = ()[fun f -> (fun x -> f(f(x)))],x = 2 |- (x * x) evalto 4 by E-Times {
              twice = ()[fun f -> (fun x -> f(f(x)))],x = 2 |- x evalto 2 by E-Var1 {};
              twice = ()[fun f -> (fun x -> f(f(x)))],x = 2 |- x evalto 2 by E-Var1 {};
              2 times 2 is 4 by B-Times {};
            };
          };
          twice = ()[fun f -> (fun x -> f(f(x)))],x = 4 |- (x * x) evalto 16 by E-Times {
            twice = ()[fun f -> (fun x -> f(f(x)))],x = 4 |- x evalto 4 by E-Var1 {};
            twice = ()[fun f -> (fun x -> f(f(x)))],x = 4 |- x evalto 4 by E-Var1 {};
            4 times 4 is 16 by B-Times {};
          };
        };
      };
      f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 16 |- f(f(x)) evalto 65536 by E-App {
        f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 16 |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var2 {
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var1 {};
        };
        f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 16 |- f(x) evalto 256 by E-App {
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 16 |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var2 {
            f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var1 {};
          };
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 16 |- x evalto 16 by E-Var1 {};
          twice = ()[fun f -> (fun x -> f(f(x)))],x = 16 |- (x * x) evalto 256 by E-Times {
            twice = ()[fun f -> (fun x -> f(f(x)))],x = 16 |- x evalto 16 by E-Var1 {};
            twice = ()[fun f -> (fun x -> f(f(x)))],x = 16 |- x evalto 16 by E-Var1 {};
            16 times 16 is 256 by B-Times {};
          };
        };
        twice = ()[fun f -> (fun x -> f(f(x)))],x = 256 |- (x * x) evalto 65536 by E-Times {
          twice = ()[fun f -> (fun x -> f(f(x)))],x = 256 |- x evalto 256 by E-Var1 {};
          twice = ()[fun f -> (fun x -> f(f(x)))],x = 256 |- x evalto 256 by E-Var1 {};
          256 times 256 is 65536 by B-Times {};
        };
      };
    };
  };
};
-}

ex-5-1-4 : ● ⊢ ℓet "compose" ≔ fun "f" ⇒ (fun "g" ⇒ (fun "x" ⇒ app (var "f") (app (var "g") (var "x")))) ιn
                ℓet "p" ≔ fun "x" ⇒ var "x" ⊛ var "x" ιn
                ℓet "q" ≔ fun "x" ⇒ var "x" ⊕ (i (+ 4)) ιn
                app (app (app (var "compose") (var "p")) (var "q")) (i (+ 4)) ⇓ i (+ 64)
ex-5-1-4 = E-Let E-Fun
                 (E-Let E-Fun
                        (E-Let E-Fun
                               (E-App (E-App (E-App (E-Var2 compose≢q (E-Var2 compose≢p E-Var1))
                                                    (E-Var2 p≢q E-Var1)
                                                    E-Fun)
                                             E-Var1 E-Fun)
                                      E-Int
                                      (E-App (E-Var2 f≢x (E-Var2 f≢g E-Var1))
                                             (E-App (E-Var2 g≢x E-Var1)
                                                    E-Var1
                                                    (E-Plus E-Var1 E-Int (B-Plus refl)))
                                             (E-Times E-Var1 E-Var1 (B-Times refl))))))
  where
    compose≢q : "compose" ≡ "q" → ⊥
    compose≢q ()
    compose≢p : "compose" ≡ "p" → ⊥
    compose≢p ()
    p≢q : "p" ≡ "q" → ⊥
    p≢q ()
    f≢x : "f" ≡ "x" → ⊥
    f≢x ()
    f≢g : "f" ≡ "g" → ⊥
    f≢g ()
    g≢x : "g" ≡ "x" → ⊥
    g≢x ()
{-
-- compile test.agda by C-cC-xC-c
-- test.agda has main action to putStrLn showDerivation⇓ ex-5-1-4

|- let compose = (fun f -> (fun g -> (fun x -> f(g(x))))) in let p = (fun x -> (x * x)) in let q = (fun x -> (x + 4)) in compose(p)(q)(4) evalto 64 by E-Let {
  |- (fun f -> (fun g -> (fun x -> f(g(x))))) evalto ()[fun f -> (fun g -> (fun x -> f(g(x))))] by E-Fun {};
  compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))] |- let p = (fun x -> (x * x)) in let q = (fun x -> (x + 4)) in compose(p)(q)(4) evalto 64 by E-Let {
    compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))] |- (fun x -> (x * x)) evalto (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] by E-Fun {};
    compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] |- let q = (fun x -> (x + 4)) in compose(p)(q)(4) evalto 64 by E-Let {
      compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] |- (fun x -> (x + 4)) evalto (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] by E-Fun {};
      compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],q = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] |- compose(p)(q)(4) evalto 64 by E-App {
        compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],q = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] |- compose(p)(q) evalto (f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],g = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)])[fun x -> f(g(x))] by E-App {
          compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],q = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] |- compose(p) evalto (f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun g -> (fun x -> f(g(x)))] by E-App {
            compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],q = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] |- compose evalto ()[fun f -> (fun g -> (fun x -> f(g(x))))] by E-Var2 {
              compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] |- compose evalto ()[fun f -> (fun g -> (fun x -> f(g(x))))] by E-Var2 {
                compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))] |- compose evalto ()[fun f -> (fun g -> (fun x -> f(g(x))))] by E-Var1 {};
              };
            };
            compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],q = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] |- p evalto (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] by E-Var2 {
              compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] |- p evalto (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] by E-Var1 {};
            };
            f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] |- (fun g -> (fun x -> f(g(x)))) evalto (f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun g -> (fun x -> f(g(x)))] by E-Fun {};
          };
          compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],q = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] |- q evalto (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] by E-Var1 {};
          f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],g = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] |- (fun x -> f(g(x))) evalto (f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],g = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)])[fun x -> f(g(x))] by E-Fun {};
        };
        compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],q = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] |- 4 evalto 4 by E-Int {};
        f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],g = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)],x = 4 |- f(g(x)) evalto 64 by E-App {
          f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],g = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)],x = 4 |- f evalto (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] by E-Var2 {
            f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],g = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] |- f evalto (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] by E-Var2 {
              f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] |- f evalto (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)] by E-Var1 {};
            };
          };
          f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],g = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)],x = 4 |- g(x) evalto 8 by E-App {
            f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],g = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)],x = 4 |- g evalto (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] by E-Var2 {
              f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],g = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] |- g evalto (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)] by E-Var1 {};
            };
            f = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],g = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)])[fun x -> (x + 4)],x = 4 |- x evalto 4 by E-Var1 {};
            compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],x = 4 |- (x + 4) evalto 8 by E-Plus {
              compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],x = 4 |- x evalto 4 by E-Var1 {};
              compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],p = (compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))])[fun x -> (x * x)],x = 4 |- 4 evalto 4 by E-Int {};
              4 plus 4 is 8 by B-Plus {};
            };
          };
          compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],x = 8 |- (x * x) evalto 64 by E-Times {
            compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],x = 8 |- x evalto 8 by E-Var1 {};
            compose = ()[fun f -> (fun g -> (fun x -> f(g(x))))],x = 8 |- x evalto 8 by E-Var1 {};
            8 times 8 is 64 by B-Times {};
          };
        };
      };
    };
  };
};
-}

q49 : ● ⊢ ℓet "s" ≔ fun "f" ⇒ fun "g" ⇒ fun "x" ⇒ app (app (var "f") (var "x")) (app (var "g") (var "x")) ιn
           ℓet "k" ≔ fun "x" ⇒ fun "y" ⇒ var "x" ιn
           app (app (app (var "s") (var "k")) (var "k")) (i (+ 7)) ⇓ i (+ 7)
q49 = E-Let E-Fun
            (E-Let E-Fun
                   (E-App (E-App (E-App (E-Var2 s≢k E-Var1) E-Var1 E-Fun) E-Var1 E-Fun)
                          E-Int
                          (E-App (E-App (E-Var2 f≢x (E-Var2 f≢g E-Var1)) E-Var1 E-Fun)
                                 (E-App (E-Var2 g≢x E-Var1) E-Var1 E-Fun)
                                 (E-Var2 x≢y E-Var1))))
  where
    s≢k : "s" ≡ "k" → ⊥
    s≢k ()
    f≢x : "f" ≡ "x" → ⊥
    f≢x ()
    f≢g : "f" ≡ "g" → ⊥
    f≢g ()
    g≢x : "g" ≡ "x" → ⊥
    g≢x ()
    x≢y : "x" ≡ "y" → ⊥
    x≢y ()
{-
|- let s = (fun f -> (fun g -> (fun x -> f(x)(g(x))))) in let k = (fun x -> (fun y -> x)) in s(k)(k)(7) evalto 7 by E-Let {
  |- (fun f -> (fun g -> (fun x -> f(x)(g(x))))) evalto ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))] by E-Fun {};
  s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))] |- let k = (fun x -> (fun y -> x)) in s(k)(k)(7) evalto 7 by E-Let {
    s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))] |- (fun x -> (fun y -> x)) evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] by E-Fun {};
    s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],k = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- s(k)(k)(7) evalto 7 by E-App {
      s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],k = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- s(k)(k) evalto (f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)])[fun x -> f(x)(g(x))] by E-App {
        s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],k = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- s(k) evalto (f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)])[fun g -> (fun x -> f(x)(g(x)))] by E-App {
          s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],k = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- s evalto ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))] by E-Var2 {
            s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))] |- s evalto ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))] by E-Var1 {};
          };
          s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],k = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- k evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] by E-Var1 {};
          f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- (fun g -> (fun x -> f(x)(g(x)))) evalto (f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)])[fun g -> (fun x -> f(x)(g(x)))] by E-Fun {};
        };
        s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],k = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- k evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] by E-Var1 {};
        f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- (fun x -> f(x)(g(x))) evalto (f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)])[fun x -> f(x)(g(x))] by E-Fun {};
      };
      s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],k = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- 7 evalto 7 by E-Int {};
      f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],x = 7 |- f(x)(g(x)) evalto 7 by E-App {
        f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],x = 7 |- f(x) evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],x = 7)[fun y -> x] by E-App {
          f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],x = 7 |- f evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] by E-Var2 {
            f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- f evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] by E-Var2 {
              f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- f evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] by E-Var1 {};
            };
          };
          f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],x = 7 |- x evalto 7 by E-Var1 {};
          s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],x = 7 |- (fun y -> x) evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],x = 7)[fun y -> x] by E-Fun {};
        };
        f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],x = 7 |- g(x) evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],x = 7)[fun y -> x] by E-App {
          f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],x = 7 |- g evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] by E-Var2 {
            f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] |- g evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)] by E-Var1 {};
          };
          f = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],g = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))])[fun x -> (fun y -> x)],x = 7 |- x evalto 7 by E-Var1 {};
          s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],x = 7 |- (fun y -> x) evalto (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],x = 7)[fun y -> x] by E-Fun {};
        };
        s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],x = 7,y = (s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],x = 7)[fun y -> x] |- x evalto 7 by E-Var2 {
          s = ()[fun f -> (fun g -> (fun x -> f(x)(g(x))))],x = 7 |- x evalto 7 by E-Var1 {};
        };
      };
    };
  };
};
-}

ex-5-1-5 : ● ⊢ ℓetrec "fact" ≔fun "n" ⇒ if var "n" ≺ i (+ 2) then i (+ 1) else var "n" ⊛ app (var "fact") (var "n" ⊝ i (+ 1)) ιn
               app (var "fact") (i (+ 3)) ⇓ i (+ 6)
ex-5-1-5 = E-LetRec (E-AppRec E-Var1
                              E-Int 
                             (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl))
                                    (E-Times E-Var1 (E-AppRec (E-Var2 fact≢n E-Var1)
                                                              (E-Minus E-Var1 E-Int (B-Minus refl))
                                                              (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl))
                                                                     (E-Times E-Var1
                                                                              (E-AppRec (E-Var2 fact≢n E-Var1)
                                                                                        (E-Minus E-Var1 E-Int (B-Minus refl))
                                                                                        (E-IfT (E-Lt E-Var1 E-Int (B-Lt refl)) E-Int))
                                                                              (B-Times refl))))
                                                    (B-Times refl))))
  where
    fact≢n : "fact" ≡ "n" → ⊥
    fact≢n ()
{-
|- let rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1))) in fact(3) evalto 6 by E-LetRec {
  fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- fact(3) evalto 6 by E-AppRec {
    fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- fact evalto ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] by E-Var1 {};
    fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- 3 evalto 3 by E-Int {};
    fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- if (n < 2) then 1 else (n * fact((n - 1))) evalto 6 by E-IfF {
      fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- (n < 2) evalto false by E-Lt {
        fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- n evalto 3 by E-Var1 {};
        fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- 2 evalto 2 by E-Int {};
        3 less than 2 is false by B-Lt {};
      };
      fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- (n * fact((n - 1))) evalto 6 by E-Times {
        fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- n evalto 3 by E-Var1 {};
        fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- fact((n - 1)) evalto 2 by E-AppRec {
          fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- fact evalto ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] by E-Var2 {
            fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- fact evalto ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] by E-Var1 {};
          };
          fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- (n - 1) evalto 2 by E-Minus {
            fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- n evalto 3 by E-Var1 {};
            fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- 1 evalto 1 by E-Int {};
            3 minus 1 is 2 by B-Minus {};
          };
          fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- if (n < 2) then 1 else (n * fact((n - 1))) evalto 2 by E-IfF {
            fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- (n < 2) evalto false by E-Lt {
              fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- n evalto 2 by E-Var1 {};
              fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- 2 evalto 2 by E-Int {};
              2 less than 2 is false by B-Lt {};
            };
            fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- (n * fact((n - 1))) evalto 2 by E-Times {
              fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- n evalto 2 by E-Var1 {};
              fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- fact((n - 1)) evalto 1 by E-AppRec {
                fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- fact evalto ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] by E-Var2 {
                  fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- fact evalto ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] by E-Var1 {};
                };
                fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- (n - 1) evalto 1 by E-Minus {
                  fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- n evalto 2 by E-Var1 {};
                  fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- 1 evalto 1 by E-Int {};
                  2 minus 1 is 1 by B-Minus {};
                };
                fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- if (n < 2) then 1 else (n * fact((n - 1))) evalto 1 by E-IfT {
                  fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- (n < 2) evalto true by E-Lt {
                    fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- n evalto 1 by E-Var1 {};
                    fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- 2 evalto 2 by E-Int {};
                    1 less than 2 is true by B-Lt {};
                  };
                  fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- 1 evalto 1 by E-Int {};
                };
              };
              2 times 1 is 2 by B-Times {};
            };
          };
        };
        3 times 2 is 6 by B-Times {};
      };
    };
  };
};
-}


q51 : ● ⊢ ℓetrec "fib" ≔fun "n" ⇒ if var "n" ≺ i (+ 3) then i (+ 1) else app (var "fib") (var "n" ⊝ i (+ 1)) ⊕ app (var "fib") (var "n" ⊝ i (+ 2)) ιn
           app (var "fib") (i (+ 5)) ⇓ i (+ 5)
q51 = E-LetRec (E-AppRec E-Var1
                         E-Int
                         (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl))
                                (E-Plus (E-AppRec (E-Var2 fib≢n E-Var1)
                                                  (E-Minus E-Var1 E-Int (B-Minus refl))
                                                  (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl))
                                                         (E-Plus (E-AppRec (E-Var2 fib≢n E-Var1)
                                                                           (E-Minus E-Var1 E-Int (B-Minus refl))
                                                                           (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl))
                                                                                  (E-Plus (E-AppRec (E-Var2 fib≢n E-Var1)
                                                                                                    (E-Minus E-Var1 E-Int (B-Minus refl))
                                                                                                    (E-IfT (E-Lt E-Var1 E-Int (B-Lt refl)) E-Int))
                                                                                          (E-AppRec (E-Var2 fib≢n E-Var1)
                                                                                                    (E-Minus E-Var1 E-Int (B-Minus refl))
                                                                                                    (E-IfT (E-Lt E-Var1 E-Int (B-Lt refl))
                                                                                                           E-Int))
                                                                                          (B-Plus refl))))
                                                                 (E-AppRec (E-Var2 fib≢n E-Var1)
                                                                           (E-Minus E-Var1 E-Int (B-Minus refl))
                                                                           (E-IfT (E-Lt E-Var1 E-Int (B-Lt refl)) E-Int))
                                                                 (B-Plus refl))))
                                        (E-AppRec (E-Var2 fib≢n E-Var1)
                                                  (E-Minus E-Var1 E-Int (B-Minus refl))
                                                  (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl))
                                                         (E-Plus (E-AppRec (E-Var2 fib≢n E-Var1)
                                                                           (E-Minus E-Var1 E-Int (B-Minus refl))
                                                                           (E-IfT (E-Lt E-Var1 E-Int (B-Lt refl)) E-Int))
                                                                 (E-AppRec (E-Var2 fib≢n E-Var1)
                                                                           (E-Minus E-Var1 E-Int (B-Minus refl))
                                                                           (E-IfT (E-Lt E-Var1 E-Int (B-Lt refl)) E-Int))
                                                                 (B-Plus refl))))
                                        (B-Plus refl))))
  where
    fib≢n : "fib" ≡ "n" → ⊥
    fib≢n ()
{-
|- let rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2))) in fib(5) evalto 5 by E-LetRec {
  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] |- fib(5) evalto 5 by E-AppRec {
    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var1 {};
    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] |- 5 evalto 5 by E-Int {};
    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2))) evalto 5 by E-IfF {
      fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- (n < 3) evalto false by E-Lt {
        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- n evalto 5 by E-Var1 {};
        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- 3 evalto 3 by E-Int {};
        5 less than 3 is false by B-Lt {};
      };
      fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- (fib((n - 1)) + fib((n - 2))) evalto 5 by E-Plus {
        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- fib((n - 1)) evalto 3 by E-AppRec {
          fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var2 {
            fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var1 {};
          };
          fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- (n - 1) evalto 4 by E-Minus {
            fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- n evalto 5 by E-Var1 {};
            fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- 1 evalto 1 by E-Int {};
            5 minus 1 is 4 by B-Minus {};
          };
          fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2))) evalto 3 by E-IfF {
            fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- (n < 3) evalto false by E-Lt {
              fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- n evalto 4 by E-Var1 {};
              fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- 3 evalto 3 by E-Int {};
              4 less than 3 is false by B-Lt {};
            };
            fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- (fib((n - 1)) + fib((n - 2))) evalto 3 by E-Plus {
              fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- fib((n - 1)) evalto 2 by E-AppRec {
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var2 {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var1 {};
                };
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- (n - 1) evalto 3 by E-Minus {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- n evalto 4 by E-Var1 {};
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- 1 evalto 1 by E-Int {};
                  4 minus 1 is 3 by B-Minus {};
                };
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2))) evalto 2 by E-IfF {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- (n < 3) evalto false by E-Lt {
                    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- n evalto 3 by E-Var1 {};
                    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- 3 evalto 3 by E-Int {};
                    3 less than 3 is false by B-Lt {};
                  };
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- (fib((n - 1)) + fib((n - 2))) evalto 2 by E-Plus {
                    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- fib((n - 1)) evalto 1 by E-AppRec {
                      fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var2 {
                        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var1 {};
                      };
                      fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- (n - 1) evalto 2 by E-Minus {
                        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- n evalto 3 by E-Var1 {};
                        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- 1 evalto 1 by E-Int {};
                        3 minus 1 is 2 by B-Minus {};
                      };
                      fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2))) evalto 1 by E-IfT {
                        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- (n < 3) evalto true by E-Lt {
                          fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- n evalto 2 by E-Var1 {};
                          fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- 3 evalto 3 by E-Int {};
                          2 less than 3 is true by B-Lt {};
                        };
                        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- 1 evalto 1 by E-Int {};
                      };
                    };
                    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- fib((n - 2)) evalto 1 by E-AppRec {
                      fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var2 {
                        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var1 {};
                      };
                      fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- (n - 2) evalto 1 by E-Minus {
                        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- n evalto 3 by E-Var1 {};
                        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- 2 evalto 2 by E-Int {};
                        3 minus 2 is 1 by B-Minus {};
                      };
                      fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 1 |- if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2))) evalto 1 by E-IfT {
                        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 1 |- (n < 3) evalto true by E-Lt {
                          fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 1 |- n evalto 1 by E-Var1 {};
                          fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 1 |- 3 evalto 3 by E-Int {};
                          1 less than 3 is true by B-Lt {};
                        };
                        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 1 |- 1 evalto 1 by E-Int {};
                      };
                    };
                    1 plus 1 is 2 by B-Plus {};
                  };
                };
              };
              fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- fib((n - 2)) evalto 1 by E-AppRec {
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var2 {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var1 {};
                };
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- (n - 2) evalto 2 by E-Minus {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- n evalto 4 by E-Var1 {};
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 4 |- 2 evalto 2 by E-Int {};
                  4 minus 2 is 2 by B-Minus {};
                };
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2))) evalto 1 by E-IfT {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- (n < 3) evalto true by E-Lt {
                    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- n evalto 2 by E-Var1 {};
                    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- 3 evalto 3 by E-Int {};
                    2 less than 3 is true by B-Lt {};
                  };
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- 1 evalto 1 by E-Int {};
                };
              };
              2 plus 1 is 3 by B-Plus {};
            };
          };
        };
        fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- fib((n - 2)) evalto 2 by E-AppRec {
          fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var2 {
            fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var1 {};
          };
          fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- (n - 2) evalto 3 by E-Minus {
            fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- n evalto 5 by E-Var1 {};
            fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 5 |- 2 evalto 2 by E-Int {};
            5 minus 2 is 3 by B-Minus {};
          };
          fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2))) evalto 2 by E-IfF {
            fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- (n < 3) evalto false by E-Lt {
              fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- n evalto 3 by E-Var1 {};
              fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- 3 evalto 3 by E-Int {};
              3 less than 3 is false by B-Lt {};
            };
            fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- (fib((n - 1)) + fib((n - 2))) evalto 2 by E-Plus {
              fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- fib((n - 1)) evalto 1 by E-AppRec {
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var2 {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var1 {};
                };
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- (n - 1) evalto 2 by E-Minus {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- n evalto 3 by E-Var1 {};
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- 1 evalto 1 by E-Int {};
                  3 minus 1 is 2 by B-Minus {};
                };
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2))) evalto 1 by E-IfT {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- (n < 3) evalto true by E-Lt {
                    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- n evalto 2 by E-Var1 {};
                    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- 3 evalto 3 by E-Int {};
                    2 less than 3 is true by B-Lt {};
                  };
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 2 |- 1 evalto 1 by E-Int {};
                };
              };
              fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- fib((n - 2)) evalto 1 by E-AppRec {
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var2 {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] |- fib evalto ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))] by E-Var1 {};
                };
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- (n - 2) evalto 1 by E-Minus {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- n evalto 3 by E-Var1 {};
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 3 |- 2 evalto 2 by E-Int {};
                  3 minus 2 is 1 by B-Minus {};
                };
                fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 1 |- if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2))) evalto 1 by E-IfT {
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 1 |- (n < 3) evalto true by E-Lt {
                    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 1 |- n evalto 1 by E-Var1 {};
                    fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 1 |- 3 evalto 3 by E-Int {};
                    1 less than 3 is true by B-Lt {};
                  };
                  fib = ()[rec fib = fun n -> if (n < 3) then 1 else (fib((n - 1)) + fib((n - 2)))],n = 1 |- 1 evalto 1 by E-Int {};
                };
              };
              1 plus 1 is 2 by B-Plus {};
            };
          };
        };
        3 plus 2 is 5 by B-Plus {};
      };
    };
  };
};
-}

ex-5-1-6 : ● ⊢ ℓetrec "sum" ≔fun "f" ⇒ fun "n" ⇒ if var "n" ≺ i (+ 1) then i (+ 0) else app (var "f") (var "n") ⊕ app (app (var "sum") (var "f")) (var "n" ⊝ i (+ 1)) ιn
               app (app (var "sum") (fun "x" ⇒ var "x" ⊛ var "x")) (i (+ 2)) ⇓ i (+ 5)
ex-5-1-6 = E-LetRec (E-App (E-AppRec E-Var1 E-Fun E-Fun)
                           E-Int
                           (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl))
                                  (E-Plus (E-App (E-Var2 f≢n E-Var1)
                                                 E-Var1
                                                 (E-Times E-Var1 E-Var1 (B-Times refl)))
                                          (E-App (E-AppRec (E-Var2 sum≢n (E-Var2 sum≢f E-Var1))
                                                           (E-Var2 f≢n E-Var1) E-Fun)
                                                 (E-Minus E-Var1 E-Int (B-Minus refl))
                                                 (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl))
                                                        (E-Plus (E-App (E-Var2 f≢n E-Var1)
                                                                       E-Var1
                                                                       (E-Times E-Var1 E-Var1 (B-Times refl)))
                                                                (E-App (E-AppRec (E-Var2 sum≢n (E-Var2 sum≢f E-Var1))
                                                                                 (E-Var2 f≢n E-Var1)
                                                                                 E-Fun)
                                                                       (E-Minus E-Var1 E-Int (B-Minus refl))
                                                                       (E-IfT (E-Lt E-Var1 E-Int (B-Lt refl)) E-Int))
                                                                (B-Plus refl))))
                                          (B-Plus refl))))
  where
    f≢n : "f" ≡ "n" → ⊥
    f≢n ()
    sum≢n : "sum" ≡ "n" → ⊥
    sum≢n ()
    sum≢f : "sum" ≡ "f" → ⊥
    sum≢f ()

{-
|- let rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1)))) in sum((fun x -> (x * x)))(2) evalto 5 by E-LetRec {
  sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] |- sum((fun x -> (x * x)))(2) evalto 5 by E-App {
    sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] |- sum((fun x -> (x * x))) evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)])[fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1)))] by E-AppRec {
      sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] |- sum evalto ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] by E-Var1 {};
      sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] |- (fun x -> (x * x)) evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] by E-Fun {};
      sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] |- (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1)))) evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)])[fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1)))] by E-Fun {};
    };
    sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] |- 2 evalto 2 by E-Int {};
    sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- if (n < 1) then 0 else (f(n) + sum(f)((n - 1))) evalto 5 by E-IfF {
      sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- (n < 1) evalto false by E-Lt {
        sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- n evalto 2 by E-Var1 {};
        sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- 1 evalto 1 by E-Int {};
        2 less than 1 is false by B-Lt {};
      };
      sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- (f(n) + sum(f)((n - 1))) evalto 5 by E-Plus {
        sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- f(n) evalto 4 by E-App {
          sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- f evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] by E-Var2 {
            sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] |- f evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] by E-Var1 {};
          };
          sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- n evalto 2 by E-Var1 {};
          sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],x = 2 |- (x * x) evalto 4 by E-Times {
            sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],x = 2 |- x evalto 2 by E-Var1 {};
            sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],x = 2 |- x evalto 2 by E-Var1 {};
            2 times 2 is 4 by B-Times {};
          };
        };
        sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- sum(f)((n - 1)) evalto 1 by E-App {
          sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- sum(f) evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)])[fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1)))] by E-AppRec {
            sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- sum evalto ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] by E-Var2 {
              sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] |- sum evalto ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] by E-Var2 {
                sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] |- sum evalto ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] by E-Var1 {};
              };
            };
            sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- f evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] by E-Var2 {
              sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] |- f evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] by E-Var1 {};
            };
            sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] |- (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1)))) evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)])[fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1)))] by E-Fun {};
          };
          sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- (n - 1) evalto 1 by E-Minus {
            sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- n evalto 2 by E-Var1 {};
            sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 2 |- 1 evalto 1 by E-Int {};
            2 minus 1 is 1 by B-Minus {};
          };
          sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- if (n < 1) then 0 else (f(n) + sum(f)((n - 1))) evalto 1 by E-IfF {
            sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- (n < 1) evalto false by E-Lt {
              sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- n evalto 1 by E-Var1 {};
              sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- 1 evalto 1 by E-Int {};
              1 less than 1 is false by B-Lt {};
            };
            sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- (f(n) + sum(f)((n - 1))) evalto 1 by E-Plus {
              sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- f(n) evalto 1 by E-App {
                sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- f evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] by E-Var2 {
                  sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] |- f evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] by E-Var1 {};
                };
                sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- n evalto 1 by E-Var1 {};
                sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],x = 1 |- (x * x) evalto 1 by E-Times {
                  sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],x = 1 |- x evalto 1 by E-Var1 {};
                  sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],x = 1 |- x evalto 1 by E-Var1 {};
                  1 times 1 is 1 by B-Times {};
                };
              };
              sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- sum(f)((n - 1)) evalto 0 by E-App {
                sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- sum(f) evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)])[fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1)))] by E-AppRec {
                  sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- sum evalto ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] by E-Var2 {
                    sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] |- sum evalto ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] by E-Var2 {
                      sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] |- sum evalto ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))] by E-Var1 {};
                    };
                  };
                  sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- f evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] by E-Var2 {
                    sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] |- f evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] by E-Var1 {};
                  };
                  sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)] |- (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1)))) evalto (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)])[fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1)))] by E-Fun {};
                };
                sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- (n - 1) evalto 0 by E-Minus {
                  sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- n evalto 1 by E-Var1 {};
                  sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 1 |- 1 evalto 1 by E-Int {};
                  1 minus 1 is 0 by B-Minus {};
                };
                sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 0 |- if (n < 1) then 0 else (f(n) + sum(f)((n - 1))) evalto 0 by E-IfT {
                  sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 0 |- (n < 1) evalto true by E-Lt {
                    sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 0 |- n evalto 0 by E-Var1 {};
                    sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 0 |- 1 evalto 1 by E-Int {};
                    0 less than 1 is true by B-Lt {};
                  };
                  sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))],f = (sum = ()[rec sum = fun f -> (fun n -> if (n < 1) then 0 else (f(n) + sum(f)((n - 1))))])[fun x -> (x * x)],n = 0 |- 0 evalto 0 by E-Int {};
                };
              };
              1 plus 0 is 1 by B-Plus {};
            };
          };
        };
        4 plus 1 is 5 by B-Plus {};
      };
    };
  };
};
-}

q53 : ● ⊢ ℓet "fact" ≔ fun "self" ⇒ fun "n" ⇒ if var "n" ≺ i (+ 2) then i (+ 1) else var "n" ⊛ app (app (var "self") (var "self")) (var "n" ⊝ i (+ 1)) ιn
          app (app (var "fact") (var "fact")) (i (+ 3)) ⇓ i (+ 6)
q53 = E-Let E-Fun (E-App (E-App E-Var1 E-Var1 E-Fun) E-Int (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl)) (E-Times E-Var1 (E-App (E-App (E-Var2 self≢n E-Var1) (E-Var2 self≢n E-Var1) E-Fun) (E-Minus E-Var1 E-Int (B-Minus refl)) (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl)) (E-Times E-Var1 (E-App (E-App (E-Var2 self≢n E-Var1) (E-Var2 self≢n E-Var1) E-Fun) (E-Minus E-Var1 E-Int (B-Minus refl)) (E-IfT (E-Lt E-Var1 E-Int (B-Lt refl)) E-Int)) (B-Times refl)))) (B-Times refl))))
  where
    self≢n : "self" ≡ "n" → ⊥
    self≢n ()
{-
|- let fact = (fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))) in fact(fact)(3) evalto 6 by E-Let {
  |- (fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))) evalto ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] by E-Fun {};
  fact = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- fact(fact)(3) evalto 6 by E-App {
    fact = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- fact(fact) evalto (self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))])[fun n -> if (n < 2) then 1 else (n * self(self)((n - 1)))] by E-App {
      fact = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- fact evalto ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] by E-Var1 {};
      fact = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- fact evalto ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] by E-Var1 {};
      self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1)))) evalto (self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))])[fun n -> if (n < 2) then 1 else (n * self(self)((n - 1)))] by E-Fun {};
    };
    fact = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- 3 evalto 3 by E-Int {};
    self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- if (n < 2) then 1 else (n * self(self)((n - 1))) evalto 6 by E-IfF {
      self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- (n < 2) evalto false by E-Lt {
        self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- n evalto 3 by E-Var1 {};
        self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- 2 evalto 2 by E-Int {};
        3 less than 2 is false by B-Lt {};
      };
      self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- (n * self(self)((n - 1))) evalto 6 by E-Times {
        self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- n evalto 3 by E-Var1 {};
        self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- self(self)((n - 1)) evalto 2 by E-App {
          self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- self(self) evalto (self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))])[fun n -> if (n < 2) then 1 else (n * self(self)((n - 1)))] by E-App {
            self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- self evalto ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] by E-Var2 {
              self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- self evalto ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] by E-Var1 {};
            };
            self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- self evalto ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] by E-Var2 {
              self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- self evalto ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] by E-Var1 {};
            };
            self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1)))) evalto (self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))])[fun n -> if (n < 2) then 1 else (n * self(self)((n - 1)))] by E-Fun {};
          };
          self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- (n - 1) evalto 2 by E-Minus {
            self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- n evalto 3 by E-Var1 {};
            self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 3 |- 1 evalto 1 by E-Int {};
             3 minus 1 is 2 by B-Minus {};
          };
          self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- if (n < 2) then 1 else (n * self(self)((n - 1))) evalto 2 by E-IfF {
            self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- (n < 2) evalto false by E-Lt {
              self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- n evalto 2 by E-Var1 {};
              self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- 2 evalto 2 by E-Int {};
              2 less than 2 is false by B-Lt {};
            };
            self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- (n * self(self)((n - 1))) evalto 2 by E-Times {
              self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- n evalto 2 by E-Var1 {};
              self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- self(self)((n - 1)) evalto 1 by E-App {
                self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- self(self) evalto (self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))])[fun n -> if (n < 2) then 1 else (n * self(self)((n - 1)))] by E-App {
                  self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- self evalto ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] by E-Var2 {
                    self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- self evalto ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] by E-Var1 {};
                  };
                  self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- self evalto ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] by E-Var2 {
                    self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- self evalto ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] by E-Var1 {};
                  };
                  self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))] |- (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1)))) evalto (self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))])[fun n -> if (n < 2) then 1 else (n * self(self)((n - 1)))] by E-Fun {};
                };
                self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- (n - 1) evalto 1 by E-Minus {
                  self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- n evalto 2 by E-Var1 {};
                  self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 2 |- 1 evalto 1 by E-Int {};
                   2 minus 1 is 1 by B-Minus {};
                };
                self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 1 |- if (n < 2) then 1 else (n * self(self)((n - 1))) evalto 1 by E-IfT {
                  self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 1 |- (n < 2) evalto true by E-Lt {
                    self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 1 |- n evalto 1 by E-Var1 {};
                    self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 1 |- 2 evalto 2 by E-Int {};
                    1 less than 2 is true by B-Lt {};
                  };
                  self = ()[fun self -> (fun n -> if (n < 2) then 1 else (n * self(self)((n - 1))))],n = 1 |- 1 evalto 1 by E-Int {};
                };
              };
              2 times 1 is 2 by B-Times {};
            };
          };
        };
        3 times 2 is 6 by B-Times {};
      };
    };
  };
};
-}

open import BCoPL.Induction3
open import Data.Empty using (⊥-elim)

theorem-5-2 : ∀ {ε e v} → ε ⊢ e ⇓ v → (∀ {v'} → ε ⊢ e ⇓ v' → v ≡ v')
theorem-5-2 prf = induction-EvalML3 help-a help-b help-c help-d help-e help-f help-g help-h {!help-i!} {!help-j!} {!help-k!} help-l {!help-m!} help-n {!help-o!} prf
  where
    help-a : ∀ ε n → ∀ v' → ε ⊢ i n ⇓ v' → i n ≡ v'
    help-a ε n .(i n) E-Int = refl
    help-b : ∀ ε v → ∀ v' → ε ⊢ b v ⇓ v' → b v ≡ v'
    help-b ε v .(b v) E-Bool = refl
    help-c : ∀ ε x v → ∀ v' → ε ⊱ (x , v) ⊢ var x ⇓ v' → v ≡ v'
    help-c ε x v .v E-Var1 = refl
    help-c ε x v v'' (E-Var2 p prf₁) = ⊥-elim (p refl)
    help-d : ∀ ε x y v₁ v₂ → (p : x ≢ y) →
             (∀ v' → ε ⊢ var x ⇓ v' → v₂ ≡ v') →
             (∀ v' → ε ⊱ (y , v₁) ⊢ var x ⇓ v' → v₂ ≡ v')
    help-d ε x .x v₁ v₂ p prf₁ .v₁ E-Var1 = ⊥-elim (p refl)
    help-d ε x y v₁ v₂ p prf₁ v'' (E-Var2 p₁ prf₂) = prf₁ _ prf₂
    help-e : ∀ ε e₁ e₂ i₁ i₂ i₃ →
             (∀ v' → ε ⊢ e₁ ⇓ v' → i i₁ ≡ v') × (∀ v' → ε ⊢ e₂ ⇓ v' → i i₂ ≡ v') × (i i₁ plus i i₂ is i i₃) →
             (∀ v' → ε ⊢ (e₁ ⊕ e₂) ⇓ v' → i i₃ ≡ v')
    help-e = {!!}
    help-f : ∀ ε e₁ e₂ i₁ i₂ i₃ →
             (∀ v' → ε ⊢ e₁ ⇓ v' → i i₁ ≡ v') × (∀ v' → ε ⊢ e₂ ⇓ v' → i i₂ ≡ v') × (i i₁ minus i i₂ is i i₃) →
             (∀ v' → ε ⊢ (e₁ ⊝ e₂) ⇓ v' → i i₃ ≡ v')
    help-f = {!!}
    help-g : ∀ ε e₁ e₂ i₁ i₂ i₃ →
             (∀ v' → ε ⊢ e₁ ⇓ v' → i i₁ ≡ v') × (∀ v' → ε ⊢ e₂ ⇓ v' → i i₂ ≡ v') × (i i₁ times i i₂ is i i₃) →
             (∀ v' → ε ⊢ (e₁ ⊛ e₂) ⇓ v' → i i₃ ≡ v')
    help-g = {!!}
    help-h : ∀ ε e₁ e₂ i₁ i₂ v₁ →
             (∀ v' → ε ⊢ e₁ ⇓ v' → i i₁ ≡ v') × (∀ v' → ε ⊢ e₂ ⇓ v' → i i₂ ≡ v') × (i i₁ less-than i i₂ is b v₁) →
             (∀ v' → ε ⊢ (e₁ ≺ e₂) ⇓ v' → b v₁ ≡ v')
    help-h = {!!}
    help-i : ∀ ε e₁ e₂ e₃ v₁ →
             (∀ v' → ε ⊢ e₁ ⇓ v' → b true ≡ v') × (∀ v' → ε ⊢ e₂ ⇓ v' → v₁ ≡ v') →
             (∀ v' → ε ⊢ if e₁ then e₂ else e₃ ⇓ v' → v₁ ≡ v')
    help-i = {!!}
    help-j : ∀ ε e₁ e₂ e₃ v₁ →
             (∀ v' → ε ⊢ e₁ ⇓ v' → b false ≡ v') × (∀ v' → ε ⊢ e₃ ⇓ v' → v₁ ≡ v') →
             (∀ v' → ε ⊢ if e₁ then e₂ else e₃ ⇓ v' → v₁ ≡ v')
    help-j = {!!}
    help-k : ∀ ε e₁ e₂ x v₁ v₂ →
             (∀ v' → ε ⊢ e₁ ⇓ v' → v₂ ≡ v') × (∀ v' → ε ⊱ (x , v₂) ⊢ e₂ ⇓ v' → v₁ ≡ v') →
             (∀ v' → ε ⊢ ℓet x ≔ e₁ ιn e₂ ⇓ v' → v₁ ≡ v')
    help-k = {!!}
    help-l : ∀ ε x e₁ → (∀ v' → ε ⊢ fun x ⇒ e₁ ⇓ v' → ⟨ ε ⟩[fun x ⇒ e₁ ] ≡ v')
    help-l = {!!}
    help-m : ∀ ε₁ ε₂ e₀ e₁ e₂ x v₁ v₂ →
             (∀ v' → ε₁ ⊢ e₁ ⇓ v' → ⟨ ε₂ ⟩[fun x ⇒ e₀ ] ≡ v') × (∀ v' → ε₁ ⊢ e₂ ⇓ v' → v₂ ≡ v') × (∀ v' → ε₂ ⊱ (x , v₂) ⊢ e₀ ⇓ v' → v₁ ≡ v') →
             (∀ v' → ε₁ ⊢ app e₁ e₂ ⇓ v' → v₁ ≡ v')
    help-m = {!!}
    help-n : ∀ ε₁ e₁ e₂ x y v₁ →
             (∀ v' → ε₁ ⊱ (x , ⟨ ε₁ ⟩[rec x ≔fun y ⇒ e₁ ]) ⊢ e₂ ⇓ v' → v₁ ≡ v') →
             (∀ v' → ε₁ ⊢ ℓetrec x ≔fun y ⇒ e₁ ιn e₂ ⇓ v' → v₁ ≡ v')
    help-n = {!!}
    help-o : ∀ ε₁ ε₂ e₀ e₁ e₂ x y v₁ v₂ →
             (∀ v' → ε₁ ⊢ e₁ ⇓ v' → ⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ] ≡ v') × (∀ v' → ε₁ ⊢ e₂ ⇓ v' → v₂ ≡ v') × (∀ v' → ε₂ ⊱ (x , ⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ]) ⊱ (y , v₂) ⊢ e₀ ⇓ v' → v₁ ≡ v') →
             (∀ v' → ε₁ ⊢ app e₁ e₂ ⇓ v' → v₁ ≡ v')
    help-o = {!!}

