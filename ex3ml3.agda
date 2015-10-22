module ex3ml3 where

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
|- let twice = (fun f -> (fun x -> f(f(x)))) in twice(twice)((fun x -> (x * x)))(1) evalto 1 by E-Let {
  |- (fun f -> (fun x -> f(f(x)))) evalto ()[fun f -> (fun x -> f(f(x)))] by E-Fun {};
  twice = ()[fun f -> (fun x -> f(f(x)))] |- twice(twice)((fun x -> (x * x)))(1) evalto 1 by E-App {
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
    twice = ()[fun f -> (fun x -> f(f(x)))] |- 1 evalto 1 by E-Int {};
    f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))],x = 1 |- f(f(x)) evalto 1 by E-App {
      f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))],x = 1 |- f evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-Var2 {
        f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] |- f evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-Var1 {};
      };
      f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))],x = 1 |- f(x) evalto 1 by E-App {
        f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))],x = 1 |- f evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-Var2 {
          f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] |- f evalto (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))] by E-Var1 {};
        };
        f = (f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)])[fun x -> f(f(x))],x = 1 |- x evalto 1 by E-Var1 {};
        f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 1 |- f(f(x)) evalto 1 by E-App {
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 1 |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var2 {
            f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var1 {};
          };
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 1 |- f(x) evalto 1 by E-App {
            f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 1 |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var2 {
              f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var1 {};
            };
            f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 1 |- x evalto 1 by E-Var1 {};
            twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- (x * x) evalto 1 by E-Times {
              twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- x evalto 1 by E-Var1 {};
              twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- x evalto 1 by E-Var1 {};
              1 times 1 is 1 by B-Times {};
            };
          };
          twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- (x * x) evalto 1 by E-Times {
            twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- x evalto 1 by E-Var1 {};
            twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- x evalto 1 by E-Var1 {};
            1 times 1 is 1 by B-Times {};
          };
        };
      };
      f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 1 |- f(f(x)) evalto 1 by E-App {
        f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 1 |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var2 {
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var1 {};
        };
        f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 1 |- f(x) evalto 1 by E-App {
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 1 |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var2 {
            f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] |- f evalto (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)] by E-Var1 {};
          };
          f = (twice = ()[fun f -> (fun x -> f(f(x)))])[fun x -> (x * x)],x = 1 |- x evalto 1 by E-Var1 {};
          twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- (x * x) evalto 1 by E-Times {
            twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- x evalto 1 by E-Var1 {};
            twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- x evalto 1 by E-Var1 {};
            1 times 1 is 1 by B-Times {};
          };
        };
        twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- (x * x) evalto 1 by E-Times {
          twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- x evalto 1 by E-Var1 {};
          twice = ()[fun f -> (fun x -> f(f(x)))],x = 1 |- x evalto 1 by E-Var1 {};
          1 times 1 is 1 by B-Times {};
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

