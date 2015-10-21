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
