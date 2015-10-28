module ex7 where

open import Data.Empty

record ex7-1 : Set where
  open import BCoPL.EvalML4
  open import BCoPL.Show.EvalML4

  ex-7-1-1 : ● ⊢ i (+ 1) ⊕ i (+ 2) ∷ i (+ 3) ⊕ i (+ 4) ∷ [] ⇓ (i (+ 3)) ∷ (i (+ 7)) ∷ []
  ex-7-1-1 = E-Cons (E-Plus E-Int E-Int (B-Plus refl))
                  (E-Cons (E-Plus E-Int E-Int (B-Plus refl)) E-Nil)
{-
|- (1 + 2) :: (3 + 4) :: [] evalto 3 :: 7 :: [] by E-Cons {
  |- (1 + 2) evalto 3 by E-Plus {
    |- 1 evalto 1 by E-Int {};
    |- 2 evalto 2 by E-Int {};
    1 plus 2 is 3 by B-Plus {};
  };
  |- (3 + 4) :: [] evalto 7 :: [] by E-Cons {
    |- (3 + 4) evalto 7 by E-Plus {
      |- 3 evalto 3 by E-Int {};
      |- 4 evalto 4 by E-Int {};
      3 plus 4 is 7 by B-Plus {};
    };
    |- [] evalto [] by E-Nil {};
  };
};
-}

  ex-7-1-2 : ● ⊢ ℓet "f" ≔ fun "x" ⇒
                     match var "x" with[]⇒ i (+ 0)
                                           ∣ "a" ∷ "b" ⇒ var "a" ιn
                 app (var "f") (i (+ 4) ∷ []) ⊕
                 app (var "f") [] ⊕
                 app (var "f") (i (+ 1) ∷ i (+ 2) ∷  i (+ 3) ∷ []) ⇓ i (+ 5)
  ex-7-1-2 = E-Let E-Fun
                   (E-Plus (E-Plus (E-App (E-Var refl)
                                          (E-Cons E-Int E-Nil)
                                          (E-MatchCons (E-Var refl) (E-Var refl)))
                                   (E-App (E-Var refl)
                                          E-Nil
                                          (E-MatchNil (E-Var refl) E-Int))
                                   (B-Plus refl))
                           (E-App (E-Var refl)
                                  (E-Cons E-Int
                                          (E-Cons E-Int (E-Cons E-Int E-Nil)))
                                  (E-MatchCons (E-Var refl) (E-Var refl)))
                           (B-Plus refl))
{-
|- let f = (fun x -> match x with [] -> 0 | a :: b -> a) in ((f(4 :: []) + f([])) + f(1 :: 2 :: 3 :: [])) evalto 5 by E-Let {
  |- (fun x -> match x with [] -> 0 | a :: b -> a) evalto ()[fun x -> match x with [] -> 0 | a :: b -> a] by E-Fun {};
  f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- ((f(4 :: []) + f([])) + f(1 :: 2 :: 3 :: [])) evalto 5 by E-Plus {
    f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- (f(4 :: []) + f([])) evalto 4 by E-Plus {
      f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- f(4 :: []) evalto 4 by E-App {
        f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- f evalto ()[fun x -> match x with [] -> 0 | a :: b -> a] by E-Var {};
        f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- 4 :: [] evalto 4 :: [] by E-Cons {
          f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- 4 evalto 4 by E-Int {};
          f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- [] evalto [] by E-Nil {};
        };
        x = 4 :: [] |- match x with [] -> 0 | a :: b -> a evalto 4 by E-MatchCons {
          x = 4 :: [] |- x evalto 4 :: [] by E-Var {};
          x = 4 :: [],a = 4,b = [] |- a evalto 4 by E-Var {};
        };
      };
      f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- f([]) evalto 0 by E-App {
        f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- f evalto ()[fun x -> match x with [] -> 0 | a :: b -> a] by E-Var {};
        f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- [] evalto [] by E-Nil {};
        x = [] |- match x with [] -> 0 | a :: b -> a evalto 0 by E-MatchNil {
          x = [] |- x evalto [] by E-Var {};
          x = [] |- 0 evalto 0 by E-Int {};
        };
      };
      4 plus 0 is 4 by B-Plus {};
    };
    f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- f(1 :: 2 :: 3 :: []) evalto 1 by E-App {
      f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- f evalto ()[fun x -> match x with [] -> 0 | a :: b -> a] by E-Var {};
      f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- 1 :: 2 :: 3 :: [] evalto 1 :: 2 :: 3 :: [] by E-Cons {
        f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- 1 evalto 1 by E-Int {};
        f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- 2 :: 3 :: [] evalto 2 :: 3 :: [] by E-Cons {
          f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- 2 evalto 2 by E-Int {};
          f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- 3 :: [] evalto 3 :: [] by E-Cons {
            f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- 3 evalto 3 by E-Int {};
            f = ()[fun x -> match x with [] -> 0 | a :: b -> a] |- [] evalto [] by E-Nil {};
          };
        };
      };
      x = 1 :: 2 :: 3 :: [] |- match x with [] -> 0 | a :: b -> a evalto 1 by E-MatchCons {
        x = 1 :: 2 :: 3 :: [] |- x evalto 1 :: 2 :: 3 :: [] by E-Var {};
        x = 1 :: 2 :: 3 :: [],a = 1,b = 2 :: 3 :: [] |- a evalto 1 by E-Var {};
      };
    };
    4 plus 1 is 5 by B-Plus {};
  };
};
-}

  ex-7-1-3 : ● ⊢ ℓetrec "f" ≔fun "x" ⇒
                        if var "x" ≺ i (+ 1) then [] else var "x" ∷ app (var "f") (var "x" ⊝ i (+ 1)) ιn
                 app (var "f") (i (+ 3)) ⇓ i (+ 3) ∷ i (+ 2) ∷ i (+ 1) ∷ []
  ex-7-1-3 = E-LetRec (E-AppRec (E-Var refl)
                                E-Int
                                (E-IfF (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                       (E-Cons (E-Var refl)
                                               (E-AppRec (E-Var refl)
                                                         (E-Minus (E-Var refl) E-Int (B-Minus refl))
                                                         (E-IfF (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                                                (E-Cons (E-Var refl)
                                                                        (E-AppRec (E-Var refl)
                                                                                  (E-Minus (E-Var refl) E-Int (B-Minus refl))
                                                                                  (E-IfF (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                                                                         (E-Cons (E-Var refl)
                                                                                                 (E-AppRec (E-Var refl)
                                                                                                           (E-Minus (E-Var refl) E-Int (B-Minus refl))
                                                                                                           (E-IfT (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                                                                                                  E-Nil)))))))))))
{-
|- let rec f = fun x -> if (x < 1) then [] else x :: f((x - 1)) in f(3) evalto 3 :: 2 :: 1 :: [] by E-LetRec {
  f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))] |- f(3) evalto 3 :: 2 :: 1 :: [] by E-AppRec {
    f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))] |- f evalto ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))] by E-Var {};
    f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))] |- 3 evalto 3 by E-Int {};
    f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 3 |- if (x < 1) then [] else x :: f((x - 1)) evalto 3 :: 2 :: 1 :: [] by E-IfF {
      f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 3 |- (x < 1) evalto false by E-Lt {
        f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 3 |- x evalto 3 by E-Var {};
        f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 3 |- 1 evalto 1 by E-Int {};
        3 less than 1 is false by B-Lt {};
      };
      f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 3 |- x :: f((x - 1)) evalto 3 :: 2 :: 1 :: [] by E-Cons {
        f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 3 |- x evalto 3 by E-Var {};
        f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 3 |- f((x - 1)) evalto 2 :: 1 :: [] by E-AppRec {
          f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 3 |- f evalto ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))] by E-Var {};
          f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 3 |- (x - 1) evalto 2 by E-Minus {
            f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 3 |- x evalto 3 by E-Var {};
            f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 3 |- 1 evalto 1 by E-Int {};
            3 minus 1 is 2 by B-Minus {};
          };
          f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 2 |- if (x < 1) then [] else x :: f((x - 1)) evalto 2 :: 1 :: [] by E-IfF {
            f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 2 |- (x < 1) evalto false by E-Lt {
              f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 2 |- x evalto 2 by E-Var {};
              f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 2 |- 1 evalto 1 by E-Int {};
              2 less than 1 is false by B-Lt {};
            };
            f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 2 |- x :: f((x - 1)) evalto 2 :: 1 :: [] by E-Cons {
              f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 2 |- x evalto 2 by E-Var {};
              f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 2 |- f((x - 1)) evalto 1 :: [] by E-AppRec {
                f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 2 |- f evalto ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))] by E-Var {};
                f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 2 |- (x - 1) evalto 1 by E-Minus {
                  f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 2 |- x evalto 2 by E-Var {};
                  f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 2 |- 1 evalto 1 by E-Int {};
                  2 minus 1 is 1 by B-Minus {};
                };
                f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 1 |- if (x < 1) then [] else x :: f((x - 1)) evalto 1 :: [] by E-IfF {
                  f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 1 |- (x < 1) evalto false by E-Lt {
                    f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 1 |- x evalto 1 by E-Var {};
                    f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 1 |- 1 evalto 1 by E-Int {};
                    1 less than 1 is false by B-Lt {};
                  };
                  f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 1 |- x :: f((x - 1)) evalto 1 :: [] by E-Cons {
                    f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 1 |- x evalto 1 by E-Var {};
                    f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 1 |- f((x - 1)) evalto [] by E-AppRec {
                      f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 1 |- f evalto ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))] by E-Var {};
                      f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 1 |- (x - 1) evalto 0 by E-Minus {
                        f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 1 |- x evalto 1 by E-Var {};
                        f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 1 |- 1 evalto 1 by E-Int {};
                        1 minus 1 is 0 by B-Minus {};
                      };
                      f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 0 |- if (x < 1) then [] else x :: f((x - 1)) evalto [] by E-IfT {
                        f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 0 |- (x < 1) evalto true by E-Lt {
                          f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 0 |- x evalto 0 by E-Var {};
                          f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 0 |- 1 evalto 1 by E-Int {};
                          0 less than 1 is true by B-Lt {};
                        };
                        f = ()[rec f = fun x -> if (x < 1) then [] else x :: f((x - 1))],x = 0 |- [] evalto [] by E-Nil {};
                      };
                    };
                  };
                };
              };
            };
          };
        };
      };
    };
  };
};
-}

  ex-7-1-4 : ● ⊢ ℓetrec "length" ≔fun "l" ⇒
                        match var "l" with[]⇒ i (+ 0)
                                              ∣ "x" ∷ "y" ⇒ i (+ 1) ⊕ app (var "length") (var "y") ιn
                 app (var "length") (i (+ 1) ∷ i (+ 2) ∷ i (+ 3) ∷ []) ⇓ i (+ 3)
  ex-7-1-4 = E-LetRec (E-AppRec (E-Var refl)
                                (E-Cons E-Int (E-Cons E-Int (E-Cons E-Int E-Nil)))
                                (E-MatchCons (E-Var refl)
                                             (E-Plus E-Int
                                                     (E-AppRec (E-Var refl)
                                                               (E-Var refl)
                                                               (E-MatchCons (E-Var refl)
                                                                            (E-Plus E-Int
                                                                                    (E-AppRec (E-Var refl)
                                                                                              (E-Var refl)
                                                                                              (E-MatchCons (E-Var refl)
                                                                                                           (E-Plus E-Int
                                                                                                                   (E-AppRec (E-Var refl)
                                                                                                                             (E-Var refl)
                                                                                                                             (E-MatchNil (E-Var refl) E-Int))
                                                                                                                   (B-Plus refl)))) (B-Plus refl))))
                                                     (B-Plus refl))))
{-
|- let rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y)) in length(1 :: 2 :: 3 :: []) evalto 3 by E-LetRec {
  length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- length(1 :: 2 :: 3 :: []) evalto 3 by E-AppRec {
    length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- length evalto ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] by E-Var {};
    length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- 1 :: 2 :: 3 :: [] evalto 1 :: 2 :: 3 :: [] by E-Cons {
      length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- 1 evalto 1 by E-Int {};
      length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- 2 :: 3 :: [] evalto 2 :: 3 :: [] by E-Cons {
        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- 2 evalto 2 by E-Int {};
        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- 3 :: [] evalto 3 :: [] by E-Cons {
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- 3 evalto 3 by E-Int {};
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- [] evalto [] by E-Nil {};
        };
      };
    };
    length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 1 :: 2 :: 3 :: [] |- match l with [] -> 0 | x :: y -> (1 + length(y)) evalto 3 by E-MatchCons {
      length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 1 :: 2 :: 3 :: [] |- l evalto 1 :: 2 :: 3 :: [] by E-Var {};
      length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 1 :: 2 :: 3 :: [],x = 1,y = 2 :: 3 :: [] |- (1 + length(y)) evalto 3 by E-Plus {
        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 1 :: 2 :: 3 :: [],x = 1,y = 2 :: 3 :: [] |- 1 evalto 1 by E-Int {};
        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 1 :: 2 :: 3 :: [],x = 1,y = 2 :: 3 :: [] |- length(y) evalto 2 by E-AppRec {
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 1 :: 2 :: 3 :: [],x = 1,y = 2 :: 3 :: [] |- length evalto ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] by E-Var {};
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 1 :: 2 :: 3 :: [],x = 1,y = 2 :: 3 :: [] |- y evalto 2 :: 3 :: [] by E-Var {};
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 2 :: 3 :: [] |- match l with [] -> 0 | x :: y -> (1 + length(y)) evalto 2 by E-MatchCons {
            length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 2 :: 3 :: [] |- l evalto 2 :: 3 :: [] by E-Var {};
            length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 2 :: 3 :: [],x = 2,y = 3 :: [] |- (1 + length(y)) evalto 2 by E-Plus {
              length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 2 :: 3 :: [],x = 2,y = 3 :: [] |- 1 evalto 1 by E-Int {};
              length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 2 :: 3 :: [],x = 2,y = 3 :: [] |- length(y) evalto 1 by E-AppRec {
                length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 2 :: 3 :: [],x = 2,y = 3 :: [] |- length evalto ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] by E-Var {};
                length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 2 :: 3 :: [],x = 2,y = 3 :: [] |- y evalto 3 :: [] by E-Var {};
                length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 3 :: [] |- match l with [] -> 0 | x :: y -> (1 + length(y)) evalto 1 by E-MatchCons {
                  length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 3 :: [] |- l evalto 3 :: [] by E-Var {};
                  length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 3 :: [],x = 3,y = [] |- (1 + length(y)) evalto 1 by E-Plus {
                    length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 3 :: [],x = 3,y = [] |- 1 evalto 1 by E-Int {};
                    length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 3 :: [],x = 3,y = [] |- length(y) evalto 0 by E-AppRec {
                      length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 3 :: [],x = 3,y = [] |- length evalto ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] by E-Var {};
                      length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = 3 :: [],x = 3,y = [] |- y evalto [] by E-Var {};
                      length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = [] |- match l with [] -> 0 | x :: y -> (1 + length(y)) evalto 0 by E-MatchNil {
                        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = [] |- l evalto [] by E-Var {};
                        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = [] |- 0 evalto 0 by E-Int {};
                      };
                    };
                    1 plus 0 is 1 by B-Plus {};
                  };
                };
              };
              1 plus 1 is 2 by B-Plus {};
            };
          };
        };
        1 plus 2 is 3 by B-Plus {};
      };
    };
  };
};
-}

  q74 : ● ⊢ ℓetrec "length" ≔fun "l" ⇒
                   match var "l" with[]⇒ i (+ 0)
                                         ∣ "x" ∷ "y" ⇒ i (+ 1) ⊕ app (var "length") (var "y") ιn
            app (var "length") ((i (+ 1) ∷ i (+ 2) ∷ []) ∷ (i (+ 3) ∷ i (+ 4) ∷ i (+ 5) ∷ []) ∷ []) ⇓ i (+ 2)
  q74 = E-LetRec (E-AppRec (E-Var refl)
                           (E-Cons (E-Cons E-Int (E-Cons E-Int E-Nil)) (E-Cons (E-Cons E-Int (E-Cons E-Int (E-Cons E-Int E-Nil))) E-Nil))
                           (E-MatchCons (E-Var refl)
                                        (E-Plus E-Int
                                                (E-AppRec (E-Var refl)
                                                          (E-Var refl)
                                                          (E-MatchCons (E-Var refl)
                                                                       (E-Plus E-Int
                                                                               (E-AppRec (E-Var refl)
                                                                                         (E-Var refl)
                                                                                         (E-MatchNil (E-Var refl) E-Int))
                                                                               (B-Plus refl))))
                                                (B-Plus refl))))
{-
|- let rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y)) in length(((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: []))) evalto 2 by E-LetRec {
  length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- length(((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: []))) evalto 2 by E-AppRec {
    length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- length evalto ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] by E-Var {};
    length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- ((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: [])) evalto ((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: [])) by E-Cons {
      length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- (1 :: (2 :: [])) evalto (1 :: (2 :: [])) by E-Cons {
        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- 1 evalto 1 by E-Int {};
        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- (2 :: []) evalto (2 :: []) by E-Cons {
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- 2 evalto 2 by E-Int {};
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- [] evalto [] by E-Nil {};
        };
      };
      length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- ((3 :: (4 :: (5 :: []))) :: []) evalto ((3 :: (4 :: (5 :: []))) :: []) by E-Cons {
        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- (3 :: (4 :: (5 :: []))) evalto (3 :: (4 :: (5 :: []))) by E-Cons {
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- 3 evalto 3 by E-Int {};
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- (4 :: (5 :: [])) evalto (4 :: (5 :: [])) by E-Cons {
            length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- 4 evalto 4 by E-Int {};
            length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- (5 :: []) evalto (5 :: []) by E-Cons {
              length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- 5 evalto 5 by E-Int {};
              length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- [] evalto [] by E-Nil {};
            };
          };
        };
        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] |- [] evalto [] by E-Nil {};
      };
    };
    length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: [])) |- match l with [] -> 0 | x :: y -> (1 + length(y)) evalto 2 by E-MatchCons {
      length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: [])) |- l evalto ((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: [])) by E-Var {};
      length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: [])),x = (1 :: (2 :: [])),y = ((3 :: (4 :: (5 :: []))) :: []) |- (1 + length(y)) evalto 2 by E-Plus {
        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: [])),x = (1 :: (2 :: [])),y = ((3 :: (4 :: (5 :: []))) :: []) |- 1 evalto 1 by E-Int {};
        length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: [])),x = (1 :: (2 :: [])),y = ((3 :: (4 :: (5 :: []))) :: []) |- length(y) evalto 1 by E-AppRec {
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: [])),x = (1 :: (2 :: [])),y = ((3 :: (4 :: (5 :: []))) :: []) |- length evalto ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] by E-Var {};
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((1 :: (2 :: [])) :: ((3 :: (4 :: (5 :: []))) :: [])),x = (1 :: (2 :: [])),y = ((3 :: (4 :: (5 :: []))) :: []) |- y evalto ((3 :: (4 :: (5 :: []))) :: []) by E-Var {};
          length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((3 :: (4 :: (5 :: []))) :: []) |- match l with [] -> 0 | x :: y -> (1 + length(y)) evalto 1 by E-MatchCons {
            length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((3 :: (4 :: (5 :: []))) :: []) |- l evalto ((3 :: (4 :: (5 :: []))) :: []) by E-Var {};
            length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((3 :: (4 :: (5 :: []))) :: []),x = (3 :: (4 :: (5 :: []))),y = [] |- (1 + length(y)) evalto 1 by E-Plus {
              length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((3 :: (4 :: (5 :: []))) :: []),x = (3 :: (4 :: (5 :: []))),y = [] |- 1 evalto 1 by E-Int {};
              length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((3 :: (4 :: (5 :: []))) :: []),x = (3 :: (4 :: (5 :: []))),y = [] |- length(y) evalto 0 by E-AppRec {
                length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((3 :: (4 :: (5 :: []))) :: []),x = (3 :: (4 :: (5 :: []))),y = [] |- length evalto ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))] by E-Var {};
                length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = ((3 :: (4 :: (5 :: []))) :: []),x = (3 :: (4 :: (5 :: []))),y = [] |- y evalto [] by E-Var {};
                length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = [] |- match l with [] -> 0 | x :: y -> (1 + length(y)) evalto 0 by E-MatchNil {
                  length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = [] |- l evalto [] by E-Var {};
                  length = ()[rec length = fun l -> match l with [] -> 0 | x :: y -> (1 + length(y))],l = [] |- 0 evalto 0 by E-Int {};
                };
              };
              1 plus 0 is 1 by B-Plus {};
            };
          };
        };
        1 plus 1 is 2 by B-Plus {};
      };
    };
  };
};
-}

  ex-7-1-5 : ● ⊢ ℓetrec "append" ≔fun "l1" ⇒ fun "l2" ⇒
                        match var "l1" with[]⇒ var "l2"
                                         ∣ "x" ∷ "y" ⇒ var "x" ∷ app (app (var "append") (var "y")) (var "l2") ιn
                 app (app (var "append") (i (+ 1) ∷ i (+ 2) ∷ [])) (i (+ 3) ∷ i (+ 4) ∷ i (+ 5) ∷ []) ⇓ i (+ 1) ∷ i (+ 2) ∷ i (+ 3) ∷ i (+ 4) ∷ i (+ 5) ∷ []
  ex-7-1-5 = E-LetRec (E-App (E-AppRec (E-Var refl) (E-Cons E-Int (E-Cons E-Int E-Nil)) E-Fun)
                             (E-Cons E-Int (E-Cons E-Int (E-Cons E-Int E-Nil)))
                             (E-MatchCons (E-Var refl)
                                          (E-Cons (E-Var refl)
                                                  (E-App (E-AppRec (E-Var refl) (E-Var refl) E-Fun)
                                                         (E-Var refl)
                                                         (E-MatchCons (E-Var refl)
                                                                      (E-Cons (E-Var refl)
                                                                              (E-App (E-AppRec (E-Var refl) (E-Var refl) E-Fun)
                                                                                     (E-Var refl)
                                                                                     (E-MatchNil (E-Var refl) (E-Var refl)))))))))
{-
|- let rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2))) in append((1 :: (2 :: [])))((3 :: (4 :: (5 :: [])))) evalto (1 :: (2 :: (3 :: (4 :: (5 :: []))))) by E-LetRec {
  append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- append((1 :: (2 :: [])))((3 :: (4 :: (5 :: [])))) evalto (1 :: (2 :: (3 :: (4 :: (5 :: []))))) by E-App {
    append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- append((1 :: (2 :: []))) evalto (append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])))[fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2))] by E-AppRec {
      append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- append evalto ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] by E-Var {};
      append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- (1 :: (2 :: [])) evalto (1 :: (2 :: [])) by E-Cons {
        append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- 1 evalto 1 by E-Int {};
        append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- (2 :: []) evalto (2 :: []) by E-Cons {
          append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- 2 evalto 2 by E-Int {};
          append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- [] evalto [] by E-Nil {};
        };
      };
      append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])) |- (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2))) evalto (append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])))[fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2))] by E-Fun {};
    };
    append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- (3 :: (4 :: (5 :: []))) evalto (3 :: (4 :: (5 :: []))) by E-Cons {
      append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- 3 evalto 3 by E-Int {};
      append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- (4 :: (5 :: [])) evalto (4 :: (5 :: [])) by E-Cons {
        append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- 4 evalto 4 by E-Int {};
        append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- (5 :: []) evalto (5 :: []) by E-Cons {
          append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- 5 evalto 5 by E-Int {};
          append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] |- [] evalto [] by E-Nil {};
        };
      };
    };
    append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])),l2 = (3 :: (4 :: (5 :: []))) |- match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)) evalto (1 :: (2 :: (3 :: (4 :: (5 :: []))))) by E-MatchCons {
      append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])),l2 = (3 :: (4 :: (5 :: []))) |- l1 evalto (1 :: (2 :: [])) by E-Var {};
      append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])),l2 = (3 :: (4 :: (5 :: []))),x = 1,y = (2 :: []) |- (x :: append(y)(l2)) evalto (1 :: (2 :: (3 :: (4 :: (5 :: []))))) by E-Cons {
        append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])),l2 = (3 :: (4 :: (5 :: []))),x = 1,y = (2 :: []) |- x evalto 1 by E-Var {};
        append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])),l2 = (3 :: (4 :: (5 :: []))),x = 1,y = (2 :: []) |- append(y)(l2) evalto (2 :: (3 :: (4 :: (5 :: [])))) by E-App {
          append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])),l2 = (3 :: (4 :: (5 :: []))),x = 1,y = (2 :: []) |- append(y) evalto (append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []))[fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2))] by E-AppRec {
            append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])),l2 = (3 :: (4 :: (5 :: []))),x = 1,y = (2 :: []) |- append evalto ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] by E-Var {};
            append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])),l2 = (3 :: (4 :: (5 :: []))),x = 1,y = (2 :: []) |- y evalto (2 :: []) by E-Var {};
            append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []) |- (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2))) evalto (append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []))[fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2))] by E-Fun {};
          };
          append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (1 :: (2 :: [])),l2 = (3 :: (4 :: (5 :: []))),x = 1,y = (2 :: []) |- l2 evalto (3 :: (4 :: (5 :: []))) by E-Var {};
          append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []),l2 = (3 :: (4 :: (5 :: []))) |- match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)) evalto (2 :: (3 :: (4 :: (5 :: [])))) by E-MatchCons {
            append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []),l2 = (3 :: (4 :: (5 :: []))) |- l1 evalto (2 :: []) by E-Var {};
            append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []),l2 = (3 :: (4 :: (5 :: []))),x = 2,y = [] |- (x :: append(y)(l2)) evalto (2 :: (3 :: (4 :: (5 :: [])))) by E-Cons {
              append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []),l2 = (3 :: (4 :: (5 :: []))),x = 2,y = [] |- x evalto 2 by E-Var {};
              append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []),l2 = (3 :: (4 :: (5 :: []))),x = 2,y = [] |- append(y)(l2) evalto (3 :: (4 :: (5 :: []))) by E-App {
                append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []),l2 = (3 :: (4 :: (5 :: []))),x = 2,y = [] |- append(y) evalto (append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = [])[fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2))] by E-AppRec {
                  append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []),l2 = (3 :: (4 :: (5 :: []))),x = 2,y = [] |- append evalto ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))] by E-Var {};
                  append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []),l2 = (3 :: (4 :: (5 :: []))),x = 2,y = [] |- y evalto [] by E-Var {};
                  append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = [] |- (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2))) evalto (append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = [])[fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2))] by E-Fun {};
                };
                append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = (2 :: []),l2 = (3 :: (4 :: (5 :: []))),x = 2,y = [] |- l2 evalto (3 :: (4 :: (5 :: []))) by E-Var {};
                append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = [],l2 = (3 :: (4 :: (5 :: []))) |- match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)) evalto (3 :: (4 :: (5 :: []))) by E-MatchNil {
                  append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = [],l2 = (3 :: (4 :: (5 :: []))) |- l1 evalto [] by E-Var {};
                  append = ()[rec append = fun l1 -> (fun l2 -> match l1 with [] -> l2 | x :: y -> (x :: append(y)(l2)))],l1 = [],l2 = (3 :: (4 :: (5 :: []))) |- l2 evalto (3 :: (4 :: (5 :: []))) by E-Var {};
                };
              };
            };
          };
        };
      };
    };
  };
};
-}

  q76 : ● ⊢ ℓetrec "apply" ≔fun "l" ⇒ fun "x" ⇒
                   match var "l" with[]⇒ var "x"
                                 ∣ "f" ∷ "l" ⇒ app (var "f") (app (app (var "apply") (var "l")) (var "x")) ιn
            app (app (var "apply") ((fun "x" ⇒ var "x" ⊛ var "x") ∷ (fun "y" ⇒ var "y" ⊕ i (+ 3)) ∷ [])) (i (+ 4)) ⇓ i (+ 49)
  q76 = E-LetRec (E-App (E-AppRec (E-Var refl) (E-Cons E-Fun (E-Cons E-Fun E-Nil)) E-Fun)
                        E-Int
                        (E-MatchCons (E-Var refl)
                                     (E-App (E-Var refl)
                                            (E-App (E-AppRec (E-Var refl) (E-Var refl) E-Fun)
                                                   (E-Var refl)
                                                   (E-MatchCons (E-Var refl)
                                                                (E-App (E-Var refl)
                                                                       (E-App (E-AppRec (E-Var refl) (E-Var refl) E-Fun)
                                                                              (E-Var refl)
                                                                              (E-MatchNil (E-Var refl) (E-Var refl)))
                                                                       (E-Plus (E-Var refl) E-Int (B-Plus refl)))))
                                            (E-Times (E-Var refl) (E-Var refl) (B-Times refl)))))
{-
|- let rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x))) in apply(((fun x -> (x * x)) :: ((fun y -> (y + 3)) :: [])))(4) evalto 49 by E-LetRec {
  apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] |- apply(((fun x -> (x * x)) :: ((fun y -> (y + 3)) :: [])))(4) evalto 49 by E-App {
    apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] |- apply(((fun x -> (x * x)) :: ((fun y -> (y + 3)) :: []))) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])))[fun x -> match l with [] -> x | f :: l -> f(apply(l)(x))] by E-AppRec {
      apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] |- apply evalto ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] by E-Var {};
      apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] |- ((fun x -> (x * x)) :: ((fun y -> (y + 3)) :: [])) evalto ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])) by E-Cons {
        apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] |- (fun x -> (x * x)) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] by E-Fun {};
        apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] |- ((fun y -> (y + 3)) :: []) evalto ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []) by E-Cons {
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] |- (fun y -> (y + 3)) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] by E-Fun {};
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] |- [] evalto [] by E-Nil {};
        };
      };
      apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])) |- (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x))) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])))[fun x -> match l with [] -> x | f :: l -> f(apply(l)(x))] by E-Fun {};
    };
    apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] |- 4 evalto 4 by E-Int {};
    apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])),x = 4 |- match l with [] -> x | f :: l -> f(apply(l)(x)) evalto 49 by E-MatchCons {
      apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])),x = 4 |- l evalto ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])) by E-Var {};
      apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []) |- f(apply(l)(x)) evalto 49 by E-App {
        apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []) |- f evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] by E-Var {};
        apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []) |- apply(l)(x) evalto 7 by E-App {
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []) |- apply(l) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []))[fun x -> match l with [] -> x | f :: l -> f(apply(l)(x))] by E-AppRec {
            apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []) |- apply evalto ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] by E-Var {};
            apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []) |- l evalto ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []) by E-Var {};
            apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []) |- (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x))) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []))[fun x -> match l with [] -> x | f :: l -> f(apply(l)(x))] by E-Fun {};
          };
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []) |- x evalto 4 by E-Var {};
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []),x = 4 |- match l with [] -> x | f :: l -> f(apply(l)(x)) evalto 7 by E-MatchCons {
            apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []),x = 4 |- l evalto ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []) by E-Var {};
            apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)],l = [] |- f(apply(l)(x)) evalto 7 by E-App {
              apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)],l = [] |- f evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] by E-Var {};
              apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)],l = [] |- apply(l)(x) evalto 4 by E-App {
                apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)],l = [] |- apply(l) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = [])[fun x -> match l with [] -> x | f :: l -> f(apply(l)(x))] by E-AppRec {
                  apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)],l = [] |- apply evalto ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))] by E-Var {};
                  apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)],l = [] |- l evalto [] by E-Var {};
                  apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = [] |- (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x))) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = [])[fun x -> match l with [] -> x | f :: l -> f(apply(l)(x))] by E-Fun {};
                };
                apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)] :: []),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))])[fun y -> (y + 3)],l = [] |- x evalto 4 by E-Var {};
                apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = [],x = 4 |- match l with [] -> x | f :: l -> f(apply(l)(x)) evalto 4 by E-MatchNil {
                  apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = [],x = 4 |- l evalto [] by E-Var {};
                  apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],l = [],x = 4 |- x evalto 4 by E-Var {};
                };
              };
              apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],y = 4 |- (y + 3) evalto 7 by E-Plus {
                apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],y = 4 |- y evalto 4 by E-Var {};
                apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],y = 4 |- 3 evalto 3 by E-Int {};
                4 plus 3 is 7 by B-Plus {};
              };
            };
          };
        };
        apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],x = 7 |- (x * x) evalto 49 by E-Times {
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],x = 7 |- x evalto 7 by E-Var {};
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> f(apply(l)(x)))],x = 7 |- x evalto 7 by E-Var {};
          7 times 7 is 49 by B-Times {};
        };
      };
    };
  };
};
-}

  q77 : ● ⊢ ℓetrec "apply" ≔fun "l" ⇒ fun "x" ⇒
                   match var "l" with[]⇒ var "x"
                                 ∣ "f" ∷ "l" ⇒ app (app (var "apply") (var "l")) (app (var "f") (var "x")) ιn
            app (app (var "apply") ((fun "x" ⇒ var "x" ⊛ var "x") ∷ (fun "y" ⇒ var "y" ⊕ i (+ 3)) ∷ [])) (i (+ 4)) ⇓ i (+ 19)
  q77 = E-LetRec (E-App (E-AppRec (E-Var refl) (E-Cons E-Fun (E-Cons E-Fun E-Nil)) E-Fun)
                        E-Int
                        (E-MatchCons (E-Var refl)
                                     (E-App (E-AppRec (E-Var refl) (E-Var refl) E-Fun)
                                            (E-App (E-Var refl) (E-Var refl) (E-Times (E-Var refl) (E-Var refl) (B-Times refl)))
                                            (E-MatchCons (E-Var refl)
                                                         (E-App (E-AppRec (E-Var refl) (E-Var refl) E-Fun)
                                                                (E-App (E-Var refl) (E-Var refl) (E-Plus (E-Var refl) E-Int (B-Plus refl)))
                                                                (E-MatchNil (E-Var refl) (E-Var refl)))))))
{-
|- let rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x))) in apply(((fun x -> (x * x)) :: ((fun y -> (y + 3)) :: [])))(4) evalto 19 by E-LetRec {
  apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] |- apply(((fun x -> (x * x)) :: ((fun y -> (y + 3)) :: [])))(4) evalto 19 by E-App {
    apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] |- apply(((fun x -> (x * x)) :: ((fun y -> (y + 3)) :: []))) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])))[fun x -> match l with [] -> x | f :: l -> apply(l)(f(x))] by E-AppRec {
      apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] |- apply evalto ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] by E-Var {};
      apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] |- ((fun x -> (x * x)) :: ((fun y -> (y + 3)) :: [])) evalto ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])) by E-Cons {
        apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] |- (fun x -> (x * x)) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] by E-Fun {};
        apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] |- ((fun y -> (y + 3)) :: []) evalto ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []) by E-Cons {
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] |- (fun y -> (y + 3)) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] by E-Fun {};
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] |- [] evalto [] by E-Nil {};
        };
      };
      apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])) |- (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x))) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])))[fun x -> match l with [] -> x | f :: l -> apply(l)(f(x))] by E-Fun {};
    };
    apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] |- 4 evalto 4 by E-Int {};
    apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])),x = 4 |- match l with [] -> x | f :: l -> apply(l)(f(x)) evalto 19 by E-MatchCons {
      apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])),x = 4 |- l evalto ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])) by E-Var {};
      apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []) |- apply(l)(f(x)) evalto 19 by E-App {
        apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []) |- apply(l) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []))[fun x -> match l with [] -> x | f :: l -> apply(l)(f(x))] by E-AppRec {
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []) |- apply evalto ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] by E-Var {};
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []) |- l evalto ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []) by E-Var {};
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []) |- (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x))) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []))[fun x -> match l with [] -> x | f :: l -> apply(l)(f(x))] by E-Fun {};
        };
        apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []) |- f(x) evalto 16 by E-App {
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []) |- f evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] by E-Var {};
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)] :: ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: [])),x = 4,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun x -> (x * x)],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []) |- x evalto 4 by E-Var {};
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],x = 4 |- (x * x) evalto 16 by E-Times {
            apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],x = 4 |- x evalto 4 by E-Var {};
            apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],x = 4 |- x evalto 4 by E-Var {};
            4 times 4 is 16 by B-Times {};
          };
        };
        apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []),x = 16 |- match l with [] -> x | f :: l -> apply(l)(f(x)) evalto 19 by E-MatchCons {
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []),x = 16 |- l evalto ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []) by E-Var {};
          apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []),x = 16,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)],l = [] |- apply(l)(f(x)) evalto 19 by E-App {
            apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []),x = 16,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)],l = [] |- apply(l) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = [])[fun x -> match l with [] -> x | f :: l -> apply(l)(f(x))] by E-AppRec {
              apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []),x = 16,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)],l = [] |- apply evalto ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))] by E-Var {};
              apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []),x = 16,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)],l = [] |- l evalto [] by E-Var {};
              apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = [] |- (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x))) evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = [])[fun x -> match l with [] -> x | f :: l -> apply(l)(f(x))] by E-Fun {};
            };
            apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []),x = 16,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)],l = [] |- f(x) evalto 19 by E-App {
              apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []),x = 16,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)],l = [] |- f evalto (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] by E-Var {};
              apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = ((apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)] :: []),x = 16,f = (apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))])[fun y -> (y + 3)],l = [] |- x evalto 16 by E-Var {};
              apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],y = 16 |- (y + 3) evalto 19 by E-Plus {
                apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],y = 16 |- y evalto 16 by E-Var {};
                apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],y = 16 |- 3 evalto 3 by E-Int {};
                16 plus 3 is 19 by B-Plus {};
              };
            };
            apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = [],x = 19 |- match l with [] -> x | f :: l -> apply(l)(f(x)) evalto 19 by E-MatchNil {
              apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = [],x = 19 |- l evalto [] by E-Var {};
              apply = ()[rec apply = fun l -> (fun x -> match l with [] -> x | f :: l -> apply(l)(f(x)))],l = [],x = 19 |- x evalto 19 by E-Var {};
            };
          };
        };
      };
    };
  };
};
-}


record ex7-2 : Set where
  open import BCoPL.EvalML5

  ex-7-2-1 : ● ⊢ ℓetrec "max" ≔fun "l" ⇒
                        match var "l" ωith
                             var "x" ∷ [] ↦ var "x"
                           ∣ var "x" ∷ var "y" ∷ var "z" ↦
                                 (if var "x" ≺ var "y"
                                   then app (var "max") (var "y" ∷ var "z")
                                   else app (var "max") (var "x" ∷ var "z")) ̣
                  ιn app (var "max") (i (+ 9) ∷ i (+ 2) ∷ i (+ 3) ∷ []) ⇓ i (+ 9)
  ex-7-2-1 = {!!}

  ex-7-2-2 : ● ⊢ ℓetrec "heads" ≔fun "l" ⇒
                        match var "l" ωith
                                [] ↦ []
                              ∣ [] ∷ (var "l'") ↦ app (var "heads") (var "l'")
                              ∣ (var "x") ∷ ̱ ↦ var "x" ∷ app (var "heads") (var "l'") ̣ ιn
                        app (var "heads") ((i (+ 1) ∷ i (+ 2) ∷ []) ∷ [] ∷ (i (+ 3) ∷ []) ∷ []) ⇓ i (+ 1) ∷ i (+ 3) ∷ []
  ex-7-2-2 = {!!}
