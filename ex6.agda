module ex6 where

open import Data.Empty using (⊥)

record ex-6-1 : Set where
  open import BCoPL.NamelessML3
  open import BCoPL.Show.NamelessML3

  ex-6-1-1 : ● ⊱ "x" ⊱ "y" ⊢ if var "x" then var "y" ⊕ i (+ 1) else var "y" ⊝ i (+ 1)
                                ⟾
                                if # 2 then # 1 ⊕̂ i (+ 1) else # 1 ⊝̂ i (+ 1)
  ex-6-1-1 = TR-If (TR-Var2 y≢x (TR-Var1 refl)) (TR-Plus (TR-Var1 refl) TR-Int) (TR-Minus (TR-Var1 refl) TR-Int)
    where
      y≢x : "y" ≡ "x" → ⊥
      y≢x ()
{-
x,y |- if x then (y + 1) else (y - 1) ==> if #2 then (#1 + 1) else (#1 - 1) by Tr-If {
  x,y |- x ==> #2 by Tr-Var2 {
    x |- x ==> #1 by Tr-Var1 {};
  };
  x,y |- (y + 1) ==> (#1 + 1) by Tr-Plus {
    x,y |- y ==> #1 by Tr-Var1 {};
    x,y |- 1 ==> 1 by Tr-Int {};
  };
  x,y |- (y - 1) ==> (#1 - 1) by Tr-Minus {
    x,y |- y ==> #1 by Tr-Var1 {};
    x,y |- 1 ==> 1 by Tr-Int {};
  };
};
-}

  ex-6-1-2 : ● ⊢ ℓet "x" ≔ i (+ 3) ⊛ i (+ 3) ιn ℓet "y" ≔ i (+ 4) ⊛ var "x" ιn var "x" ⊕ var "y"
                 ⟾
                 ℓeṭ≔ i (+ 3) ⊛̂ i (+ 3) ιn ℓeṭ≔ i (+ 4) ⊛̂ # 1 ιn # 2 ⊕̂ # 1
  ex-6-1-2 = TR-Let (TR-Times TR-Int TR-Int) (TR-Let (TR-Times TR-Int (TR-Var1 refl)) (TR-Plus (TR-Var2 y≢x (TR-Var1 refl)) (TR-Var1 refl)))
    where
      y≢x : "y" ≡ "x" → ⊥
      y≢x ()
{-
|- let x = (3 * 3) in let y = (4 * x) in (x + y) ==> let . = (3 * 3) in let . = (4 * #1) in (#2 + #1) by Tr-Let {
  |- (3 * 3) ==> (3 * 3) by Tr-Times {
    |- 3 ==> 3 by Tr-Int {};
    |- 3 ==> 3 by Tr-Int {};
  };
  x |- let y = (4 * x) in (x + y) ==> let . = (4 * #1) in (#2 + #1) by Tr-Let {
    x |- (4 * x) ==> (4 * #1) by Tr-Times {
      x |- 4 ==> 4 by Tr-Int {};
      x |- x ==> #1 by Tr-Var1 {};
    };
    x,y |- (x + y) ==> (#2 + #1) by Tr-Plus {
      x,y |- x ==> #2 by Tr-Var2 {
        x |- x ==> #1 by Tr-Var1 {};
      };
      x,y |- y ==> #1 by Tr-Var1 {};
    };
  };
};
-}

  q58 : ● ⊱ "x" ⊢ ℓet "x" ≔ var "x" ⊛ i (+ 2) ιn var "x" ⊕ var "x"
                      ⟾
                      ℓeṭ≔ # 1 ⊛̂ i (+ 2) ιn # 1 ⊕̂ # 1
  q58 = TR-Let (TR-Times (TR-Var1 refl) TR-Int) (TR-Plus (TR-Var1 refl) (TR-Var1 refl))
{-
x |- let x = (x * 2) in (x + x) ==> let . = (#1 * 2) in (#1 + #1) by Tr-Let {
  x |- (x * 2) ==> (#1 * 2) by Tr-Times {
    x |- x ==> #1 by Tr-Var1 {};
    x |- 2 ==> 2 by Tr-Int {};
  };
  x,x |- (x + x) ==> (#1 + #1) by Tr-Plus {
    x,x |- x ==> #1 by Tr-Var1 {};
    x,x |- x ==> #1 by Tr-Var1 {};
  };
};
-}

  ex-6-1-3 : ● ⊢ ℓet "x" ≔ ℓet "y" ≔ i (+ 3) ⊝ i (+ 2) ιn var "y" ⊛ var "y" ιn
                 ℓet "y" ≔ i (+ 4) ιn var "x" ⊕ var "y"
                 ⟾
                 ℓeṭ≔ ℓeṭ≔ i (+ 3) ⊝̂ i (+ 2) ιn # 1 ⊛̂ # 1 ιn
                 ℓeṭ≔ i (+ 4) ιn # 2 ⊕̂ # 1
  ex-6-1-3 = TR-Let (TR-Let (TR-Minus TR-Int TR-Int) (TR-Times (TR-Var1 refl) (TR-Var1 refl))) (TR-Let TR-Int (TR-Plus (TR-Var2 y≢x (TR-Var1 refl)) (TR-Var1 refl)))
    where
      y≢x : "y" ≡ "x" → ⊥
      y≢x ()
{-
|- let x = let y = (3 - 2) in (y * y) in let y = 4 in (x + y) ==> let . = let . = (3 - 2) in (#1 * #1) in let . = 4 in (#2 + #1) by Tr-Let {
  |- let y = (3 - 2) in (y * y) ==> let . = (3 - 2) in (#1 * #1) by Tr-Let {
    |- (3 - 2) ==> (3 - 2) by Tr-Minus {
      |- 3 ==> 3 by Tr-Int {};
      |- 2 ==> 2 by Tr-Int {};
    };
    y |- (y * y) ==> (#1 * #1) by Tr-Times {
      y |- y ==> #1 by Tr-Var1 {};
      y |- y ==> #1 by Tr-Var1 {};
    };
  };
  x |- let y = 4 in (x + y) ==> let . = 4 in (#2 + #1) by Tr-Let {
    x |- 4 ==> 4 by Tr-Int {};
    x,y |- (x + y) ==> (#2 + #1) by Tr-Plus {
      x,y |- x ==> #2 by Tr-Var2 {
        x |- x ==> #1 by Tr-Var1 {};
      };
      x,y |- y ==> #1 by Tr-Var1 {};
    };
  };
};
-}

  q62 : ● ⊢ ℓet "y" ≔ i (+ 2) ιn fun "x" ⇒ var "x" ⊕ var "y"
            ⟾
            ℓeṭ≔ i (+ 2) ιn fuṇ⇒ # 1 ⊕̂ # 2
  q62 = TR-Let TR-Int (TR-Fun (TR-Plus (TR-Var1 refl) (TR-Var2 x≢y (TR-Var1 refl))))
    where
      x≢y : "x" ≡ "y" → ⊥
      x≢y ()
{-
|- let y = 2 in (fun x -> (x + y)) ==> let . = 2 in (fun . -> (#1 + #2)) by Tr-Let {
  |- 2 ==> 2 by Tr-Int {};
  y |- (fun x -> (x + y)) ==> (fun . -> (#1 + #2)) by Tr-Fun {
    y,x |- (x + y) ==> (#1 + #2) by Tr-Plus {
      y,x |- x ==> #1 by Tr-Var1 {};
      y,x |- y ==> #2 by Tr-Var2 {
        y |- y ==> #1 by Tr-Var1 {};
      };
    };
  };
};
-}

  q64 : ● ⊢ ℓet "sm" ≔ fun "f" ⇒ app (var "f") (i (+ 3)) ⊕ app (var "f") (i (+ 4)) ιn app (var "sm") (fun "x" ⇒ var "x" ⊛ var "x")
            ⟾
            ℓeṭ≔ fuṇ⇒ app (# 1) (i (+ 3)) ⊕̂ app (# 1) (i (+ 4)) ιn app (# 1) (fuṇ⇒ # 1 ⊛̂ # 1)
  q64 = TR-Let (TR-Fun (TR-Plus (TR-App (TR-Var1 refl) TR-Int) (TR-App (TR-Var1 refl) TR-Int))) (TR-App (TR-Var1 refl) (TR-Fun (TR-Times (TR-Var1 refl) (TR-Var1 refl))))
{-
|- let sm = (fun f -> (f(3) + f(4))) in sm((fun x -> (x * x))) ==> let . = (fun . -> (#1(3) + #1(4))) in #1((fun . -> (#1 * #1))) by Tr-Let {
  |- (fun f -> (f(3) + f(4))) ==> (fun . -> (#1(3) + #1(4))) by Tr-Fun {
    f |- (f(3) + f(4)) ==> (#1(3) + #1(4)) by Tr-Plus {
      f |- f(3) ==> #1(3) by Tr-App {
        f |- f ==> #1 by Tr-Var1 {};
        f |- 3 ==> 3 by Tr-Int {};
      };
      f |- f(4) ==> #1(4) by Tr-App {
        f |- f ==> #1 by Tr-Var1 {};
        f |- 4 ==> 4 by Tr-Int {};
      };
    };
  };
  sm |- sm((fun x -> (x * x))) ==> #1((fun . -> (#1 * #1))) by Tr-App {
    sm |- sm ==> #1 by Tr-Var1 {};
    sm |- (fun x -> (x * x)) ==> (fun . -> (#1 * #1)) by Tr-Fun {
      sm,x |- (x * x) ==> (#1 * #1) by Tr-Times {
        sm,x |- x ==> #1 by Tr-Var1 {};
        sm,x |- x ==> #1 by Tr-Var1 {};
      };
    };
  };
};
-}

  ex-6-1-4 : ● ⊢ ℓet "a" ≔ i (+ 3) ιn
                 ℓet "f" ≔ fun "y" ⇒ var "y" ⊛ var "a" ιn
                 ℓet "a" ≔ i (+ 5) ιn app (var "f") (i (+ 4))
                 ⟾
                 ℓeṭ≔ i (+ 3) ιn
                 ℓeṭ≔ fuṇ⇒ # 1 ⊛̂ # 2 ιn
                 ℓeṭ≔ i (+ 5) ιn app (# 2) (i (+ 4))
  ex-6-1-4 = TR-Let TR-Int (TR-Let (TR-Fun (TR-Times (TR-Var1 refl) (TR-Var2 y≢a (TR-Var1 refl)))) (TR-Let TR-Int (TR-App (TR-Var2 a≢f (TR-Var1 refl)) TR-Int)))
    where
      a≢f : "a" ≡ "f" → ⊥
      a≢f ()
      y≢a : "y" ≡ "a" → ⊥
      y≢a ()
{-
|- let a = 3 in let f = (fun y -> (y * a)) in let a = 5 in f(4) ==> let . = 3 in let . = (fun . -> (#1 * #2)) in let . = 5 in #2(4) by Tr-Let {
  |- 3 ==> 3 by Tr-Int {};
  a |- let f = (fun y -> (y * a)) in let a = 5 in f(4) ==> let . = (fun . -> (#1 * #2)) in let . = 5 in #2(4) by Tr-Let {
    a |- (fun y -> (y * a)) ==> (fun . -> (#1 * #2)) by Tr-Fun {
      a,y |- (y * a) ==> (#1 * #2) by Tr-Times {
        a,y |- y ==> #1 by Tr-Var1 {};
        a,y |- a ==> #2 by Tr-Var2 {
          a |- a ==> #1 by Tr-Var1 {};
        };
      };
    };
    a,f |- let a = 5 in f(4) ==> let . = 5 in #2(4) by Tr-Let {
      a,f |- 5 ==> 5 by Tr-Int {};
      a,f,a |- f(4) ==> #2(4) by Tr-App {
        a,f,a |- f ==> #2 by Tr-Var2 {
          a,f |- f ==> #1 by Tr-Var1 {};
        };
        a,f,a |- 4 ==> 4 by Tr-Int {};
      };
    };
  };
};
-}


  ex-6-1-5 : ● ⊢ ℓetrec "fact" ≔fun "n" ⇒
                        if var "n" ≺ i (+ 2) then i (+ 1) else var "n" ⊛ app (var "fact") (var "n" ⊝ i (+ 1)) ιn
                 app (var "fact") (i (+ 3))
                 ⟾
                 ℓetrec̣≔fuṇ⇒ if # 1 ≺̂ i (+ 2) then i (+ 1) else # 1 ⊛̂ app (# 2) (# 1 ⊝̂ i (+ 1)) ιn
                 app (# 1) (i (+ 3))
  ex-6-1-5 = TR-LetRec (TR-If (TR-Lt (TR-Var1 refl) TR-Int) TR-Int (TR-Times (TR-Var1 refl) (TR-App (TR-Var2 n≢fact (TR-Var1 refl)) (TR-Minus (TR-Var1 refl) TR-Int)))) (TR-App (TR-Var1 refl) TR-Int)
    where
      n≢fact : "n" ≡ "fact" → ⊥
      n≢fact ()
{-
|- let rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1))) in fact(3) ==> let rec . = fun . -> if (#1 < 2) then 1 else (#1 * #2((#1 - 1))) in #1(3) by Tr-LetRec {
  fact,n |- if (n < 2) then 1 else (n * fact((n - 1))) ==> if (#1 < 2) then 1 else (#1 * #2((#1 - 1))) by Tr-If {
    fact,n |- (n < 2) ==> (#1 < 2) by Tr-Lt {
      fact,n |- n ==> #1 by Tr-Var1 {};
      fact,n |- 2 ==> 2 by Tr-Int {};
    };
    fact,n |- 1 ==> 1 by Tr-Int {};
    fact,n |- (n * fact((n - 1))) ==> (#1 * #2((#1 - 1))) by Tr-Times {
      fact,n |- n ==> #1 by Tr-Var1 {};
      fact,n |- fact((n - 1)) ==> #2((#1 - 1)) by Tr-App {
        fact,n |- fact ==> #2 by Tr-Var2 {
          fact |- fact ==> #1 by Tr-Var1 {};
        };
        fact,n |- (n - 1) ==> (#1 - 1) by Tr-Minus {
          fact,n |- n ==> #1 by Tr-Var1 {};
          fact,n |- 1 ==> 1 by Tr-Int {};
        };
      };
    };
  };
  fact |- fact(3) ==> #1(3) by Tr-App {
    fact |- fact ==> #1 by Tr-Var1 {};
    fact |- 3 ==> 3 by Tr-Int {};
  };
};
-}

record ex-6-2 : Set where
  open import BCoPL.EvalNamelessML3

  ex-6-2-1 : ● ⊱ b true ⊱ i (+ 4) ⊢ if # 2 then # 1 ⊕̂ i (+ 1) else # 1 ⊝̂ i (+ 1) ⇓ i (+ 5)
  ex-6-2-1 = E-IfT (E-Var refl) (E-Plus (E-Var refl) E-Int (B-Plus refl))
{-

-}

  ex-6-2-2 : ● ⊢ ℓeṭ≔ i (+ 3) ⊛̂ i (+ 3) ιn ℓeṭ≔ i (+ 4) ⊛̂ # 1 ιn # 2 ⊕̂ # 1 ⇓ i (+ 45)
  ex-6-2-2 = E-Let (E-Times E-Int E-Int (B-Times refl)) (E-Let (E-Times E-Int (E-Var refl) (B-Times refl)) (E-Plus (E-Var refl) (E-Var refl) (B-Plus refl)))
{-

-}

  ex-6-2-3 : ● ⊢ ℓeṭ≔ ℓeṭ≔ i (+ 3) ⊝̂ i (+ 2) ιn # 1 ⊛̂ # 1 ιn
                  ℓeṭ≔ i (+ 4) ιn # 2 ⊕̂ # 1 ⇓ i (+ 5)
  ex-6-2-3 = E-Let (E-Let (E-Minus E-Int E-Int (B-Minus refl)) (E-Times (E-Var refl) (E-Var refl) (B-Times refl))) (E-Let E-Int (E-Plus (E-Var refl) (E-Var refl) (B-Plus refl)))
{-

-}

  ex-6-2-4 : ● ⊢ ℓeṭ≔ i (+ 3) ιn
                  ℓeṭ≔ fuṇ⇒ # 1 ⊛̂ # 2 ιn
                  ℓeṭ≔ i (+ 5) ιn app (# 2) (i (+ 4)) ⇓ i (+ 12)
  ex-6-2-4 = E-Let E-Int (E-Let E-Fun (E-Let E-Int (E-App (E-Var refl) E-Int (E-Times (E-Var refl) (E-Var refl) (B-Times refl)))))
{-

-}

  ex-6-2-5 : ● ⊢ ℓetrec̣≔fuṇ⇒ if # 1 ≺̂ i (+ 2) then i (+ 1) else # 1 ⊛̂ app (# 2) (# 1 ⊝̂ i (+ 1)) ιn
                  app (# 1) (i (+ 3)) ⇓ i (+ 6)
  ex-6-2-5 = E-LetRec (E-AppRec (E-Var refl) E-Int (E-IfF (E-Lt (E-Var refl) E-Int (B-Lt refl)) (E-Times (E-Var refl) (E-AppRec (E-Var refl) (E-Minus (E-Var refl) E-Int (B-Minus refl)) (E-IfF (E-Lt (E-Var refl) E-Int (B-Lt refl)) (E-Times (E-Var refl) (E-AppRec (E-Var refl) (E-Minus (E-Var refl) E-Int (B-Minus refl)) (E-IfT (E-Lt (E-Var refl) E-Int (B-Lt refl)) E-Int)) (B-Times refl)))) (B-Times refl))))
{-

-}
