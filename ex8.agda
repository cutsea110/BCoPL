module ex8 where

open import BCoPL.TypingEvalML4
open import BCoPL.Show.TypingEvalML4

ex-8-1-1 : ● ⊢ i (+ 3) ⊕ i (+ 5) ∶ int
ex-8-1-1 = T-Plus T-Int T-Int
{-
|- (3 + 5) : int by T-Plus {
  |- 3 : int by T-Int {};
  |- 5 : int by T-Int {};
};
-}

q81 : ● ⊢ if i (+ 4) ≺ i (+ 5) then i (+ 2) ⊕ i (+ 3) else i (+ 8) ⊛ i (+ 8) ∶ int
q81 = T-If (T-Lt T-Int T-Int) (T-Plus T-Int T-Int) (T-Times T-Int T-Int)
{-
|- if (4 < 5) then (2 + 3) else (8 * 8) : int by T-If {
  |- (4 < 5) : bool by T-Lt {
    |- 4 : int by T-Int {};
    |- 5 : int by T-Int {};
  };
  |- (2 + 3) : int by T-Plus {
    |- 2 : int by T-Int {};
    |- 3 : int by T-Int {};
  };
  |- (8 * 8) : int by T-Times {
    |- 8 : int by T-Int {};
    |- 8 : int by T-Int {};
  };
};
-}

ex-8-1-2 : ● ⊱ ("x" , bool) ⊱ ("y" , int) ⊢ if var "x" then var "y" ⊕ i (+ 1) else var "y" ⊝ i (+ 1) ∶ int
ex-8-1-2 = T-If (T-Var refl) (T-Plus (T-Var refl) T-Int) (T-Minus (T-Var refl) T-Int)
{-
x:bool,y:int |- if x then (y + 1) else (y - 1) : int by T-If {
  x:bool,y:int |- x : bool by (T-Var refl) {};
  x:bool,y:int |- (y + 1) : int by T-Plus {
    x:bool,y:int |- y : int by (T-Var refl) {};
    x:bool,y:int |- 1 : int by T-Int {};
  };
  x:bool,y:int |- (y - 1) : int by T-Minus {
    x:bool,y:int |- y : int by (T-Var refl) {};
    x:bool,y:int |- 1 : int by T-Int {};
  };
};
-}

ex-8-1-3 : ● ⊢ ℓet "x" ≔ i (+ 3) ≺ i (+ 2) ιn
                ℓet "y" ≔ i (+ 5) ιn
                if var "x" then var "y" else i (+ 2) ∶ int
ex-8-1-3 = T-Let (T-Lt T-Int T-Int) (T-Let T-Int (T-If (T-Var refl) (T-Var refl) T-Int))
{-
|- let x = (3 < 2) in let y = 5 in if x then y else 2 : int by T-Let {
  |- (3 < 2) : bool by T-Lt {
    |- 3 : int by T-Int {};
    |- 2 : int by T-Int {};
  };
  x:bool |- let y = 5 in if x then y else 2 : int by T-Let {
    x:bool |- 5 : int by T-Int {};
    x:bool,y:int |- if x then y else 2 : int by T-If {
      x:bool,y:int |- x : bool by (T-Var refl) {};
      x:bool,y:int |- y : int by (T-Var refl) {};
      x:bool,y:int |- 2 : int by T-Int {};
    };
  };
};
-}

ex-8-1-4 : ● ⊢ fun "x" ⇒ var "x" ⊕ i (+ 1) ∶ int ⇀ int
ex-8-1-4 = T-Fun (T-Plus (T-Var refl) T-Int)
{-
|- (fun x -> (x + 1)) : int -> int by T-Fun {
  x:int |- (x + 1) : int by T-Plus {
    x:int |- x : int by (T-Var refl) {};
    x:int |- 1 : int by T-Int {};
  };
};
-}

q85 : ● ⊢ ℓet "f" ≔ fun "x" ⇒ var "x" ⊕ i (+ 1) ιn app (var "f") (i (+ 4)) ∶ int
q85 = T-Let (T-Fun (T-Plus (T-Var refl) T-Int)) (T-App (T-Var refl) T-Int)
{-
|- let f = (fun x -> (x + 1)) in f(4) : int by T-Let {
  |- (fun x -> (x + 1)) : int -> int by T-Fun {
    x:int |- (x + 1) : int by T-Plus {
      x:int |- x : int by (T-Var refl) {};
      x:int |- 1 : int by T-Int {};
    };
  };
  f:int -> int |- f(4) : int by T-App {
    f:int -> int |- f : int -> int by (T-Var refl) {};
    f:int -> int |- 4 : int by T-Int {};
  };
};
-}

ex-8-1-5 : ● ⊢ fun "f" ⇒ app (var "f") (i (+ 0)) ⊕ app (var "f") (i (+ 1)) ∶ (int ⇀ int) ⇀ int
ex-8-1-5 = T-Fun (T-Plus (T-App (T-Var refl) T-Int) (T-App (T-Var refl) T-Int))
{-
|- (fun f -> (f(0) + f(1))) : ((int) -> int) -> int by T-Fun {
  f:(int) -> int |- (f(0) + f(1)) : int by T-Plus {
    f:(int) -> int |- f(0) : int by T-App {
      f:(int) -> int |- f : (int) -> int by (T-Var refl) {};
      f:(int) -> int |- 0 : int by T-Int {};
    };
    f:(int) -> int |- f(1) : int by T-App {
      f:(int) -> int |- f : (int) -> int by (T-Var refl) {};
      f:(int) -> int |- 1 : int by T-Int {};
    };
  };
};
-}

q87 : ● ⊢ ℓet "max" ≔ fun "x" ⇒ fun "y" ⇒
              if var "x" ≺ var "y"
              then var "y"
              else var "x" ιn app (app (var "max") (i (+ 3))) (i (+ 5)) ∶ int
q87 = T-Let (T-Fun (T-Fun (T-If (T-Lt (T-Var refl) (T-Var refl)) (T-Var refl) (T-Var refl)))) (T-App (T-App (T-Var refl) T-Int) T-Int)
{-
|- let max = (fun x -> (fun y -> if (x < y) then y else x)) in max(3)(5) : int by T-Let {
  |- (fun x -> (fun y -> if (x < y) then y else x)) : (int) -> (int) -> int by T-Fun {
    x:int |- (fun y -> if (x < y) then y else x) : (int) -> int by T-Fun {
      x:int,y:int |- if (x < y) then y else x : int by T-If {
        x:int,y:int |- (x < y) : bool by T-Lt {
          x:int,y:int |- x : int by (T-Var refl) {};
          x:int,y:int |- y : int by (T-Var refl) {};
        };
        x:int,y:int |- y : int by (T-Var refl) {};
        x:int,y:int |- x : int by (T-Var refl) {};
      };
    };
  };
  max:(int) -> (int) -> int |- max(3)(5) : int by T-App {
    max:(int) -> (int) -> int |- max(3) : (int) -> int by T-App {
      max:(int) -> (int) -> int |- max : (int) -> (int) -> int by (T-Var refl) {};
      max:(int) -> (int) -> int |- 3 : int by T-Int {};
    };
    max:(int) -> (int) -> int |- 5 : int by T-Int {};
  };
};
-}

q88 : ● ⊢ i (+ 4) ∷ [] ∶ int list
q88 = T-Cons T-Int T-Nil
{-
|- (4 :: []) : (int list) by T-Cons {
  |- 4 : int by T-Int {};
  |- [] : (int list) by T-Nil {};
};
-}

q89 : ● ⊢ b true ∷ b false ∷ [] ∶ bool list
q89 = T-Cons T-Bool (T-Cons T-Bool T-Nil)
{-
|- (true :: (false :: [])) : (bool list) by T-Cons {
  |- true : bool by T-Bool {};
  |- (false :: []) : (bool list) by T-Cons {
    |- false : bool by T-Bool {};
    |- [] : (bool list) by T-Nil {};
  };
};
-}

q90 : ● ⊢ fun "x" ⇒ fun "y" ⇒ var "x" ∶ int ⇀ int ⇀ int
q90 = T-Fun (T-Fun (T-Var refl))
{-
|- (fun x -> (fun y -> x)) : (int) -> (int) -> int by T-Fun {
  x:int |- (fun y -> x) : (int) -> int by T-Fun {
    x:int,y:int |- x : int by (T-Var refl) {};
  };
};
-}

q91 : ● ⊢ fun "x" ⇒ fun "y" ⇒ var "x" ∶ bool ⇀ int ⇀ bool
q91 = T-Fun (T-Fun (T-Var refl))
{-
|- (fun x -> (fun y -> x)) : (bool) -> (int) -> bool by T-Fun {
  x:bool |- (fun y -> x) : (int) -> bool by T-Fun {
    x:bool,y:int |- x : bool by (T-Var refl) {};
  };
};
-}

ex-8-1-6 : ● ⊢ ℓet "k" ≔ fun "x" ⇒ fun "y" ⇒ var "x" ιn app (app (var "k") (i (+ 3))) (b true) ∶ int
ex-8-1-6 = T-Let (T-Fun (T-Fun (T-Var refl))) (T-App (T-App (T-Var refl) T-Int) T-Bool)
{-
|- let k = (fun x -> (fun y -> x)) in k(3)(true) : int by T-Let {
  |- (fun x -> (fun y -> x)) : (int) -> (bool) -> int by T-Fun {
    x:int |- (fun y -> x) : (bool) -> int by T-Fun {
      x:int,y:bool |- x : int by (T-Var refl) {};
    };
  };
  k:(int) -> (bool) -> int |- k(3)(true) : int by T-App {
    k:(int) -> (bool) -> int |- k(3) : (bool) -> int by T-App {
      k:(int) -> (bool) -> int |- k : (int) -> (bool) -> int by (T-Var refl) {};
      k:(int) -> (bool) -> int |- 3 : int by T-Int {};
    };
    k:(int) -> (bool) -> int |- true : bool by T-Bool {};
  };
};
-}

ex-8-1-7 : ● ⊢ ℓet "k" ≔ fun "x" ⇒ fun "y" ⇒ var "x" ιn app (app (var "k") (i (+ 1) ∷ [])) (i (+ 3)) ∶ int list
ex-8-1-7 = T-Let (T-Fun (T-Fun (T-Var refl))) (T-App (T-App (T-Var refl) (T-Cons T-Int T-Nil)) T-Int)
{-
|- let k = (fun x -> (fun y -> x)) in k((1 :: []))(3) : (int list) by T-Let {
  |- (fun x -> (fun y -> x)) : ((int list)) -> (int) -> (int list) by T-Fun {
    x:(int list) |- (fun y -> x) : (int) -> (int list) by T-Fun {
      x:(int list),y:int |- x : (int list) by (T-Var refl) {};
    };
  };
  k:((int list)) -> (int) -> (int list) |- k((1 :: []))(3) : (int list) by T-App {
    k:((int list)) -> (int) -> (int list) |- k((1 :: [])) : (int) -> (int list) by T-App {
      k:((int list)) -> (int) -> (int list) |- k : ((int list)) -> (int) -> (int list) by (T-Var refl) {};
      k:((int list)) -> (int) -> (int list) |- (1 :: []) : (int list) by T-Cons {
        k:((int list)) -> (int) -> (int list) |- 1 : int by T-Int {};
        k:((int list)) -> (int) -> (int list) |- [] : (int list) by T-Nil {};
      };
    };
    k:((int list)) -> (int) -> (int list) |- 3 : int by T-Int {};
  };
};
-}

q94 : ● ⊢ ℓet "k" ≔ fun "x" ⇒ fun "y" ⇒ var "x" ιn
              app (app (var "k") (b true)) (fun "x" ⇒ var "x" ⊕ i (+ 1)) ∶ bool
q94 = T-Let (T-Fun (T-Fun (T-Var refl))) (T-App (T-App (T-Var refl) T-Bool) (T-Fun (T-Plus (T-Var refl) T-Int)))
{-
|- let k = (fun x -> (fun y -> x)) in k(true)((fun x -> (x + 1))) : bool by T-Let {
  |- (fun x -> (fun y -> x)) : (bool) -> ((int) -> int) -> bool by T-Fun {
    x:bool |- (fun y -> x) : ((int) -> int) -> bool by T-Fun {
      x:bool,y:(int) -> int |- x : bool by (T-Var refl) {};
    };
  };
  k:(bool) -> ((int) -> int) -> bool |- k(true)((fun x -> (x + 1))) : bool by T-App {
    k:(bool) -> ((int) -> int) -> bool |- k(true) : ((int) -> int) -> bool by T-App {
      k:(bool) -> ((int) -> int) -> bool |- k : (bool) -> ((int) -> int) -> bool by (T-Var refl) {};
      k:(bool) -> ((int) -> int) -> bool |- true : bool by T-Bool {};
    };
    k:(bool) -> ((int) -> int) -> bool |- (fun x -> (x + 1)) : (int) -> int by T-Fun {
      k:(bool) -> ((int) -> int) -> bool,x:int |- (x + 1) : int by T-Plus {
        k:(bool) -> ((int) -> int) -> bool,x:int |- x : int by (T-Var refl) {};
        k:(bool) -> ((int) -> int) -> bool,x:int |- 1 : int by T-Int {};
      };
    };
  };
};
-}

ex-8-1-8 : ● ⊢ ℓet "compose" ≔ fun "f" ⇒ fun "g" ⇒ fun "x" ⇒ app (var "f") (app (var "g") (var "x")) ιn
                ℓet "p" ≔ fun "x" ⇒ var "x" ⊛ var "x" ιn
                ℓet "q" ≔ fun "x" ⇒ var "x" ⊕ i (+ 4) ιn
                app (app (var "compose") (var "p")) (var "q") ∶ int ⇀ int
ex-8-1-8 = T-Let (T-Fun (T-Fun (T-Fun (T-App (T-Var refl) (T-App (T-Var refl) (T-Var refl)))))) (T-Let (T-Fun (T-Times (T-Var refl) (T-Var refl))) (T-Let (T-Fun (T-Plus (T-Var refl) T-Int)) (T-App (T-App (T-Var refl) (T-Var refl)) (T-Var refl))))
{-
|- let compose = (fun f -> (fun g -> (fun x -> f(g(x))))) in let p = (fun x -> (x * x)) in let q = (fun x -> (x + 4)) in compose(p)(q) : (int) -> int by T-Let {
  |- (fun f -> (fun g -> (fun x -> f(g(x))))) : ((int) -> int) -> ((int) -> int) -> (int) -> int by T-Fun {
    f:(int) -> int |- (fun g -> (fun x -> f(g(x)))) : ((int) -> int) -> (int) -> int by T-Fun {
      f:(int) -> int,g:(int) -> int |- (fun x -> f(g(x))) : (int) -> int by T-Fun {
        f:(int) -> int,g:(int) -> int,x:int |- f(g(x)) : int by T-App {
          f:(int) -> int,g:(int) -> int,x:int |- f : (int) -> int by (T-Var refl) {};
          f:(int) -> int,g:(int) -> int,x:int |- g(x) : int by T-App {
            f:(int) -> int,g:(int) -> int,x:int |- g : (int) -> int by (T-Var refl) {};
            f:(int) -> int,g:(int) -> int,x:int |- x : int by (T-Var refl) {};
          };
        };
      };
    };
  };
  compose:((int) -> int) -> ((int) -> int) -> (int) -> int |- let p = (fun x -> (x * x)) in let q = (fun x -> (x + 4)) in compose(p)(q) : (int) -> int by T-Let {
    compose:((int) -> int) -> ((int) -> int) -> (int) -> int |- (fun x -> (x * x)) : (int) -> int by T-Fun {
      compose:((int) -> int) -> ((int) -> int) -> (int) -> int,x:int |- (x * x) : int by T-Times {
        compose:((int) -> int) -> ((int) -> int) -> (int) -> int,x:int |- x : int by (T-Var refl) {};
        compose:((int) -> int) -> ((int) -> int) -> (int) -> int,x:int |- x : int by (T-Var refl) {};
      };
    };
    compose:((int) -> int) -> ((int) -> int) -> (int) -> int,p:(int) -> int |- let q = (fun x -> (x + 4)) in compose(p)(q) : (int) -> int by T-Let {
      compose:((int) -> int) -> ((int) -> int) -> (int) -> int,p:(int) -> int |- (fun x -> (x + 4)) : (int) -> int by T-Fun {
        compose:((int) -> int) -> ((int) -> int) -> (int) -> int,p:(int) -> int,x:int |- (x + 4) : int by T-Plus {
          compose:((int) -> int) -> ((int) -> int) -> (int) -> int,p:(int) -> int,x:int |- x : int by (T-Var refl) {};
          compose:((int) -> int) -> ((int) -> int) -> (int) -> int,p:(int) -> int,x:int |- 4 : int by T-Int {};
        };
      };
      compose:((int) -> int) -> ((int) -> int) -> (int) -> int,p:(int) -> int,q:(int) -> int |- compose(p)(q) : (int) -> int by T-App {
        compose:((int) -> int) -> ((int) -> int) -> (int) -> int,p:(int) -> int,q:(int) -> int |- compose(p) : ((int) -> int) -> (int) -> int by T-App {
          compose:((int) -> int) -> ((int) -> int) -> (int) -> int,p:(int) -> int,q:(int) -> int |- compose : ((int) -> int) -> ((int) -> int) -> (int) -> int by (T-Var refl) {};
          compose:((int) -> int) -> ((int) -> int) -> (int) -> int,p:(int) -> int,q:(int) -> int |- p : (int) -> int by (T-Var refl) {};
        };
        compose:((int) -> int) -> ((int) -> int) -> (int) -> int,p:(int) -> int,q:(int) -> int |- q : (int) -> int by (T-Var refl) {};
      };
    };
  };
};
-}

q96 : ● ⊢ ℓet "compose" ≔ fun "f" ⇒ fun "g" ⇒ fun "x" ⇒ app (var "f") (app (var "g") (var "x")) ιn
           ℓet "p" ≔ fun "x" ⇒ if var "x" then i (+ 3) else i (+ 4) ιn
           ℓet "q" ≔ fun "x" ⇒ var "x" ≺ i (+ 4) ιn
           app (app (var "compose") (var "p")) (var "q") ∶ int ⇀ int
q96 = T-Let (T-Fun (T-Fun (T-Fun (T-App (T-Var refl) (T-App (T-Var refl) (T-Var refl)))))) (T-Let (T-Fun (T-If (T-Var refl) T-Int T-Int)) (T-Let (T-Fun (T-Lt (T-Var refl) T-Int)) (T-App (T-App (T-Var refl) (T-Var refl)) (T-Var refl))))
{-
|- let compose = (fun f -> (fun g -> (fun x -> f(g(x))))) in let p = (fun x -> if x then 3 else 4) in let q = (fun x -> (x < 4)) in compose(p)(q) : (int) -> int by T-Let {
  |- (fun f -> (fun g -> (fun x -> f(g(x))))) : ((bool) -> int) -> ((int) -> bool) -> (int) -> int by T-Fun {
    f:(bool) -> int |- (fun g -> (fun x -> f(g(x)))) : ((int) -> bool) -> (int) -> int by T-Fun {
      f:(bool) -> int,g:(int) -> bool |- (fun x -> f(g(x))) : (int) -> int by T-Fun {
        f:(bool) -> int,g:(int) -> bool,x:int |- f(g(x)) : int by T-App {
          f:(bool) -> int,g:(int) -> bool,x:int |- f : (bool) -> int by (T-Var refl) {};
          f:(bool) -> int,g:(int) -> bool,x:int |- g(x) : bool by T-App {
            f:(bool) -> int,g:(int) -> bool,x:int |- g : (int) -> bool by (T-Var refl) {};
            f:(bool) -> int,g:(int) -> bool,x:int |- x : int by (T-Var refl) {};
          };
        };
      };
    };
  };
  compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int |- let p = (fun x -> if x then 3 else 4) in let q = (fun x -> (x < 4)) in compose(p)(q) : (int) -> int by T-Let {
    compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int |- (fun x -> if x then 3 else 4) : (bool) -> int by T-Fun {
      compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,x:bool |- if x then 3 else 4 : int by T-If {
        compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,x:bool |- x : bool by (T-Var refl) {};
        compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,x:bool |- 3 : int by T-Int {};
        compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,x:bool |- 4 : int by T-Int {};
      };
    };
    compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,p:(bool) -> int |- let q = (fun x -> (x < 4)) in compose(p)(q) : (int) -> int by T-Let {
      compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,p:(bool) -> int |- (fun x -> (x < 4)) : (int) -> bool by T-Fun {
        compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,p:(bool) -> int,x:int |- (x < 4) : bool by T-Lt {
          compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,p:(bool) -> int,x:int |- x : int by (T-Var refl) {};
          compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,p:(bool) -> int,x:int |- 4 : int by T-Int {};
        };
      };
      compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,p:(bool) -> int,q:(int) -> bool |- compose(p)(q) : (int) -> int by T-App {
        compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,p:(bool) -> int,q:(int) -> bool |- compose(p) : ((int) -> bool) -> (int) -> int by T-App {
          compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,p:(bool) -> int,q:(int) -> bool |- compose : ((bool) -> int) -> ((int) -> bool) -> (int) -> int by (T-Var refl) {};
          compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,p:(bool) -> int,q:(int) -> bool |- p : (bool) -> int by (T-Var refl) {};
        };
        compose:((bool) -> int) -> ((int) -> bool) -> (int) -> int,p:(bool) -> int,q:(int) -> bool |- q : (int) -> bool by (T-Var refl) {};
      };
    };
  };
};
-}

q97 : ● ⊢ ℓet "s" ≔ (fun "f" ⇒ fun "g" ⇒ fun "x" ⇒ app (app (var "f") (var "x")) (app (var "g") (var "x"))) ιn
           ℓet "k1" ≔ fun "x" ⇒ fun "y" ⇒ var "x" ιn
           ℓet "k2" ≔ fun "x" ⇒ fun "y" ⇒ var "x" ιn
           app (app (var "s") (var "k1")) (var "k2") ∶ int ⇀ int
q97 = T-Let (T-Fun (T-Fun (T-Fun (T-App (T-App (T-Var refl) (T-Var refl))
                                        (T-App (T-Var refl) (T-Var refl))))))
            (T-Let (T-Fun (T-Fun (T-Var refl)))
                   (T-Let (T-Fun (T-Fun (T-Var refl)))
                          (T-App (T-App (T-Var refl) (T-Var refl))
                                 (T-Var refl))))
{-

-}
