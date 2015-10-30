module ex9 where

open import BCoPL.PolyTypingML4
open import BCoPL.Show.PolyTypingML4

q107 : ● ⊢ fun "x" ⇒ var "x" ∶ ′ "a" ⇀ ′ "a"
q107 = T-Abs (T-Var refl raw)
{-
|- (fun x -> x) : ('a) -> 'a by T-Abs {
  x:'a |- x : 'a by T-Var {};
};
-}

ex-9-1-1 : ● ⊱ ("f" , [ "a" ] ̣ ′ "a" ⇀ ′ "a") ⊢ app (var "f") (i (+ 3)) ∶ int
ex-9-1-1 = T-App (T-Var refl (concretion ([ int ] , refl))) T-Int
{-
f:'a .('a) -> 'a |- f(3) : int by T-App {
  f:'a .('a) -> 'a |- f : (int) -> int by T-Var {};
  f:'a .('a) -> 'a |- 3 : int by T-Int {};
};
-}

ex-9-1-2 : ● ⊱ ("f" , [ "a" ] ̣ ′ "a" ⇀ ′ "a") ⊢ app (var "f") (fun "x" ⇒ var "x" ⊕ i (+ 3)) ∶ int ⇀ int
ex-9-1-2 = T-App (T-Var refl (concretion ([ int ⇀ int ] , refl))) (T-Abs (T-Plus (T-Var refl raw) T-Int))
{-
f:'a .('a) -> 'a |- f((fun x -> (x + 3))) : (int) -> int by T-App {
  f:'a .('a) -> 'a |- f : ((int) -> int) -> (int) -> int by T-Var {};
  f:'a .('a) -> 'a |- (fun x -> (x + 3)) : (int) -> int by T-Abs {
    f:'a .('a) -> 'a,x:int |- (x + 3) : int by T-Plus {
      f:'a .('a) -> 'a,x:int |- x : int by T-Var {};
      f:'a .('a) -> 'a,x:int |- 3 : int by T-Int {};
    };
  };
};
-}

ex-9-1-3 : ● ⊢ ℓet "id" ≔ fun "x" ⇒ var "x" ιn app (var "id") (var "id") ∶ bool ⇀ bool
ex-9-1-3 = T-Let (T-Abs (T-Var refl raw))
                 (T-App (T-Var refl (concretion ([ bool ⇀ bool ] , refl)))
                        (T-Var refl (concretion ([ bool ] , refl))))
                 (refl , refl)
{-
|- let id = fun x -> x in id id : bool -> bool by T-Let {
  |- fun x -> x : 'a -> 'a by T-Abs {
    x: 'a |- x : 'a by T-Var {};
  };
  id: 'a.'a -> 'a |- id id : bool -> bool by T-App {
    id: 'a.'a -> 'a |- id : (bool -> bool) -> bool -> bool by T-Var {};
    id: 'a.'a -> 'a |- id : bool -> bool by T-Var {};
  };
};
-}

q111 : ● ⊱ ("f" , ("a" ◂ [ "b" ]) ̣ ′ "a" ⇀ ′ "b" ⇀ ′ "a" ) ⊢
       app (app (var "f") (i (+ 3))) (b true) ⊕ app (app (var "f") (i (+ 2))) (i (+ 4)) ∶ int
q111 = T-Plus (T-App (T-App (T-Var refl (concretion ((int ◂ [ bool ]) , refl))) T-Int) T-Bool)
              (T-App (T-App (T-Var refl (concretion ((int ◂ [ int ]) , refl))) T-Int) T-Int)
{-
f: 'a 'b.'a->'b->'a |- f 3 true + f 2 4  : int by T-Plus {
  f: 'a 'b.'a->'b->'a |- f 3 true : int by T-App {
    f: 'a 'b.'a->'b->'a |- f 3 : bool -> int by T-App {
      f: 'a 'b.'a->'b->'a |- f : int -> bool -> int by T-Var {};
      f: 'a 'b.'a->'b->'a |- 3 : int by T-Int {};
    };
    f: 'a 'b.'a->'b->'a |- true : bool by T-Bool {};
  };
  f: 'a 'b.'a->'b->'a |- f 2 4 : int by T-App {
    f: 'a 'b.'a->'b->'a |- f 2 : int -> int by T-App {
      f: 'a 'b.'a->'b->'a |- f : int -> int -> int by T-Var {};
      f: 'a 'b.'a->'b->'a |- 2 : int by T-Int {};
    };
    f: 'a 'b.'a->'b->'a |- 4 : int by T-Int {};
  };
};
-}

ex-9-1-4 : ● ⊢ ℓet "k" ≔ fun "x" ⇒ fun "y" ⇒ var "x" ιn
                   (app (app (var "k") (i (+ 3))) (b true)) ∷ (app (app (var "k") ((i (+ 1)) ∷ [])) (i (+ 3)))
                ∶ int list
ex-9-1-4 = T-Let (T-Abs (T-Abs (T-Var refl raw)))
                 (T-Cons (T-App (T-App (T-Var refl (concretion ((int ◂ [ bool ]) , refl))) T-Int) T-Bool)
                         (T-App (T-App (T-Var refl (concretion ((int list) ◂ [ int ] , refl)))
                                       (T-Cons T-Int T-Nil))
                                T-Int))
                 (refl , refl)
{-
|- let k = fun x -> fun y -> x in (k 3 true) :: (k (1 :: []) 3) : int list by T-Let {
  |- fun x -> fun y -> x : 'a -> 'b -> 'a by T-Abs {
    x: 'a |- fun y -> x : 'b -> 'a by T-Abs {
      x: 'a, y: 'b |- x : 'a by T-Var {};
    };
  };
  k: 'a 'b.'a->'b->'a |- (k 3 true) :: (k (1 :: []) 3) : int list by T-Cons {
    k: 'a 'b.'a->'b->'a |- k 3 true : int by T-App {
      k: 'a 'b.'a->'b->'a |- k 3 : bool -> int by T-App {
        k: 'a 'b.'a->'b->'a |- k : int -> bool -> int by T-Var {};
        k: 'a 'b.'a->'b->'a |- 3 : int by T-Int {};
      };
      k: 'a 'b.'a->'b->'a |- true : bool by T-Bool {};
    };
    k: 'a 'b.'a->'b->'a |- k (1 :: []) 3 : int list by T-App {
      k: 'a 'b.'a->'b->'a |- k (1 :: []) : int -> int list by T-App {
        k: 'a 'b.'a->'b->'a |- k : int list -> int -> int list by T-Var {};
        k: 'a 'b.'a->'b->'a |- 1 :: [] : int list by T-Cons {
          k: 'a 'b.'a->'b->'a |- 1 : int by T-Int {};
          k: 'a 'b.'a->'b->'a |- [] : int list by T-Nil {};
        };
      };
      k: 'a 'b.'a->'b->'a |- 3 : int by T-Int {};
    };
  };
};
-}

ex-9-1-5 : ● ⊢ ℓet "compose" ≔ fun "f" ⇒ fun "g" ⇒ fun "x" ⇒ app (var "f") (app (var "g") (var "x")) ιn
                ℓet "f" ≔ fun "x" ⇒ if var "x" then i (+ 3) else i (+ 4) ιn
                ℓet "g" ≔ fun "x" ⇒ var "x" ≺ i (+ 4) ιn
                app (app (app (var "compose") (var "f"))
                         (app (app (var "compose") (var "g"))
                                   (var "f")))
                    (b true) ∶ int
ex-9-1-5 = T-Let (T-Abs (T-Abs (T-Abs (T-App (T-Var refl raw)
                                             (T-App (T-Var refl raw)
                                                    (T-Var refl raw))))))
                 (T-Let (T-Abs (T-If (T-Var refl raw) T-Int T-Int))
                        (T-Let (T-Abs (T-Lt (T-Var refl raw) T-Int))
                               (T-App (T-App (T-App (T-Var refl (concretion ((bool ⇀ int) ◂ [ int ⇀ bool ] , refl)))
                                                    (T-Var refl (concretion ([ bool ] , refl))))
                                             (T-App (T-App (T-Var refl (concretion (((bool ⇀ int) ◂ [ int ⇀ bool ]) , refl)))
                                                           (T-Var refl (concretion ([ int ] , refl))))
                                                    (T-Var refl (concretion ([ bool ] , refl)))))
                                      T-Bool)
                               (refl , refl))
                        (refl , refl))
                 (refl , refl)
{-
-}
