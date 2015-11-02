module ex9 where

open import BCoPL.PolyTypingML4
open import BCoPL.Show.PolyTypingML4

q107 : ● ⊢ fun "x" ⇒ var "x" ∶ ′ "a" ⇀ ′ "a"
q107 = T-Abs (T-Var "x" (t (′ "a")) refl raw)
{-
|- (fun x -> x) : ('a) -> 'a by T-Abs {
  x:'a |- x : 'a by T-Var {};
};
-}

ex-9-1-1 : ● ⊱ ("f" , [ "a" ] ̣ ′ "a" ⇀ ′ "a") ⊢ app (var "f") (i (+ 3)) ∶ int
ex-9-1-1 = T-App (T-Var "f" ([ "a" ] ̣ ′ "a" ⇀ ′ "a") refl (concretion ([ int ] , refl))) T-Int
{-
f:'a .('a) -> 'a |- f(3) : int by T-App {
  f:'a .('a) -> 'a |- f : (int) -> int by T-Var {};
  f:'a .('a) -> 'a |- 3 : int by T-Int {};
};
-}

ex-9-1-2 : ● ⊱ ("f" , [ "a" ] ̣ ′ "a" ⇀ ′ "a") ⊢ app (var "f") (fun "x" ⇒ var "x" ⊕ i (+ 3)) ∶ int ⇀ int
ex-9-1-2 = T-App (T-Var "f" ([ "a" ] ̣ ′ "a" ⇀ ′ "a") refl (concretion ([ int ⇀ int ] , refl)))
                 (T-Abs (T-Plus (T-Var "x" (t int) refl raw) T-Int))
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
ex-9-1-3 = T-Let {!!}
                 (T-Abs (T-Var "x" (t (′ "a")) refl raw))
                 (T-App (T-Var "id" ([ "a" ] ̣ ′ "a" ⇀ ′ "a") refl (concretion ([ bool ⇀ bool ] , refl)))
                        (T-Var "id" ([ "a" ] ̣ ′ "a" ⇀ ′ "a") refl (concretion ([ bool ] , refl))))
                 (refl , refl)
{-
|- let id = (fun x -> x) in id(id) : (bool) -> bool by T-Let {
  |- (fun x -> x) : ('a) -> 'a by T-Abs {
    x:'a |- x : 'a by T-Var {};
  };
  id:'a .('a) -> 'a |- id(id) : (bool) -> bool by T-App {
    id:'a .('a) -> 'a |- id : ((bool) -> bool) -> (bool) -> bool by T-Var {};
    id:'a .('a) -> 'a |- id : (bool) -> bool by T-Var {};
  };
};
-}

q111 : ● ⊱ ("f" , ("a" ◂ [ "b" ]) ̣ ′ "a" ⇀ ′ "b" ⇀ ′ "a" ) ⊢
       app (app (var "f") (i (+ 3))) (b true) ⊕ app (app (var "f") (i (+ 2))) (i (+ 4)) ∶ int
q111 = T-Plus (T-App (T-App (T-Var "f"
                                   (("a" ◂ [ "b" ]) ̣ ′ "a" ⇀ ′ "b" ⇀ ′ "a")
                                   refl
                                   (concretion ((int ◂ [ bool ]) , refl))) T-Int) T-Bool)
              (T-App (T-App (T-Var "f"
                                   (("a" ◂ [ "b" ]) ̣ ′ "a" ⇀ ′ "b" ⇀ ′ "a")
                                   refl
                                   (concretion ((int ◂ [ int ]) , refl))) T-Int) T-Int)
{-
f:'a 'b .('a) -> ('b) -> 'a |- (f(3)(true) + f(2)(4)) : int by T-Plus {
  f:'a 'b .('a) -> ('b) -> 'a |- f(3)(true) : int by T-App {
    f:'a 'b .('a) -> ('b) -> 'a |- f(3) : (bool) -> int by T-App {
      f:'a 'b .('a) -> ('b) -> 'a |- f : (int) -> (bool) -> int by T-Var {};
      f:'a 'b .('a) -> ('b) -> 'a |- 3 : int by T-Int {};
    };
    f:'a 'b .('a) -> ('b) -> 'a |- true : bool by T-Bool {};
  };
  f:'a 'b .('a) -> ('b) -> 'a |- f(2)(4) : int by T-App {
    f:'a 'b .('a) -> ('b) -> 'a |- f(2) : (int) -> int by T-App {
      f:'a 'b .('a) -> ('b) -> 'a |- f : (int) -> (int) -> int by T-Var {};
      f:'a 'b .('a) -> ('b) -> 'a |- 2 : int by T-Int {};
    };
    f:'a 'b .('a) -> ('b) -> 'a |- 4 : int by T-Int {};
  };
};
-}

ex-9-1-4 : ● ⊢ ℓet "k" ≔ fun "x" ⇒ fun "y" ⇒ var "x" ιn
                   (app (app (var "k") (i (+ 3))) (b true)) ∷ (app (app (var "k") ((i (+ 1)) ∷ [])) (i (+ 3)))
                ∶ int list
ex-9-1-4 = T-Let {!!}
                 (T-Abs (T-Abs (T-Var "x" (t (′ "a")) refl raw)))
                 (T-Cons (T-App (T-App (T-Var "k"
                                              (("a" ◂ [ "b" ]) ̣ ′ "a" ⇀ ′ "b" ⇀ ′ "a")
                                              refl
                                              (concretion ((int ◂ [ bool ]) , refl)))
                                       T-Int) T-Bool)
                         (T-App (T-App (T-Var "k"
                                              (("a" ◂ [ "b" ]) ̣ ′ "a" ⇀ ′ "b" ⇀ ′ "a")
                                              refl (concretion ((int list) ◂ [ int ] , refl)))
                                       (T-Cons T-Int T-Nil))
                                T-Int))
                 (refl , refl)
{-
|- let k = (fun x -> (fun y -> x)) in (k(3)(true) :: k((1 :: []))(3)) : ((int) list) by T-Let {
  |- (fun x -> (fun y -> x)) : ('a) -> ('b) -> 'a by T-Abs {
    x:'a |- (fun y -> x) : ('b) -> 'a by T-Abs {
      x:'a,y:'b |- x : 'a by T-Var {};
    };
  };
  k:'a 'b .('a) -> ('b) -> 'a |- (k(3)(true) :: k((1 :: []))(3)) : ((int) list) by T-Cons {
    k:'a 'b .('a) -> ('b) -> 'a |- k(3)(true) : int by T-App {
      k:'a 'b .('a) -> ('b) -> 'a |- k(3) : (bool) -> int by T-App {
        k:'a 'b .('a) -> ('b) -> 'a |- k : (int) -> (bool) -> int by T-Var {};
        k:'a 'b .('a) -> ('b) -> 'a |- 3 : int by T-Int {};
      };
      k:'a 'b .('a) -> ('b) -> 'a |- true : bool by T-Bool {};
    };
    k:'a 'b .('a) -> ('b) -> 'a |- k((1 :: []))(3) : ((int) list) by T-App {
      k:'a 'b .('a) -> ('b) -> 'a |- k((1 :: [])) : (int) -> ((int) list) by T-App {
        k:'a 'b .('a) -> ('b) -> 'a |- k : (((int) list)) -> (int) -> ((int) list) by T-Var {};
        k:'a 'b .('a) -> ('b) -> 'a |- (1 :: []) : ((int) list) by T-Cons {
          k:'a 'b .('a) -> ('b) -> 'a |- 1 : int by T-Int {};
          k:'a 'b .('a) -> ('b) -> 'a |- [] : ((int) list) by T-Nil {};
        };
      };
      k:'a 'b .('a) -> ('b) -> 'a |- 3 : int by T-Int {};
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
ex-9-1-5 = T-Let {!!}
                 (T-Abs (T-Abs (T-Abs (T-App (T-Var "f" (t (′ "b" ⇀ ′ "c")) refl raw)
                                             (T-App (T-Var "g" (t (′ "a" ⇀ ′ "b")) refl raw)
                                                    (T-Var "x" (t (′ "a")) refl raw))))))
                 (T-Let {!!}
                        (T-Abs (T-If (T-Var "x" (t bool) refl raw)
                                     T-Int
                                     T-Int))
                        (T-Let {!!}
                               (T-Abs (T-Lt (T-Var "x" (t int) refl raw)
                                            T-Int))
                               (T-App (T-App (T-App (T-Var "compose" ("a" ◂ ("b" ◂ [ "c" ]) ̣ (′ "b" ⇀ ′ "c") ⇀ (′ "a" ⇀ ′ "b") ⇀ ′ "a" ⇀ ′ "c") refl (concretion (bool ◂ (bool ◂ [ int ]) , refl)))
                                                    (T-Var "f" (("b" ◂ [ "c" ]) ̣ bool ⇀ int)
                                                           refl (concretion ((bool ◂ [ int ]) , refl))))
                                             (T-App (T-App (T-Var "compose" ("a" ◂ ("b" ◂ [ "c" ]) ̣ (′ "b" ⇀ ′ "c") ⇀ (′ "a" ⇀ ′ "b") ⇀ ′ "a" ⇀ ′ "c")
                                                                            refl (concretion (bool ◂ (int ◂ [ bool ]) , refl)))
                                                           (T-Var "g" (("a" ◂ [ "b" ]) ̣ int ⇀ bool)
                                                                  refl (concretion ((int ◂ [ bool ]) , refl))))
                                                    (T-Var "f" (("b" ◂ [ "c" ]) ̣ bool ⇀ int)
                                                           refl (concretion ((bool ◂ [ int ]) , refl)))))
                                      T-Bool)
                               (refl , refl))
                        (refl , refl))
                 (refl , refl)

{-
|- let compose = (fun f -> (fun g -> (fun x -> f(g(x))))) in let f = (fun x -> if x then 3 else 4) in let g = (fun x -> (x < 4)) in compose(f)(compose(g)(f))(true) : int by T-Let {
  |- (fun f -> (fun g -> (fun x -> f(g(x))))) : (('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c by T-Abs {
    f:('b) -> 'c |- (fun g -> (fun x -> f(g(x)))) : (('a) -> 'b) -> ('a) -> 'c by T-Abs {
      f:('b) -> 'c,g:('a) -> 'b |- (fun x -> f(g(x))) : ('a) -> 'c by T-Abs {
        f:('b) -> 'c,g:('a) -> 'b,x:'a |- f(g(x)) : 'c by T-App {
          f:('b) -> 'c,g:('a) -> 'b,x:'a |- f : ('b) -> 'c by T-Var {};
          f:('b) -> 'c,g:('a) -> 'b,x:'a |- g(x) : 'b by T-App {
            f:('b) -> 'c,g:('a) -> 'b,x:'a |- g : ('a) -> 'b by T-Var {};
            f:('b) -> 'c,g:('a) -> 'b,x:'a |- x : 'a by T-Var {};
          };
        };
      };
    };
  };
  compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c |- let f = (fun x -> if x then 3 else 4) in let g = (fun x -> (x < 4)) in compose(f)(compose(g)(f))(true) : int by T-Let {
    compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c |- (fun x -> if x then 3 else 4) : (bool) -> int by T-Abs {
      compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,x:bool |- if x then 3 else 4 : int by T-If {
        compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,x:bool |- x : bool by T-Var {};
        compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,x:bool |- 3 : int by T-Int {};
        compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,x:bool |- 4 : int by T-Int {};
      };
    };
    compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int |- let g = (fun x -> (x < 4)) in compose(f)(compose(g)(f))(true) : int by T-Let {
      compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int |- (fun x -> (x < 4)) : (int) -> bool by T-Abs {
        compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,x:int |- (x < 4) : bool by T-Lt {
          compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,x:int |- x : int by T-Var {};
          compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,x:int |- 4 : int by T-Int {};
        };
      };
      compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,g:'a 'b .(int) -> bool |- compose(f)(compose(g)(f))(true) : int by T-App {
        compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,g:'a 'b .(int) -> bool |- compose(f)(compose(g)(f)) : (bool) -> int by T-App {
          compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,g:'a 'b .(int) -> bool |- compose(f) : ((bool) -> bool) -> (bool) -> int by T-App {
            compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,g:'a 'b .(int) -> bool |- compose : ((bool) -> int) -> ((bool) -> bool) -> (bool) -> int by T-Var {};
            compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,g:'a 'b .(int) -> bool |- f : (bool) -> int by T-Var {};
          };
          compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,g:'a 'b .(int) -> bool |- compose(g)(f) : (bool) -> bool by T-App {
            compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,g:'a 'b .(int) -> bool |- compose(g) : ((bool) -> int) -> (bool) -> bool by T-App {
              compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,g:'a 'b .(int) -> bool |- compose : ((int) -> bool) -> ((bool) -> int) -> (bool) -> bool by T-Var {};
              compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,g:'a 'b .(int) -> bool |- g : (int) -> bool by T-Var {};
            };
            compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,g:'a 'b .(int) -> bool |- f : (bool) -> int by T-Var {};
          };
        };
        compose:'a 'b 'c .(('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,f:'b 'c .(bool) -> int,g:'a 'b .(int) -> bool |- true : bool by T-Bool {};
      };
    };
  };
};
-}

ex-9-1-6 : ● ⊢ ℓet "twice" ≔ fun "f" ⇒ fun "x" ⇒ app (var "f") (app (var "f") (var "x")) ιn
                app (app (var "twice") (fun "x" ⇒ var "x" ⊕ i (+ 4))) (i (+ 5)) ∶ int
ex-9-1-6 = T-Let {!!}
                 (T-Abs (T-Abs (T-App (T-Var "f" (t (′ "a" ⇀ ′ "a")) refl raw)
                                      (T-App (T-Var "f" (t (′ "a" ⇀ ′ "a")) refl raw)
                                             (T-Var "x" (t (′ "a")) refl raw)))))
                 (T-App (T-App (T-Var "twice" ([ "a" ] ̣ (′ "a" ⇀ ′ "a") ⇀ ′ "a" ⇀ ′ "a") refl (concretion ([ int ] , refl)))
                               (T-Abs (T-Plus (T-Var "x" (t int) refl raw) T-Int)))
                        T-Int)
                 (refl , refl)
{-
|- let twice = (fun f -> (fun x -> f(f(x)))) in twice((fun x -> (x + 4)))(5) : int by T-Let {
  |- (fun f -> (fun x -> f(f(x)))) : (('a) -> 'a) -> ('a) -> 'a by T-Abs {
    f:('a) -> 'a |- (fun x -> f(f(x))) : ('a) -> 'a by T-Abs {
      f:('a) -> 'a,x:'a |- f(f(x)) : 'a by T-App {
        f:('a) -> 'a,x:'a |- f : ('a) -> 'a by T-Var {};
        f:('a) -> 'a,x:'a |- f(x) : 'a by T-App {
          f:('a) -> 'a,x:'a |- f : ('a) -> 'a by T-Var {};
          f:('a) -> 'a,x:'a |- x : 'a by T-Var {};
        };
      };
    };
  };
  twice:'a .(('a) -> 'a) -> ('a) -> 'a |- twice((fun x -> (x + 4)))(5) : int by T-App {
    twice:'a .(('a) -> 'a) -> ('a) -> 'a |- twice((fun x -> (x + 4))) : (int) -> int by T-App {
      twice:'a .(('a) -> 'a) -> ('a) -> 'a |- twice : ((int) -> int) -> (int) -> int by T-Var {};
      twice:'a .(('a) -> 'a) -> ('a) -> 'a |- (fun x -> (x + 4)) : (int) -> int by T-Abs {
        twice:'a .(('a) -> 'a) -> ('a) -> 'a,x:int |- (x + 4) : int by T-Plus {
          twice:'a .(('a) -> 'a) -> ('a) -> 'a,x:int |- x : int by T-Var {};
          twice:'a .(('a) -> 'a) -> ('a) -> 'a,x:int |- 4 : int by T-Int {};
        };
      };
    };
    twice:'a .(('a) -> 'a) -> ('a) -> 'a |- 5 : int by T-Int {};
  };
};
-}

ex-9-1-7 : ● ⊢ ℓet "twice" ≔ fun "f" ⇒ fun "x" ⇒ app (var "f") (app (var "f") (var "x")) ιn
                app (app (app (var "twice") (var "twice")) (fun "x" ⇒ var "x" ⊕ i (+ 4))) (i (+ 5)) ∶ int
ex-9-1-7 = T-Let {!!}
                 (T-Abs (T-Abs (T-App (T-Var "f" (t (′ "a" ⇀ ′ "a")) refl raw)
                                      (T-App (T-Var "f" (t (′ "a" ⇀ ′ "a")) refl raw)
                                             (T-Var "x" (t (′ "a")) refl raw)))))
                 (T-App (T-App (T-App (T-Var "twice" ([ "a" ] ̣ (′ "a" ⇀ ′ "a") ⇀ ′ "a" ⇀ ′ "a")
                                             refl (concretion ([ int ⇀ int ] , refl)))
                                      (T-Var "twice" ([ "a" ] ̣ (′ "a" ⇀ ′ "a") ⇀ ′ "a" ⇀ ′ "a")
                                             refl (concretion ([ int ] , refl))))
                               (T-Abs (T-Plus (T-Var "x" (t int) refl raw) T-Int)))
                        T-Int)
                 (refl , refl)
{-
|- let twice = (fun f -> (fun x -> f(f(x)))) in twice(twice)((fun x -> (x + 4)))(5) : int by T-Let {
  |- (fun f -> (fun x -> f(f(x)))) : (('a) -> 'a) -> ('a) -> 'a by T-Abs {
    f:('a) -> 'a |- (fun x -> f(f(x))) : ('a) -> 'a by T-Abs {
      f:('a) -> 'a,x:'a |- f(f(x)) : 'a by T-App {
        f:('a) -> 'a,x:'a |- f : ('a) -> 'a by T-Var {};
        f:('a) -> 'a,x:'a |- f(x) : 'a by T-App {
          f:('a) -> 'a,x:'a |- f : ('a) -> 'a by T-Var {};
          f:('a) -> 'a,x:'a |- x : 'a by T-Var {};
        };
      };
    };
  };
  twice:'a .(('a) -> 'a) -> ('a) -> 'a |- twice(twice)((fun x -> (x + 4)))(5) : int by T-App {
    twice:'a .(('a) -> 'a) -> ('a) -> 'a |- twice(twice)((fun x -> (x + 4))) : (int) -> int by T-App {
      twice:'a .(('a) -> 'a) -> ('a) -> 'a |- twice(twice) : ((int) -> int) -> (int) -> int by T-App {
        twice:'a .(('a) -> 'a) -> ('a) -> 'a |- twice : (((int) -> int) -> (int) -> int) -> ((int) -> int) -> (int) -> int by T-Var {};
        twice:'a .(('a) -> 'a) -> ('a) -> 'a |- twice : ((int) -> int) -> (int) -> int by T-Var {};
      };
      twice:'a .(('a) -> 'a) -> ('a) -> 'a |- (fun x -> (x + 4)) : (int) -> int by T-Abs {
        twice:'a .(('a) -> 'a) -> ('a) -> 'a,x:int |- (x + 4) : int by T-Plus {
          twice:'a .(('a) -> 'a) -> ('a) -> 'a,x:int |- x : int by T-Var {};
          twice:'a .(('a) -> 'a) -> ('a) -> 'a,x:int |- 4 : int by T-Int {};
        };
      };
    };
    twice:'a .(('a) -> 'a) -> ('a) -> 'a |- 5 : int by T-Int {};
  };
};
-}

q116 : ● ⊢ ℓet "s" ≔ fun "f" ⇒ fun "g" ⇒ fun "x" ⇒ app (app (var "f") (var "x")) (app (var "g") (var "x")) ιn
            ℓet "k" ≔ fun "x" ⇒ fun "y" ⇒ var "x" ιn
            app (app (var "s") (var "k")) (var "k") ∶ ′ "a" ⇀ ′ "a"
q116 = T-Let {!!}
             (T-Abs (T-Abs (T-Abs (T-App (T-App (T-Var "f" (t (′ "a" ⇀ ′ "b" ⇀ ′ "c")) refl raw)
                                                (T-Var "x" (t (′ "a")) refl raw))
                                         (T-App (T-Var "g" (t (′ "a" ⇀ ′ "b")) refl raw)
                                                (T-Var "x" (t (′ "a")) refl raw))))))
             (T-Let {!!}
                    (T-Abs (T-Abs (T-Var "x" (t (′ "a")) refl raw)))
                    (T-App (T-App (T-Var "s" ("a" ◂ ("b" ◂ [ "c" ]) ̣
                                             (′ "a" ⇀ ′ "b" ⇀ ′ "c") ⇀ (′ "a" ⇀ ′ "b") ⇀ ′ "a" ⇀ ′ "c")
                                             refl (concretion (′ "a" ◂ ((′ "b" ⇀ ′ "a") ◂ [ ′ "a" ]) , refl)))
                                  (T-Var "k" (("a" ◂ [ "b" ]) ̣ ′ "a" ⇀ ′ "b" ⇀ ′ "a")
                                         refl (concretion ((′ "a" ◂ [ ′ "b" ⇀ ′ "a" ]) , refl))))
                           (T-Var "k" (("a" ◂ [ "b" ]) ̣ ′ "a" ⇀ ′ "b" ⇀ ′ "a")
                                  refl (concretion ((′ "a" ◂ [ ′ "b" ]) , refl))))
                    (refl , refl))
             (refl , refl)
{-
|- let s = (fun f -> (fun g -> (fun x -> f(x)(g(x))))) in let k = (fun x -> (fun y -> x)) in s(k)(k) : ('a) -> 'a by T-Let {
  |- (fun f -> (fun g -> (fun x -> f(x)(g(x))))) : (('a) -> ('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c by T-Abs {
    f:('a) -> ('b) -> 'c |- (fun g -> (fun x -> f(x)(g(x)))) : (('a) -> 'b) -> ('a) -> 'c by T-Abs {
      f:('a) -> ('b) -> 'c,g:('a) -> 'b |- (fun x -> f(x)(g(x))) : ('a) -> 'c by T-Abs {
        f:('a) -> ('b) -> 'c,g:('a) -> 'b,x:'a |- f(x)(g(x)) : 'c by T-App {
          f:('a) -> ('b) -> 'c,g:('a) -> 'b,x:'a |- f(x) : ('b) -> 'c by T-App {
            f:('a) -> ('b) -> 'c,g:('a) -> 'b,x:'a |- f : ('a) -> ('b) -> 'c by T-Var {};
            f:('a) -> ('b) -> 'c,g:('a) -> 'b,x:'a |- x : 'a by T-Var {};
          };
          f:('a) -> ('b) -> 'c,g:('a) -> 'b,x:'a |- g(x) : 'b by T-App {
            f:('a) -> ('b) -> 'c,g:('a) -> 'b,x:'a |- g : ('a) -> 'b by T-Var {};
            f:('a) -> ('b) -> 'c,g:('a) -> 'b,x:'a |- x : 'a by T-Var {};
          };
        };
      };
    };
  };
  s:'a 'b 'c .(('a) -> ('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c |- let k = (fun x -> (fun y -> x)) in s(k)(k) : ('a) -> 'a by T-Let {
    s:'a 'b 'c .(('a) -> ('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c |- (fun x -> (fun y -> x)) : ('a) -> ('b) -> 'a by T-Abs {
      s:'a 'b 'c .(('a) -> ('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,x:'a |- (fun y -> x) : ('b) -> 'a by T-Abs {
        s:'a 'b 'c .(('a) -> ('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,x:'a,y:'b |- x : 'a by T-Var {};
      };
    };
    s:'a 'b 'c .(('a) -> ('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,k:'a 'b .('a) -> ('b) -> 'a |- s(k)(k) : ('a) -> 'a by T-App {
      s:'a 'b 'c .(('a) -> ('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,k:'a 'b .('a) -> ('b) -> 'a |- s(k) : (('a) -> ('b) -> 'a) -> ('a) -> 'a by T-App {
        s:'a 'b 'c .(('a) -> ('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,k:'a 'b .('a) -> ('b) -> 'a |- s : (('a) -> (('b) -> 'a) -> 'a) -> (('a) -> ('b) -> 'a) -> ('a) -> 'a by T-Var {};
        s:'a 'b 'c .(('a) -> ('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,k:'a 'b .('a) -> ('b) -> 'a |- k : ('a) -> (('b) -> 'a) -> 'a by T-Var {};
      };
      s:'a 'b 'c .(('a) -> ('b) -> 'c) -> (('a) -> 'b) -> ('a) -> 'c,k:'a 'b .('a) -> ('b) -> 'a |- k : ('a) -> ('b) -> 'a by T-Var {};
    };
  };
};
-}

ex-9-1-8 : ● ⊢ ℓet "x" ≔ [] ιn
                ℓet "y" ≔ i (+ 3) ∷ var "x" ιn
                b true ∷ var "x" ∶ bool list
ex-9-1-8 = T-Let [ "a" ] T-Nil
                 (T-Let [ "a" ]
                        (T-Cons T-Int (T-Var "x" ([ "a" ] ̣ ′ "a" list) refl (concretion ([ int ] , refl))))
                        (T-Cons T-Bool (T-Var "x" ([ "a" ] ̣ ′ "a" list) refl (concretion ([ bool ] , refl))))
                        (refl , refl))
                 (refl , refl)
{-
|- let x = [] in let y = (3 :: x) in (true :: x) : ((bool) list) by T-Let {
  |- [] : (('a) list) by T-Nil {};
  x:'a .(('a) list) |- let y = (3 :: x) in (true :: x) : ((bool) list) by T-Let {
    x:'a .(('a) list) |- (3 :: x) : ((int) list) by T-Cons {
      x:'a .(('a) list) |- 3 : int by T-Int {};
      x:'a .(('a) list) |- x : ((int) list) by T-Var {};
    };
    x:'a .(('a) list),y:'a .((int) list) |- (true :: x) : ((bool) list) by T-Cons {
      x:'a .(('a) list),y:'a .((int) list) |- true : bool by T-Bool {};
      x:'a .(('a) list),y:'a .((int) list) |- x : ((bool) list) by T-Var {};
    };
  };
};
-}

ex-9-1-9 : ● ⊢ ℓet "l" ≔ (fun "x" ⇒ var "x") ∷ [] ιn
                ℓet "l1" ≔ (fun "y" ⇒ var "y" ⊕ i (+ 1)) ∷ var "l" ιn
                (fun "z" ⇒ if var "z" then b false else b true) ∷ var "l" ∶ (bool ⇀ bool) list
ex-9-1-9 = T-Let [ "a" ]
                 (T-Cons (T-Abs (T-Var "x" (t (′ "a")) refl raw)) T-Nil)
                 (T-Let [ "a" ]
                        (T-Cons (T-Abs (T-Plus (T-Var "y" (t int) refl raw) T-Int))
                                (T-Var "l" ([ "a" ] ̣ (′ "a" ⇀ ′ "a") list) refl (concretion ([ int ] , refl))))
                        (T-Cons (T-Abs (T-If (T-Var "z" (t bool) refl raw) T-Bool T-Bool))
                                (T-Var "l" ([ "a" ] ̣ (′ "a" ⇀ ′ "a") list) refl (concretion ([ bool ] , refl))))
                        (refl , refl))
                 (refl , refl)
{-
|- let l = ((fun x -> x) :: []) in let l1 = ((fun y -> (y + 1)) :: l) in ((fun z -> if z then false else true) :: l) : (((bool) -> bool) list) by T-Let {
  |- ((fun x -> x) :: []) : ((('a) -> 'a) list) by T-Cons {
    |- (fun x -> x) : ('a) -> 'a by T-Abs {
      x:'a |- x : 'a by T-Var {};
    };
    |- [] : ((('a) -> 'a) list) by T-Nil {};
  };
  l:'a .((('a) -> 'a) list) |- let l1 = ((fun y -> (y + 1)) :: l) in ((fun z -> if z then false else true) :: l) : (((bool) -> bool) list) by T-Let {
    l:'a .((('a) -> 'a) list) |- ((fun y -> (y + 1)) :: l) : (((int) -> int) list) by T-Cons {
      l:'a .((('a) -> 'a) list) |- (fun y -> (y + 1)) : (int) -> int by T-Abs {
        l:'a .((('a) -> 'a) list),y:int |- (y + 1) : int by T-Plus {
          l:'a .((('a) -> 'a) list),y:int |- y : int by T-Var {};
          l:'a .((('a) -> 'a) list),y:int |- 1 : int by T-Int {};
        };
      };
      l:'a .((('a) -> 'a) list) |- l : (((int) -> int) list) by T-Var {};
    };
    l:'a .((('a) -> 'a) list),l1:'a .(((int) -> int) list) |- ((fun z -> if z then false else true) :: l) : (((bool) -> bool) list) by T-Cons {
      l:'a .((('a) -> 'a) list),l1:'a .(((int) -> int) list) |- (fun z -> if z then false else true) : (bool) -> bool by T-Abs {
        l:'a .((('a) -> 'a) list),l1:'a .(((int) -> int) list),z:bool |- if z then false else true : bool by T-If {
          l:'a .((('a) -> 'a) list),l1:'a .(((int) -> int) list),z:bool |- z : bool by T-Var {};
          l:'a .((('a) -> 'a) list),l1:'a .(((int) -> int) list),z:bool |- false : bool by T-Bool {};
          l:'a .((('a) -> 'a) list),l1:'a .(((int) -> int) list),z:bool |- true : bool by T-Bool {};
        };
      };
      l:'a .((('a) -> 'a) list),l1:'a .(((int) -> int) list) |- l : (((bool) -> bool) list) by T-Var {};
    };
  };
};
-}
