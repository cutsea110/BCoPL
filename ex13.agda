module ex13 where

open import BCoPL.EvalRefML3
open import BCoPL.Show.EvalRefML3

q141 : ● ⊱ ("@l" , i (+ 2)) ╱ ● ⊱ ("x" , ℓ "@l") ⊢ ! (var "x") ⊕ i (+ 3) ⇓ i (+ 5) ╱ ● ⊱ ("@l" , i (+ 2))
q141 = E-Plus (E-Deref (E-Var refl) refl)
              E-Int
              (B-Plus refl)
{-
@l = 2 / x = @l |- ((! x) + 3) evalto 5 / @l = 2 by E-Plus {
  @l = 2 / x = @l |- (! x) evalto 2 / @l = 2 by E-Deref {
    @l = 2 / x = @l |- x evalto @l / @l = 2 by E-Var {};
  };
  @l = 2 / x = @l |- 3 evalto 3 / @l = 2 by E-Int {};
  2 plus 3 is 5 by B-Plus {};
};
-}

q142 : ● ⊱ ("@l" , i (+ 2)) ╱ ● ⊱ ("x" , ℓ "@l") ⊢ var "x" ≔ ! (var "x") ⊕ i (+ 1) ⇓ i (+ 3) ╱ ● ⊱ ("@l" , i (+ 3))
q142 = E-Assign (E-Var refl)
                (E-Plus (E-Deref (E-Var refl) refl)
                        E-Int
                        (B-Plus refl))
                refl
{-
@l = 2 / x = @l |- (x := ((! x) + 1)) evalto 3 / @l = 3 by E-Assign {
  @l = 2 / x = @l |- x evalto @l / @l = 2 by E-Var {};
  @l = 2 / x = @l |- ((! x) + 1) evalto 3 / @l = 2 by E-Plus {
    @l = 2 / x = @l |- (! x) evalto 2 / @l = 2 by E-Deref {
      @l = 2 / x = @l |- x evalto @l / @l = 2 by E-Var {};
    };
    @l = 2 / x = @l |- 1 evalto 1 / @l = 2 by E-Int {};
    2 plus 1 is 3 by B-Plus {};
  };
};
-}

q143 : ● ╱ ● ⊢ ℓet "r" ≔ ref (b true) ιn ! (var "r") ⇓ b true ╱ ● ⊱ ("@l" , b true)
q143 = E-Let (E-Ref E-Bool refl)
             (E-Deref (E-Var refl) refl)
{-
|- let r = (ref true) in (! r) evalto true / @l = true by E-Let {
  |- (ref true) evalto @l / @l = true by E-Ref {
    |- true evalto true by E-Bool {};
  };
  @l = true / r = @l |- (! r) evalto true / @l = true by E-Deref {
    @l = true / r = @l |- r evalto @l / @l = true by E-Var {};
  };
};
-}

q144 : ● ╱ ● ⊢ ℓet "incr" ≔ fun "x" ⇒ (var "x" ≔ ! (var "x") ⊕ i (+ 1)) ιn
                 ℓet "x" ≔ ref (i (+ 0)) ιn
                 ℓet "z" ≔ app (var "incr") (var "x") ιn
                 ! (var "x") ⇓ i (+ 1) ╱ ● ⊱ ("@l" , i (+ 1))
q144 = E-Let E-Fun (E-Let (E-Ref {l = "@l"} E-Int refl)
                          (E-Let (E-App (E-Var refl)
                                        (E-Var refl)
                                        (E-Assign (E-Var refl)
                                                  (E-Plus (E-Deref (E-Var refl) refl) E-Int (B-Plus refl))
                                                  refl))
                                 (E-Deref (E-Var refl) refl)))
{-
|- let incr = (fun x -> (x := ((! x) + 1))) in let x = (ref 0) in let z = incr(x) in (! x) evalto 1 / @l = 1 by E-Let {
  |- (fun x -> (x := ((! x) + 1))) evalto ()[fun x -> (x := ((! x) + 1))] by E-Fun {};
  incr = ()[fun x -> (x := ((! x) + 1))] |- let x = (ref 0) in let z = incr(x) in (! x) evalto 1 / @l = 1 by E-Let {
    incr = ()[fun x -> (x := ((! x) + 1))] |- (ref 0) evalto @l / @l = 0 by E-Ref {
      incr = ()[fun x -> (x := ((! x) + 1))] |- 0 evalto 0 by E-Int {};
    };
    @l = 0 / incr = ()[fun x -> (x := ((! x) + 1))],x = @l |- let z = incr(x) in (! x) evalto 1 / @l = 1 by E-Let {
      @l = 0 / incr = ()[fun x -> (x := ((! x) + 1))],x = @l |- incr(x) evalto 1 / @l = 1 by E-App {
        @l = 0 / incr = ()[fun x -> (x := ((! x) + 1))],x = @l |- incr evalto ()[fun x -> (x := ((! x) + 1))] / @l = 0 by E-Var {};
        @l = 0 / incr = ()[fun x -> (x := ((! x) + 1))],x = @l |- x evalto @l / @l = 0 by E-Var {};
        @l = 0 / x = @l |- (x := ((! x) + 1)) evalto 1 / @l = 1 by E-Assign {
          @l = 0 / x = @l |- x evalto @l / @l = 0 by E-Var {};
          @l = 0 / x = @l |- ((! x) + 1) evalto 1 / @l = 0 by E-Plus {
            @l = 0 / x = @l |- (! x) evalto 0 / @l = 0 by E-Deref {
              @l = 0 / x = @l |- x evalto @l / @l = 0 by E-Var {};
            };
            @l = 0 / x = @l |- 1 evalto 1 / @l = 0 by E-Int {};
            0 plus 1 is 1 by B-Plus {};
          };
        };
      };
      @l = 1 / incr = ()[fun x -> (x := ((! x) + 1))],x = @l,z = 1 |- (! x) evalto 1 / @l = 1 by E-Deref {
        @l = 1 / incr = ()[fun x -> (x := ((! x) + 1))],x = @l,z = 1 |- x evalto @l / @l = 1 by E-Var {};
      };
    };
  };
};
-}

q145 : ● ╱ ● ⊢ ℓet "c" ≔
                   ℓet "x" ≔ ref (i (+ 0)) ιn
                   (fun "y" ⇒ if var "y" then var "x" ≔ ! (var "x") ⊕ i (+ 1) else ! (var "x")) ιn
                 ℓet "y" ≔ app (var "c") (b true) ιn
                 ℓet "y" ≔ app (var "c") (b true) ιn
                 app (var "c") (b false) ⇓ i (+ 2) ╱ ● ⊱ ("@l" , i (+ 2))
q145 = E-Let (E-Let (E-Ref {l = "@l"} E-Int refl)
                    E-Fun)
             (E-Let (E-App (E-Var refl)
                           E-Bool
                           (E-IfT (E-Var refl)
                                  (E-Assign (E-Var refl)
                                            (E-Plus (E-Deref (E-Var refl) refl) E-Int (B-Plus refl))
                                            refl)))
                    (E-Let (E-App (E-Var refl)
                                  E-Bool
                                  (E-IfT (E-Var refl)
                                         (E-Assign (E-Var refl)
                                                   (E-Plus (E-Deref (E-Var refl) refl) E-Int (B-Plus refl))
                                                   refl)))
                           (E-App (E-Var refl)
                                  E-Bool
                                  (E-IfF (E-Var refl)
                                         (E-Deref (E-Var refl) refl)))))
{-
|- let c = let x = (ref 0) in (fun y -> if y then (x := ((! x) + 1)) else (! x)) in let y = c(true) in let y = c(true) in c(false) evalto 2 / @l = 2 by E-Let {
  |- let x = (ref 0) in (fun y -> if y then (x := ((! x) + 1)) else (! x)) evalto (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l = 0 by E-Let {
    |- (ref 0) evalto @l / @l = 0 by E-Ref {
      |- 0 evalto 0 by E-Int {};
    };
    @l = 0 / x = @l |- (fun y -> if y then (x := ((! x) + 1)) else (! x)) evalto (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l = 0 by E-Fun {};
  };
  @l = 0 / c = (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- let y = c(true) in let y = c(true) in c(false) evalto 2 / @l = 2 by E-Let {
    @l = 0 / c = (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- c(true) evalto 1 / @l = 1 by E-App {
      @l = 0 / c = (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- c evalto (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l = 0 by E-Var {};
      @l = 0 / c = (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- true evalto true / @l = 0 by E-Bool {};
      @l = 0 / x = @l,y = true |- if y then (x := ((! x) + 1)) else (! x) evalto 1 / @l = 1 by E-IfT {
        @l = 0 / x = @l,y = true |- y evalto true / @l = 0 by E-Var {};
        @l = 0 / x = @l,y = true |- (x := ((! x) + 1)) evalto 1 / @l = 1 by E-Assign {
          @l = 0 / x = @l,y = true |- x evalto @l / @l = 0 by E-Var {};
          @l = 0 / x = @l,y = true |- ((! x) + 1) evalto 1 / @l = 0 by E-Plus {
            @l = 0 / x = @l,y = true |- (! x) evalto 0 / @l = 0 by E-Deref {
              @l = 0 / x = @l,y = true |- x evalto @l / @l = 0 by E-Var {};
            };
            @l = 0 / x = @l,y = true |- 1 evalto 1 / @l = 0 by E-Int {};
            0 plus 1 is 1 by B-Plus {};
          };
        };
      };
    };
    @l = 1 / c = (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 1 |- let y = c(true) in c(false) evalto 2 / @l = 2 by E-Let {
      @l = 1 / c = (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 1 |- c(true) evalto 2 / @l = 2 by E-App {
        @l = 1 / c = (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 1 |- c evalto (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l = 1 by E-Var {};
        @l = 1 / c = (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 1 |- true evalto true / @l = 1 by E-Bool {};
        @l = 1 / x = @l,y = true |- if y then (x := ((! x) + 1)) else (! x) evalto 2 / @l = 2 by E-IfT {
          @l = 1 / x = @l,y = true |- y evalto true / @l = 1 by E-Var {};
          @l = 1 / x = @l,y = true |- (x := ((! x) + 1)) evalto 2 / @l = 2 by E-Assign {
            @l = 1 / x = @l,y = true |- x evalto @l / @l = 1 by E-Var {};
            @l = 1 / x = @l,y = true |- ((! x) + 1) evalto 2 / @l = 1 by E-Plus {
              @l = 1 / x = @l,y = true |- (! x) evalto 1 / @l = 1 by E-Deref {
                @l = 1 / x = @l,y = true |- x evalto @l / @l = 1 by E-Var {};
              };
              @l = 1 / x = @l,y = true |- 1 evalto 1 / @l = 1 by E-Int {};
              1 plus 1 is 2 by B-Plus {};
            };
          };
        };
      };
      @l = 2 / c = (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 1,y = 2 |- c(false) evalto 2 / @l = 2 by E-App {
        @l = 2 / c = (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 1,y = 2 |- c evalto (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l = 2 by E-Var {};
        @l = 2 / c = (x = @l)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 1,y = 2 |- false evalto false / @l = 2 by E-Bool {};
        @l = 2 / x = @l,y = false |- if y then (x := ((! x) + 1)) else (! x) evalto 2 / @l = 2 by E-IfF {
          @l = 2 / x = @l,y = false |- y evalto false / @l = 2 by E-Var {};
          @l = 2 / x = @l,y = false |- (! x) evalto 2 / @l = 2 by E-Deref {
            @l = 2 / x = @l,y = false |- x evalto @l / @l = 2 by E-Var {};
          };
        };
      };
    };
  };
};
-}

q146 : ● ╱ ● ⊢ ℓet "newc" ≔ fun "x" ⇒
                   ℓet "x" ≔ ref (var "x") ιn
                   (fun "y" ⇒ if var "y" then var "x" ≔ ! (var "x") ⊕ i (+ 1) else ! (var "x")) ιn
                 ℓet "c1" ≔ app (var "newc") (i (+ 5)) ιn
                 ℓet "c2" ≔ app (var "newc") (i (+ 4)) ιn
                 ℓet "y" ≔ app (var "c1") (b true) ιn
                 ℓet "y" ≔ app (var "c2") (b true) ιn
                 app (var "c1") (b false) ⇓ i (+ 6) ╱ ● ⊱ ("@l1" , i (+ 6)) ⊱ ("@l2" , i (+ 5))
q146 = E-Let E-Fun
             (E-Let (E-App (E-Var refl)
                           E-Int
                           (E-Let (E-Ref {l = "@l1"} (E-Var refl) refl)
                                  E-Fun))
                    (E-Let (E-App (E-Var refl)
                                  E-Int
                                  (E-Let (E-Ref {l = "@l2"} (E-Var refl) refl)
                                         E-Fun))
                           (E-Let (E-App (E-Var refl)
                                         E-Bool
                                         (E-IfT (E-Var refl)
                                                (E-Assign (E-Var refl)
                                                          (E-Plus (E-Deref (E-Var refl) refl)
                                                                           E-Int
                                                                           (B-Plus refl))
                                                          refl)))
                                  (E-Let (E-App (E-Var refl)
                                                E-Bool
                                                (E-IfT (E-Var refl)
                                                       (E-Assign (E-Var refl)
                                                                 (E-Plus (E-Deref (E-Var refl) refl)
                                                                         E-Int
                                                                         (B-Plus refl))
                                                                 refl)))
                                         (E-App (E-Var refl)
                                                E-Bool
                                                (E-IfF (E-Var refl)
                                                       (E-Deref (E-Var refl) refl)))))))
{-
|- let newc = (fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))) in let c1 = newc(5) in let c2 = newc(4) in let y = c1(true) in let y = c2(true) in c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-Let {
  |- (fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))) evalto ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] by E-Fun {};
  newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] |- let c1 = newc(5) in let c2 = newc(4) in let y = c1(true) in let y = c2(true) in c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-Let {
    newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] |- newc(5) evalto (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5 by E-App {
      newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] |- newc evalto ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] by E-Var {};
      newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] |- 5 evalto 5 by E-Int {};
      x = 5 |- let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x)) evalto (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5 by E-Let {
        x = 5 |- (ref x) evalto @l1 / @l1 = 5 by E-Ref {
          x = 5 |- x evalto 5 by E-Var {};
        };
        @l1 = 5 / x = 5,x = @l1 |- (fun y -> if y then (x := ((! x) + 1)) else (! x)) evalto (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5 by E-Fun {};
      };
    };
    @l1 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- let c2 = newc(4) in let y = c1(true) in let y = c2(true) in c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-Let {
      @l1 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- newc(4) evalto (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5,@l2 = 4 by E-App {
        @l1 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- newc evalto ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] / @l1 = 5 by E-Var {};
        @l1 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- 4 evalto 4 / @l1 = 5 by E-Int {};
        @l1 = 5 / x = 4 |- let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x)) evalto (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5,@l2 = 4 by E-Let {
          @l1 = 5 / x = 4 |- (ref x) evalto @l2 / @l1 = 5,@l2 = 4 by E-Ref {
            @l1 = 5 / x = 4 |- x evalto 4 / @l1 = 5 by E-Var {};
          };
          @l1 = 5,@l2 = 4 / x = 4,x = @l2 |- (fun y -> if y then (x := ((! x) + 1)) else (! x)) evalto (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5,@l2 = 4 by E-Fun {};
        };
      };
      @l1 = 5,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- let y = c1(true) in let y = c2(true) in c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-Let {
        @l1 = 5,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- c1(true) evalto 6 / @l1 = 6,@l2 = 4 by E-App {
          @l1 = 5,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- c1 evalto (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5,@l2 = 4 by E-Var {};
          @l1 = 5,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- true evalto true / @l1 = 5,@l2 = 4 by E-Bool {};
          @l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- if y then (x := ((! x) + 1)) else (! x) evalto 6 / @l1 = 6,@l2 = 4 by E-IfT {
            @l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- y evalto true / @l1 = 5,@l2 = 4 by E-Var {};
            @l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- (x := ((! x) + 1)) evalto 6 / @l1 = 6,@l2 = 4 by E-Assign {
              @l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- x evalto @l1 / @l1 = 5,@l2 = 4 by E-Var {};
              @l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- ((! x) + 1) evalto 6 / @l1 = 5,@l2 = 4 by E-Plus {
                @l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- (! x) evalto 5 / @l1 = 5,@l2 = 4 by E-Deref {
                  @l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- x evalto @l1 / @l1 = 5,@l2 = 4 by E-Var {};
                };
                @l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- 1 evalto 1 / @l1 = 5,@l2 = 4 by E-Int {};
                5 plus 1 is 6 by B-Plus {};
              };
            };
          };
        };
        @l1 = 6,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6 |- let y = c2(true) in c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-Let {
          @l1 = 6,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6 |- c2(true) evalto 5 / @l1 = 6,@l2 = 5 by E-App {
            @l1 = 6,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6 |- c2 evalto (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 6,@l2 = 4 by E-Var {};
            @l1 = 6,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6 |- true evalto true / @l1 = 6,@l2 = 4 by E-Bool {};
            @l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- if y then (x := ((! x) + 1)) else (! x) evalto 5 / @l1 = 6,@l2 = 5 by E-IfT {
              @l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- y evalto true / @l1 = 6,@l2 = 4 by E-Var {};
              @l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- (x := ((! x) + 1)) evalto 5 / @l1 = 6,@l2 = 5 by E-Assign {
                @l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- x evalto @l2 / @l1 = 6,@l2 = 4 by E-Var {};
                @l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- ((! x) + 1) evalto 5 / @l1 = 6,@l2 = 4 by E-Plus {
                  @l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- (! x) evalto 4 / @l1 = 6,@l2 = 4 by E-Deref {
                    @l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- x evalto @l2 / @l1 = 6,@l2 = 4 by E-Var {};
                  };
                  @l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- 1 evalto 1 / @l1 = 6,@l2 = 4 by E-Int {};
                  4 plus 1 is 5 by B-Plus {};
                };
              };
            };
          };
          @l1 = 6,@l2 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6,y = 5 |- c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-App {
            @l1 = 6,@l2 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6,y = 5 |- c1 evalto (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 6,@l2 = 5 by E-Var {};
            @l1 = 6,@l2 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6,y = 5 |- false evalto false / @l1 = 6,@l2 = 5 by E-Bool {};
            @l1 = 6,@l2 = 5 / x = 5,x = @l1,y = false |- if y then (x := ((! x) + 1)) else (! x) evalto 6 / @l1 = 6,@l2 = 5 by E-IfF {
              @l1 = 6,@l2 = 5 / x = 5,x = @l1,y = false |- y evalto false / @l1 = 6,@l2 = 5 by E-Var {};
              @l1 = 6,@l2 = 5 / x = 5,x = @l1,y = false |- (! x) evalto 6 / @l1 = 6,@l2 = 5 by E-Deref {
                @l1 = 6,@l2 = 5 / x = 5,x = @l1,y = false |- x evalto @l1 / @l1 = 6,@l2 = 5 by E-Var {};
              };
            };
          };
        };
      };
    };
  };
};
-}

q147 : ● ╱ ● ⊢ ℓet "f" ≔ fun "r1" ⇒
                   (fun "r2" ⇒
                     ℓet "z" ≔ (var "r2" ≔ i (+ 3)) ιn
                     ! (var "r1")) ιn
                 ℓet "r" ≔ ref (i (+ 0)) ιn
                 app (app (var "f") (var "r")) (var "r") ⇓ i (+ 3) ╱ ● ⊱ ("@l" , i (+ 3))
q147 = E-Let E-Fun
             (E-Let (E-Ref {l = "@l"} E-Int refl)
                    (E-App (E-App (E-Var refl)
                                  (E-Var refl)
                                  E-Fun)
                           (E-Var refl)
                           (E-Let (E-Assign (E-Var refl)
                                            E-Int
                                            refl)
                                  (E-Deref (E-Var refl)
                                           refl))))
{-
|- let f = (fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))) in let r = (ref 0) in f(r)(r) evalto 3 / @l = 3 by E-Let {
  |- (fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))) evalto ()[fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))] by E-Fun {};
  f = ()[fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))] |- let r = (ref 0) in f(r)(r) evalto 3 / @l = 3 by E-Let {
    f = ()[fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))] |- (ref 0) evalto @l / @l = 0 by E-Ref {
      f = ()[fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))] |- 0 evalto 0 by E-Int {};
    };
    @l = 0 / f = ()[fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))],r = @l |- f(r)(r) evalto 3 / @l = 3 by E-App {
      @l = 0 / f = ()[fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))],r = @l |- f(r) evalto (r1 = @l)[fun r2 -> let z = (r2 := 3) in (! r1)] / @l = 0 by E-App {
        @l = 0 / f = ()[fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))],r = @l |- f evalto ()[fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))] / @l = 0 by E-Var {};
        @l = 0 / f = ()[fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))],r = @l |- r evalto @l / @l = 0 by E-Var {};
        @l = 0 / r1 = @l |- (fun r2 -> let z = (r2 := 3) in (! r1)) evalto (r1 = @l)[fun r2 -> let z = (r2 := 3) in (! r1)] / @l = 0 by E-Fun {};
      };
      @l = 0 / f = ()[fun r1 -> (fun r2 -> let z = (r2 := 3) in (! r1))],r = @l |- r evalto @l / @l = 0 by E-Var {};
      @l = 0 / r1 = @l,r2 = @l |- let z = (r2 := 3) in (! r1) evalto 3 / @l = 3 by E-Let {
        @l = 0 / r1 = @l,r2 = @l |- (r2 := 3) evalto 3 / @l = 3 by E-Assign {
          @l = 0 / r1 = @l,r2 = @l |- r2 evalto @l / @l = 0 by E-Var {};
          @l = 0 / r1 = @l,r2 = @l |- 3 evalto 3 / @l = 0 by E-Int {};
        };
        @l = 3 / r1 = @l,r2 = @l,z = 3 |- (! r1) evalto 3 / @l = 3 by E-Deref {
          @l = 3 / r1 = @l,r2 = @l,z = 3 |- r1 evalto @l / @l = 3 by E-Var {};
        };
      };
    };
  };
};
-}

q148 : ● ╱ ● ⊢ ℓet "x" ≔ ref (i (+ 2)) ιn
                 ℓet "y" ≔ ref (i (+ 3)) ιn
                 ℓet "refx" ≔ ref (var "x") ιn
                 ℓet "refy" ≔ ref (var "y") ιn
                 ℓet "z" ≔ (! (var "refx") ≔ ! (! (var "refy"))) ιn
                 ! (var "x") ⇓ i (+ 3) ╱ ● ⊱ ("@l1" , i (+ 3)) ⊱ ("@l2" , i (+ 3)) ⊱ ("@l3" , ℓ "@l1") ⊱ ("@l4" , ℓ "@l2")
q148 = E-Let (E-Ref {l = "@l1"} E-Int refl)
             (E-Let (E-Ref {l = "@l2"} E-Int refl)
                    (E-Let (E-Ref {l = "@l3"} (E-Var refl) refl)
                           (E-Let (E-Ref {l = "@l4"} (E-Var refl) refl)
                                  (E-Let (E-Assign (E-Deref (E-Var refl) refl)
                                                   (E-Deref (E-Deref (E-Var refl) refl) refl)
                                                   refl)
                                         (E-Deref (E-Var refl) refl)))))
{-
|- let x = (ref 2) in let y = (ref 3) in let refx = (ref x) in let refy = (ref y) in let z = ((! refx) := (! (! refy))) in (! x) evalto 3 / @l1 = 3,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Let {
  |- (ref 2) evalto @l1 / @l1 = 2 by E-Ref {
    |- 2 evalto 2 by E-Int {};
  };
  @l1 = 2 / x = @l1 |- let y = (ref 3) in let refx = (ref x) in let refy = (ref y) in let z = ((! refx) := (! (! refy))) in (! x) evalto 3 / @l1 = 3,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Let {
    @l1 = 2 / x = @l1 |- (ref 3) evalto @l2 / @l1 = 2,@l2 = 3 by E-Ref {
      @l1 = 2 / x = @l1 |- 3 evalto 3 / @l1 = 2 by E-Int {};
    };
    @l1 = 2,@l2 = 3 / x = @l1,y = @l2 |- let refx = (ref x) in let refy = (ref y) in let z = ((! refx) := (! (! refy))) in (! x) evalto 3 / @l1 = 3,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Let {
      @l1 = 2,@l2 = 3 / x = @l1,y = @l2 |- (ref x) evalto @l3 / @l1 = 2,@l2 = 3,@l3 = @l1 by E-Ref {
        @l1 = 2,@l2 = 3 / x = @l1,y = @l2 |- x evalto @l1 / @l1 = 2,@l2 = 3 by E-Var {};
      };
      @l1 = 2,@l2 = 3,@l3 = @l1 / x = @l1,y = @l2,refx = @l3 |- let refy = (ref y) in let z = ((! refx) := (! (! refy))) in (! x) evalto 3 / @l1 = 3,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Let {
        @l1 = 2,@l2 = 3,@l3 = @l1 / x = @l1,y = @l2,refx = @l3 |- (ref y) evalto @l4 / @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Ref {
          @l1 = 2,@l2 = 3,@l3 = @l1 / x = @l1,y = @l2,refx = @l3 |- y evalto @l2 / @l1 = 2,@l2 = 3,@l3 = @l1 by E-Var {};
        };
        @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 / x = @l1,y = @l2,refx = @l3,refy = @l4 |- let z = ((! refx) := (! (! refy))) in (! x) evalto 3 / @l1 = 3,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Let {
          @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 / x = @l1,y = @l2,refx = @l3,refy = @l4 |- ((! refx) := (! (! refy))) evalto 3 / @l1 = 3,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Assign {
            @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 / x = @l1,y = @l2,refx = @l3,refy = @l4 |- (! refx) evalto @l1 / @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Deref {
              @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 / x = @l1,y = @l2,refx = @l3,refy = @l4 |- refx evalto @l3 / @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Var {};
            };
            @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 / x = @l1,y = @l2,refx = @l3,refy = @l4 |- (! (! refy)) evalto 3 / @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Deref {
              @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 / x = @l1,y = @l2,refx = @l3,refy = @l4 |- (! refy) evalto @l2 / @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Deref {
                @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 / x = @l1,y = @l2,refx = @l3,refy = @l4 |- refy evalto @l4 / @l1 = 2,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Var {};
              };
            };
          };
          @l1 = 3,@l2 = 3,@l3 = @l1,@l4 = @l2 / x = @l1,y = @l2,refx = @l3,refy = @l4,z = 3 |- (! x) evalto 3 / @l1 = 3,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Deref {
            @l1 = 3,@l2 = 3,@l3 = @l1,@l4 = @l2 / x = @l1,y = @l2,refx = @l3,refy = @l4,z = 3 |- x evalto @l1 / @l1 = 3,@l2 = 3,@l3 = @l1,@l4 = @l2 by E-Var {};
          };
        };
      };
    };
  };
};
-}

q149 : ● ╱ ● ⊢ ℓet "f" ≔ ref (fun "x" ⇒ var "x") ιn
                 ℓet "fact" ≔ fun "n" ⇒
                   (if var "n" ≺ i (+ 1)
                    then i (+ 1)
                    else var "n" ⊛ app (! (var "f")) (var "n" ⊝ i (+ 1))) ιn
                 ℓet "z" ≔ (var "f" ≔ var "fact") ιn
                 app (var "fact") (i (+ 3)) ⇓ i (+ 6)
         ╱ ● ⊱ ("@l1" , ⟨ ● ⊱ ("f" , ℓ "@l1") ⟩[fun "n" ⇒
                                                    if var "n" ≺ i (+ 1)
                                                    then i (+ 1)
                                                    else var "n" ⊛ app (! (var "f")) (var "n" ⊝ i (+ 1)) ])
q149 = E-Let (E-Ref {l = "@l1"} E-Fun refl)
             (E-Let E-Fun
                    (E-Let (E-Assign (E-Var refl)
                                     (E-Var refl)
                                     refl)
                           (E-App (E-Var refl)
                                  E-Int
                                  (E-IfF (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                         (E-Mult (E-Var refl)
                                                 (E-App (E-Deref (E-Var refl) refl)
                                                        (E-Minus (E-Var refl) E-Int (B-Minus refl))
                                                        (E-IfF (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                                               (E-Mult (E-Var refl)
                                                                       (E-App (E-Deref (E-Var refl) refl)
                                                                              (E-Minus (E-Var refl) E-Int (B-Minus refl))
                                                                              (E-IfF (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                                                                     (E-Mult (E-Var refl)
                                                                                             (E-App (E-Deref (E-Var refl) refl)
                                                                                                    (E-Minus (E-Var refl) E-Int (B-Minus refl))
                                                                                                    (E-IfT (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                                                                                           E-Int))
                                                                                             (B-Times refl))))
                                                                       (B-Times refl))))
                                                 (B-Times refl))))))
{-
|- let f = (ref (fun x -> x)) in let fact = (fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))) in let z = (f := fact) in fact(3) evalto 6 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Let {
  |- (ref (fun x -> x)) evalto @l1 / @l1 = ()[fun x -> x] by E-Ref {
    |- (fun x -> x) evalto ()[fun x -> x] by E-Fun {};
  };
  @l1 = ()[fun x -> x] / f = @l1 |- let fact = (fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))) in let z = (f := fact) in fact(3) evalto 6 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Let {
    @l1 = ()[fun x -> x] / f = @l1 |- (fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))) evalto (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / @l1 = ()[fun x -> x] by E-Fun {};
    @l1 = ()[fun x -> x] / f = @l1,fact = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] |- let z = (f := fact) in fact(3) evalto 6 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Let {
      @l1 = ()[fun x -> x] / f = @l1,fact = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] |- (f := fact) evalto (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Assign {
        @l1 = ()[fun x -> x] / f = @l1,fact = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] |- f evalto @l1 / @l1 = ()[fun x -> x] by E-Var {};
        @l1 = ()[fun x -> x] / f = @l1,fact = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] |- fact evalto (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / @l1 = ()[fun x -> x] by E-Var {};
      };
      @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,fact = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))],z = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] |- fact(3) evalto 6 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-App {
        @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,fact = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))],z = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] |- fact evalto (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
        @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,fact = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))],z = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] |- 3 evalto 3 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Int {};
        @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- if (n < 1) then 1 else (n * (! f)((n - 1))) evalto 6 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-IfF {
          @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- (n < 1) evalto false / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Lt {
            @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- n evalto 3 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
            @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- 1 evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Int {};
            3 less than 1 is false by B-Lt {};
          };
          @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- (n * (! f)((n - 1))) evalto 6 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Mult {
            @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- n evalto 3 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
            @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- (! f)((n - 1)) evalto 2 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-App {
              @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- (! f) evalto (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Deref {
                @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- f evalto @l1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
              };
              @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- (n - 1) evalto 2 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Minus {
                @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- n evalto 3 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
                @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 3 |- 1 evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Int {};
                3 minus 1 is 2 by B-Minus {};
              };
              @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- if (n < 1) then 1 else (n * (! f)((n - 1))) evalto 2 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-IfF {
                @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- (n < 1) evalto false / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Lt {
                  @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- n evalto 2 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
                  @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- 1 evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Int {};
                  2 less than 1 is false by B-Lt {};
                };
                @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- (n * (! f)((n - 1))) evalto 2 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Mult {
                  @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- n evalto 2 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
                  @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- (! f)((n - 1)) evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-App {
                    @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- (! f) evalto (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Deref {
                      @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- f evalto @l1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
                    };
                    @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- (n - 1) evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Minus {
                      @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- n evalto 2 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
                      @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 2 |- 1 evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Int {};
                      2 minus 1 is 1 by B-Minus {};
                    };
                    @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- if (n < 1) then 1 else (n * (! f)((n - 1))) evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-IfF {
                      @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- (n < 1) evalto false / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Lt {
                        @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- n evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
                        @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- 1 evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Int {};
                        1 less than 1 is false by B-Lt {};
                      };
                      @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- (n * (! f)((n - 1))) evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Mult {
                        @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- n evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
                        @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- (! f)((n - 1)) evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-App {
                          @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- (! f) evalto (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Deref {
                            @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- f evalto @l1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
                          };
                          @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- (n - 1) evalto 0 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Minus {
                            @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- n evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
                            @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 1 |- 1 evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Int {};
                            1 minus 1 is 0 by B-Minus {};
                          };
                          @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 0 |- if (n < 1) then 1 else (n * (! f)((n - 1))) evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-IfT {
                            @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 0 |- (n < 1) evalto true / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Lt {
                              @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 0 |- n evalto 0 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Var {};
                              @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 0 |- 1 evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Int {};
                              0 less than 1 is true by B-Lt {};
                            };
                            @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] / f = @l1,n = 0 |- 1 evalto 1 / @l1 = (f = @l1)[fun n -> if (n < 1) then 1 else (n * (! f)((n - 1)))] by E-Int {};
                          };
                        };
                        1 times 1 is 1 by B-Mult {};
                      };
                    };
                  };
                  2 times 1 is 2 by B-Mult {};
                };
              };
            };
            3 times 2 is 6 by B-Mult {};
          };
        };
      };
    };
  };
};
-}

q150 : ● ╱ ● ⊢ ℓetrec "do" ≔fun "f" ⇒ fun "i" ⇒
                      if var "i" ≺ i (+ 1) then i (+ 0)
                      else (ℓet "x" ≔ app (var "f") (var "i") ιn app (app (var "do") (var "f")) (var "i" ⊝ i (+ 1))) ιn
                 ℓet "x" ≔ ref (i (+ 0)) ιn
                 ℓet "sum" ≔ fun "i" ⇒ (var "x" ≔ ! (var "x") ⊕ var "i") ιn
                 ℓet "y" ≔ app (app (var "do") (var "sum")) (i (+ 3)) ιn
                 ! (var "x") ⇓ i (+ 6) ╱ ● ⊱ ("@l" , i (+ 6))
q150 = E-LetRec (E-Let (E-Ref {l = "@l"} E-Int refl)
                       (E-Let E-Fun
                              (E-Let (E-App (E-AppRec (E-Var refl)
                                                      (E-Var refl)
                                                      E-Fun)
                                            E-Int
                                            (E-IfF (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                                   (E-Let (E-App (E-Var refl)
                                                                 (E-Var refl)
                                                                 (E-Assign (E-Var refl)
                                                                           (E-Plus (E-Deref (E-Var refl) refl)
                                                                                   (E-Var refl)
                                                                                   (B-Plus refl))
                                                                           refl))
                                                          (E-App (E-AppRec (E-Var refl)
                                                                           (E-Var refl)
                                                                           E-Fun)
                                                                 (E-Minus (E-Var refl) E-Int (B-Minus refl))
                                                                 (E-IfF (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                                                        (E-Let (E-App (E-Var refl)
                                                                                      (E-Var refl)
                                                                                      (E-Assign (E-Var refl)
                                                                                                (E-Plus (E-Deref (E-Var refl) refl)
                                                                                                        (E-Var refl)
                                                                                                        (B-Plus refl))
                                                                                                refl))
                                                                               (E-App (E-AppRec (E-Var refl)
                                                                                                (E-Var refl)
                                                                                                E-Fun)
                                                                                      (E-Minus (E-Var refl) E-Int (B-Minus refl))
                                                                                      (E-IfF (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                                                                             (E-Let (E-App (E-Var refl)
                                                                                                           (E-Var refl)
                                                                                                           (E-Assign (E-Var refl)
                                                                                                                     (E-Plus (E-Deref (E-Var refl) refl) (E-Var refl) (B-Plus refl))
                                                                                                                     refl))
                                                                                                    (E-App (E-AppRec (E-Var refl)
                                                                                                                     (E-Var refl)
                                                                                                                     E-Fun)
                                                                                                           (E-Minus (E-Var refl) E-Int (B-Minus refl))
                                                                                                           (E-IfT (E-Lt (E-Var refl) E-Int (B-Lt refl))
                                                                                                                  E-Int)))))))))))
                                     (E-Deref (E-Var refl) refl))))
{-
|- let rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))) in let x = (ref 0) in let sum = (fun i -> (x := ((! x) + i))) in let y = do(sum)(3) in (! x) evalto 6 / @l = 6 by E-LetRec {
  do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))] |- let x = (ref 0) in let sum = (fun i -> (x := ((! x) + i))) in let y = do(sum)(3) in (! x) evalto 6 / @l = 6 by E-Let {
    do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))] |- (ref 0) evalto @l / @l = 0 by E-Ref {
      do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))] |- 0 evalto 0 by E-Int {};
    };
    @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l |- let sum = (fun i -> (x := ((! x) + i))) in let y = do(sum)(3) in (! x) evalto 6 / @l = 6 by E-Let {
      @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l |- (fun i -> (x := ((! x) + i))) evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] / @l = 0 by E-Fun {};
      @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,sum = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] |- let y = do(sum)(3) in (! x) evalto 6 / @l = 6 by E-Let {
        @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,sum = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] |- do(sum)(3) evalto 0 / @l = 6 by E-App {
          @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,sum = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] |- do(sum) evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))])[fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))] / @l = 0 by E-AppRec {
            @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,sum = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] |- do evalto ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))] / @l = 0 by E-Var {};
            @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,sum = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] |- sum evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] / @l = 0 by E-Var {};
            @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] |- (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))) evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))])[fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))] / @l = 0 by E-Fun {};
          };
          @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,sum = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] |- 3 evalto 3 / @l = 0 by E-Int {};
          @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3 |- if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)) evalto 0 / @l = 6 by E-IfF {
            @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3 |- (i < 1) evalto false / @l = 0 by E-Lt {
              @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3 |- i evalto 3 / @l = 0 by E-Var {};
              @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3 |- 1 evalto 1 / @l = 0 by E-Int {};
              3 less than 1 is false by B-Lt {};
            };
            @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3 |- let x = f(i) in do(f)((i - 1)) evalto 0 / @l = 6 by E-Let {
              @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3 |- f(i) evalto 3 / @l = 3 by E-App {
                @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3 |- f evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] / @l = 0 by E-Var {};
                @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3 |- i evalto 3 / @l = 0 by E-Var {};
                @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 3 |- (x := ((! x) + i)) evalto 3 / @l = 3 by E-Assign {
                  @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 3 |- x evalto @l / @l = 0 by E-Var {};
                  @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 3 |- ((! x) + i) evalto 3 / @l = 0 by E-Plus {
                    @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 3 |- (! x) evalto 0 / @l = 0 by E-Deref {
                      @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 3 |- x evalto @l / @l = 0 by E-Var {};
                    };
                    @l = 0 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 3 |- i evalto 3 / @l = 0 by E-Var {};
                    0 plus 3 is 3 by B-Plus {};
                  };
                };
              };
              @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3,x = 3 |- do(f)((i - 1)) evalto 0 / @l = 6 by E-App {
                @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3,x = 3 |- do(f) evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))])[fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))] / @l = 3 by E-AppRec {
                  @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3,x = 3 |- do evalto ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))] / @l = 3 by E-Var {};
                  @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3,x = 3 |- f evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] / @l = 3 by E-Var {};
                  @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] |- (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))) evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))])[fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))] / @l = 3 by E-Fun {};
                };
                @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3,x = 3 |- (i - 1) evalto 2 / @l = 3 by E-Minus {
                  @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3,x = 3 |- i evalto 3 / @l = 3 by E-Var {};
                  @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 3,x = 3 |- 1 evalto 1 / @l = 3 by E-Int {};
                  3 minus 1 is 2 by B-Minus {};
                };
                @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2 |- if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)) evalto 0 / @l = 6 by E-IfF {
                  @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2 |- (i < 1) evalto false / @l = 3 by E-Lt {
                    @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2 |- i evalto 2 / @l = 3 by E-Var {};
                    @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2 |- 1 evalto 1 / @l = 3 by E-Int {};
                    2 less than 1 is false by B-Lt {};
                  };
                  @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2 |- let x = f(i) in do(f)((i - 1)) evalto 0 / @l = 6 by E-Let {
                    @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2 |- f(i) evalto 5 / @l = 5 by E-App {
                      @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2 |- f evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] / @l = 3 by E-Var {};
                      @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2 |- i evalto 2 / @l = 3 by E-Var {};
                      @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 2 |- (x := ((! x) + i)) evalto 5 / @l = 5 by E-Assign {
                        @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 2 |- x evalto @l / @l = 3 by E-Var {};
                        @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 2 |- ((! x) + i) evalto 5 / @l = 3 by E-Plus {
                          @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 2 |- (! x) evalto 3 / @l = 3 by E-Deref {
                            @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 2 |- x evalto @l / @l = 3 by E-Var {};
                          };
                          @l = 3 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 2 |- i evalto 2 / @l = 3 by E-Var {};
                          3 plus 2 is 5 by B-Plus {};
                        };
                      };
                    };
                    @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2,x = 5 |- do(f)((i - 1)) evalto 0 / @l = 6 by E-App {
                      @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2,x = 5 |- do(f) evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))])[fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))] / @l = 5 by E-AppRec {
                        @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2,x = 5 |- do evalto ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))] / @l = 5 by E-Var {};
                        @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2,x = 5 |- f evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] / @l = 5 by E-Var {};
                        @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] |- (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))) evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))])[fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))] / @l = 5 by E-Fun {};
                      };
                      @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2,x = 5 |- (i - 1) evalto 1 / @l = 5 by E-Minus {
                        @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2,x = 5 |- i evalto 2 / @l = 5 by E-Var {};
                        @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 2,x = 5 |- 1 evalto 1 / @l = 5 by E-Int {};
                        2 minus 1 is 1 by B-Minus {};
                      };
                      @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1 |- if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)) evalto 0 / @l = 6 by E-IfF {
                        @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1 |- (i < 1) evalto false / @l = 5 by E-Lt {
                          @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1 |- i evalto 1 / @l = 5 by E-Var {};
                          @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1 |- 1 evalto 1 / @l = 5 by E-Int {};
                          1 less than 1 is false by B-Lt {};
                        };
                        @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1 |- let x = f(i) in do(f)((i - 1)) evalto 0 / @l = 6 by E-Let {
                          @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1 |- f(i) evalto 6 / @l = 6 by E-App {
                            @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1 |- f evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] / @l = 5 by E-Var {};
                            @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1 |- i evalto 1 / @l = 5 by E-Var {};
                            @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 1 |- (x := ((! x) + i)) evalto 6 / @l = 6 by E-Assign {
                              @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 1 |- x evalto @l / @l = 5 by E-Var {};
                              @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 1 |- ((! x) + i) evalto 6 / @l = 5 by E-Plus {
                                @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 1 |- (! x) evalto 5 / @l = 5 by E-Deref {
                                  @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 1 |- x evalto @l / @l = 5 by E-Var {};
                                };
                                @l = 5 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,i = 1 |- i evalto 1 / @l = 5 by E-Var {};
                                5 plus 1 is 6 by B-Plus {};
                              };
                            };
                          };
                          @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1,x = 6 |- do(f)((i - 1)) evalto 0 / @l = 6 by E-App {
                            @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1,x = 6 |- do(f) evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))])[fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))] / @l = 6 by E-AppRec {
                              @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1,x = 6 |- do evalto ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))] / @l = 6 by E-Var {};
                              @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1,x = 6 |- f evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] / @l = 6 by E-Var {};
                              @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))] |- (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))) evalto (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))])[fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1))] / @l = 6 by E-Fun {};
                            };
                            @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1,x = 6 |- (i - 1) evalto 0 / @l = 6 by E-Minus {
                              @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1,x = 6 |- i evalto 1 / @l = 6 by E-Var {};
                              @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 1,x = 6 |- 1 evalto 1 / @l = 6 by E-Int {};
                              1 minus 1 is 0 by B-Minus {};
                            };
                            @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 0 |- if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)) evalto 0 / @l = 6 by E-IfT {
                              @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 0 |- (i < 1) evalto true / @l = 6 by E-Lt {
                                @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 0 |- i evalto 0 / @l = 6 by E-Var {};
                                @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 0 |- 1 evalto 1 / @l = 6 by E-Int {};
                                0 less than 1 is true by B-Lt {};
                              };
                              @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],f = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],i = 0 |- 0 evalto 0 / @l = 6 by E-Int {};
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
        @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,sum = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],y = 0 |- (! x) evalto 6 / @l = 6 by E-Deref {
          @l = 6 / do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l,sum = (do = ()[rec do = fun f -> (fun i -> if (i < 1) then 0 else let x = f(i) in do(f)((i - 1)))],x = @l)[fun i -> (x := ((! x) + i))],y = 0 |- x evalto @l / @l = 6 by E-Var {};
        };
      };
    };
  };
};
-}
