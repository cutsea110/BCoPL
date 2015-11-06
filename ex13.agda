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
|- let newc = (fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))) in let c1 = newc(5) in let c2 = newc(4) in let y = c1(true) in let y = c2(true) in c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-Let { |- (fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))) evalto ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] by E-Fun {};newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] |- let c1 = newc(5) in let c2 = newc(4) in let y = c1(true) in let y = c2(true) in c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-Let {newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] |- newc(5) evalto (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5 by E-App {newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] |- newc evalto ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] by E-Var {};newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] |- 5 evalto 5 by E-Int {};x = 5 |- let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x)) evalto (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5 by E-Let {x = 5 |- (ref x) evalto @l1 / @l1 = 5 by E-Ref {x = 5 |- x evalto 5 by E-Var {};};@l1 = 5 / x = 5,x = @l1 |- (fun y -> if y then (x := ((! x) + 1)) else (! x)) evalto (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5 by E-Fun {};};};@l1 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- let c2 = newc(4) in let y = c1(true) in let y = c2(true) in c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-Let {@l1 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- newc(4) evalto (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5,@l2 = 4 by E-App {@l1 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- newc evalto ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))] / @l1 = 5 by E-Var {};@l1 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- 4 evalto 4 / @l1 = 5 by E-Int {};@l1 = 5 / x = 4 |- let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x)) evalto (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5,@l2 = 4 by E-Let {@l1 = 5 / x = 4 |- (ref x) evalto @l2 / @l1 = 5,@l2 = 4 by E-Ref {@l1 = 5 / x = 4 |- x evalto 4 / @l1 = 5 by E-Var {};};@l1 = 5,@l2 = 4 / x = 4,x = @l2 |- (fun y -> if y then (x := ((! x) + 1)) else (! x)) evalto (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5,@l2 = 4 by E-Fun {};};};@l1 = 5,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- let y = c1(true) in let y = c2(true) in c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-Let {@l1 = 5,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- c1(true) evalto 6 / @l1 = 6,@l2 = 4 by E-App {@l1 = 5,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- c1 evalto (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 5,@l2 = 4 by E-Var {};@l1 = 5,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] |- true evalto true / @l1 = 5,@l2 = 4 by E-Bool {};@l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- if y then (x := ((! x) + 1)) else (! x) evalto 6 / @l1 = 6,@l2 = 4 by E-IfT {@l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- y evalto true / @l1 = 5,@l2 = 4 by E-Var {};@l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- (x := ((! x) + 1)) evalto 6 / @l1 = 6,@l2 = 4 by E-Assign {@l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- x evalto @l1 / @l1 = 5,@l2 = 4 by E-Var {};@l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- ((! x) + 1) evalto 6 / @l1 = 5,@l2 = 4 by E-Plus {@l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- (! x) evalto 5 / @l1 = 5,@l2 = 4 by E-Deref {@l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- x evalto @l1 / @l1 = 5,@l2 = 4 by E-Var {};};@l1 = 5,@l2 = 4 / x = 5,x = @l1,y = true |- 1 evalto 1 / @l1 = 5,@l2 = 4 by E-Int {};5 plus 1 is 6 by B-Plus {};};};};};@l1 = 6,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6 |- let y = c2(true) in c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-Let {@l1 = 6,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6 |- c2(true) evalto 5 / @l1 = 6,@l2 = 5 by E-App {@l1 = 6,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6 |- c2 evalto (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 6,@l2 = 4 by E-Var {};@l1 = 6,@l2 = 4 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6 |- true evalto true / @l1 = 6,@l2 = 4 by E-Bool {};@l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- if y then (x := ((! x) + 1)) else (! x) evalto 5 / @l1 = 6,@l2 = 5 by E-IfT {@l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- y evalto true / @l1 = 6,@l2 = 4 by E-Var {};@l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- (x := ((! x) + 1)) evalto 5 / @l1 = 6,@l2 = 5 by E-Assign {@l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- x evalto @l2 / @l1 = 6,@l2 = 4 by E-Var {};@l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- ((! x) + 1) evalto 5 / @l1 = 6,@l2 = 4 by E-Plus {@l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- (! x) evalto 4 / @l1 = 6,@l2 = 4 by E-Deref {@l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- x evalto @l2 / @l1 = 6,@l2 = 4 by E-Var {};};@l1 = 6,@l2 = 4 / x = 4,x = @l2,y = true |- 1 evalto 1 / @l1 = 6,@l2 = 4 by E-Int {};4 plus 1 is 5 by B-Plus {};};};};};@l1 = 6,@l2 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6,y = 5 |- c1(false) evalto 6 / @l1 = 6,@l2 = 5 by E-App {@l1 = 6,@l2 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6,y = 5 |- c1 evalto (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)] / @l1 = 6,@l2 = 5 by E-Var {};@l1 = 6,@l2 = 5 / newc = ()[fun x -> let x = (ref x) in (fun y -> if y then (x := ((! x) + 1)) else (! x))],c1 = (x = 5,x = @l1)[fun y -> if y then (x := ((! x) + 1)) else (! x)],c2 = (x = 4,x = @l2)[fun y -> if y then (x := ((! x) + 1)) else (! x)],y = 6,y = 5 |- false evalto false / @l1 = 6,@l2 = 5 by E-Bool {};@l1 = 6,@l2 = 5 / x = 5,x = @l1,y = false |- if y then (x := ((! x) + 1)) else (! x) evalto 6 / @l1 = 6,@l2 = 5 by E-IfF {@l1 = 6,@l2 = 5 / x = 5,x = @l1,y = false |- y evalto false / @l1 = 6,@l2 = 5 by E-Var {};@l1 = 6,@l2 = 5 / x = 5,x = @l1,y = false |- (! x) evalto 6 / @l1 = 6,@l2 = 5 by E-Deref {@l1 = 6,@l2 = 5 / x = 5,x = @l1,y = false |- x evalto @l1 / @l1 = 6,@l2 = 5 by E-Var {};};};};};};};};};
-}
