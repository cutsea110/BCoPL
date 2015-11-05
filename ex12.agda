module ex12 where

open import BCoPL.EvalContML4
open import BCoPL.Show.EvalContML4

q130 : ● ⊢ ℓet "x" ≔ i (+ 1) ⊕ i (+ 2) ιn var "x" ⊛ i (+ 4) ≫ ⋆ ⇓ i (+ 12)
q130 = E-Let (E-BinOp (E-Int (C-EvalR (E-Int (C-Plus (B-Plus refl) (C-LetBody (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Times (B-Times refl) C-Ret)))))))))))
{-
|- let x = (1 + 2) in (x * 4) >> _ evalto 12 by E-Let { |- (1 + 2) >> { |- let x = _ in (x * 4)} >> _ evalto 12 by E-BinOp { |- 1 >> { |- _  +  2} >> { |- let x = _ in (x * 4)} >> _ evalto 12 by E-Int {1 => { |- _  +  2} >> { |- let x = _ in (x * 4)} >> _ evalto 12 by C-EvalR { |- 2 >> {1 +  _} >> { |- let x = _ in (x * 4)} >> _ evalto 12 by E-Int {2 => {1 +  _} >> { |- let x = _ in (x * 4)} >> _ evalto 12 by C-Plus {1 plus 2 is 3 by B-Plus {};3 => { |- let x = _ in (x * 4)} >> _ evalto 12 by C-LetBody {x = 3 |- (x * 4) >> _ evalto 12 by E-BinOp {x = 3 |- x >> {x = 3 |- _  *  4} >> _ evalto 12 by E-Var {3 => {x = 3 |- _  *  4} >> _ evalto 12 by C-EvalR {x = 3 |- 4 >> {3 *  _} >> _ evalto 12 by E-Int {4 => {3 *  _} >> _ evalto 12 by C-Times {3 times 4 is 12 by B-Times {};12 => _ evalto 12 by C-Ret {};};};};};};};};};};};};};
-}

q131 : ● ⊢ ℓet "add1" ≔ fun "x" ⇒ var "x" ⊕ i (+ 1) ιn app (var "add1") (i (+ 3)) ≫ ⋆ ⇓ i (+ 4)
q131 = E-Let (E-Fun (C-LetBody (E-App (E-Var refl (C-EvalArg (E-Int (C-EvalFun (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Plus (B-Plus refl) C-Ret))))))))))))
{-
|- let add1 = (fun x -> (x + 1)) in add1(3) >> _ evalto 4 by E-Let {
  |- (fun x -> (x + 1)) >> {|- let add1 = _ in add1(3)} >> _ evalto 4 by E-Fun {
    ()[fun x -> (x + 1)] => { |- let add1 = _ in add1(3)} >> _ evalto 4 by C-LetBody {
      add1 = ()[fun x -> (x + 1)] |- add1(3) >> _ evalto 4 by E-App {
        add1 = ()[fun x -> (x + 1)] |- add1 >> {add1 = ()[fun x -> (x + 1)] |- _ 3} >> _ evalto 4 by E-Var {
          ()[fun x -> (x + 1)] => {add1 = ()[fun x -> (x + 1)] |- _ 3} >> _ evalto 4 by C-EvalArg {
            add1 = ()[fun x -> (x + 1)] |- 3 >> {()[fun x -> (x + 1)] _} >> _ evalto 4 by E-Int {
              3 => {()[fun x -> (x + 1)] _} >> _ evalto 4 by C-EvalFun {
                x = 3 |- (x + 1) >> _ evalto 4 by E-BinOp {
                  x = 3 |- x >> {x = 3 |- _  +  1} >> _ evalto 4 by E-Var {
                    3 => {x = 3 |- _  +  1} >> _ evalto 4 by C-EvalR {
                      x = 3 |- 1 >> {3 +  _} >> _ evalto 4 by E-Int {
                        1 => {3 +  _} >> _ evalto 4 by C-Plus {
                          3 plus 1 is 4 by B-Plus {};
                          4 => _ evalto 4 by C-Ret {};
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
};
-}

q132 : ● ⊢ ℓetrec "fact" ≔fun "n" ⇒
                  if var "n" ≺ i (+ 2) then i (+ 1) else var "n" ⊛ app (var "fact") (var "n" ⊝ i (+ 1)) ιn
            app (var "fact") (i (+ 3)) ≫ ⋆ ⇓ i (+ 6)
q132 = E-LetRec (E-App (E-Var refl (C-EvalArg (E-Int (C-EvalFunR (E-If (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Lt (B-Lt refl) (C-IfF (E-BinOp (E-Var refl (C-EvalR (E-App (E-Var refl (C-EvalArg (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Minus (B-Minus refl) (C-EvalFunR (E-If (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Lt (B-Lt refl) (C-IfF (E-BinOp (E-Var refl (C-EvalR (E-App (E-Var refl (C-EvalArg (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Minus (B-Minus refl) (C-EvalFunR (E-If (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Lt (B-Lt refl) (C-IfT (E-Int (C-Times (B-Times refl) (C-Times (B-Times refl) C-Ret)))))))))))))))))))))))))))))))))))))))))))))))))))))
{-
|- let rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1))) in fact(3) >> _ evalto 6 by E-LetRec {
  fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- fact(3) >> _ evalto 6 by E-App {
    fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- fact >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- _ 3} >> _ evalto 6 by E-Var {
      ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- _ 3} >> _ evalto 6 by C-EvalArg {
        fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- 3 >> {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> _ evalto 6 by E-Int {
          3 => {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> _ evalto 6 by C-EvalFunR {
            fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- if (n < 2) then 1 else (n * fact((n - 1))) >> _ evalto 6 by E-If {
              fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- (n < 2) >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- if _ then 1 else (n * fact((n - 1)))} >> _ evalto 6 by E-BinOp {
                fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- n >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- _  <  2} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- if _ then 1 else (n * fact((n - 1)))} >> _ evalto 6 by E-Var {
                  3 => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- _  <  2} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- if _ then 1 else (n * fact((n - 1)))} >> _ evalto 6 by C-EvalR {
                    fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- 2 >> {3 <  _} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- if _ then 1 else (n * fact((n - 1)))} >> _ evalto 6 by E-Int {
                      2 => {3 <  _} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- if _ then 1 else (n * fact((n - 1)))} >> _ evalto 6 by C-Lt {
                        3 less than 2 is false by B-Lt {};
                        false => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- if _ then 1 else (n * fact((n - 1)))} >> _ evalto 6 by C-IfF {
                          fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- (n * fact((n - 1))) >> _ evalto 6 by E-BinOp {
                            fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- n >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- _  *  fact((n - 1))} >> _ evalto 6 by E-Var {3 => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- _  *  fact((n - 1))} >> _ evalto 6 by C-EvalR {
                              fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- fact((n - 1)) >> {3 *  _} >> _ evalto 6 by E-App {
                                fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- fact >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- _ (n - 1)} >> {3 *  _} >> _ evalto 6 by E-Var {
                                  ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- _ (n - 1)} >> {3 *  _} >> _ evalto 6 by C-EvalArg {
                                    fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- (n - 1) >> {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {3 *  _} >> _ evalto 6 by E-BinOp {
                                      fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- n >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- _  -  1} >> {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {3 *  _} >> _ evalto 6 by E-Var {
                                        3 => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- _  -  1} >> {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {3 *  _} >> _ evalto 6 by C-EvalR {
                                          fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 3 |- 1 >> {3 -  _} >> {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {3 *  _} >> _ evalto 6 by E-Int {
                                            1 => {3 -  _} >> {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {3 *  _} >> _ evalto 6 by C-Minus {
                                              3 minus 1 is 2 by B-Minus {};
                                              2 => {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {3 *  _} >> _ evalto 6 by C-EvalFunR {
                                                fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- if (n < 2) then 1 else (n * fact((n - 1))) >> {3 *  _} >> _ evalto 6 by E-If {
                                                  fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- (n < 2) >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- if _ then 1 else (n * fact((n - 1)))} >> {3 *  _} >> _ evalto 6 by E-BinOp {
                                                    fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- n >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- _  <  2} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- if _ then 1 else (n * fact((n - 1)))} >> {3 *  _} >> _ evalto 6 by E-Var {
                                                      2 => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- _  <  2} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- if _ then 1 else (n * fact((n - 1)))} >> {3 *  _} >> _ evalto 6 by C-EvalR {
                                                        fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- 2 >> {2 <  _} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- if _ then 1 else (n * fact((n - 1)))} >> {3 *  _} >> _ evalto 6 by E-Int {
                                                          2 => {2 <  _} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- if _ then 1 else (n * fact((n - 1)))} >> {3 *  _} >> _ evalto 6 by C-Lt {
                                                            2 less than 2 is false by B-Lt {};
                                                            false => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- if _ then 1 else (n * fact((n - 1)))} >> {3 *  _} >> _ evalto 6 by C-IfF {
                                                              fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- (n * fact((n - 1))) >> {3 *  _} >> _ evalto 6 by E-BinOp {
                                                                fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- n >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- _  *  fact((n - 1))} >> {3 *  _} >> _ evalto 6 by E-Var {
                                                                  2 => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- _  *  fact((n - 1))} >> {3 *  _} >> _ evalto 6 by C-EvalR {
                                                                    fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- fact((n - 1)) >> {2 *  _} >> {3 *  _} >> _ evalto 6 by E-App {
                                                                      fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- fact >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- _ (n - 1)} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by E-Var {
                                                                        ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- _ (n - 1)} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by C-EvalArg {
                                                                          fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- (n - 1) >> {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by E-BinOp {
                                                                            fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- n >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- _  -  1} >> {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by E-Var {
                                                                              2 => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- _  -  1} >> {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by C-EvalR {
                                                                                fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 2 |- 1 >> {2 -  _} >> {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by E-Int {
                                                                                  1 => {2 -  _} >> {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by C-Minus {
                                                                                    2 minus 1 is 1 by B-Minus {};
                                                                                      1 => {()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] _} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by C-EvalFunR {
                                                                                        fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- if (n < 2) then 1 else (n * fact((n - 1))) >> {2 *  _} >> {3 *  _} >> _ evalto 6 by E-If {
                                                                                          fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- (n < 2) >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- if _ then 1 else (n * fact((n - 1)))} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by E-BinOp {
                                                                                            fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- n >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- _  <  2} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- if _ then 1 else (n * fact((n - 1)))} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by E-Var {
                                                                                              1 => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- _  <  2} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- if _ then 1 else (n * fact((n - 1)))} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by C-EvalR {
                                                                                                fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- 2 >> {1 <  _} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- if _ then 1 else (n * fact((n - 1)))} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by E-Int {
                                                                                                  2 => {1 <  _} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- if _ then 1 else (n * fact((n - 1)))} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by C-Lt {
                                                                                                    1 less than 2 is true by B-Lt {};
                                                                                                    true => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- if _ then 1 else (n * fact((n - 1)))} >> {2 *  _} >> {3 *  _} >> _ evalto 6 by C-IfT {
                                                                                                      fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],n = 1 |- 1 >> {2 *  _} >> {3 *  _} >> _ evalto 6 by E-Int {
                                                                                                        1 => {2 *  _} >> {3 *  _} >> _ evalto 6 by C-Times {
                                                                                                          2 times 1 is 2 by B-Times {};
                                                                                                          2 => {3 *  _} >> _ evalto 6 by C-Times {
                                                                                                            3 times 2 is 6 by B-Times {};
                                                                                                            6 => _ evalto 6 by C-Ret {};
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
          };
        };
      };
    };
  };
};
-}

q133 : ● ⊱ ("k" , ⟪ ⟦ i (+ 3) ⊕⋆ ⟧≫ ⋆ ⟫) ⊢ i (+ 1) ⊕ app (var "k") (i (+ 2)) ≫ ⋆ ⇓ i (+ 5)
q133 = E-BinOp (E-Int (C-EvalR (E-App (E-Var refl (C-EvalArg (E-Int (C-EvalFunC (C-Plus (B-Plus refl) C-Ret))))))))
{-
k = [{3 +  _} >> _] |- (1 + k(2)) >> _ evalto 5 by E-BinOp {
  k = [{3 +  _} >> _] |- 1 >> {k = [{3 +  _} >> _] |- _  +  k(2)} >> _ evalto 5 by E-Int {
    1 => {k = [{3 +  _} >> _] |- _  +  k(2)} >> _ evalto 5 by C-EvalR {
      k = [{3 +  _} >> _] |- k(2) >> {1 +  _} >> _ evalto 5 by E-App {
        k = [{3 +  _} >> _] |- k >> {k = [{3 +  _} >> _] |- _ 2} >> {1 +  _} >> _ evalto 5 by E-Var {
          [{3 +  _} >> _] => {k = [{3 +  _} >> _] |- _ 2} >> {1 +  _} >> _ evalto 5 by C-EvalArg {
            k = [{3 +  _} >> _] |- 2 >> {[{3 +  _} >> _] _} >> {1 +  _} >> _ evalto 5 by E-Int {
              2 => {[{3 +  _} >> _] _} >> {1 +  _} >> _ evalto 5 by C-EvalFunC {
                2 => {3 +  _} >> _ evalto 5 by C-Plus {
                  3 plus 2 is 5 by B-Plus {};
                  5 => _ evalto 5 by C-Ret {};
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

q134 : ● ⊢ i (+ 3) ⊕ letcc "k" ιn (i (+ 1) ⊕ app (var "k") (i (+ 2))) ≫ ⋆ ⇓ i (+ 5)
q134 = E-BinOp (E-Int (C-EvalR (E-LetCc (E-BinOp (E-Int (C-EvalR (E-App (E-Var refl (C-EvalArg (E-Int (C-EvalFunC (C-Plus (B-Plus refl) C-Ret))))))))))))
{-
|- (3 + letcc k in (1 + k(2))) >> _ evalto 5 by E-BinOp { |- 3 >> { |- _  +  letcc k in (1 + k(2))} >> _ evalto 5 by E-Int {3 => { |- _  +  letcc k in (1 + k(2))} >> _ evalto 5 by C-EvalR { |- letcc k in (1 + k(2)) >> {3 +  _} >> _ evalto 5 by E-LetCc {k = [{3 +  _} >> _] |- (1 + k(2)) >> {3 +  _} >> _ evalto 5 by E-BinOp {k = [{3 +  _} >> _] |- 1 >> {k = [{3 +  _} >> _] |- _  +  k(2)} >> {3 +  _} >> _ evalto 5 by E-Int {1 => {k = [{3 +  _} >> _] |- _  +  k(2)} >> {3 +  _} >> _ evalto 5 by C-EvalR {k = [{3 +  _} >> _] |- k(2) >> {1 +  _} >> {3 +  _} >> _ evalto 5 by E-App {k = [{3 +  _} >> _] |- k >> {k = [{3 +  _} >> _] |- _ 2} >> {1 +  _} >> {3 +  _} >> _ evalto 5 by E-Var {[{3 +  _} >> _] => {k = [{3 +  _} >> _] |- _ 2} >> {1 +  _} >> {3 +  _} >> _ evalto 5 by C-EvalArg {k = [{3 +  _} >> _] |- 2 >> {[{3 +  _} >> _] _} >> {1 +  _} >> {3 +  _} >> _ evalto 5 by E-Int {2 => {[{3 +  _} >> _] _} >> {1 +  _} >> {3 +  _} >> _ evalto 5 by C-EvalFunC {2 => {3 +  _} >> _ evalto 5 by C-Plus {3 plus 2 is 5 by B-Plus {};5 => _ evalto 5 by C-Ret {};};};};};};};};};};};};};};
-}

q135 : ● ⊢ ℓetrec "fact" ≔fun "n" ⇒
                  if var "n" ≺ i (+ 2) then i (+ 1) else var "n" ⊛ app (var "fact") (var "n" ⊝ i (+ 1)) ιn
            i (+ 3) ⊕ letcc "k" ιn (i (+ 1) ⊕ app (var "k") (i (+ 2)) ⊕ app (var "fact") (i (+ 7))) ≫ ⋆ ⇓ i (+ 5)
q135 = E-LetRec (E-BinOp (E-Int (C-EvalR (E-LetCc (E-BinOp (E-BinOp (E-Int (C-EvalR (E-App (E-Var refl (C-EvalArg (E-Int (C-EvalFunC (C-Plus (B-Plus refl) C-Ret))))))))))))))
{-
|- let rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1))) in (3 + letcc k in ((1 + k(2)) + fact(100))) >> _ evalto 5 by E-LetRec {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- (3 + letcc k in ((1 + k(2)) + fact(100))) >> _ evalto 5 by E-BinOp {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- 3 >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- _  +  letcc k in ((1 + k(2)) + fact(100))} >> _ evalto 5 by E-Int {3 => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- _  +  letcc k in ((1 + k(2)) + fact(100))} >> _ evalto 5 by C-EvalR {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))] |- letcc k in ((1 + k(2)) + fact(100)) >> {3 +  _} >> _ evalto 5 by E-LetCc {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- ((1 + k(2)) + fact(100)) >> {3 +  _} >> _ evalto 5 by E-BinOp {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- (1 + k(2)) >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _  +  fact(100)} >> {3 +  _} >> _ evalto 5 by E-BinOp {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- 1 >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _  +  k(2)} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _  +  fact(100)} >> {3 +  _} >> _ evalto 5 by E-Int {1 => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _  +  k(2)} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _  +  fact(100)} >> {3 +  _} >> _ evalto 5 by C-EvalR {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- k(2) >> {1 +  _} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _  +  fact(100)} >> {3 +  _} >> _ evalto 5 by E-App {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- k >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _ 2} >> {1 +  _} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _  +  fact(100)} >> {3 +  _} >> _ evalto 5 by E-Var {[{3 +  _} >> _] => {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _ 2} >> {1 +  _} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _  +  fact(100)} >> {3 +  _} >> _ evalto 5 by C-EvalArg {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- 2 >> {[{3 +  _} >> _] _} >> {1 +  _} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _  +  fact(100)} >> {3 +  _} >> _ evalto 5 by E-Int {2 => {[{3 +  _} >> _] _} >> {1 +  _} >> {fact = ()[rec fact = fun n -> if (n < 2) then 1 else (n * fact((n - 1)))],k = [{3 +  _} >> _] |- _  +  fact(100)} >> {3 +  _} >> _ evalto 5 by C-EvalFunC {2 => {3 +  _} >> _ evalto 5 by C-Plus {3 plus 2 is 5 by B-Plus {};5 => _ evalto 5 by C-Ret {};};};};};};};};};};};};};};};};
-}

q136 : ● ⊢ ℓet "sm" ≔ fun "f" ⇒ app (var "f") (i (+ 3)) ⊕ app (var "f") (i (+ 4)) ιn
            letcc "k" ιn app (var "sm") (var "k") ≫ ⋆ ⇓ i (+ 3)
q136 = E-Let (E-Fun (C-LetBody (E-LetCc (E-App (E-Var refl (C-EvalArg (E-Var refl (C-EvalFun (E-BinOp (E-App (E-Var refl (C-EvalArg (E-Int (C-EvalFunC C-Ret))))))))))))))
{-
|- let sm = (fun f -> (f(3) + f(4))) in letcc k in sm(k) >> _ evalto 3 by E-Let { |- (fun f -> (f(3) + f(4))) >> { |- let sm = _ in letcc k in sm(k)} >> _ evalto 3 by E-Fun {()[fun f -> (f(3) + f(4))] => { |- let sm = _ in letcc k in sm(k)} >> _ evalto 3 by C-LetBody {sm = ()[fun f -> (f(3) + f(4))] |- letcc k in sm(k) >> _ evalto 3 by E-LetCc {sm = ()[fun f -> (f(3) + f(4))],k = [_] |- sm(k) >> _ evalto 3 by E-App {sm = ()[fun f -> (f(3) + f(4))],k = [_] |- sm >> {sm = ()[fun f -> (f(3) + f(4))],k = [_] |- _ k} >> _ evalto 3 by E-Var {()[fun f -> (f(3) + f(4))] => {sm = ()[fun f -> (f(3) + f(4))],k = [_] |- _ k} >> _ evalto 3 by C-EvalArg {sm = ()[fun f -> (f(3) + f(4))],k = [_] |- k >> {()[fun f -> (f(3) + f(4))] _} >> _ evalto 3 by E-Var {[_] => {()[fun f -> (f(3) + f(4))] _} >> _ evalto 3 by C-EvalFun {f = [_] |- (f(3) + f(4)) >> _ evalto 3 by E-BinOp {f = [_] |- f(3) >> {f = [_] |- _  +  f(4)} >> _ evalto 3 by E-App {f = [_] |- f >> {f = [_] |- _ 3} >> {f = [_] |- _  +  f(4)} >> _ evalto 3 by E-Var {[_] => {f = [_] |- _ 3} >> {f = [_] |- _  +  f(4)} >> _ evalto 3 by C-EvalArg {f = [_] |- 3 >> {[_] _} >> {f = [_] |- _  +  f(4)} >> _ evalto 3 by E-Int {3 => {[_] _} >> {f = [_] |- _  +  f(4)} >> _ evalto 3 by C-EvalFunC {3 => _ evalto 3 by C-Ret {};};};};};};};};};};};};};};};};
-}

q137 : ● ⊢ ℓet "f" ≔ fun "x" ⇒ fun "k1" ⇒ fun "k2" ⇒
               (if var "x" ≺ i (+ 0) then app (var "k1") (var "x") else app (var "k2") (var "x")) ιn
            i (+ 1) ⊕ (letcc "k1" ιn (i (+ 2)) ⊕ (letcc "k2" ιn app (app (app (var "f") (i -[1+ 1 ])) (var "k1")) (var "k2"))) ≫ ⋆ ⇓ i -[1+ 0 ]
q137 = ?
