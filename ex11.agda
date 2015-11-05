module ex11 where

open import BCoPL.EvalContML1
open import BCoPL.Show.EvalContML1

q124 : i (+ 3) ≫ ⋆ ⇓ i (+ 3)
q124 = E-Int C-Ret
{-
3 >> _ evalto 3 by E-Int {
  3 => _ evalto 3 by C-Ret {};
};
-}

q125 : i (+ 5) ≫ ⟦ i (+ 3) ⊕⋆ ⟧≫ ⋆ ⇓ i (+ 8)
q125 = E-Int (C-Plus (B-Plus refl) C-Ret)
{-
5 >> {3  +  _} >> _ evalto 8 by E-Int {
  5 => {3  +  _} >> _ evalto 8 by C-Plus {
    3 plus 5 is 8 by B-Plus {};
    8 => _ evalto 8 by C-Ret {};
  };
};
-}

q126 : i (+ 3) ⊕ i (+ 5) ≫ ⋆ ⇓ i (+ 8)
q126 = E-BinOp (E-Int (C-EvalR (E-Int (C-Plus (B-Plus refl) C-Ret))))
{-
(3 + 5) >> _ evalto 8 by E-BinOp {
  3 >> {_  +  5} >> _ evalto 8 by E-Int {
    3 => {_  +  5} >> _ evalto 8 by C-EvalR {
      5 >> {3  +  _} >> _ evalto 8 by E-Int {
        5 => {3  +  _} >> _ evalto 8 by C-Plus {
          3 plus 5 is 8 by B-Plus {};
          8 => _ evalto 8 by C-Ret {};
        };
      };
    };
  };
};
-}

q127 : (i (+ 4) ⊕ i (+ 5)) ⊛ (i (+ 1) ⊝ i (+ 10)) ≫ ⋆ ⇓ i -[1+ 80 ]
-- q127 : (i (+ 1) ⊕ i (+ 2)) ⊛ (i (+ 1) ⊝ i (+ 3)) ≫ ⋆ ⇓ i -[1+ 5 ]
q127 = E-BinOp (E-BinOp (E-Int (C-EvalR (E-Int (C-Plus (B-Plus refl) (C-EvalR (E-BinOp (E-Int (C-EvalR (E-Int (C-Minus (B-Minus refl) (C-Times (B-Times refl) C-Ret))))))))))))
{-
((4 + 5) * (1 - 10)) >> _ evalto -81 by E-BinOp {
  (4 + 5) >> {_  *  (1 - 10)} >> _ evalto -81 by E-BinOp {
    4 >> {_  +  5} >> {_  *  (1 - 10)} >> _ evalto -81 by E-Int {
      4 => {_  +  5} >> {_  *  (1 - 10)} >> _ evalto -81 by C-EvalR {
        5 >> {4  +  _} >> {_  *  (1 - 10)} >> _ evalto -81 by E-Int {
          5 => {4  +  _} >> {_  *  (1 - 10)} >> _ evalto -81 by C-Plus {
            4 plus 5 is 9 by B-Plus {};
            9 => {_  *  (1 - 10)} >> _ evalto -81 by C-EvalR {
              (1 - 10) >> {9  *  _} >> _ evalto -81 by E-BinOp {
                1 >> {_  -  10} >> {9  *  _} >> _ evalto -81 by E-Int {
                  1 => {_  -  10} >> {9  *  _} >> _ evalto -81 by C-EvalR {
                    10 >> {1  -  _} >> {9  *  _} >> _ evalto -81 by E-Int {
                      10 => {1  -  _} >> {9  *  _} >> _ evalto -81 by C-Minus {
                        1 minus 10 is -9 by B-Minus {};
                        -9 => {9  *  _} >> _ evalto -81 by C-Times {
                          9 times -9 is -81 by B-Times {};
                          -81 => _ evalto -81 by C-Ret {};
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

q128 : if i (+ 4) ≺ i (+ 5) then i (+ 2) ⊕ i (+ 3) else i (+ 8) ⊛ i (+ 8) ≫ ⋆ ⇓ i (+ 5)
q128 = E-If (E-BinOp (E-Int (C-EvalR (E-Int (C-Lt (B-Lt refl) (C-IfT (E-BinOp (E-Int (C-EvalR (E-Int (C-Plus (B-Plus refl) C-Ret)))))))))))
{-
if (4 < 5) then (2 + 3) else (8 * 8) >> _ evalto 5 by E-If {
  (4 < 5) >> {if _ then (2 + 3) else (8 * 8)} >> _ evalto 5 by E-BinOp {
    4 >> {_  <  5} >> {if _ then (2 + 3) else (8 * 8)} >> _ evalto 5 by E-Int {
      4 => {_  <  5} >> {if _ then (2 + 3) else (8 * 8)} >> _ evalto 5 by C-EvalR {
        5 >> {4  <  _} >> {if _ then (2 + 3) else (8 * 8)} >> _ evalto 5 by E-Int {
          5 => {4  <  _} >> {if _ then (2 + 3) else (8 * 8)} >> _ evalto 5 by C-Lt {
            4 less than 5 is true by B-Lt {};true => {if _ then (2 + 3) else (8 * 8)} >> _ evalto 5 by C-IfT {
              (2 + 3) >> _ evalto 5 by E-BinOp {
                2 >> {_  +  3} >> _ evalto 5 by E-Int {
                  2 => {_  +  3} >> _ evalto 5 by C-EvalR {
                    3 >> {2  +  _} >> _ evalto 5 by E-Int {
                      3 => {2  +  _} >> _ evalto 5 by C-Plus {
                        2 plus 3 is 5 by B-Plus {};
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
    };
  };
};
-}

q129 : i (+ 3) ⊕ (if i -[1+ 2 ] ≺ i -[1+ 1 ] ⊛ i (+ 8) then i (+ 8) else i (+ 2)) ⊕ i (+ 4) ≫ ⋆ ⇓ i (+ 9)
q129 = E-BinOp (E-BinOp (E-Int (C-EvalR (E-If (E-BinOp (E-Int (C-EvalR (E-BinOp (E-Int (C-EvalR (E-Int (C-Times (B-Times refl) (C-Lt (B-Lt refl) (C-IfF (E-Int (C-Plus (B-Plus refl) (C-EvalR (E-Int (C-Plus (B-Plus refl) C-Ret)))))))))))))))))))
{-
((3 + if (-3 < (-2 * 8)) then 8 else 2) + 4) >> _ evalto 9 by E-BinOp {
  (3 + if (-3 < (-2 * 8)) then 8 else 2) >> {_  +  4} >> _ evalto 9 by E-BinOp {
    3 >> {_  +  if (-3 < (-2 * 8)) then 8 else 2} >> {_  +  4} >> _ evalto 9 by E-Int {
      3 => {_  +  if (-3 < (-2 * 8)) then 8 else 2} >> {_  +  4} >> _ evalto 9 by C-EvalR {
        if (-3 < (-2 * 8)) then 8 else 2 >> {3  +  _} >> {_  +  4} >> _ evalto 9 by E-If {
          (-3 < (-2 * 8)) >> {if _ then 8 else 2} >> {3  +  _} >> {_  +  4} >> _ evalto 9 by E-BinOp {
            -3 >> {_  <  (-2 * 8)} >> {if _ then 8 else 2} >> {3  +  _} >> {_  +  4} >> _ evalto 9 by E-Int {
              -3 => {_  <  (-2 * 8)} >> {if _ then 8 else 2} >> {3  +  _} >> {_  +  4} >> _ evalto 9 by C-EvalR {
                (-2 * 8) >> { -3  <  _} >> {if _ then 8 else 2} >> {3  +  _} >> {_  +  4} >> _ evalto 9 by E-BinOp {
                  -2 >> {_  *  8} >> { -3  <  _} >> {if _ then 8 else 2} >> {3  +  _} >> {_  +  4} >> _ evalto 9 by E-Int {
                    -2 => {_  *  8} >> { -3  <  _} >> {if _ then 8 else 2} >> {3  +  _} >> {_  +  4} >> _ evalto 9 by C-EvalR {
                      8 >> { -2  *  _} >> { -3  <  _} >> {if _ then 8 else 2} >> {3  +  _} >> {_  +  4} >> _ evalto 9 by E-Int {
                        8 => { -2  *  _} >> { -3  <  _} >> {if _ then 8 else 2} >> {3  +  _} >> {_  +  4} >> _ evalto 9 by C-Times {
                          -2 times 8 is -16 by B-Times {};
                          -16 => { -3  <  _} >> {if _ then 8 else 2} >> {3  +  _} >> {_  +  4} >> _ evalto 9 by C-Lt {
                            -3 less than -16 is false by B-Lt {};
                            false => {if _ then 8 else 2} >> {3  +  _} >> {_  +  4} >> _ evalto 9 by C-IfF {
                              2 >> {3  +  _} >> {_  +  4} >> _ evalto 9 by E-Int {
                                2 => {3  +  _} >> {_  +  4} >> _ evalto 9 by C-Plus {
                                  3 plus 2 is 5 by B-Plus {};
                                  5 => {_  +  4} >> _ evalto 9 by C-EvalR {
                                    4 >> {5  +  _} >> _ evalto 9 by E-Int {
                                      4 => {5  +  _} >> _ evalto 9 by C-Plus {
                                        5 plus 4 is 9 by B-Plus {};
                                        9 => _ evalto 9 by C-Ret {};
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

