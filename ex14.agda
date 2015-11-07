module ex14 where

open import BCoPL.While
open import BCoPL.Show.While

q151 : skip changes ● ⊱ ("s" , i (+ 0)) to ● ⊱ ("s" , i (+ 0))
q151 = C-Skip
{-
skip changes s = 0 to s = 0 by C-Skip {};
-}

q152 : "x" ≔ i (+ 1) changes ● ⊱ ("x" , i (+ 0)) to ● ⊱ ("x" , i (+ 1))
q152 = C-Assign A-Const refl
{-
x:=1 changes x = 0 to x = 1 by C-Assign {
  x = 0 |- 1 evalto 1 by A-Const {};
};
-}

q153 : "x" ≔ i (+ 1) >> "y" ≔ i (+ 2) changes ● ⊱ ("x" , i (+ 0)) ⊱ ("y" , i (+ 0)) to ● ⊱ ("x" , i (+ 1)) ⊱ ("y" , i (+ 2))
q153 = C-Seq (C-Assign A-Const refl) (C-Assign A-Const refl)
{-
x:=1;y:=2 changes x = 0,y = 0 to x = 1,y = 2 by C-Seq {
  x:=1 changes x = 0,y = 0 to x = 1,y = 0 by C-Assign {
    x = 0,y = 0 |- 1 evalto 1 by A-Const {};
  };
  y:=2 changes x = 1,y = 0 to x = 1,y = 2 by C-Assign {
    x = 1,y = 0 |- 2 evalto 2 by A-Const {};
  };
};
-}

q154 : "x" ≔ var "x" ⊕ i (+ 1) changes ● ⊱ ("x" , i (+ 2)) to ● ⊱ ("x" , i (+ 3))
q154 = C-Assign (A-Plus (A-Var refl) A-Const refl) refl
{-
x:=(x + 1) changes x = 2 to x = 3 by C-Assign {
  x = 2 |- (x + 1) evalto 3 by A-Plus {
    x = 2 |- x evalto 2 by A-Var {};
    x = 2 |- 1 evalto 1 by A-Const {};
  };
};
-}

q155 : if i (+ 1) ≺ var "x" then "x" ≔ i (+ 1) else "x" ≔ i (+ 2) changes ● ⊱ ("x" , i (+ 5)) to ● ⊱ ("x" , i (+ 1))
q155 = C-IfT (B-Lt A-Const (A-Var refl) refl) (C-Assign A-Const refl)
{-
if (1 < x) then x:=1 else x:=2 changes x = 5 to x = 1 by C-IfT {
  x = 5 |- (1 < x) evalto true by B-Lt {
    x = 5 |- 1 evalto 1 by A-Const {};
    x = 5 |- x evalto 5 by A-Var {};
  };
  x:=1 changes x = 5 to x = 1 by C-Assign {
    x = 5 |- 1 evalto 1 by A-Const {};
  };
};
-}

q156 : if i (+ 1) ≺ var "x" then "x" ≔ var "x" ⊕ i (+ 1) else "x" ≔ var "x" ⊕ i (+ 2) changes ● ⊱ ("x" , i (+ 0)) to ● ⊱ ("x" , i (+ 2))
q156 = C-IfF (B-Lt A-Const (A-Var refl) refl) (C-Assign (A-Plus (A-Var refl) A-Const refl) refl)
{-
if (1 < x) then x:=(x + 1) else x:=(x + 2) changes x = 0 to x = 2 by C-IfF {
  x = 0 |- (1 < x) evalto false by B-Lt {
    x = 0 |- 1 evalto 1 by A-Const {};
    x = 0 |- x evalto 0 by A-Var {};
  };
  x:=(x + 2) changes x = 0 to x = 2 by C-Assign {
    x = 0 |- (x + 2) evalto 2 by A-Plus {
      x = 0 |- x evalto 0 by A-Var {};
      x = 0 |- 2 evalto 2 by A-Const {};
    };
  };
};
-}

q157 : while i (+ 1) ≺ var "x" do ("x" ≔ var "x" ⊝ i (+ 1)) changes ● ⊱ ("x" , i (+ 3)) to ● ⊱ ("x" , i (+ 1))
q157 = C-WhileT (B-Lt A-Const (A-Var refl) refl) (C-Assign (A-Minus (A-Var refl) A-Const refl) refl) (C-WhileT (B-Lt A-Const (A-Var refl) refl) (C-Assign (A-Minus (A-Var refl) A-Const refl) refl) (C-WhileF (B-Lt A-Const (A-Var refl) refl)))
{-
while ((1 < x)) do x:=(x - 1) changes x = 3 to x = 1 by C-WhileT {
  x = 3 |- (1 < x) evalto true by B-Lt {
    x = 3 |- 1 evalto 1 by A-Const {};
    x = 3 |- x evalto 3 by A-Var {};
  };
  x:=(x - 1) changes x = 3 to x = 2 by C-Assign {
    x = 3 |- (x - 1) evalto 2 by A-Minus {
      x = 3 |- x evalto 3 by A-Var {};
      x = 3 |- 1 evalto 1 by A-Const {};
    };
  };
  while ((1 < x)) do x:=(x - 1) changes x = 2 to x = 1 by C-WhileT {
    x = 2 |- (1 < x) evalto true by B-Lt {
      x = 2 |- 1 evalto 1 by A-Const {};
      x = 2 |- x evalto 2 by A-Var {};
    };
    x:=(x - 1) changes x = 2 to x = 1 by C-Assign {
      x = 2 |- (x - 1) evalto 1 by A-Minus {
        x = 2 |- x evalto 2 by A-Var {};
        x = 2 |- 1 evalto 1 by A-Const {};
      };
    };
    while ((1 < x)) do x:=(x - 1) changes x = 1 to x = 1 by C-WhileF {
      x = 1 |- (1 < x) evalto false by B-Lt {
        x = 1 |- 1 evalto 1 by A-Const {};
        x = 1 |- x evalto 1 by A-Var {};
      };
    };
  };
};
-}

q158 : while i (+ 1) ≺ var "x" do ("x" ≔ var "x" ⊝ i (+ 1)) changes ● ⊱ ("x" , i (+ 0)) to ● ⊱ ("x" , i (+ 0))
q158 = C-WhileF (B-Lt A-Const (A-Var refl) refl)
{-
while ((1 < x)) do x:=(x - 1) changes x = 0 to x = 0 by C-WhileF {
  x = 0 |- (1 < x) evalto false by B-Lt {
    x = 0 |- 1 evalto 1 by A-Const {};
    x = 0 |- x evalto 0 by A-Var {};
  };
};
-}

q159 : while i (+ 0) ≺ var "i"
       do ("s" ≔ var "s" ⊕ var "i" >>
           "i" ≔ var "i" ⊝ i (+ 1))
       changes ● ⊱ ("s" , i (+ 0)) ⊱ ("i" , i (+ 1))
            to ● ⊱ ("s" , i (+ 1)) ⊱ ("i" , i (+ 0))
q159 = C-WhileT (B-Lt A-Const (A-Var refl) refl) (C-Seq (C-Assign (A-Plus (A-Var refl) (A-Var refl) refl) refl) (C-Assign (A-Minus (A-Var refl) A-Const refl) refl)) (C-WhileF (B-Lt A-Const (A-Var refl) refl))
{-
while ((0 < i)) do s:=(s + i);i:=(i - 1) changes s = 0,i = 1 to s = 1,i = 0 by C-WhileT {
  s = 0,i = 1 |- (0 < i) evalto true by B-Lt {
    s = 0,i = 1 |- 0 evalto 0 by A-Const {};
    s = 0,i = 1 |- i evalto 1 by A-Var {};
  };
  s:=(s + i);i:=(i - 1) changes s = 0,i = 1 to s = 1,i = 0 by C-Seq {
    s:=(s + i) changes s = 0,i = 1 to s = 1,i = 1 by C-Assign {
      s = 0,i = 1 |- (s + i) evalto 1 by A-Plus {
        s = 0,i = 1 |- s evalto 0 by A-Var {};
        s = 0,i = 1 |- i evalto 1 by A-Var {};
      };
    };
    i:=(i - 1) changes s = 1,i = 1 to s = 1,i = 0 by C-Assign {
      s = 1,i = 1 |- (i - 1) evalto 0 by A-Minus {
        s = 1,i = 1 |- i evalto 1 by A-Var {};
        s = 1,i = 1 |- 1 evalto 1 by A-Const {};
      };
    };
  };
  while ((0 < i)) do s:=(s + i);i:=(i - 1) changes s = 1,i = 0 to s = 1,i = 0 by C-WhileF {
    s = 1,i = 0 |- (0 < i) evalto false by B-Lt {
      s = 1,i = 0 |- 0 evalto 0 by A-Const {};
      s = 1,i = 0 |- i evalto 0 by A-Var {};
    };
  };
};
-}

q160 : while (i (+ 0) ≺ var "x") && (i (+ 0) ≺ var "y")
       do (if var "y" ≺ var "x"
           then "x" ≔ var "x" ⊝ i (+ 1)
           else "y" ≔ var "y" ⊝ i (+ 1))
       changes ● ⊱ ("x" , i (+ 2)) ⊱ ("y" , i (+ 2))
            to ● ⊱ ("x" , i (+ 1)) ⊱ ("y" , i (+ 0))
q160 = C-WhileT (B-And (B-Lt A-Const (A-Var refl) refl) (B-Lt A-Const (A-Var refl) refl) refl) (C-IfF (B-Lt (A-Var refl) (A-Var refl) refl) (C-Assign (A-Minus (A-Var refl) A-Const refl) refl)) (C-WhileT (B-And (B-Lt A-Const (A-Var refl) refl) (B-Lt A-Const (A-Var refl) refl) refl) (C-IfT (B-Lt (A-Var refl) (A-Var refl) refl) (C-Assign (A-Minus (A-Var refl) A-Const refl) refl)) (C-WhileT (B-And (B-Lt A-Const (A-Var refl) refl) (B-Lt A-Const (A-Var refl) refl) refl) (C-IfF (B-Lt (A-Var refl) (A-Var refl) refl) (C-Assign (A-Minus (A-Var refl) A-Const refl) refl)) (C-WhileF (B-And (B-Lt A-Const (A-Var refl) refl) (B-Lt A-Const (A-Var refl) refl) refl))))
{-
while (((0 < x) && (0 < y))) do if (y < x) then x:=(x - 1) else y:=(y - 1) changes x = 2,y = 2 to x = 1,y = 0 by C-WhileT {x = 2,y = 2 |- ((0 < x) && (0 < y)) evalto true by B-And {x = 2,y = 2 |- (0 < x) evalto true by B-Lt {x = 2,y = 2 |- 0 evalto 0 by A-Const {};x = 2,y = 2 |- x evalto 2 by A-Var {};};x = 2,y = 2 |- (0 < y) evalto true by B-Lt {x = 2,y = 2 |- 0 evalto 0 by A-Const {};x = 2,y = 2 |- y evalto 2 by A-Var {};};};if (y < x) then x:=(x - 1) else y:=(y - 1) changes x = 2,y = 2 to x = 2,y = 1 by C-IfF {x = 2,y = 2 |- (y < x) evalto false by B-Lt {x = 2,y = 2 |- y evalto 2 by A-Var {};x = 2,y = 2 |- x evalto 2 by A-Var {};};y:=(y - 1) changes x = 2,y = 2 to x = 2,y = 1 by C-Assign {x = 2,y = 2 |- (y - 1) evalto 1 by A-Minus {x = 2,y = 2 |- y evalto 2 by A-Var {};x = 2,y = 2 |- 1 evalto 1 by A-Const {};};};};while (((0 < x) && (0 < y))) do if (y < x) then x:=(x - 1) else y:=(y - 1) changes x = 2,y = 1 to x = 1,y = 0 by C-WhileT {x = 2,y = 1 |- ((0 < x) && (0 < y)) evalto true by B-And {x = 2,y = 1 |- (0 < x) evalto true by B-Lt {x = 2,y = 1 |- 0 evalto 0 by A-Const {};x = 2,y = 1 |- x evalto 2 by A-Var {};};x = 2,y = 1 |- (0 < y) evalto true by B-Lt {x = 2,y = 1 |- 0 evalto 0 by A-Const {};x = 2,y = 1 |- y evalto 1 by A-Var {};};};if (y < x) then x:=(x - 1) else y:=(y - 1) changes x = 2,y = 1 to x = 1,y = 1 by C-IfT {x = 2,y = 1 |- (y < x) evalto true by B-Lt {x = 2,y = 1 |- y evalto 1 by A-Var {};x = 2,y = 1 |- x evalto 2 by A-Var {};};x:=(x - 1) changes x = 2,y = 1 to x = 1,y = 1 by C-Assign {x = 2,y = 1 |- (x - 1) evalto 1 by A-Minus {x = 2,y = 1 |- x evalto 2 by A-Var {};x = 2,y = 1 |- 1 evalto 1 by A-Const {};};};};while (((0 < x) && (0 < y))) do if (y < x) then x:=(x - 1) else y:=(y - 1) changes x = 1,y = 1 to x = 1,y = 0 by C-WhileT {x = 1,y = 1 |- ((0 < x) && (0 < y)) evalto true by B-And {x = 1,y = 1 |- (0 < x) evalto true by B-Lt {x = 1,y = 1 |- 0 evalto 0 by A-Const {};x = 1,y = 1 |- x evalto 1 by A-Var {};};x = 1,y = 1 |- (0 < y) evalto true by B-Lt {x = 1,y = 1 |- 0 evalto 0 by A-Const {};x = 1,y = 1 |- y evalto 1 by A-Var {};};};if (y < x) then x:=(x - 1) else y:=(y - 1) changes x = 1,y = 1 to x = 1,y = 0 by C-IfF {x = 1,y = 1 |- (y < x) evalto false by B-Lt {x = 1,y = 1 |- y evalto 1 by A-Var {};x = 1,y = 1 |- x evalto 1 by A-Var {};};y:=(y - 1) changes x = 1,y = 1 to x = 1,y = 0 by C-Assign {x = 1,y = 1 |- (y - 1) evalto 0 by A-Minus {x = 1,y = 1 |- y evalto 1 by A-Var {};x = 1,y = 1 |- 1 evalto 1 by A-Const {};};};};while (((0 < x) && (0 < y))) do if (y < x) then x:=(x - 1) else y:=(y - 1) changes x = 1,y = 0 to x = 1,y = 0 by C-WhileF {x = 1,y = 0 |- ((0 < x) && (0 < y)) evalto false by B-And {x = 1,y = 0 |- (0 < x) evalto true by B-Lt {x = 1,y = 0 |- 0 evalto 0 by A-Const {};x = 1,y = 0 |- x evalto 1 by A-Var {};};x = 1,y = 0 |- (0 < y) evalto false by B-Lt {x = 1,y = 0 |- 0 evalto 0 by A-Const {};x = 1,y = 0 |- y evalto 0 by A-Var {};};};};};};};
-}
