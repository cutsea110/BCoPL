module ex6 where

open import Data.Empty using (⊥)
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