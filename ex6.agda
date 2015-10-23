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
ex-6-1-2 = {!!}

ex-6-1-3 : ● ⊢ ℓet "x" ≔ ℓet "y" ≔ i (+ 3) ⊝ i (+ 2) ιn var "y" ⊛ var "y" ιn
                ℓet "y" ≔ i (+ 4) ιn var "x" ⊕ var "y"
               ⟾
               ℓeṭ≔ ℓeṭ≔ i (+ 3) ⊝̂ i (+ 2) ιn # 1 ⊛̂ # 1 ιn
               ℓeṭ≔ i (+ 4) ιn # 2 ⊕̂ # 1
ex-6-1-3 = {!!}
