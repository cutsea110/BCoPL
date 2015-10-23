module ex6 where

open import BCoPL.NamelessML3

ex-6-1-1 : ● ⊱ "x" ⊱ "y" ⊢ if var "x" then var "y" ⊕ i (+ 1) else var "y" ⊝ i (+ 1)
                              ⟾
                              if # 2 then # 1 ⊕̂ i (+ 1) else # 1 ⊝̂ i (+ 1)
ex-6-1-1 = {!!}

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
