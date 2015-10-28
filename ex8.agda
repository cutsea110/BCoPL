module ex8 where

open import BCoPL.TypingEvalML4
open import BCoPL.Show.TypingEvalML4

ex-8-1-1 : ● ⊢ i (+ 3) ⊕ i (+ 5) ∶ int
ex-8-1-1 = T-Plus T-Int T-Int
{-
|- (3 + 5) : int by T-Plus {
  |- 3 : int by T-Int {};
  |- 5 : int by T-Int {};
};
-}
