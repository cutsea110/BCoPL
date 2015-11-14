module q47 where

open import IO
open import BCoPL.Show.EvalML3
open import ex5

main = run (putStrLn (showDerivation⇓ q47))
