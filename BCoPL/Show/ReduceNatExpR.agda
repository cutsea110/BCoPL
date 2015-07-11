module BCoPL.Show.ReduceNatExpR where

open import Data.String
open import BCoPL.ReduceNatExpR
open import BCoPL.Show.EvalNatExp public

showDerivation-d-> : ∀  {e e′} → e -d-> e′ → String

private
  showJudge-d-> : ∀ {e e′} → e -d-> e′ → String
  showJudge-d-> (DR-Plus p) = "DR-Plus {" ++ showDerivationPlus p ++ "};"
  showJudge-d-> (DR-Times t) = "DR-Times {" ++ showDerivationTimes t ++ "};"
  showJudge-d-> (DR-PlusL r) = "DR-PlusL {" ++ showDerivation-d-> r ++ "};"
  showJudge-d-> (DR-PlusR r) = "DR-PlusR {" ++ showDerivation-d-> r ++ "};"
  showJudge-d-> (DR-TimesL r) = "DR-TimesL {" ++ showDerivation-d-> r ++ "};"
  showJudge-d-> (DR-TimesR r) = "DR-TimesR {" ++ showDerivation-d-> r ++ "};"

  showDerivation-d-> {e} {e′} p =
    showExp e ++ " -d-> " ++ showExp e′ ++ " by " ++ showJudge-d-> p
