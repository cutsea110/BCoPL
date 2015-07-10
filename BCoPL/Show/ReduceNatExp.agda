module BCoPL.Show.ReduceNatExp where

open import Data.String
open import BCoPL.Nat
open import BCoPL.ReduceNatExp
open import BCoPL.Show.EvalNatExp public

showDerivation⟶ : ∀ {e e′} → e ⟶ e′ → String
showDerivation-*-> : ∀  {e e′} → e -*-> e′ → String
showDerivation-d-> : ∀  {e e′} → e -d-> e′ → String

private

  showJudge⟶ : ∀ {e e′} → e ⟶ e′ → String
  showJudge⟶ (R-Plus p) = "R-Plus {" ++ showDerivationPlus p ++ "};"
  showJudge⟶ (R-Times t) = "R-Times {" ++ showDerivationTimes t ++ "};"
  showJudge⟶ (R-PlusL r) = "R-PlusL {" ++ showDerivation⟶ r ++ "};"
  showJudge⟶ (R-PlusR r) = "R-PlusR {" ++ showDerivation⟶ r ++ "};"
  showJudge⟶ (R-TimesL r) = "R-TimesL {" ++ showDerivation⟶ r ++ "};"
  showJudge⟶ (R-TimesR r) = "R-TimesR {" ++ showDerivation⟶ r ++ "};"

  showJudge-*-> : ∀ {e e′} → e -*-> e′ → String
  showJudge-*-> MR-Zero = "MR-Zero {};"
  showJudge-*-> (MR-One r) = "MR-One {" ++ showDerivation⟶ r ++ "};"
  showJudge-*-> (MR-Multi r₁ r₂) = "MR-Multi {" ++ showDerivation-*-> r₁ ++ showDerivation-*-> r₂ ++ "};"

  showJudge-d-> : ∀ {e e′} → e -d-> e′ → String
  showJudge-d-> (DR-Plus p) = "DR-Plus {" ++ showDerivationPlus p ++ "};"
  showJudge-d-> (DR-Times t) = "DR-Times {" ++ showDerivationTimes t ++ "};"
  showJudge-d-> (DR-PlusL r) = "DR-PlusL {" ++ showDerivation-d-> r ++ "};"
  showJudge-d-> (DR-PlusR r) = "DR-PlusR {" ++ showDerivation-d-> r ++ "};"
  showJudge-d-> (DR-TimesL r) = "DR-TimesL {" ++ showDerivation-d-> r ++ "};"
  showJudge-d-> (DR-TimesR r) = "DR-TimesR {" ++ showDerivation-d-> r ++ "};"

  showDerivation⟶ {e} {e′} p =
    showExp e ++ " ---> " ++ showExp e′ ++ " by " ++ showJudge⟶ p
  showDerivation-*-> {e} {e′} p =
    showExp e ++ " -*-> " ++ showExp e′ ++ " by " ++ showJudge-*-> p
  showDerivation-d-> {e} {e′} p =
    showExp e ++ " -d-> " ++ showExp e′ ++ " by " ++ showJudge-d-> p
