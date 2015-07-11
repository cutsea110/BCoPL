module ex1 where

open import BCoPL.Show
open import BCoPL.Nat

ex-plus-0 : S (S Z) plus S (S (S Z)) is S (S (S (S (S Z))))
ex-plus-0 = P-Succ (P-Succ P-Zero)
{-
S(S(Z)) plus S(S(S(Z))) is S(S(S(S(S(Z))))) by P-Succ {
  S(Z) plus S(S(S(Z))) is S(S(S(S(Z)))) by P-Succ {
    Z plus S(S(S(Z))) is S(S(S(Z))) by P-Zero {};
  };
};
-}

ex-times-0 : S (S Z) times S (S Z) is S (S (S (S Z)))
ex-times-0 = T-Succ (T-Succ T-Zero (P-Succ (P-Succ P-Zero))) (P-Succ (P-Succ P-Zero))
{-
S(S(Z)) times S(S(Z)) is S(S(S(S(Z)))) by T-Succ {
  S(Z) times S(S(Z)) is S(S(Z)) by T-Succ {
    Z times S(S(Z)) is Z by T-Zero {};
    S(S(Z)) plus Z is S(S(Z)) by P-Succ {
      S(Z) plus Z is S(Z) by P-Succ {
        Z plus Z is Z by P-Zero {};
      };
    };
  };
  S(S(Z)) plus S(S(Z)) is S(S(S(S(Z)))) by P-Succ {
    S(Z) plus S(S(Z)) is S(S(S(Z))) by P-Succ {
      Z plus S(S(Z)) is S(S(Z)) by P-Zero {};
    };
  };
};
-}

ex-1-1 : S (S Z) times S (S Z) is S (S (S (S Z)))
ex-1-1 = T-Succ (T-Succ T-Zero (P-Succ (P-Succ P-Zero))) (P-Succ (P-Succ P-Zero))
{--
-- C-cC-n (showDerivationTimes ex-1-1)
S(S(Z)) times S(S(Z)) is S(S(S(S(Z)))) by T-Succ {   -- step 9
  S(Z) times S(S(Z)) is S(S(Z)) by T-Succ {          -- step 5
    Z times S(S(Z)) is Z by T-Zero {};               -- step 1
    S(S(Z)) plus Z is S(S(Z)) by P-Succ {            -- step 4
      S(Z) plus Z is S(Z) by P-Succ {                -- step 3
        Z plus Z is Z by P-Zero {};                  -- step 2
      };
    };
  };
  S(S(Z)) plus S(S(Z)) is S(S(S(S(Z)))) by P-Succ {  -- step 8
    S(Z) plus S(S(Z)) is S(S(S(Z))) by P-Succ {      -- step 7
      Z plus S(S(Z)) is S(S(Z)) by P-Zero {};        -- step 6
    };
  };
};
--}

ex-1-2-1 : S (S (S Z)) plus S Z is S (S (S (S Z)))
ex-1-2-1 = P-Succ (P-Succ (P-Succ P-Zero))
{-
S(S(S(Z))) plus S(Z) is S(S(S(S(Z)))) by P-Succ {
  S(S(Z)) plus S(Z) is S(S(S(Z))) by P-Succ {
    S(Z) plus S(Z) is S(S(Z)) by P-Succ {
      Z plus S(Z) is S(Z) by P-Zero {};
    };
  };
};
-}

ex-1-2-2 : S Z plus S (S (S Z)) is S (S (S (S Z)))
ex-1-2-2 = P-Succ P-Zero
{-
S(Z) plus S(S(S(Z))) is S(S(S(S(Z)))) by P-Succ {
  Z plus S(S(S(Z))) is S(S(S(Z))) by P-Zero {};
};
-}

ex-1-2-3 : S (S (S Z)) times Z is Z
ex-1-2-3 = T-Succ (T-Succ (T-Succ T-Zero P-Zero) P-Zero) P-Zero
{-
S(S(S(Z))) times Z is Z by T-Succ {
  S(S(Z)) times Z is Z by T-Succ {
    S(Z) times Z is Z by T-Succ {
      Z times Z is Z by T-Zero {};
      Z plus Z is Z by P-Zero {};
    };
    Z plus Z is Z by P-Zero {};
  };
  Z plus Z is Z by P-Zero {};
};
-}

steps-plus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → ℕ
steps-plus P-Zero = 1
steps-plus (P-Succ p) = 1 + steps-plus p

steps-times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → ℕ
steps-times T-Zero = 1
steps-times (T-Succ p q) = 1 + steps-plus q + steps-times p

open import Relation.Binary.PropositionalEquality as PropEq

ex-1-3-1 : ∀ {n₁ n₂ n₃} → (p : n₁ plus n₂ is n₃) → steps-plus p ≡ 1 + n₁
ex-1-3-1 P-Zero = refl
ex-1-3-1 (P-Succ p) = cong S (ex-1-3-1 p)

ex-1-3-2 : ∀ {n₁ n₂ n₃} → (p : n₁ times n₂ is n₃) → steps-times p ≡ 1 + n₁ * (n₂ + 2)
ex-1-3-2 T-Zero = refl
ex-1-3-2 (T-Succ t p) = cong S (plus+times≡n₂+2+n₁[n₂+2] t p)
  where
    S[a+Sb]≡a+2+b : (a b : ℕ) → S (a + S b) ≡ a + 2 + b
    S[a+Sb]≡a+2+b Z b = refl
    S[a+Sb]≡a+2+b (S a) b = cong S (S[a+Sb]≡a+2+b a b)
    plus+times≡n₂+2+n₁[n₂+2] : ∀ {n₁ n₂ n₃ n₄}
                             (t : n₁ times n₂ is n₄) → (p : n₂ plus n₄ is n₃) →
                             steps-plus p + steps-times t ≡ n₂ + 2 + n₁ * (n₂ + 2)
    plus+times≡n₂+2+n₁[n₂+2] {n₁} {n₂} {n₃} {n₄} t p rewrite
      ex-1-3-1 p | ex-1-3-2 t | S[a+Sb]≡a+2+b n₂ (n₁ * (n₂ + 2)) = refl

ex-1-4-1 : S (S (S Z)) plus S Z is S (S (S (S Z)))
ex-1-4-1 = P-Succ (P-Succ (P-Succ P-Zero))
{-
S(S(S(Z))) plus S(Z) is S(S(S(S(Z)))) by P-Succ {
  S(S(Z)) plus S(Z) is S(S(S(Z))) by P-Succ {
    S(Z) plus S(Z) is S(S(Z)) by P-Succ {
      Z plus S(Z) is S(Z) by P-Zero {};
    };
  };
};
-}

ex-1-4-2 : S Z plus S (S (S Z)) is S (S (S (S Z)))
ex-1-4-2 = P-Succ P-Zero
{-
S(Z) plus S(S(S(Z))) is S(S(S(S(Z)))) by P-Succ {
  Z plus S(S(S(Z))) is S(S(S(Z))) by P-Zero {};
};
-}

ex-1-4-3 : S (S (S Z)) times Z is Z
ex-1-4-3 = T-Succ (T-Succ (T-Succ T-Zero P-Zero) P-Zero) P-Zero
{-
S(S(S(Z))) times Z is Z by T-Succ {
  S(S(Z)) times Z is Z by T-Succ {
    S(Z) times Z is Z by T-Succ {
      Z times Z is Z by T-Zero {};
      Z plus Z is Z by P-Zero {};
    };
    Z plus Z is Z by P-Zero {};
  };
  Z plus Z is Z by P-Zero {};
};
-}

open import BCoPL.CompareNat1 renaming (_is-less-than_ to _is-less-than1_)
open import BCoPL.CompareNat2 renaming (_is-less-than_ to _is-less-than2_)
open import BCoPL.CompareNat3 renaming (_is-less-than_ to _is-less-than3_)
open import BCoPL.Show.CompareNat1 renaming (showDerivationLessThan to showDerivationLessThan1)
open import BCoPL.Show.CompareNat2 renaming (showDerivationLessThan to showDerivationLessThan2)
open import BCoPL.Show.CompareNat3 renaming (showDerivationLessThan to showDerivationLessThan3)

open import BCoPL.EvalNatExp
open import BCoPL.Show.EvalNatExp

ex-1-8-1 : Nat Z ⊕ Nat (S (S Z)) ⇓ S (S Z)
ex-1-8-1 = E-Plus E-Const E-Const P-Zero
{-
Z + S(S(Z)) evalto S(S(Z)) by E-Plus {
  Z evalto Z by E-Const {};
  S(S(Z)) evalto S(S(Z)) by E-Const {};
  Z plus S(S(Z)) is S(S(Z)) by P-Zero {};
};
-}

ex-1-8-2 : Nat (S (S Z)) ⊕ Nat Z ⇓ S (S Z)
ex-1-8-2 = E-Plus E-Const E-Const (P-Succ (P-Succ P-Zero))
{-
S(S(Z)) + Z evalto S(S(Z)) by E-Plus {
  S(S(Z)) evalto S(S(Z)) by E-Const {};
  Z evalto Z by E-Const {};
  S(S(Z)) plus Z is S(S(Z)) by P-Succ {
    S(Z) plus Z is S(Z) by P-Succ {
      Z plus Z is Z by P-Zero {};
    };
  };
};
-}

ex-1-8-3 : Nat (S Z) ⊕ Nat (S Z) ⊕ Nat (S Z) ⇓ S (S (S Z))
ex-1-8-3 = E-Plus (E-Plus E-Const E-Const (P-Succ P-Zero)) E-Const
             (P-Succ (P-Succ P-Zero))
{-
S(Z) + S(Z) + S(Z) evalto S(S(S(Z))) by E-Plus {
  S(Z) + S(Z) evalto S(S(Z)) by E-Plus {
    S(Z) evalto S(Z) by E-Const {};
    S(Z) evalto S(Z) by E-Const {};
    S(Z) plus S(Z) is S(S(Z)) by P-Succ {
      Z plus S(Z) is S(Z) by P-Zero {};
    };
  };
  S(Z) evalto S(Z) by E-Const {};
  S(S(Z)) plus S(Z) is S(S(S(Z))) by P-Succ {
    S(Z) plus S(Z) is S(S(Z)) by P-Succ {
      Z plus S(Z) is S(Z) by P-Zero {};
    };
  };
};
-}

ex-1-8-4 : Nat (S (S (S Z))) ⊕ Nat (S (S Z)) ⊛ Nat (S Z) ⇓ S (S (S (S (S Z))))
ex-1-8-4 = E-Plus E-Const
             (E-Times E-Const E-Const
              (T-Succ (T-Succ T-Zero (P-Succ P-Zero)) (P-Succ P-Zero)))
             (P-Succ (P-Succ (P-Succ P-Zero)))
{-
S(S(S(Z))) + S(S(Z)) * S(Z) evalto S(S(S(S(S(Z))))) by E-Plus {
  S(S(S(Z))) evalto S(S(S(Z))) by E-Const {};
  S(S(Z)) * S(Z) evalto S(S(Z)) by E-Times {
    S(S(Z)) evalto S(S(Z)) by E-Const {};
    S(Z) evalto S(Z) by E-Const {};
    S(S(Z)) times S(Z) is S(S(Z)) by T-Succ {
      S(Z) times S(Z) is S(Z) by T-Succ {
        Z times S(Z) is Z by T-Zero {};
        S(Z) plus Z is S(Z) by P-Succ {
          Z plus Z is Z by P-Zero {};
        };
      };
      S(Z) plus S(Z) is S(S(Z)) by P-Succ {
        Z plus S(Z) is S(Z) by P-Zero {};
      };
    };
  };
  S(S(S(Z))) plus S(S(Z)) is S(S(S(S(S(Z))))) by P-Succ {
    S(S(Z)) plus S(S(Z)) is S(S(S(S(Z)))) by P-Succ {
      S(Z) plus S(S(Z)) is S(S(S(Z))) by P-Succ {
        Z plus S(S(Z)) is S(S(Z)) by P-Zero {};
      };
    };
  };
};
-}

ex-1-8-5 : (Nat (S (S Z)) ⊕ Nat (S (S Z))) ⊛ Nat Z ⇓ Z
ex-1-8-5 = E-Times (E-Plus E-Const E-Const (P-Succ (P-Succ P-Zero))) E-Const
             (T-Succ (T-Succ (T-Succ (T-Succ T-Zero P-Zero) P-Zero) P-Zero)
              P-Zero)
{-
S(S(Z)) + S(S(Z)) * Z evalto Z by E-Times {
  S(S(Z)) + S(S(Z)) evalto S(S(S(S(Z)))) by E-Plus {
    S(S(Z)) evalto S(S(Z)) by E-Const {};
    S(S(Z)) evalto S(S(Z)) by E-Const {};
    S(S(Z)) plus S(S(Z)) is S(S(S(S(Z)))) by P-Succ {
      S(Z) plus S(S(Z)) is S(S(S(Z))) by P-Succ {
        Z plus S(S(Z)) is S(S(Z)) by P-Zero {};
      };
    };
  };
  Z evalto Z by E-Const {};
  S(S(S(S(Z)))) times Z is Z by T-Succ {
    S(S(S(Z))) times Z is Z by T-Succ {
      S(S(Z)) times Z is Z by T-Succ {
        S(Z) times Z is Z by T-Succ {
          Z times Z is Z by T-Zero {};
          Z plus Z is Z by P-Zero {};
        };
        Z plus Z is Z by P-Zero {};
      };
      Z plus Z is Z by P-Zero {};
    };
    Z plus Z is Z by P-Zero {};
  };
};
-}

ex-1-8-6 : Nat Z ⊛ (Nat (S (S Z)) ⊕ Nat (S (S Z))) ⇓ Z
ex-1-8-6 = E-Times E-Const (E-Plus E-Const E-Const (P-Succ (P-Succ P-Zero)))
             T-Zero
{-
Z * S(S(Z)) + S(S(Z)) evalto Z by E-Times {
  Z evalto Z by E-Const {};
  S(S(Z)) + S(S(Z)) evalto S(S(S(S(Z)))) by E-Plus {
    S(S(Z)) evalto S(S(Z)) by E-Const {};
    S(S(Z)) evalto S(S(Z)) by E-Const {};
    S(S(Z)) plus S(S(Z)) is S(S(S(S(Z)))) by P-Succ {
      S(Z) plus S(S(Z)) is S(S(S(Z))) by P-Succ {
        Z plus S(S(Z)) is S(S(Z)) by P-Zero {};
      };
    };
  };
  Z times S(S(S(S(Z)))) is Z by T-Zero {};
};
-}

--- ReduceNatExp
open import BCoPL.ReduceNatExp
open import BCoPL.Show.ReduceNatExp

ex-1-9-1 : Nat Z ⊕ Nat (S (S Z)) -*-> Nat (S (S Z))
ex-1-9-1 = MR-One (R-Plus P-Zero)
{-
Z + S(S(Z)) -*-> S(S(Z)) by MR-One {
  Z + S(S(Z)) ---> S(S(Z)) by R-Plus {
    Z plus S(S(Z)) is S(S(Z)) by P-Zero {};
  };
};
-}

ex-1-9-2 : Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z) ⊛ Nat (S Z) -d-> Nat (S Z) ⊕ Nat (S Z) ⊛ Nat (S Z)
ex-1-9-2 = DR-PlusL (DR-Times (T-Succ T-Zero (P-Succ P-Zero)))
{-
S(Z) * S(Z) + S(Z) * S(Z) -d-> S(Z) + S(Z) * S(Z) by DR-PlusL {
  S(Z) * S(Z) -d-> S(Z) by DR-Times {
    S(Z) times S(Z) is S(Z) by T-Succ {
      Z times S(Z) is Z by T-Zero {};
      S(Z) plus Z is S(Z) by P-Succ {
        Z plus Z is Z by P-Zero {};
      };
    };
  };
};
-}

ex-1-9-3 : Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z) ⊛ Nat (S Z) ⟶ Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z)
ex-1-9-3 = R-PlusR (R-Times (T-Succ T-Zero (P-Succ P-Zero)))
{-
S(Z) * S(Z) + S(Z) * S(Z) ---> S(Z) * S(Z) + S(Z) by R-PlusR {
  S(Z) * S(Z) ---> S(Z) by R-Times {
    S(Z) times S(Z) is S(Z) by T-Succ {
      Z times S(Z) is Z by T-Zero {};
      S(Z) plus Z is S(Z) by P-Succ {
        Z plus Z is Z by P-Zero {};
      };
    };
  };
};
-}

ex-1-9-4 : (Nat (S Z) ⊛ Nat (S Z)) ⊕ (Nat (S Z) ⊛ Nat (S Z)) -*-> Nat (S (S Z))
ex-1-9-4 = MR-Multi (MR-One (R-PlusL (R-Times (T-Succ T-Zero (P-Succ P-Zero)))))
                    (MR-Multi (MR-One (R-PlusR (R-Times (T-Succ T-Zero (P-Succ P-Zero)))))
                              (MR-One (R-Plus (P-Succ P-Zero))))
{--
S(Z) * S(Z) + S(Z) * S(Z) -*-> S(S(Z)) by MR-Multi {
  S(Z) * S(Z) + S(Z) * S(Z) -*-> S(Z) + S(Z) * S(Z) by MR-One {
    S(Z) * S(Z) + S(Z) * S(Z) ---> S(Z) + S(Z) * S(Z) by R-PlusL {
      S(Z) * S(Z) ---> S(Z) by R-Times {
        S(Z) times S(Z) is S(Z) by T-Succ {
          Z times S(Z) is Z by T-Zero {};
          S(Z) plus Z is S(Z) by P-Succ {
            Z plus Z is Z by P-Zero {}
          }
        }
      }
    }
  };
  S(Z) + S(Z) * S(Z) -*-> S(S(Z)) by MR-Multi {
    S(Z) + S(Z) * S(Z) -*-> S(Z) + S(Z) by MR-One {
      S(Z) + S(Z) * S(Z) ---> S(Z) + S(Z) by R-PlusR {
        S(Z) * S(Z) ---> S(Z) by R-Times {
          S(Z) times S(Z) is S(Z) by T-Succ {
            Z times S(Z) is Z by T-Zero {};
            S(Z) plus Z is S(Z) by P-Succ {
              Z plus Z is Z by P-Zero {}
            }
          }
        }
      }
    };
    S(Z) + S(Z) -*-> S(S(Z)) by MR-One {
      S(Z) + S(Z) ---> S(S(Z)) by R-Plus {
        S(Z) plus S(Z) is S(S(Z)) by P-Succ {
          Z plus S(Z) is S(Z) by P-Zero {}
        }
      }
    }
  }
}
--}

open import BCoPL.ReduceNatExpR renaming (_-d->_ to _-d+>_)
open import BCoPL.Show.ReduceNatExpR renaming (showDerivation-d-> to showDerivation-d+>)

ex-1-10-1 : Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z) ⊛ Nat (S Z) -d+> Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z)
ex-1-10-1 = DR-PlusL (DR-Times (T-Succ T-Zero (P-Succ P-Zero)))
{-
S(Z) * S(Z) + S(Z) * S(Z) -d-> S(Z) * S(Z) + S(Z) by DR-PlusL {
  S(Z) * S(Z) -d-> S(Z) by DR-Times {
    S(Z) times S(Z) is S(Z) by T-Succ {
      Z times S(Z) is Z by T-Zero {};
      S(Z) plus Z is S(Z) by P-Succ {
        Z plus Z is Z by P-Zero {};
      };
    };
  };
};
-}

ex-1-10-2 : Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z) -d+> Nat (S Z) ⊕ Nat (S Z)
ex-1-10-2 = DR-PlusR (DR-Times (T-Succ T-Zero (P-Succ P-Zero)))
{-
S(Z) * S(Z) + S(Z) -d-> S(Z) + S(Z) by DR-PlusR {
  S(Z) * S(Z) -d-> S(Z) by DR-Times {
    S(Z) times S(Z) is S(Z) by T-Succ {
      Z times S(Z) is Z by T-Zero {};
      S(Z) plus Z is S(Z) by P-Succ {
        Z plus Z is Z by P-Zero {};
      };
    };
  };
};
-}
