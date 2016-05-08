module PigCanFly where

-- | discussion for completeness vs soundness
-- ref. japanese wikipedia for soundness
--
open import Relation.Nullary using (¬_)

data Animal : Set where
  bird : Animal
  pig : Animal

data _CanFly : Animal → Set where
  bird-can-fly : bird CanFly

pig-can-fly : (∀ x → x CanFly) → pig CanFly
pig-can-fly prf = prf pig

pig-can't-fly : ¬ pig CanFly
pig-can't-fly ()
