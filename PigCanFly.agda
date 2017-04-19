module PigCanFly where

-- | discussion for completeness vs soundness
-- ref. japanese wikipedia for soundness
--
{--
健全な論証
==========

次のような健全な論証があるとする（三段論法）。

全ての人間は死ぬ。
ソクラテスは人間である。
従って、ソクラテスは死ぬ。

この論証は妥当であり（前提から結論が導かれ、前提を真とすれば結論が真であるため）、前提が真なので、論証全体としては健全である。

以下の論証は妥当だが、健全ではない。

全ての動物は飛ぶことができる。
豚は動物である。
従って、豚は飛ぶことができる。

大前提は実際には偽であるため、この論証は妥当だが健全ではない。
--}
open import Relation.Nullary using (¬_)
import Relation.Nullary.Negation

data Animal : Set where
  bird : Animal
  pig : Animal

data _CanFly : Animal → Set where
  bird-can-fly : bird CanFly

pig-can-fly : (∀ x → x CanFly) → pig CanFly
pig-can-fly prf = prf pig

pig-can't-fly : ¬ pig CanFly
pig-can't-fly ()
