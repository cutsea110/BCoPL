module BCoPL.ReduceNatExp.Properties where

open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq

open import BCoPL.Nat.Properties
open import BCoPL.EvalNatExp.Properties

-- theorem 2.21
open import BCoPL.ReduceNatExp
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Core using (¬_)

notPeano : (e : Exp) → Set
notPeano (Nat n) = ⊥
notPeano (e₁ ⊕ e₂) = ⊤
notPeano (e₁ ⊛ e₂) = ⊤

reduceability-⟶ : (e : Exp) → notPeano e → ∃ λ e′ → e ⟶ e′
reduceability-⟶ (Nat n) ()
reduceability-⟶ (Nat n₁ ⊕ Nat n₂) tt = Nat (n₁ + n₂) , R-Plus (eval-plus n₁ n₂)
reduceability-⟶ (Nat n₁ ⊕ (e₂ ⊕ e₃)) tt with reduceability-⟶ (e₂ ⊕ e₃) tt
... | proj₁ , proj₂ = (Nat n₁ ⊕ proj₁) , R-PlusR proj₂
reduceability-⟶ (Nat n₁ ⊕ (e₂ ⊛ e₃)) tt with reduceability-⟶ (e₂ ⊛ e₃) tt
... | proj₁ , proj₂ = (Nat n₁ ⊕ proj₁) , R-PlusR proj₂
reduceability-⟶ ((e₁ ⊕ e₂) ⊕ e₃) tt with reduceability-⟶ (e₁ ⊕ e₂) tt
... | proj₁ , proj₂ = (proj₁ ⊕ e₃) , R-PlusL proj₂
reduceability-⟶ ((e₁ ⊛ e₂) ⊕ e₃) tt with reduceability-⟶ (e₁ ⊛ e₂) tt
... | proj₁ , proj₂ = (proj₁ ⊕ e₃) , R-PlusL proj₂
reduceability-⟶ (Nat n₁ ⊛ Nat n₂) tt = (Nat (n₁ * n₂)) , (R-Times (eval-times n₁ n₂))
reduceability-⟶ (Nat n₁ ⊛ (e₂ ⊕ e₃)) tt with reduceability-⟶ (e₂ ⊕ e₃) tt
... | proj₁ , proj₂ = Nat n₁ ⊛ proj₁ , R-TimesR proj₂
reduceability-⟶ (Nat n₁ ⊛ (e₂ ⊛ e₃)) tt with reduceability-⟶ (e₂ ⊛ e₃) tt
... | proj₁ , proj₂ = Nat n₁ ⊛ proj₁ , R-TimesR proj₂
reduceability-⟶ ((e₁ ⊕ e₂) ⊛ e₃) tt with reduceability-⟶ (e₁ ⊕ e₂) tt
... | proj₁ , proj₂ = proj₁ ⊛ e₃ , R-TimesL proj₂
reduceability-⟶ ((e₁ ⊛ e₂) ⊛ e₃) tt with reduceability-⟶ (e₁ ⊛ e₂) tt
... | proj₁ , proj₂ = proj₁ ⊛ e₃ , R-TimesL proj₂

-- theorem 2.22
reduce-same-exp : ∀ {e₁ e₂ e₃} → notPeano e₁ × notPeano e₂ × notPeano e₃ →
  e₁ ⟶ e₂ × e₁ ⟶ e₃ → ∃ λ e₄ → e₂ ⟶ e₄ × e₃ ⟶ e₄
reduce-same-exp {Nat x} (() , ¬Pe₂ , ¬Pe₃) prf
reduce-same-exp {e₁ ⊕ e₂} {Nat x} (¬Pe₁ , () , ¬Pe₃) prf
reduce-same-exp {e₁ ⊕ e₂} {e₃ = Nat x} (¬Pe₁ , ¬Pe₂ , ()) prf
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊕ .e₂} {e₅ ⊕ .e₂} ¬Pe (R-PlusL x₁ , R-PlusL x₂) with reduce-same-exp {e₁} {e₃} {e₅} {!!} (x₁ , x₂)
... | e₁′ , x₁′ , x₂′ = (e₁′ ⊕ e₂) , (R-PlusL x₁′ , R-PlusL x₂′)
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊕ .e₂} {.e₁ ⊕ e₆} ¬Pe (R-PlusL x₁ , R-PlusR x₂)
  = (e₃ ⊕ e₆) , (R-PlusR x₂ , R-PlusL x₁)
reduce-same-exp {e₁ ⊕ e₂} {.e₁ ⊕ e₄} {e₅ ⊕ .e₂} ¬Pe (R-PlusR x₁ , R-PlusL x₂)
  = (e₅ ⊕ e₄) , (R-PlusL x₂ , R-PlusR x₁)
reduce-same-exp {e₁ ⊕ e₂} {.e₁ ⊕ e₄} {.e₁ ⊕ e₆} ¬Pe (R-PlusR x₁ , R-PlusR x₂) with reduce-same-exp {e₂} {e₄} {e₆} {!!} (x₁ , x₂)
... | e₂′ , x₁′ , x₂′ = (e₁ ⊕ e₂′) , (R-PlusR x₁′ , R-PlusR x₂′)
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊕ e₄} {e₅ ⊛ e₆} ¬Pe (x₁ , ())
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊛ e₄} ¬Pe (() , x₂)
reduce-same-exp {e₁ ⊛ e₂} {Nat x} (proj₁ , () , proj₃) prf
reduce-same-exp {e₁ ⊛ e₂} {e₃ = Nat x} (proj₁ , proj₂ , ()) prf
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊕ e₄} ¬Pe (() , x₂)
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊛ e₄} {e₅ ⊕ e₆} ¬Pe (x₁ , ())
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊛ .e₂} {e₅ ⊛ .e₂} ¬Pe (R-TimesL x₁ , R-TimesL x₂) with reduce-same-exp {e₁} {e₃} {e₅} {!!} (x₁ , x₂)
... | e₁′ , x₁′ , x₂′ = (e₁′ ⊛ e₂) , (R-TimesL x₁′ , R-TimesL x₂′)
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊛ .e₂} {.e₁ ⊛ e₆} ¬Pe (R-TimesL x₁ , R-TimesR x₂)
  = (e₃ ⊛ e₆) , (R-TimesR x₂ , R-TimesL x₁)
reduce-same-exp {e₁ ⊛ e₂} {.e₁ ⊛ e₄} {e₅ ⊛ .e₂} ¬Pe (R-TimesR x₁ , R-TimesL x₂)
  = (e₅ ⊛ e₄) , (R-TimesL x₂ , R-TimesR x₁)
reduce-same-exp {e₁ ⊛ e₂} {.e₁ ⊛ e₄} {.e₁ ⊛ e₆} ¬Pe (R-TimesR x₁ , R-TimesR x₂) with reduce-same-exp {e₂} {e₄} {e₆} {!!} (x₁ , x₂)
... | e₂′ , x₁′ , x₂′ = (e₁ ⊛ e₂′) , (R-TimesR x₁′ , R-TimesR x₂′)
{--
reduce-same-exp {Nat n} (() , x₂)
reduce-same-exp {._ ⊕ ._} {Nat n₁} {Nat n₂} (R-Plus x₁ , R-Plus x₂) = {!!}
reduce-same-exp {._ ⊕ ._} {Nat n₁} {e₃ ⊕ ._} (R-Plus x₁ , R-PlusL ())
reduce-same-exp {._ ⊕ ._} {Nat n₁} {._ ⊕ e₄} (R-Plus x₁ , R-PlusR ())
reduce-same-exp {._ ⊕ ._} {Nat n₁} {e₃ ⊛ e₄} (R-Plus x₁ , ())
reduce-same-exp {._ ⊕ ._} {e₃ ⊕ ._} {Nat n₂} (R-PlusL () , R-Plus x₂)
reduce-same-exp {._ ⊕ ._} {._ ⊕ e₄} {Nat n₂} (R-PlusR () , R-Plus x₂)
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊕ .e₂} {e₅ ⊕ .e₂} (R-PlusL x₁ , R-PlusL x₂) with reduce-same-exp (x₁ , x₂)
... | proj₁ , proj₂ , proj₃ = (proj₁ ⊕ e₂) , R-PlusL proj₂ , R-PlusL proj₃
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊕ .e₂} {.e₁ ⊕ e₆} (R-PlusL x₁ , R-PlusR x₂)
  = (e₃ ⊕ e₆) , R-PlusR x₂ , R-PlusL x₁
reduce-same-exp {e₁ ⊕ e₂} {.e₁ ⊕ e₄} {e₅ ⊕ .e₂} (R-PlusR x₁ , R-PlusL x₂)
  = (e₅ ⊕ e₄) , R-PlusL x₂ , R-PlusR x₁
reduce-same-exp {e₁ ⊕ e₂} {.e₁ ⊕ e₄} {.e₁ ⊕ e₆} (R-PlusR x₁ , R-PlusR x₂) with reduce-same-exp (x₁ , x₂)
... | proj₁ , proj₂ , proj₃ = (e₁ ⊕ proj₁) , R-PlusR proj₂ , R-PlusR proj₃
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊕ e₄} {e₅ ⊛ e₆} (x₁ , ())
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊛ e₄} (() , x₂)
reduce-same-exp {._ ⊛ ._} {Nat n₁} {Nat n₂} (R-Times x₁ , R-Times x₂) = {!!}
reduce-same-exp {e₁ ⊛ e₂} {Nat n₁} {e₃ ⊕ e₄} (x₁ , ())
reduce-same-exp {._ ⊛ ._} {Nat n₁} {e₃ ⊛ ._} (R-Times x₁ , R-TimesL ())
reduce-same-exp {._ ⊛ ._} {Nat n₁} {._ ⊛ e₄} (R-Times x₁ , R-TimesR ())
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊕ e₄} (() , x₂)
reduce-same-exp {._ ⊛ ._} {e₃ ⊛ ._} {Nat n₂} (R-TimesL () , R-Times x₂)
reduce-same-exp {._ ⊛ ._} {._ ⊛ e₄} {Nat n₂} (R-TimesR () , R-Times x₂)
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊛ e₄} {e₅ ⊕ e₆} (x₁ , ())
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊛ .e₂} {e₅ ⊛ .e₂} (R-TimesL x₁ , R-TimesL x₂) with reduce-same-exp (x₁ , x₂)
... | proj₁ , proj₂ , proj₃ = proj₁ ⊛ e₂ , R-TimesL proj₂ , R-TimesL proj₃
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊛ .e₂} {.e₁ ⊛ e₆} (R-TimesL x₁ , R-TimesR x₂)
  = (e₃ ⊛ e₆) , R-TimesR x₂ , R-TimesL x₁
reduce-same-exp {e₁ ⊛ e₂} {.e₁ ⊛ e₄} {e₅ ⊛ .e₂} (R-TimesR x₁ , R-TimesL x₂)
  = (e₅ ⊛ e₄) , R-TimesL x₂ , R-TimesR x₁
reduce-same-exp {e₁ ⊛ e₂} {.e₁ ⊛ e₄} {.e₁ ⊛ e₆} (R-TimesR x₁ , R-TimesR x₂) with reduce-same-exp (x₁ , x₂)
... | proj₁ , proj₂ , proj₃ = e₁ ⊛ proj₁ , R-TimesR proj₂ , R-TimesR proj₃
--}

-- theorem 2.23
uniqueness--d-> : ∀ {e e′ e″} → e -d-> e′ × e -d-> e″ → e′ ≡ e″
uniqueness--d-> (DR-Plus x₁ , DR-Plus x₂) rewrite uniqueness-plus (x₁ , x₂) = refl
uniqueness--d-> (DR-Plus x₁ , DR-PlusL ())
uniqueness--d-> (DR-Plus x₁ , DR-PlusR ())
uniqueness--d-> (DR-Times x₁ , DR-Times x₂) rewrite uniqueness-times (x₁ , x₂) = refl
uniqueness--d-> (DR-Times x₁ , DR-TimesL ())
uniqueness--d-> (DR-Times x₁ , DR-TimesR ())
uniqueness--d-> (DR-PlusL () , DR-Plus x₂)
uniqueness--d-> (DR-PlusL x₁ , DR-PlusL x₂) rewrite uniqueness--d-> (x₁ , x₂) = refl
uniqueness--d-> (DR-PlusL () , DR-PlusR x₂)
uniqueness--d-> (DR-PlusR () , DR-Plus x₂)
uniqueness--d-> (DR-PlusR x₁ , DR-PlusL ())
uniqueness--d-> (DR-PlusR x₁ , DR-PlusR x₂) rewrite uniqueness--d-> (x₁ , x₂) = refl
uniqueness--d-> (DR-TimesL () , DR-Times x₂)
uniqueness--d-> (DR-TimesL x₁ , DR-TimesL x₂) rewrite uniqueness--d-> (x₁ , x₂) = refl
uniqueness--d-> (DR-TimesL () , DR-TimesR x₂)
uniqueness--d-> (DR-TimesR () , DR-Times x₂)
uniqueness--d-> (DR-TimesR x₁ , DR-TimesL ())
uniqueness--d-> (DR-TimesR x₁ , DR-TimesR x₂) rewrite uniqueness--d-> (x₁ , x₂) = refl

-- theorem 2.24
-d->→⟶ : ∀ {e e′} → e -d-> e′ → e ⟶ e′
-d->→⟶ (DR-Plus x) = R-Plus x
-d->→⟶ (DR-Times x) = R-Times x
-d->→⟶ (DR-PlusL p) with -d->→⟶ p
... | prf = R-PlusL prf
-d->→⟶ (DR-PlusR p) with -d->→⟶ p
... | prf = R-PlusR prf
-d->→⟶ (DR-TimesL p) with -d->→⟶ p
... | prf = R-TimesL prf
-d->→⟶ (DR-TimesR p) with -d->→⟶ p
... | prf = R-TimesR prf

-- theorem 2.25
weak-normalization : (e : Exp) → ∃ λ n → e -*-> n
weak-normalization (Nat n) = (Nat n) , MR-Zero
weak-normalization (e₁ ⊕ e₂) with weak-normalization e₁ | weak-normalization e₂
... | prf₁ | prf₂ = (e₁ ⊕ e₂) , MR-Zero
weak-normalization (e₁ ⊛ e₂) with weak-normalization e₁ | weak-normalization e₂
... | prf₁ | prf₂ = e₁ ⊛ e₂ , MR-Zero

-- theorem 2.26
-- size? p42?


-- theorem 2.27
left-reduction-⊕ : ∀ {e₁ e₁′ e₂} → e₁ -*-> e₁′ → e₁ ⊕ e₂ -*-> e₁′ ⊕ e₂
left-reduction-⊕ MR-Zero = MR-Zero
left-reduction-⊕ (MR-One x) = MR-One (R-PlusL x)
left-reduction-⊕ (MR-Multi x x₁) = MR-Multi (left-reduction-⊕ x) (left-reduction-⊕ x₁)

right-reduction-⊕ : ∀ {e₁ e₂ e₂′} → e₂ -*-> e₂′ → e₁ ⊕ e₂ -*-> e₁ ⊕ e₂′
right-reduction-⊕ MR-Zero = MR-Zero
right-reduction-⊕ (MR-One x) = MR-One (R-PlusR x)
right-reduction-⊕ (MR-Multi p p₁) = MR-Multi (right-reduction-⊕ p) (right-reduction-⊕ p₁)

both-reduction-⊕ : ∀ {e₁ e₂ n₁ n₂} → e₁ -*-> Nat n₁ → e₂ -*-> Nat n₂ → e₁ ⊕ e₂ -*-> Nat n₁ ⊕ Nat n₂
both-reduction-⊕ p q = MR-Multi (left-reduction-⊕ p) (right-reduction-⊕ q)

left-reduction-⊛ : ∀ {e₁ e₁′ e₂} → e₁ -*-> e₁′ → e₁ ⊛ e₂ -*-> e₁′ ⊛ e₂
left-reduction-⊛ MR-Zero = MR-Zero
left-reduction-⊛ (MR-One x) = MR-One (R-TimesL x)
left-reduction-⊛ (MR-Multi p p₁) = MR-Multi (left-reduction-⊛ p) (left-reduction-⊛ p₁)

right-reduction-⊛ : ∀ {e₁ e₂ e₂′} → e₂ -*-> e₂′ → e₁ ⊛ e₂ -*-> e₁ ⊛ e₂′
right-reduction-⊛ MR-Zero = MR-Zero
right-reduction-⊛ (MR-One x) = MR-One (R-TimesR x)
right-reduction-⊛ (MR-Multi p p₁) = MR-Multi (right-reduction-⊛ p) (right-reduction-⊛ p₁)

both-reduction-⊛ : ∀ {e₁ e₂ n₁ n₂} → e₁ -*-> Nat n₁ → e₂ -*-> Nat n₂ → e₁ ⊛ e₂ -*-> Nat n₁ ⊛ Nat n₂
both-reduction-⊛ p q = MR-Multi (left-reduction-⊛ p) (right-reduction-⊛ q)

⇓→-*-> : ∀ {e n} → e ⇓ n → e -*-> Nat n
⇓→-*-> E-Const = MR-Zero
⇓→-*-> (E-Plus e₁ e₂ p) with ⇓→-*-> e₁ | ⇓→-*-> e₂
... | MR-Zero | MR-Zero
  = MR-One (R-Plus p)
... | MR-Zero | MR-One x
  = MR-Multi (MR-One (R-PlusR x)) (MR-One (R-Plus p))
... | MR-Zero | MR-Multi prf₂ prf₃
  = MR-Multi (right-reduction-⊕ (MR-Multi prf₂ prf₃)) (MR-One (R-Plus p))
... | MR-One x | MR-Zero
  = MR-Multi (MR-One (R-PlusL x)) (MR-One (R-Plus p))
... | MR-One x | MR-One x₁
  = MR-Multi (MR-One (R-PlusL x)) (MR-Multi (MR-One (R-PlusR x₁)) (MR-One (R-Plus p)))
... | MR-One x | MR-Multi prf₂ prf₃
  = MR-Multi (both-reduction-⊕ (MR-One x) (MR-Multi prf₂ prf₃)) (MR-One (R-Plus p))
... | MR-Multi prf₁ prf₂ | MR-Zero
  = MR-Multi (left-reduction-⊕ (MR-Multi prf₁ prf₂)) (MR-One (R-Plus p))
... | MR-Multi prf₁ prf₂ | MR-One x
  = MR-Multi (both-reduction-⊕ (MR-Multi prf₁ prf₂) (MR-One x)) (MR-One (R-Plus p))
... | MR-Multi prf₁ prf₂ | MR-Multi prf₃ prf₄
  = MR-Multi (both-reduction-⊕ (MR-Multi prf₁ prf₂) (MR-Multi prf₃ prf₄)) (MR-One (R-Plus p))
⇓→-*-> (E-Times e₁ e₂ t) with ⇓→-*-> e₁ | ⇓→-*-> e₂
... | MR-Zero | MR-Zero
  = MR-One (R-Times t)
... | MR-Zero | MR-One x
  = MR-Multi (MR-One (R-TimesR x)) (MR-One (R-Times t))
... | MR-Zero | MR-Multi prf₂ prf₃
  = MR-Multi (right-reduction-⊛ (MR-Multi prf₂ prf₃)) (MR-One (R-Times t))
... | MR-One x | MR-Zero
  = MR-Multi (MR-One (R-TimesL x)) (MR-One (R-Times t))
... | MR-One x | MR-One x₁
  = MR-Multi (MR-Multi (MR-One (R-TimesL x)) (MR-One (R-TimesR x₁))) (MR-One (R-Times t))
... | MR-One x | MR-Multi prf₂ prf₃
  = MR-Multi (both-reduction-⊛ (MR-One x) (MR-Multi prf₂ prf₃)) (MR-One (R-Times t))
... | MR-Multi prf₁ prf₂ | MR-Zero
  = MR-Multi (left-reduction-⊛ (MR-Multi prf₁ prf₂)) (MR-One (R-Times t))
... | MR-Multi prf₁ prf₂ | MR-One x
  = MR-Multi (both-reduction-⊛ (MR-Multi prf₁ prf₂) (MR-One x)) (MR-One (R-Times t))
... | MR-Multi prf₁ prf₂ | MR-Multi prf₃ prf₄
  = MR-Multi (both-reduction-⊛ (MR-Multi prf₁ prf₂) (MR-Multi prf₃ prf₄)) (MR-One (R-Times t))

-- theorem 2.28
n-*->e→e≡n : ∀ {e n} → Nat n -*-> e → e ≡ Nat n
n-*->e→e≡n MR-Zero = refl
n-*->e→e≡n (MR-One ())
n-*->e→e≡n (MR-Multi p₁ p₂) rewrite n-*->e→e≡n p₁ | n-*->e→e≡n p₂ = refl

left-⇓-⊕ : ∀ {e₁ e₂ n₁ n} → e₁ ⇓ n₁ → e₁ ⊕ e₂ ⇓ n → Nat n₁ ⊕ e₂ ⇓ n
left-⇓-⊕ {e₁} {e₂} {n₁} {n} p (E-Plus q₁ q₂ x) rewrite uniqueness-⇓ (p , q₁) = E-Plus E-Const q₂ x

right-⇓-⊕ : ∀ {e₁ e₂ n₂ n} → e₂ ⇓ n₂ → e₁ ⊕ e₂ ⇓ n → e₁ ⊕ Nat n₂ ⇓ n
right-⇓-⊕ {e₁} {e₂} {n₂} {n} p (E-Plus q₁ q₂ x) rewrite uniqueness-⇓ (p , q₂) = E-Plus q₁ E-Const x

left-⇓-⊛ : ∀ {e₁ e₂ n₁ n} → e₁ ⇓ n₁ → e₁ ⊛ e₂ ⇓ n → Nat n₁ ⊛ e₂ ⇓ n
left-⇓-⊛ {e₁} {e₂} {n₁} {n} p (E-Times q₁ q₂ x) rewrite uniqueness-⇓ (p , q₁) = E-Times E-Const q₂ x

right-⇓-⊛ : ∀ {e₁ e₂ n₂ n} → e₂ ⇓ n₂ → e₁ ⊛ e₂ ⇓ n → e₁ ⊛ Nat n₂ ⇓ n
right-⇓-⊛ {e₁} {e₂} {n₂} {n} p (E-Times q₁ q₂ x) rewrite uniqueness-⇓ (p , q₂) = E-Times q₁ E-Const x

⇓-ability-⊕ : ∀ {e₁ e₂ n} → e₁ ⊕ e₂ ⇓ n → ∃ λ n₁ → ∃ λ n₂ → e₁ ⇓ n₁ × e₂ ⇓ n₂ × n₁ plus n₂ is n
⇓-ability-⊕ {e₁} {e₂} {n} (E-Plus p₁ p₂ x) with totality-⇓ e₁ | totality-⇓ e₂
... | n₁ , proj₂ | n₂ , proj₄ with uniqueness-⇓ (p₁ , proj₂) | uniqueness-⇓ (p₂ , proj₄)
... | refl | refl = n₁ , n₂ , p₁ , p₂ , x

⇓-ability-⊛ : ∀ {e₁ e₂ n} → e₁ ⊛ e₂ ⇓ n → ∃ λ n₁ → ∃ λ n₂ → e₁ ⇓ n₁ × e₂ ⇓ n₂ × n₁ times n₂ is n
⇓-ability-⊛ {e₁} {e₂} {n} (E-Times p₁ p₂ x) with totality-⇓ e₁ | totality-⇓ e₂
... | n₁ , proj₂ | n₂ , proj₄ with uniqueness-⇓ (p₁ , proj₂) | uniqueness-⇓ (p₂ , proj₄)
... | refl | refl = n₁ , n₂ , p₁ , p₂ , x

-*->→⇓ : ∀ {e n} → e -*-> Nat n → e ⇓ n
-*->→⇓ MR-Zero = E-Const
-*->→⇓ (MR-One (R-Plus x)) = E-Plus E-Const E-Const x
-*->→⇓ (MR-One (R-Times x)) = E-Times E-Const E-Const x
-*->→⇓ (MR-Multi p₁ p₂) = {!!}
{--
-*->→⇓ {Nat n} MR-Zero = E-Const
-*->→⇓ {Nat n} (MR-One ())
-*->→⇓ {Nat n} (MR-Multi p₁ p₂) with n-*->e→e≡n p₁
... | refl with n-*->e→e≡n p₂
... | refl = E-Const
-*->→⇓ {._ ⊕ ._} (MR-One (R-Plus x)) = E-Plus E-Const E-Const x
-*->→⇓ {e₁ ⊕ e₂} (MR-Multi p₁ p₂) = {!!}
-*->→⇓ {._ ⊛ ._} (MR-One (R-Times x)) = E-Times E-Const E-Const x
-*->→⇓ {e₁ ⊛ e₂} (MR-Multi p₁ p₂) = {!!}
--}