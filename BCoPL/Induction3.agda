module BCoPL.Induction3 where

open import BCoPL.EvalML3

{- principal 5.1 -}
induction-EvalML3 : {P : Env → Exp → Value → Set} →
       {- a -}    (∀ ε n → P ε (i n) (i n)) →
       {- b -}    (∀ ε v → P ε (b v) (b v)) →
       {- c -}    (∀ ε x v  → P (ε ⊱ (x , v)) (var x) v) →
       {- d -}    (∀ ε x y v₁ v₂ → x ≢ y → P ε (var x) v₂ → P (ε ⊱ (y , v₁)) (var x) v₂) →
       {- e -}    (∀ ε e₁ e₂ i₁ i₂ i₃ → P ε e₁ (i i₁) × P ε e₂ (i i₂) × i i₁ plus i i₂ is i i₃ → P ε (e₁ ⊕ e₂) (i i₃)) →
       {- f -}    (∀ ε e₁ e₂ i₁ i₂ i₃ → P ε e₁ (i i₁) × P ε e₂ (i i₂) × i i₁ minus i i₂ is i i₃ → P ε (e₁ ⊝ e₂) (i i₃)) →
       {- g -}    (∀ ε e₁ e₂ i₁ i₂ i₃ → P ε e₁ (i i₁) × P ε e₂ (i i₂) × i i₁ times i i₂ is i i₃ → P ε (e₁ ⊛ e₂) (i i₃)) →
       {- h -}    (∀ ε e₁ e₂ i₁ i₂ v → P ε e₁ (i i₁) × P ε e₂ (i i₂) × i i₁ less-than i i₂ is b v → P ε (e₁ ≺ e₂) (b v)) →
       {- i -}    (∀ ε e₁ e₂ e₃ v → P ε e₁ (b true) × P ε e₂ v → P ε (if e₁ then e₂ else e₃) v) →
       {- j -}    (∀ ε e₁ e₂ e₃ v → P ε e₁ (b false) × P ε e₃ v → P ε (if e₁ then e₂ else e₃) v) →
       {- k -}    (∀ ε e₁ e₂ x v v₁ → P ε e₁ v₁ × P (ε ⊱ (x , v₁)) e₂ v → P ε (ℓet x  ≔ e₁ ιn e₂) v) →
       {- l -}    (∀ ε x e → P ε (fun x ⇒ e) ⟨ ε ⟩[fun x ⇒ e ]) →
       {- m -}    (∀ ε ε₂ e₀ e₁ e₂ x v v₂ → P ε e₁ ⟨ ε₂ ⟩[fun x ⇒ e₀ ] × P ε e₂ v₂ × P (ε₂ ⊱ (x , v₂)) e₀ v → P ε (app e₁ e₂) v) →
       {- n -}    (∀ ε e₁ e₂ x y v → P (ε ⊱ (x , ⟨ ε ⟩[rec x ≔fun y ⇒ e₁ ])) e₂ v → P ε (ℓetrec x ≔fun y ⇒ e₁ ιn e₂) v) →
       {- o -}    (∀ ε ε₂ e₀ e₁ e₂ x y v v₂ → P ε e₁ ⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ] × P ε e₂ v₂ × P (ε₂ ⊱ (x , ⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ]) ⊱ (y , v₂)) e₀ v → P ε (app e₁ e₂) v) →
                  ∀ {ε e v} → ε ⊢ e ⇓ v → P ε e v
induction-EvalML3 a b' c d e' f g h i' j k l m n o E-Int = a _ _
induction-EvalML3 a b' c d e' f g h i' j k l m n o E-Bool = b' _ _
induction-EvalML3 a b' c d e' f g h i' j k l m n o E-Var1 = c _ _ _
induction-EvalML3 a b' c d e' f g h i' j k l m n o (E-Var2 p prf)
  = d _ _ _ _ _ p (induction-EvalML3 a b' c d e' f g h i' j k l m n o prf)
induction-EvalML3 a b' c d e' f g h i' j k l m n o (E-Plus prf prf₁ (B-Plus x))
  = e' _ _ _ _ _ _ (induction-EvalML3 a b' c d e' f g h i' j k l m n o prf , induction-EvalML3 a b' c d e' f g h i' j k l m n o prf₁ , B-Plus x)
induction-EvalML3 a b' c d e' f g h i' j k l m n o (E-Minus prf prf₁ (B-Minus x))
  = f _ _ _ _ _ _ (induction-EvalML3 a b' c d e' f g h i' j k l m n o prf , induction-EvalML3 a b' c d e' f g h i' j k l m n o prf₁ , B-Minus x)
induction-EvalML3 a b' c d e' f g h i' j k l m n o (E-Times prf prf₁ (B-Times x))
  = g _ _ _ _ _ _ (induction-EvalML3 a b' c d e' f g h i' j k l m n o prf , induction-EvalML3 a b' c d e' f g h i' j k l m n o prf₁ , B-Times x)
induction-EvalML3 a b' c d e' f g h i' j k l m n o (E-Lt prf prf₁ (B-Lt x))
  = h _ _ _ _ _ _ (induction-EvalML3 a b' c d e' f g h i' j k l m n o prf , induction-EvalML3 a b' c d e' f g h i' j k l m n o prf₁ , B-Lt x)
induction-EvalML3 a b' c d e' f g h i' j k l m n o (E-IfT prf prf₁)
  = i' _ _ _ _ _ ((induction-EvalML3 a b' c d e' f g h i' j k l m n o prf) , (induction-EvalML3 a b' c d e' f g h i' j k l m n o prf₁))
induction-EvalML3 a b' c d e' f g h i' j k l m n o (E-IfF prf prf₁)
  = j _ _ _ _ _ ((induction-EvalML3 a b' c d e' f g h i' j k l m n o prf) , (induction-EvalML3 a b' c d e' f g h i' j k l m n o prf₁))
induction-EvalML3 a b' c d e' f g h i' j k l m n o (E-Let prf prf₁)
  = k _ _ _ _ _ _ ((induction-EvalML3 a b' c d e' f g h i' j k l m n o prf) , (induction-EvalML3 a b' c d e' f g h i' j k l m n o prf₁))
induction-EvalML3 a b' c d e' f g h i' j k l m n o (E-LetRec prf)
  = n _ _ _ _ _ _ (induction-EvalML3 a b' c d e' f g h i' j k l m n o prf)
induction-EvalML3 a b' c d e' f g h i' j k l m n o E-Fun = l _ _ _
induction-EvalML3 a b' c d e' f g h i' j k l m n o (E-App prf prf₁ prf₂)
  = m _ _ _ _ _ _ _ _ (induction-EvalML3 a b' c d e' f g h i' j k l m n o prf , induction-EvalML3 a b' c d e' f g h i' j k l m n o prf₁ , induction-EvalML3 a b' c d e' f g h i' j k l m n o prf₂)
induction-EvalML3 a b' c d e' f g h i' j k l m n o (E-AppRec prf prf₁ prf₂)
  = o _ _ _ _ _ _ _ _ _ (induction-EvalML3 a b' c d e' f g h i' j k l m n o prf , induction-EvalML3 a b' c d e' f g h i' j k l m n o prf₁ , induction-EvalML3 a b' c d e' f g h i' j k l m n o prf₂)
