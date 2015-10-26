module ex7 where

open import Data.Empty

open import BCoPL.EvalML4

ex-7-1-1 : ● ⊢ i (+ 1) ⊕ i (+ 2) ∷ i (+ 3) ⊕ i (+ 4) ∷ [] ⇓ (i (+ 3)) ∷ (i (+ 7)) ∷ []
ex-7-1-1 = E-Cons (E-Plus E-Int E-Int (B-Plus refl))
                  (E-Cons (E-Plus E-Int E-Int (B-Plus refl)) E-Nil)

ex-7-1-2 : ● ⊢ ℓet "f" ≔ fun "x" ⇒
                   match var "x" with[]⇒ i (+ 0)
                                   ∣ "a" ∷ "b" ⇒ var "a" ιn
                app (var "f") (i (+ 4) ∷ []) ⊕
                app (var "f") [] ⊕
                app (var "f") (i (+ 1) ∷ i (+ 2) ∷  i (+ 3) ∷ []) ⇓ i (+ 5)
ex-7-1-2 = E-Let E-Fun
                 (E-Plus (E-Plus (E-App E-Var1
                                        (E-Cons E-Int E-Nil)
                                        (E-MatchCons E-Var1 (E-Var2 a≢b E-Var1)))
                                 (E-App E-Var1
                                        E-Nil
                                        (E-MatchNil E-Var1 E-Int))
                                 (B-Plus refl))
                         (E-App E-Var1
                                (E-Cons E-Int (E-Cons E-Int (E-Cons E-Int E-Nil)))
                                (E-MatchCons E-Var1 (E-Var2 a≢b E-Var1)))
                         (B-Plus refl))
  where
    a≢b : "a" ≡ "b" → ⊥
    a≢b ()

ex-7-1-3 : ● ⊢ ℓetrec "f" ≔fun "x" ⇒
                      if var "x" ≺ i (+ 1) then [] else var "x" ∷ app (var "f") (var "x" ⊝ i (+ 1)) ιn
                app (var "f") (i (+ 3)) ⇓ i (+ 3) ∷ i (+ 2) ∷ i (+ 1) ∷ []
ex-7-1-3 = E-LetRec (E-AppRec E-Var1
                              E-Int
                              (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl))
                                     (E-Cons E-Var1
                                             (E-AppRec (E-Var2 f≢x E-Var1)
                                                       (E-Minus E-Var1 E-Int (B-Minus refl))
                                                       (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl))
                                                              (E-Cons E-Var1
                                                                      (E-AppRec (E-Var2 f≢x E-Var1)
                                                                                (E-Minus E-Var1 E-Int (B-Minus refl))
                                                                                (E-IfF (E-Lt E-Var1 E-Int (B-Lt refl))
                                                                                       (E-Cons E-Var1
                                                                                               (E-AppRec (E-Var2 f≢x E-Var1)
                                                                                                         (E-Minus E-Var1 E-Int (B-Minus refl))
                                                                                                         (E-IfT (E-Lt E-Var1 E-Int (B-Lt refl))
                                                                                                                E-Nil)))))))))))
  where
    f≢x : "f" ≡ "x" → ⊥
    f≢x ()

ex-7-1-4 : ● ⊢ ℓetrec "length" ≔fun "l" ⇒
                      match var "l" with[]⇒ i (+ 0)
                                      ∣ "x" ∷ "y" ⇒ i (+ 1) ⊕ app (var "length") (var "y") ιn
                app (var "length") (i (+ 1) ∷ i (+ 2) ∷ i (+ 3) ∷ []) ⇓ i (+ 3)
ex-7-1-4 = E-LetRec (E-AppRec E-Var1
                              (E-Cons E-Int
                                      (E-Cons E-Int (E-Cons E-Int E-Nil)))
                              (E-MatchCons E-Var1
                                           (E-Plus E-Int
                                                   (E-AppRec (E-Var2 length≢y (E-Var2 length≢x (E-Var2 length≢l E-Var1)))
                                                             E-Var1
                                                             (E-MatchCons E-Var1
                                                                          (E-Plus E-Int
                                                                                  (E-AppRec (E-Var2 length≢y (E-Var2 length≢x (E-Var2 length≢l E-Var1)))
                                                                                            E-Var1
                                                                                            (E-MatchCons E-Var1
                                                                                                         (E-Plus E-Int
                                                                                                                 (E-AppRec (E-Var2 length≢y (E-Var2 length≢x (E-Var2 length≢l E-Var1)))
                                                                                                                           E-Var1 (E-MatchNil E-Var1 E-Int)) (B-Plus refl))))
                                                                                  (B-Plus refl))))
                                                   (B-Plus refl))))
  where
    length≢y : "length" ≡ "y" → ⊥
    length≢y ()
    length≢x : "length" ≡ "x" → ⊥
    length≢x ()
    length≢l : "length" ≡ "l" → ⊥
    length≢l ()


q74 : ● ⊢ ℓetrec "length" ≔fun "l" ⇒
                 match var "l" with[]⇒ i (+ 0)
                                 ∣ "x" ∷ "y" ⇒ i (+ 1) ⊕ app (var "length") (var "y") ιn
           app (var "length") ((i (+ 1) ∷ i (+ 2) ∷ []) ∷ (i (+ 3) ∷ i (+ 4) ∷ i (+ 5) ∷ []) ∷ []) ⇓ i (+ 2)
q74 = E-LetRec (E-AppRec E-Var1
                         (E-Cons (E-Cons E-Int (E-Cons E-Int E-Nil))
                                 (E-Cons (E-Cons E-Int (E-Cons E-Int (E-Cons E-Int E-Nil))) E-Nil))
                         (E-MatchCons E-Var1
                                      (E-Plus E-Int
                                              (E-AppRec (E-Var2 length≢y (E-Var2 length≢x (E-Var2 length≢l E-Var1)))
                                                        E-Var1
                                                        (E-MatchCons E-Var1
                                                                     (E-Plus E-Int
                                                                             (E-AppRec (E-Var2 length≢y (E-Var2 length≢x (E-Var2 length≢l E-Var1)))
                                                                                       E-Var1
                                                                                       (E-MatchNil E-Var1 E-Int))
                                                                             (B-Plus refl))))
                                              (B-Plus refl))))
  where
    length≢y : "length" ≡ "y" → ⊥
    length≢y ()
    length≢x : "length" ≡ "x" → ⊥
    length≢x ()
    length≢l : "length" ≡ "l" → ⊥
    length≢l ()


ex-7-1-5 : ● ⊢ ℓetrec "append" ≔fun "l1" ⇒ fun "l2" ⇒
                      match var "l1" with[]⇒ var "l2"
                                       ∣ "x" ∷ "y" ⇒ var "x" ∷ app (app (var "append") (var "y")) (var "l2") ιn
                app (app (var "append") (i (+ 1) ∷ i (+ 2) ∷ [])) (i (+ 3) ∷ i (+ 4) ∷ i (+ 5) ∷ []) ⇓ i (+ 1) ∷ i (+ 2) ∷ i (+ 3) ∷ i (+ 4) ∷ i (+ 5) ∷ []
ex-7-1-5 = E-LetRec (E-App (E-AppRec E-Var1 (E-Cons E-Int (E-Cons E-Int E-Nil)) E-Fun)
                           (E-Cons E-Int (E-Cons E-Int (E-Cons E-Int E-Nil)))
                           (E-MatchCons (E-Var2 l1≢l2 E-Var1)
                                        (E-Cons (E-Var2 x≢y E-Var1)
                                                (E-App (E-AppRec (E-Var2 append≢y (E-Var2 append≢x (E-Var2 append≢l2 (E-Var2 append≢l1 E-Var1)))) E-Var1 E-Fun)
                                                       (E-Var2 l2≢y (E-Var2 l2≢x E-Var1))
                                                       (E-MatchCons (E-Var2 l1≢l2 E-Var1)
                                                                    (E-Cons (E-Var2 x≢y E-Var1)
                                                                            (E-App (E-AppRec (E-Var2 append≢y
                                                                                                     (E-Var2 append≢x
                                                                                                             (E-Var2 append≢l2
                                                                                                                     (E-Var2 append≢l1 E-Var1))))
                                                                                             E-Var1
                                                                                             E-Fun)
                                                                                   (E-Var2 l2≢y (E-Var2 l2≢x E-Var1))
                                                                                   (E-MatchNil (E-Var2 l1≢l2 E-Var1) E-Var1))))))))
  where
    l1≢l2 : "l1" ≡ "l2" → ⊥
    l1≢l2 ()
    x≢y : "x" ≡ "y" → ⊥
    x≢y ()
    append≢y : "append" ≡ "y" → ⊥
    append≢y ()
    append≢x : "append" ≡ "x" → ⊥
    append≢x ()
    append≢l2 : "append" ≡ "l2" → ⊥
    append≢l2 ()
    append≢l1 : "append" ≡ "l1" → ⊥
    append≢l1 ()
    l2≢y : "l2" ≡ "y" → ⊥
    l2≢y ()
    l2≢x : "l2" ≡ "x" → ⊥
    l2≢x ()

q76 : ● ⊢ ℓetrec "apply" ≔fun "l" ⇒ fun "x" ⇒
               match var "l" with[]⇒ var "x"
                               ∣ "f" ∷ "l" ⇒ app (var "f") (app (app (var "apply") (var "l")) (var "x")) ιn
           app (app (var "apply") ((fun "x" ⇒ var "x" ⊛ var "x") ∷ (fun "y" ⇒ var "y" ⊕ i (+ 3)) ∷ [])) (i (+ 4)) ⇓ i (+ 49)
q76 = E-LetRec (E-App (E-AppRec E-Var1 (E-Cons E-Fun (E-Cons E-Fun E-Nil)) E-Fun)
                      E-Int
                      (E-MatchCons (E-Var2 l≢x E-Var1)
                                   (E-App (E-Var2 f≢l E-Var1)
                                          (E-App (E-AppRec (E-Var2 apply≢l
                                                                   (E-Var2 apply≢f
                                                                           (E-Var2 apply≢x
                                                                                   (E-Var2 apply≢l E-Var1))))
                                                           E-Var1
                                                           E-Fun)
                                                 (E-Var2 x≢l (E-Var2 x≢f E-Var1))
                                                 (E-MatchCons (E-Var2 l≢x E-Var1)
                                                              (E-App (E-Var2 f≢l E-Var1)
                                                                     (E-App (E-AppRec (E-Var2 apply≢l
                                                                                              (E-Var2 apply≢f
                                                                                                      (E-Var2 apply≢x
                                                                                                              (E-Var2 apply≢l E-Var1))))
                                                                                      E-Var1
                                                                                      E-Fun)
                                                                            (E-Var2 x≢l (E-Var2 x≢f E-Var1))
                                                                            (E-MatchNil (E-Var2 l≢x E-Var1) E-Var1))
                                                                     (E-Plus E-Var1 E-Int (B-Plus refl)))))
                                          (E-Times E-Var1 E-Var1 (B-Times refl)))))
  where
    l≢x : "l" ≡ "x" → ⊥
    l≢x ()
    f≢l : "f" ≡ "l" → ⊥
    f≢l ()
    apply≢l : "apply" ≡ "l" → ⊥
    apply≢l ()
    apply≢f : "apply" ≡ "f" → ⊥
    apply≢f ()
    apply≢x : "apply" ≡ "x" → ⊥
    apply≢x ()
    x≢l : "x" ≡ "l" → ⊥
    x≢l ()
    x≢f : "x" ≡ "f" → ⊥
    x≢f ()

q77 : ● ⊢ ℓetrec "apply" ≔fun "l" ⇒ fun "x" ⇒
               match var "l" with[]⇒ var "x"
                               ∣ "f" ∷ "l" ⇒ app (app (var "apply") (var "l")) (app (var "f") (var "x")) ιn
           app (app (var "apply") ((fun "x" ⇒ var "x" ⊛ var "x") ∷ (fun "y" ⇒ var "y" ⊕ i (+ 3)) ∷ [])) (i (+ 4)) ⇓ i (+ 19)
q77 = E-LetRec (E-App (E-AppRec E-Var1
                                (E-Cons E-Fun (E-Cons E-Fun E-Nil))
                                E-Fun)
                      E-Int
                      (E-MatchCons (E-Var2 l≢x E-Var1)
                                   (E-App (E-AppRec (E-Var2 apply≢l
                                                            (E-Var2 apply≢f
                                                                    (E-Var2 apply≢x
                                                                            (E-Var2 apply≢l E-Var1))))
                                                    E-Var1
                                                    E-Fun)
                                          (E-App (E-Var2 f≢l E-Var1)
                                                 (E-Var2 x≢l (E-Var2 x≢f E-Var1))
                                                 (E-Times E-Var1 E-Var1 (B-Times refl)))
                                          (E-MatchCons (E-Var2 l≢x E-Var1)
                                                       (E-App (E-AppRec (E-Var2 apply≢l
                                                                                (E-Var2 apply≢f
                                                                                        (E-Var2 apply≢x
                                                                                                (E-Var2 apply≢l E-Var1))))
                                                                        E-Var1
                                                                        E-Fun)
                                                              (E-App (E-Var2 f≢l E-Var1)
                                                                     (E-Var2 x≢l (E-Var2 x≢f E-Var1))
                                                                     (E-Plus E-Var1 E-Int (B-Plus refl)))
                                                              (E-MatchNil (E-Var2 l≢x E-Var1) E-Var1))))))
  where
    l≢x : "l" ≡ "x" → ⊥
    l≢x ()
    apply≢l : "apply" ≡ "l" → ⊥
    apply≢l ()
    apply≢f : "apply" ≡ "f" → ⊥
    apply≢f ()
    apply≢x : "apply" ≡ "x" → ⊥
    apply≢x ()
    f≢l : "f" ≡ "l" → ⊥
    f≢l ()
    x≢l : "x" ≡ "l" → ⊥
    x≢l ()
    x≢f : "x" ≡ "f" → ⊥
    x≢f ()
