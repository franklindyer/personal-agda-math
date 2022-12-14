{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module basic_logic where
  open import HoTT-UF-Agda

  ex-nihilo : {A : ð¤ Ì} â ð â A
  ex-nihilo ()

  lnc : {A : ð¤ Ì} â Â¬ (A Ã (Â¬ A))
  lnc t = (prâ t) (prâ t)

  _â_ : ð¤ Ì â ð¤ Ì â ð¤ Ì
  X â Y = (X â Y) Ã (Y â X)

  Ï-case1 : {A : ð¤ Ì}{B : ð¥ Ì} {b1 b2 : B} â (a : A) â (x : A + Â¬ A) â +-recursion {X = A} {Y = Â¬ A} (Î» _ â b1) (Î» _ â b2) x â¡ b1
  Ï-case1 {A = A} {B = B} {b1 = b1} {b2 = b2} a = +-induction (Î» x â +-recursion {X = A} {Y = Â¬ A} (Î» _ â b1) (Î» _ â b2) x â¡ b1)
                                                              (Î» ya â refl (+-recursion {X = A} {Y = Â¬ A} (Î» _ â b1) (Î» _ â b2) (inl ya)))
                                                              (Î» na â ex-nihilo (na a))

  Ï-case2 : {A : ð¤ Ì}{B : ð¥ Ì} {b1 b2 : B} â (na : Â¬ A) â (x : A + Â¬ A) â +-recursion {X = A} {Y = Â¬ A} (Î» _ â b1) (Î» _ â b2) x â¡ b2
  Ï-case2 {A = A} {B = B} {b1 = b1} {b2 = b2} na = +-induction (Î» x â +-recursion {X = A} {Y = Â¬ A} (Î» _ â b1) (Î» _ â b2) x â¡ b2)
                                                               (Î» a â ex-nihilo (na a))
                                                               (Î» na' â refl (+-recursion {X = A} {Y = Â¬ A} (Î» _ â b1) (Î» _ â b2) (inr na')))
