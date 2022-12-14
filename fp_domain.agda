{-# OPTIONS --without-K #-}

module fp_domain where
  open import HoTT-UF-Agda public

  pair : {X : ð¤ Ì}{Y : X â ð¥ Ì} â (x : X) â Y x â Î£ Y
  pair x y = (x , y)

  is-fixpoint-domain : ð¤ Ì â ð¤ Ì
  is-fixpoint-domain A = (f : A â A) â Î£ (Î» (a : A) â a â¡ f a)

  unit-is-fp-domain : is-fixpoint-domain ð
  unit-is-fp-domain f = â , ((prâ ð-is-singleton) (f â))

  projections-are-fp-domains : {A : ð¤ Ì}{B : ð¥ Ì} â is-fixpoint-domain (A Ã B) â is-fixpoint-domain A
  projections-are-fp-domains fixAxB f = pair ((prâ â prâ) (fixAxB g))
                                             (ap prâ (prâ (fixAxB g)))
                                             where g = Î» {(a , b) â ((f a) , b)}

  pairs-equal-projections-equal : {A : ð¤ Ì}{B : ð¥ Ì} â (x y : A Ã B) â (prâ x â¡ prâ y) â (prâ x â¡ prâ y) â x â¡ y
  pairs-equal-projections-equal (x1 , x2) (y1 , y2) p1 p2 = (ap (Î» a â (a , x2)) p1) â (ap (Î» b â (y1 , b)) p2)

  product-is-fp-domain : {A : ð¤ Ì}{B : ð¥ Ì} â is-fixpoint-domain A â is-fixpoint-domain B â is-fixpoint-domain (A Ã B)
  product-is-fp-domain {A}{B} fixA fixB f = pair ((Ï Ï) , Ï)
                                                 (pairs-equal-projections-equal
                                                   ((Ï Ï) , Ï)
                                                   (f ((Ï Ï) , Ï))
                                                   (Ïeq Ï)
                                                   Ïeq
                                                 )
                                            where Ï = Î» b â prâ (fixA (Î» a â prâ (f (a , b))))
                                                  Ïeq = Î» b â prâ (fixA (Î» a â prâ (f (a , b))))
                                                  Ï = prâ (fixB (Î» b â prâ (f ((Ï b) , b))))
                                                  Ïeq = prâ (fixB (Î» b â prâ (f ((Ï b) , b))))

  shift : {A : ð¤ Ì} â (â â A) â (â â A)
  shift f n = f (succ n)

  append : {A : ð¤ Ì} â (â â A) â A â (â â A)
  append f a = Î» {0 â a; (succ n) â f n}

  equiv-is-fp-domain : {A : ð¤ Ì}{B : ð¥ Ì} â (A â B) â is-fixpoint-domain A â is-fixpoint-domain B
  equiv-is-fp-domain eqv fixA = Î» g â let Î± = prâ eqv
                                          Î±' = inverse Î± (prâ eqv)
                                          Ï = Î± (prâ (fixA (Î±' â g â Î±))) 
                                      in
                                      pair Ï
                                           (
                                             (ap Î± (prâ (fixA (Î±' â g â Î±))))
                                             â (inverses-are-sections Î± (prâ eqv) (g Ï))
                                           )

  is-fixpoint : {A : ð¤ Ì} â (f : A â A) â (Ï : A) â ð¤ Ì
  is-fixpoint f Ï = (Ï â¡ f Ï)

  has-fixpoint : {A : ð¤ Ì} â (f : A â A) â ð¤ Ì
  has-fixpoint f = Î£ (Î» Ï â is-fixpoint f Ï)

  fixpoint : {A : ð¤ Ì} â (f : A â A) â ð¤ Ì
  fixpoint f = Î£ (Î» Ï â is-fixpoint f Ï)

  selector : {A : ð¤ Ì} {B : ð¥ Ì} {C : ð¦  Ì} â C â C â (A + B â C)
  selector c1 c2 (inl _) = c1
  selector c1 c2 (inr _) = c2

  swapper : {A : ð¤ Ì} â has-decidable-equality A â A â A â (A â A)
  swapper deceq a x y = selector x a (deceq a y)

                         
                                           
