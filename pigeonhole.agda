module pigeonhole where
  open import HoTT-UF-Agda public
  open import basic_logic public
  
  finset : â â ð¤â Ì
  finset zero     = ð
  finset (succ n) = ð + (finset n)

  [_] = finset

  deq-sum : (A : ð¤ Ì) â (B : ð¥ Ì) â has-decidable-equality A
                                â has-decidable-equality B
                                â has-decidable-equality (A + B)
  deq-sum A B deqA _    (inl x) (inl y) = +-recursion (inl â (ap inl))
                                                      (Î» neq â inr (Î» eq â neq (ap (Î» {(inl z) â z; (inr _) â x}) eq)))
                                                      (deqA x y)
  deq-sum A B _    _    (inr x) (inl y) = inr (Î» eq â transport (Î» {(inl _) â ð; (inr _) â ð}) eq â)
  deq-sum A B _    _    (inl x) (inr y) = inr (Î» eq â transport (Î» {(inl _) â ð; (inr _) â ð}) eq â)
  deq-sum A B deqA deqB (inr x) (inr y) = +-recursion (inl â (ap inr))
                                                      (Î» neq â inr (Î» eq â neq (ap (Î» {(inl _) â x; (inr z) â z}) eq)))
                                                      (deqB x y)

  deq-plus-ð : (A : ð¤ Ì) â has-decidable-equality A
                        â has-decidable-equality (ð + A)
  deq-plus-ð A deqA = deq-sum ð A (Î» x â Î» y â inl (ð-is-subsingleton x y)) deqA

  deq-finset : (n : â) â has-decidable-equality [ n ]
  deq-finset zero     = Î» x â Î» y â inl (ð-is-subsingleton x y)
  deq-finset (succ n) = deq-plus-ð [ n ] (deq-finset n)

  open basic-arithmetic-and-order

  noninjective : {A : ð¤ Ì} {B : ð¥ Ì} (f : A â B) â (ð¤ â ð¥) Ì
  noninjective f = Î£ (Î» t â (prâ t â¢ prâ t) Ã (f (prâ t) â¡ f (prâ t)))

  succ-not-â¤ : (m : â) â Â¬ (succ m â¤ m)
  succ-not-â¤ 0 leq        = leq
  succ-not-â¤ (succ m) leq = succ-not-â¤ m leq

  â¤-not-> : (m n : â) â (m â¤ n) â Â¬ (n < m)
  â¤-not-> m n leq sl = succ-not-â¤ n (â¤-trans (succ n) m n sl leq)

  pigeon-base : (m : â) â (1 < m) â (f : [ m ] â ð) â noninjective f
  pigeon-base 0 sl _ = ex-nihilo (â¤-not-> 0 2 â sl) 
  pigeon-base 1 sl _ = ex-nihilo (â¤-not-> 1 2 â sl)
  pigeon-base (succ (succ n)) _ f = ((x1 , x2) , (
                                                    (Î» eq â transport (Î» {(inl _) â ð; (inr _) â ð}) eq â) ,
                                                    (ð-is-subsingleton (f x1) (f x2))
                                                 ))
                                  where x1 = inl â
                                        x2 = inr (inl â)

  data List {ð¤} (A : ð¤ Ì) : ð¤ Ì where
    empty : List A
    append : A â List A â List A

  finset-fxn-to-list : {A : ð¤ Ì} {n : â} â (f : [ n ] â A) â List A
  finset-fxn-to-list {n = 0}        f = empty
  finset-fxn-to-list {n = (succ m)} f = append (f (inl â)) (finset-fxn-to-list (f â inr))

  list-has-value : {A : ð¤ Ì} â (has-decidable-equality A) â List A â A â ð¤â Ì
  list-has-value _    empty         _ = ð
  list-has-value deqA (append a as) v = +-recursion (Î» _ â ð) (Î» _ â list-has-value deqA as v) (deqA a v) 

  decide-list-has-value : {A : ð¤ Ì} â (deqA : has-decidable-equality A) â (as : List A) â (v : A) â decidable (list-has-value deqA as v) 
  decide-list-has-value _ empty _ = inr id
  decide-list-has-value deqA (append a as) v = +-recursion (Î» eq â inl (transport id ((Ï-case1 eq (deqA a v)) â»Â¹) â))
                                                           (Î» neq â transport decidable ((Ï-case2 neq (deqA a v)) â»Â¹) (decide-list-has-value deqA as v))
                                                           (deqA a v)

  decide-f-has-value : {A : ð¤ Ì}
                          â (n : â)
                          â (has-decidable-equality A)
                          â (f : [ n ] â A)
                          â (a : A)
                          â decidable (Î£ (Î» x â f x â¡ a))
  decide-f-has-value 0        _    _ _ = inr (ex-nihilo â prâ)
  decide-f-has-value (succ n) deqA f a = +-recursion
                                           (Î» eq â inl (z , eq))
                                           (Î» neq â +-recursion
                                             (Î» hv â inl (inr (prâ hv) , prâ hv))
                                             (Î» nv â inr (Î» sol â +-induction
                                               (Î» x â (f x â¡ a) â ð)
                                               (Î» lx â Î» eq â neq (transport
                                                 (Î» y â (f (inl y) â¡ a))
                                                 (ð-is-subsingleton lx â)
                                                 eq))
                                               (Î» rx â Î» eq â nv (rx , eq))
                                               (prâ sol)
                                               (prâ sol)))
                                             (decide-f-has-value n deqA (f â inr) a)
                                            )
                                            (deqA (f z) a)
                                       where z = inl â

  decide-f0-repeated : {A : ð¤ Ì}
                          â (n : â)
                          â (has-decidable-equality A)
                          â (f : [ (succ n) ] â A)
                          â decidable (Î£ (Î» x â (f (inr x)) â¡ (f (inl â))))
  decide-f0-repeated n deqA f = decide-f-has-value n deqA (f â inr) (f (inl â))

  fintree-splice : (n : â) â [ (succ n) ] â [ n ] â [ (succ n) ]
  fintree-splice 0 _ ()
  fintree-splice (succ n) spl = +-recursion
                                  (Î» _ â inr)
                                  (Î» spl' â Î» {(inl x) â inl â; (inr x) â inr (fintree-splice n spl' x)})
                                  spl

  -- pigeonhole : (m n : â) â (n < m) â (2 < m) â (f : [ m ] â [ n ]) â noninjective f
