{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module sequence_props where
  open import HoTT-UF-Agda public
  open basic-arithmetic-and-order
  open import basic_logic public

  ℕ-SEQ : 𝓤₀ ̇
  ℕ-SEQ = ℕ → ℕ

  ORACLE : {A : 𝓤 ̇} → (A → 𝓥 ̇) → (𝓤 ⊔ 𝓥) ̇
  ORACLE {A = A} P = (a : A) → decidable (P a)

  bounded : ℕ-SEQ → 𝓤₀ ̇
  bounded α = Σ (λ M → (n : ℕ) → α n ≤ M)

  unbounded : ℕ-SEQ → 𝓤₀ ̇
  unbounded α = Σ (λ (m : ℕ) → Σ (λ n → α n ≥ m))

  has-value : ℕ → ℕ-SEQ → 𝓤₀ ̇
  has-value v α = Σ (λ n → α n ≡ v)

  monotone : ℕ-SEQ → 𝓤₀ ̇
  monotone α = (n : ℕ) → α n ≤ α (succ n)

  increasing : ℕ-SEQ → 𝓤₀ ̇
  increasing α = (n : ℕ) → α n < α (succ n)

  strong-monotone : ℕ-SEQ → 𝓤₀ ̇
  strong-monotone α = (m n : ℕ) → (m ≤ n) → α m ≤ α n

  strong-increasing : ℕ-SEQ → 𝓤₀ ̇
  strong-increasing α = (m n : ℕ) → (m < n) → α m < α n

  has-value-∞ : ℕ → ℕ-SEQ → 𝓤₀ ̇
  has-value-∞ v α = Σ {X = ℕ → ℕ} (λ f → (increasing f) × ((n : ℕ) → α (f n) ≡ v))

  strongmon-mon : {α : ℕ-SEQ} → (strong-monotone α) → monotone α
  strongmon-mon sm n = sm n (succ n) (≤-succ n)

  sleq-split : (m n : ℕ) → (m ≤ succ n) → (m ≡ succ n) + (m ≤ n)
  sleq-split 0 0 leq = inr (≤-succ 0)
  sleq-split 0 (succ n) leq = inr (zero-minimal n)
  sleq-split (succ m) 0 leq = inl (ap succ (unique-minimal m leq))
  sleq-split (succ m) (succ n) leq = (+-recursion (inl ∘ (ap succ)) inr) (sleq-split m n leq)

  mon-strongmon : {α : ℕ-SEQ} → (monotone α) → strong-monotone α
  mon-strongmon {α} wm 0 n _ = (ℕ-induction (λ k → (α 0 ≤ α k))
                                            (≤-refl (α 0))
                                            (λ k → λ leq → ≤-trans (α 0) (α k) (α (succ k)) leq (wm k))
                               ) n
  mon-strongmon {α} wm (succ m) 0 leq = ex-nihilo leq
  mon-strongmon {α} wm (succ m) (succ n) = (+-recursion (λ eq → transport (λ x → α (succ m) ≤ x)
                                                                          (ap α eq) (≤-refl (α (succ m))))
                                                        (λ leq → ≤-trans (α (succ m)) (α n) (α (succ n))
                                                                 (mon-strongmon {α} wm (succ m) n leq)
                                                                 (wm n)
                                                        )
                                           ) ∘ (sleq-split (succ m) n)
                                                   
  deceq-ℕ : ℕ → ℕ → 𝟚
  deceq-ℕ x y = (+-recursion (λ _ → ₁) (λ _ → ₀)) (ℕ-has-decidable-equality x y)

  has-zero-within : ℕ → (ℕ → ℕ) → 𝓤₀ ̇
  has-zero-within n f = Σ (λ r → (r ≤ n) × (f r ≡ zero))

  has-zero-within-succ : (n : ℕ) → (f : ℕ → ℕ) → has-zero-within n f
                                               → has-zero-within (succ n) f
  has-zero-within-succ n f hz = (r , (≤-trans r n (succ n) leq (≤-succ n) , eq))
                              where r = pr₁ hz
                                    leq = pr₁ (pr₂ hz)
                                    eq = pr₂ (pr₂ hz)

  has-zero-within-inc : (n m : ℕ) → (f : ℕ → ℕ) → (n ≤ m) → has-zero-within n f → has-zero-within m f
  has-zero-within-inc n m f m≤n hz = (r , (≤-trans r n m leq m≤n) , eq)
                                   where r = pr₁ hz
                                         leq = pr₁ (pr₂ hz)
                                         eq = pr₂ (pr₂ hz)

  decide-zero-within : (n : ℕ) → (f : ℕ → ℕ) → decidable (has-zero-within n f)
  decide-zero-within zero f = +-recursion (λ eq → inl (zero , (≤-refl zero , eq)))
                                          (λ neq → inr (
                                                    λ zwz → neq (transport
                                                                  (λ x → f x ≡ zero)
                                                                  (unique-minimal (pr₁ zwz) (pr₁ (pr₂ zwz)))
                                                                  (pr₂ (pr₂ zwz)))))
                                          (ℕ-has-decidable-equality (f zero) zero)
  decide-zero-within (succ n) f = +-recursion (λ eq → inl (succ n , (≤-refl (succ n)), eq))
                                              (λ neq →
                                                +-recursion (λ yz → inl (has-zero-within-succ n f yz))
                                                            (λ nz → inr (λ zwz →
                                                                        +-recursion (λ eq → neq (transport (λ x → f x ≡ zero) eq (pr₂ (pr₂ zwz))))
                                                                                    (λ leq → nz (pr₁ zwz , (leq , (pr₂ (pr₂ zwz)))))
                                                                                    (sleq-split (pr₁ zwz) n (pr₁ (pr₂ zwz)))
                                                                        ))
                                                            (decide-zero-within n f)
                                              )
                                              (ℕ-has-decidable-equality (f (succ n)) zero)
                                  

  -- Given a function f : ℕ → ℕ, we get a new function z : ℕ → ℕ
  --  such that z(n) = 0 if f has a zero before n, and z(n) = n otherwise
  zero-ticker : (ℕ → ℕ) → (ℕ → ℕ)
  zero-ticker f n = +-recursion (λ _ → 0)
                                (λ _ → n)
                                (decide-zero-within n f)

  ≤-decide : (m n : ℕ) → decidable (m ≤ n)
  ≤-decide 0 n = inl ⋆
  ≤-decide (succ m) 0 = inr id
  ≤-decide (succ m) (succ n) = ≤-decide m n

  <-gives-≤ : (m n : ℕ) → (m < n) → (m ≤ n)
  <-gives-≤ m n sl = ≤-trans m (succ m) n (≤-succ m) sl

  not-≤-gives-≥ : (m n : ℕ) → ¬ (m ≤ n) → (n ≤ m)
  not-≤-gives-≥ m n nleq = not-<-gives-≥ n m (λ sl → nleq (<-gives-≤ m n sl))

  ticker-under-n : (f : ℕ → ℕ) → (n : ℕ) → (zero-ticker f n) ≤ n
  ticker-under-n f n = +-recursion (λ yz → transport (λ x → x ≤ n) ((χ-case1 yz (decide-zero-within n f)) ⁻¹) (zero-minimal n))
                                   (λ nz → transport (λ x → x ≤ n) ((χ-case2 nz (decide-zero-within n f)) ⁻¹) (≤-refl n))
                                   (decide-zero-within n f)

  has-zero-bounded-ticker : (f : ℕ → ℕ) → (has-value 0 f) → bounded (zero-ticker f)
  has-zero-bounded-ticker f (z , eq) = (z , λ n → +-recursion (λ leq → ≤-trans (zero-ticker f n) n z (ticker-under-n f n) leq)
                                                              (λ nleq → transport (λ x → x ≤ z)
                                                                                  ((χ-case1 (z , (not-≤-gives-≥ n z nleq , eq))
                                                                                            (decide-zero-within n f)) ⁻¹)
                                                                                  (zero-minimal z))
                                                              (≤-decide n z))

  unbounded-ticker-no-zero : (f : ℕ → ℕ) → ¬ (bounded (zero-ticker f)) → ¬ (has-value 0 f)
  unbounded-ticker-no-zero f = contrapositive (has-zero-bounded-ticker f)

  no-zero-ticker-id : (f : ℕ → ℕ) → ¬ (has-value 0 f) → (zero-ticker f) ∼ id
  no-zero-ticker-id f nz n = +-recursion (λ yz → ex-nihilo (nz (pr₁ yz , pr₂ (pr₂ yz))))
                                         (λ nz → χ-case2 nz (decide-zero-within n f))
                                         (decide-zero-within n f)

  succ-≰ : (n : ℕ) → ¬ (succ n ≤ n)
  succ-≰ = ℕ-induction (λ n → ¬ (succ n ≤ n)) id (λ _ → id)

  no-zero-unbounded-ticker : (f : ℕ → ℕ) → ¬ (has-value 0 f) → ¬ (bounded (zero-ticker f))
  no-zero-unbounded-ticker f nz (B , Bmax) = succ-≰ B (transport (λ x → x ≤ B)
                                                                 (no-zero-ticker-id f nz (succ B))
                                                                 (Bmax (succ B)))

  bounded-ticker-gets-zero : (f : ℕ → ℕ) → bounded (zero-ticker f) → has-value 0 f
  bounded-ticker-gets-zero f (B , Bmax) = +-recursion (λ yz → (pr₁ yz , pr₂ (pr₂ yz)))
                                                      (λ nz → ex-nihilo (succ-≰ B (transport (λ x → x ≤ B)
                                                                                             (χ-case2 nz (decide-zero-within (succ B) f))
                                                                                             (Bmax (succ B)))))
                                                      (decide-zero-within (succ B) f)

  Ωbdd-gives-Ωzero : ORACLE bounded → ORACLE (has-value 0)
  Ωbdd-gives-Ωzero Ωbdd f = +-recursion (inl ∘ (bounded-ticker-gets-zero f))
                                        (inr ∘ (unbounded-ticker-no-zero f))
                                        (Ωbdd (zero-ticker f))

  Ωm-gives-Ωn : {m n : ℕ} → ORACLE (has-value m) → ORACLE (has-value n)
  Ωm-gives-Ωn {m} {n} Ωm f = +-recursion (inl ∘ χm-gives-fn)
                                         (inr ∘ (contrapositive fn-gives-χm))
                                         (Ωm χ')
                           where χ' : ℕ → ℕ
                                 χ' k = +-recursion (λ _ → m) (λ _ → (succ m)) (ℕ-has-decidable-equality (f k) n)
                                 fn-gives-χm : (has-value n f) → (has-value m χ')
                                 fn-gives-χm (k , eq) = (k , χ-case1 eq (ℕ-has-decidable-equality (f k) n))
                                 χm-gives-fn : (has-value m χ') → (has-value n f)
                                 χm-gives-fn (k , eq) = +-recursion (λ eq' → (k , eq'))
                                                                    (λ neq → ex-nihilo (succ-no-fixed-point m ((χ-case2 neq (ℕ-has-decidable-equality (f k) n)) ⁻¹
                                                                                                                             ∙ eq)))
                                                                    (ℕ-has-decidable-equality (f k) n)

  zero-if-exceeds : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  zero-if-exceeds B f n = +-recursion (λ leq → 1)
                                      (λ nleq → 0)
                                      (≤-decide (f n) B)

  nozero-gives-bound : (B : ℕ) → (f : ℕ → ℕ) → ¬ (has-value 0 (zero-if-exceeds B f))
                                             → bounded f
  nozero-gives-bound B f nz = (B , λ n → +-recursion id
                                                     (λ nleq → ex-nihilo (nz (n , χ-case2 nleq (≤-decide (f n) B))))
                                                     (≤-decide (f n) B))

  bound-gives-nozero : (f : ℕ → ℕ) → (bdd : bounded f) → ¬ (has-value 0 (zero-if-exceeds (pr₁ bdd) f))
  bound-gives-nozero f bdd hz = +-recursion (λ leq → positive-not-zero 0 ((χ-case1 leq (≤-decide (f n) B)) ⁻¹ ∙ eq))
                                            (λ nleq → nleq (B-isbound n))
                                            (≤-decide (f n) B)
                              where n = pr₁ hz
                                    eq = pr₂ hz
                                    B = pr₁ bdd
                                    B-isbound = pr₂ bdd

  zero-if-isbound : ORACLE (has-value 0) → (ℕ → ℕ) → (ℕ → ℕ)
  zero-if-isbound Ω0 f b = +-recursion (λ nbd → 1)
                                       (λ bd → 0)
                                       (Ω0 (zero-if-exceeds b f))

  zero-gives-bound : (Ω0 : ORACLE (has-value 0)) → (f : ℕ → ℕ) → has-value 0 (zero-if-isbound Ω0 f) → bounded f
  zero-gives-bound Ω0 f (B , eq) = nozero-gives-bound B f
                                                      (+-recursion (λ yz → ex-nihilo (positive-not-zero 0 ((χ-case1 yz (Ω0 (zero-if-exceeds B f))) ⁻¹ ∙ eq)))
                                                                   id
                                                                   (Ω0 (zero-if-exceeds B f)))

  bound-gives-zero : (Ω0 : ORACLE (has-value 0)) → (f : ℕ → ℕ) → bounded f → has-value 0 (zero-if-isbound Ω0 f)
  bound-gives-zero Ω0 f (B , B-isbound) = (B , χ-case2 (bound-gives-nozero f (B , B-isbound))
                                                       (Ω0 (zero-if-exceeds B f)))

  Ωzero-gives-Ωbdd : ORACLE (has-value 0) → ORACLE bounded
  Ωzero-gives-Ωbdd Ω0 f = +-recursion (inl ∘ (zero-gives-bound Ω0 f))
                                      (inr ∘ (contrapositive (bound-gives-zero Ω0 f)))
                                      (Ω0 (zero-if-isbound Ω0 f))

  decider : {A : 𝓤 ̇} → (P : A → 𝓥 ̇) → (𝓤 ⊔ 𝓥) ̇
  decider {A = A} P = (a : A) → decidable (P a)

  neg-decide : {A : 𝓤 ̇} {P : A → 𝓥 ̇} → (decider P) → decider (λ a → ¬ (P a))
  neg-decide {A = A} {P = P} decP a = +-recursion (inr ∘ (dni (P a)))
                                                  inl
                                                  (decP a)

  zero-if-P : (P : ℕ → 𝓤 ̇) → (decider P) → ℕ → ℕ
  zero-if-P P decP n = +-recursion (λ x → 0)
                                   (λ x → 1)
                                   (decP n)

  P-gives-zero : (P : ℕ → 𝓤 ̇) → (decP : decider P) → {n : ℕ} → (P n) → has-value 0 (zero-if-P P decP)
  P-gives-zero P decP {n} p = (n , χ-case1 p (decP n))

  zero-gives-P : (P : ℕ → 𝓤 ̇) → (decP : decider P) → has-value 0 (zero-if-P P decP) → Σ P
  zero-gives-P P decP (n , eq) = (n , +-recursion id
                                                  (λ notP → ex-nihilo (positive-not-zero 0 ((χ-case2 notP (decP n)) ⁻¹ ∙ eq)))
                                                  (decP n))

  Ω0-decide-exists : ORACLE (has-value 0) → (P : ℕ → 𝓤 ̇) → (decider P) → decidable (Σ P)
  Ω0-decide-exists Ω0 P decP = +-recursion (λ yz → inl (zero-gives-P P decP yz))
                                           (λ nz → inr (λ yP → nz (P-gives-zero P decP (pr₂ yP))))
                                           (Ω0 (zero-if-P P decP))

  Ω0-decide-forall : ORACLE (has-value 0) → (P : ℕ → 𝓤 ̇) → (decider P) → decidable ((n : ℕ) → (P n))
  Ω0-decide-forall Ω0 P decP = +-recursion (λ yz → inr (λ allP → (pr₂ (zero-gives-P (λ n → ¬ (P n)) dec¬P yz))
                                                                 (allP (pr₁ (zero-gives-P (λ n → ¬ (P n)) dec¬P yz)))))
                                           (λ nz → inl (λ n → +-recursion id
                                                                          (λ notP → ex-nihilo (nz (n , χ-case1 notP (dec¬P n))))
                                                                          (decP n)))
                                           (Ω0 (zero-if-P (λ n → ¬ (P n)) dec¬P))
                               where dec¬P : decider (λ n → ¬ (P n))
                                     dec¬P = neg-decide decP

  -- Streamlined reproduction of previous proof using our new general-purpose tools!
  Ωzero-gives-Ωbdd' : ORACLE (has-value 0) → ORACLE bounded
  Ωzero-gives-Ωbdd' Ω0 f = Ω0-decide-exists Ω0 (λ B → (n : ℕ) → (f n) ≤ B)
                                               (λ B → Ω0-decide-forall Ω0 (λ n → (f n) ≤ B) (λ n → ≤-decide (f n) B))
