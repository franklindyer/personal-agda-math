{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module basic_logic where
  open import HoTT-UF-Agda

  ex-nihilo : {A : 𝓤 ̇} → 𝟘 → A
  ex-nihilo ()

  lnc : {A : 𝓤 ̇} → ¬ (A × (¬ A))
  lnc t = (pr₂ t) (pr₁ t)

  _↔_ : 𝓤 ̇ → 𝓤 ̇ → 𝓤 ̇
  X ↔ Y = (X → Y) × (Y → X)

  χ-case1 : {A : 𝓤 ̇}{B : 𝓥 ̇} {b1 b2 : B} → (a : A) → (x : A + ¬ A) → +-recursion {X = A} {Y = ¬ A} (λ _ → b1) (λ _ → b2) x ≡ b1
  χ-case1 {A = A} {B = B} {b1 = b1} {b2 = b2} a = +-induction (λ x → +-recursion {X = A} {Y = ¬ A} (λ _ → b1) (λ _ → b2) x ≡ b1)
                                                              (λ ya → refl (+-recursion {X = A} {Y = ¬ A} (λ _ → b1) (λ _ → b2) (inl ya)))
                                                              (λ na → ex-nihilo (na a))

  χ-case2 : {A : 𝓤 ̇}{B : 𝓥 ̇} {b1 b2 : B} → (na : ¬ A) → (x : A + ¬ A) → +-recursion {X = A} {Y = ¬ A} (λ _ → b1) (λ _ → b2) x ≡ b2
  χ-case2 {A = A} {B = B} {b1 = b1} {b2 = b2} na = +-induction (λ x → +-recursion {X = A} {Y = ¬ A} (λ _ → b1) (λ _ → b2) x ≡ b2)
                                                               (λ a → ex-nihilo (na a))
                                                               (λ na' → refl (+-recursion {X = A} {Y = ¬ A} (λ _ → b1) (λ _ → b2) (inr na')))
