{-# OPTIONS --without-K #-}

module fp_domain where
  open import HoTT-UF-Agda public

  pair : {X : 𝓤 ̇}{Y : X → 𝓥 ̇} → (x : X) → Y x → Σ Y
  pair x y = (x , y)

  is-fixpoint-domain : 𝓤 ̇ → 𝓤 ̇
  is-fixpoint-domain A = (f : A → A) → Σ (λ (a : A) → a ≡ f a)

  unit-is-fp-domain : is-fixpoint-domain 𝟙
  unit-is-fp-domain f = ⋆ , ((pr₂ 𝟙-is-singleton) (f ⋆))

  projections-are-fp-domains : {A : 𝓤 ̇}{B : 𝓥 ̇} → is-fixpoint-domain (A × B) → is-fixpoint-domain A
  projections-are-fp-domains fixAxB f = pair ((pr₁ ∘ pr₁) (fixAxB g))
                                             (ap pr₁ (pr₂ (fixAxB g)))
                                             where g = λ {(a , b) → ((f a) , b)}

  pairs-equal-projections-equal : {A : 𝓤 ̇}{B : 𝓥 ̇} → (x y : A × B) → (pr₁ x ≡ pr₁ y) → (pr₂ x ≡ pr₂ y) → x ≡ y
  pairs-equal-projections-equal (x1 , x2) (y1 , y2) p1 p2 = (ap (λ a → (a , x2)) p1) ∙ (ap (λ b → (y1 , b)) p2)

  product-is-fp-domain : {A : 𝓤 ̇}{B : 𝓥 ̇} → is-fixpoint-domain A → is-fixpoint-domain B → is-fixpoint-domain (A × B)
  product-is-fp-domain {A}{B} fixA fixB f = pair ((ϕ ψ) , ψ)
                                                 (pairs-equal-projections-equal
                                                   ((ϕ ψ) , ψ)
                                                   (f ((ϕ ψ) , ψ))
                                                   (ϕeq ψ)
                                                   ψeq
                                                 )
                                            where ϕ = λ b → pr₁ (fixA (λ a → pr₁ (f (a , b))))
                                                  ϕeq = λ b → pr₂ (fixA (λ a → pr₁ (f (a , b))))
                                                  ψ = pr₁ (fixB (λ b → pr₂ (f ((ϕ b) , b))))
                                                  ψeq = pr₂ (fixB (λ b → pr₂ (f ((ϕ b) , b))))

  shift : {A : 𝓤 ̇} → (ℕ → A) → (ℕ → A)
  shift f n = f (succ n)

  append : {A : 𝓤 ̇} → (ℕ → A) → A → (ℕ → A)
  append f a = λ {0 → a; (succ n) → f n}

  equiv-is-fp-domain : {A : 𝓤 ̇}{B : 𝓥 ̇} → (A ≃ B) → is-fixpoint-domain A → is-fixpoint-domain B
  equiv-is-fp-domain eqv fixA = λ g → let α = pr₁ eqv
                                          α' = inverse α (pr₂ eqv)
                                          ϕ = α (pr₁ (fixA (α' ∘ g ∘ α))) 
                                      in
                                      pair ϕ
                                           (
                                             (ap α (pr₂ (fixA (α' ∘ g ∘ α))))
                                             ∙ (inverses-are-sections α (pr₂ eqv) (g ϕ))
                                           )

  is-fixpoint : {A : 𝓤 ̇} → (f : A → A) → (ϕ : A) → 𝓤 ̇
  is-fixpoint f ϕ = (ϕ ≡ f ϕ)

  has-fixpoint : {A : 𝓤 ̇} → (f : A → A) → 𝓤 ̇
  has-fixpoint f = Σ (λ ϕ → is-fixpoint f ϕ)

  fixpoint : {A : 𝓤 ̇} → (f : A → A) → 𝓤 ̇
  fixpoint f = Σ (λ ϕ → is-fixpoint f ϕ)

  selector : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦  ̇} → C → C → (A + B → C)
  selector c1 c2 (inl _) = c1
  selector c1 c2 (inr _) = c2

  swapper : {A : 𝓤 ̇} → has-decidable-equality A → A → A → (A → A)
  swapper deceq a x y = selector x a (deceq a y)

                         
                                           
