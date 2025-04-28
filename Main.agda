module Main where

open import 1Lab.Prelude
open import Data.Sum using (_⊎_ ; inl ; inr)

private variable
  ℓ ℓ′ ℴ ℴ′ 𝒽 𝒽′ : Level
  A A′ B B′ X Y : Type ℴ
  F G P Q P′ Q′ : Type ℴ → Type ℴ

record Functor (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  ₀ = F
  field ₁ : (A → B) → F A → F B

open Functor

-- A normalized polynomial functor
record SomePoly (p₀ : Type ℓ) (p♯ : p₀ → Type ℓ) (y : Type ℓ) : Type ℓ where
  constructor some-poly
  field
    position : p₀
    direction : p♯ position → y

open SomePoly

instance
  SomePolyFunctor : {p₀ : Type ℓ} {p♯ : p₀ → Type ℓ} → Functor (SomePoly p₀ p♯)
  SomePolyFunctor .₁ f p .position = p .position
  SomePolyFunctor .₁ f p .direction y = f (p .direction y)

-- To show that a functor is polynomial, we just ask that it be isomorphic to
-- some normalized polynomial
record Poly (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  constructor poly
  field
    ⦃ is-Functor ⦄ : Functor F
    positions : Type ℓ
    directions : positions → Type ℓ
    is-Poly : F ≡ SomePoly positions directions

  open Functor is-Functor public

record _⨰_ (P Q : Type ℓ → Type ℓ) (y : Type ℓ) : Type ℓ where
  constructor pair
  field
    π₁ : P y
    π₂ : Q y

open _⨰_

⨰≃× : ∀ y → (P ⨰ Q) y ≃ (P y × Q y)
⨰≃× _ = Iso→Equiv (⨰→× , (iso ×→⨰ (λ _ → refl) (λ _ → refl)))
  where
    ⨰→× : _
    ⨰→× z = z .π₁ , z .π₂
    ×→⨰ : _
    ×→⨰ z = pair (z .fst) (z .snd)

⨰-ap : ∀ y → (P y ≃ P′ y) → (Q y ≃ Q′ y) → (P ⨰ Q) y ≃ (P′ ⨰ Q′) y
⨰-ap y P≃P′ Q≃Q′ =
  ⨰≃× y ∙e Σ-ap P≃P′ (λ _ → Q≃Q′) ∙e ((⨰≃× y) e⁻¹)

⨰-Poly-distrib
  : ∀ (p₀ q₀ : Type ℓ) (p♯ : p₀ → Type ℓ) (q♯ : q₀ → Type ℓ) (y : Type ℓ)
  → (SomePoly p₀ p♯ ⨰ SomePoly q₀ q♯) y
  ≃ SomePoly (p₀ × q₀) (λ (a , b) → p♯ a ⊎ q♯ b) y
⨰-Poly-distrib p₀ q₀ p♯ q♯ y =
  Iso→Equiv (⨰→Poly , (iso Poly→⨰ ⨰→Poly→⨰ λ _ → refl))
  where
    open import Data.Sum using ([_,_] ; []-η ; []-unique)
    open _⨰_
    ⨰→Poly : _
    ⨰→Poly (pair p q) =
      some-poly (p .position , q .position) [ p .direction , q .direction ]
    Poly→⨰ : _
    Poly→⨰ (some-poly pos dir) =
      pair
        (some-poly (pos .fst) (λ x → dir (inl x)))
        (some-poly (pos .snd) (λ x → dir (inr x)))

    -- Agda doesn't automatically reduce [ f ∘ inl , f ∘ inr ] → f, so we need
    -- to use []-unique explicitly
    ⨰→Poly→⨰ : (p : SomePoly (p₀ × q₀) _ y) → ⨰→Poly (Poly→⨰ p) ≡ p
    ⨰→Poly→⨰ (some-poly pos _) =
      ap (some-poly pos) ([]-unique refl refl)

module _
  {P Q : Type ℓ → Type ℓ}
  {p₀ : Type ℴ} {q₀ : Type ℴ′} {p♯ : p₀ → Type 𝒽} {q♯ : q₀ → Type 𝒽}
  ⦃ polyP@(poly p₀ p♯ P-is-Poly) : Poly P ⦄
  ⦃ polyQ@(poly q₀ q♯ Q-is-Poly) : Poly Q ⦄
  where
  open Poly
  open _⨰_

  f-P-is-Poly : ∀ (y : Type ℓ) → P y ≡ SomePoly p₀ p♯ y
  f-P-is-Poly = happly P-is-Poly

  f-Q-is-Poly : ∀ (y : Type ℓ) → Q y ≡ SomePoly q₀ q♯ y
  f-Q-is-Poly = happly Q-is-Poly

  ⨰≃Poly
    : (y : Type ℓ)
    → (P ⨰ Q) y ≃ SomePoly (p₀ × q₀) (λ (a , b) → (p♯ a ⊎ q♯ b)) y
  ⨰≃Poly y =
    (P ⨰ Q) y                                 ≃⟨ ⨰-ap y P≃Poly Q≃Poly ⟩
    (SomePoly p₀ p♯ ⨰ SomePoly q₀ q♯) y       ≃⟨ ⨰-Poly-distrib p₀ q₀ p♯ q♯ y ⟩
    SomePoly (p₀ × q₀)
             (λ (a , b) → (p♯ a ⊎ q♯ b)) y    ≃∎
    where
      P≃Poly : _
      P≃Poly = path→equiv (happly P-is-Poly y)
      Q≃Poly : _
      Q≃Poly = path→equiv (happly Q-is-Poly y)

  ⨰≡Poly : (P ⨰ Q) ≡ SomePoly (p₀ × q₀) (λ (a , b) → (p♯ a ⊎ q♯ b))
  ⨰≡Poly = funext (ua ∘ ⨰≃Poly)

  instance
    ⨰-Poly : Poly (P ⨰ Q)
    ⨰-Poly .is-Functor .₁ f pq .π₁ = (polyP .₁) f (pq .π₁)
    ⨰-Poly .is-Functor .₁ f pq .π₂ = (polyQ .₁) f (pq .π₂)
    ⨰-Poly .positions = p₀ × q₀
    ⨰-Poly .directions (a , b) = p♯ a ⊎ q♯ b
    ⨰-Poly .is-Poly = ⨰≡Poly

record _⊗_ (P Q : Type ℓ → Type ℓ)
  ⦃ p : Poly P ⦄ ⦃ q : Poly Q ⦄
  (y : Type ℓ)
  : Type ℓ where
  private module p = Poly p
  private module q = Poly q
  field
    p-positions : p.positions
    q-positions : q.positions
    directions : p.directions p-positions × q.directions q-positions → y

data _◃_ (P Q : Type ℓ → Type ℓ) (y : Type ℓ) : Type ℓ where
  composite : P (Q y) → (P ◃ Q) y

Fun : Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
Fun A B = A → B

module _
  {P Q : Type ℓ → Type ℓ}
  {p₀ : Type ℴ} {q₀ : Type ℴ′} {p♯ : p₀ → Type 𝒽} {q♯ : q₀ → Type 𝒽′}
  ⦃ polyP@(poly p₀ p♯ _) : Poly P ⦄ ⦃ polyQ@(poly q₀ q♯ _) : Poly Q ⦄
  where
  open Poly
  open _⊗_

  f⊗≡Poly
    : (y : Type ℓ)
    → (P ⊗ Q) y ≡ SomePoly (p₀ × q₀) (λ (a , b) → (p♯ a × q♯ b)) y
  f⊗≡Poly y = Iso→Path (⊗→Poly , (iso Poly→⊗ (λ _ → refl) λ _ → refl))
    where
      ⊗→Poly : _
      ⊗→Poly pq = some-poly (pq .p-positions , pq .q-positions) (pq .directions)
      Poly→⊗ : _
      Poly→⊗ p .p-positions = p .position .fst
      Poly→⊗ p .q-positions = p .position .snd
      Poly→⊗ p .directions = p .direction

  ⊗≡Poly : (P ⊗ Q) ≡ SomePoly (p₀ × q₀) (λ (a , b) → (p♯ a × q♯ b))
  ⊗≡Poly = funext f⊗≡Poly

  instance
    ⊗-Poly : Poly (P ⊗ Q)
    ⊗-Poly .is-Functor .₁ f pq .p-positions = pq .p-positions
    ⊗-Poly .is-Functor .₁ f pq .q-positions = pq .q-positions
    ⊗-Poly .is-Functor .₁ f pq .directions y = f (pq .directions y)
    ⊗-Poly .positions = polyP .positions × polyQ .positions
    ⊗-Poly .directions pq =
      polyP .directions (fst pq) × polyQ .directions (snd pq)
    ⊗-Poly .is-Poly = ⊗≡Poly
