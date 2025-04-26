module Main where

open import 1Lab.Prelude renaming (_∘_ to _·_)

private variable
  ℓ ℓ′ ℴ ℴ′ 𝒽 𝒽′ : Level
  A A′ B B′ X Y : Type ℴ
  F G P Q : Type ℴ → Type ℴ

record Functor (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  _₀ = F
  field _₁ : (A → B) → F A → F B
  infixl 100 _₀
  infixl 100 _₁

open Functor

module ₚ where
  record Poly (p₀ : Type ℓ) (p♯ : p₀ → Type ℓ) (y : Type ℓ) : Type ℓ where
    constructor poly
    field
      position : p₀
      direction : p♯ position → y

  instance
    open Poly
    PolyFunctor : {p₀ : Type ℓ} {p♯ : p₀ → Type ℓ} → Functor (Poly p₀ p♯)
    (PolyFunctor ₁) f p .position = p .position
    (PolyFunctor ₁) f p .direction y = f (p .direction y)

open ₚ.Poly

record Poly (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  constructor poly
  field
    ⦃ is-Functor ⦄ : Functor F
    positions : Type ℓ
    directions : positions → Type ℓ
    is-Poly : F ≡ ₚ.Poly positions directions

  open Functor is-Functor public

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

Fun : Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
Fun A B = A → B

module _
  {P Q : Type ℓ → Type ℓ}
  {p₀ : Type ℴ} {q₀ : Type ℴ′} {p♯ : p₀ → Type 𝒽} {q♯ : q₀ → Type 𝒽′}
  ⦃ polyP@(poly p₀ p♯ _) : Poly P ⦄ ⦃ polyQ@(poly q₀ q♯ _) : Poly Q ⦄
  where
  open Poly

  f⊗≡Poly
    : (y : Type ℓ)
    → (P ⊗ Q) y ≡ ₚ.Poly (p₀ × q₀) (λ (a , b) → (p♯ a × q♯ b)) y
  f⊗≡Poly y = Iso→Path (⊗→Poly , (iso Poly→⊗ (λ _ → refl) λ _ → refl))
    where
      open _⊗_
      ⊗→Poly : _
      ⊗→Poly pq = ₚ.poly (pq .p-positions , pq .q-positions) (pq .directions)
      Poly→⊗ : _
      Poly→⊗ p .p-positions = p .position .fst
      Poly→⊗ p .q-positions = p .position .snd
      Poly→⊗ p .directions = p .direction

  ⊗≡Poly : (P ⊗ Q) ≡ ₚ.Poly (p₀ × q₀) (λ (a , b) → (p♯ a × q♯ b))
  ⊗≡Poly = funext f⊗≡Poly

  instance
    open Poly

    open _⊗_
    ⊗-Poly : Poly (P ⊗ Q)
    (⊗-Poly .is-Functor ₁) f pq .p-positions = pq .p-positions
    (⊗-Poly .is-Functor ₁) f pq .q-positions = pq .q-positions
    (⊗-Poly .is-Functor ₁) f pq .directions y = f (pq .directions y)
    ⊗-Poly .positions = polyP .positions × polyQ .positions
    ⊗-Poly .directions pq =
      polyP .directions (fst pq) × polyQ .directions (snd pq)
    ⊗-Poly .is-Poly = ⊗≡Poly
