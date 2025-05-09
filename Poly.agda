open import Cat.Prelude
open import Cat.Displayed.Instances.Family
open import Cat.Displayed.Total
open import Cat.Instances.Poly
open import Cat.Instances.Functor
open import Cat.Functor.Properties
open import 1Lab.Function.Embedding

module Poly {ℓ : Level} where

open Functor
open Total-hom
open Precategory (Sets ℓ)
open Precategory (Poly ℓ ℓ) using ()
  renaming ( id to idₚ
           ; _∘_ to _∘ₚ_
           ; Ob to poly
           ; Hom to DLens
           )

private
  variable
    A A′ B B′ p1 p′1 q1 q′1 : Set ℓ

𝟙ₛ : Set ℓ
𝟙ₛ = el! (Lift ℓ ⊤)

module _ where
  open import Cat.Functor.Constant
  open import Cat.Instances.Shape.Terminal

  𝟙 : Poly.Ob ℓ ℓ
  𝟙 .fst = 𝟙ₛ
  𝟙 .snd _ = el! (Lift ℓ ⊥)

  κ⊤ : Functor (Sets ℓ) (Sets ℓ)
  κ⊤ = Const (el! (Lift ℓ ⊤))

[Sets,Sets] : Precategory _ _
[Sets,Sets] = Cat[ Sets ℓ , Sets ℓ ]

Poly→Functor : Functor (Poly ℓ ℓ) Cat[ Sets ℓ , Sets ℓ ]
Poly→Functor .F₀ = Polynomial-functor
Poly→Functor .F₁ (total-hom l⁺ l⁻) ._=>_.η _ (x , h) =
  l⁺ x , (λ z → h (l⁻ x z))
Poly→Functor .F₁ (total-hom l⁺ l⁻) ._=>_.is-natural _ _ _ = refl
Poly→Functor .F-id = Nat-path λ _ → refl
Poly→Functor .F-∘ k@(total-hom k⁺ k⁻) l@(total-hom l⁺ l⁻) =
  Nat-path λ _ → refl


-- Poly→Functor-faithful : is-fully-faithful Poly→Functor
-- Poly→Functor-faithful = is-iso→is-equiv isom
--   where
--     open is-iso
--     open _=>_
--     open import 1Lab.Underlying using (apply)
--     isom : is-iso (Poly→Functor .F₁)
--     isom .inv nt =
--       total-hom
--         (λ a → nt .η 𝟙ₛ (a , λ _ → lift tt) .fst)
--         λ a u → {!!}
--     isom .rinv x = {!!}
--     isom .linv = {!!}
