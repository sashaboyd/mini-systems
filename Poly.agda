open import Cat.Prelude
open import Cat.Displayed.Total
open import Cat.Instances.Poly

module Poly {ℴ 𝒽 : Level} where

open Functor
open Total-hom

private
  variable
    A A′ B B′ p1 p′1 q1 q′1 : Set ℴ

module _ where
  open import Cat.Functor.Constant
  open import Cat.Instances.Shape.Terminal

  𝟙 : Poly.Ob ℴ 𝒽
  𝟙 .fst = el! (Lift ℴ ⊤)
  𝟙 .snd _ = el! (Lift 𝒽 ⊥)

  κ⊤ : Functor (Sets ℴ) (Sets (ℴ ⊔ 𝒽))
  κ⊤ = Const (el! (Lift (ℴ ⊔ 𝒽) ⊤))
