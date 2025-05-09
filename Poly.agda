open import Cat.Prelude
open import Cat.Displayed.Instances.Family
open import Cat.Displayed.Total
open import Cat.Instances.Sets
open import Cat.Instances.Poly
open import Cat.Instances.Functor
open import Cat.Functor.Properties
open import 1Lab.Function.Embedding
open import Cat.Functor.Hom
open import Cat.Functor.Base

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

𝟙ₜ : Type ℓ
𝟙ₜ = Lift ℓ ⊤

𝟙ₛ : Set ℓ
𝟙ₛ = el! 𝟙ₜ

[Sets,Sets] : Precategory _ _
[Sets,Sets] = Cat[ Sets ℓ , Sets ℓ ]

module _ where
  open import Cat.Functor.Constant
  open import Cat.Instances.Shape.Terminal
  open import 1Lab.HLevel.Universe
  open import 1Lab.Path

  𝟙 : Poly.Ob ℓ ℓ
  𝟙 .fst = 𝟙ₛ
  𝟙 .snd _ = 𝟙ₛ

  κ⊤ : Functor (Sets ℓ) (Sets ℓ)
  κ⊤ = Const 𝟙ₛ

-- Representable polynomial functors
module _ where
  import Cat.Reasoning
  open Cat.Reasoning (Sets ℓ) renaming (_≅_ to _≅ₛ_ ; Hom to _→ₛ_)
  open import Cat.Morphism hiding (_≅_)
  open Univalent (Sets-is-category {ℓ})

  Σ1A≃A : ∀{ℓ : Level} (x : Type ℓ) → (Σ[ _ ∈ 𝟙ₜ ] x) ≃ x
  Σ1A≃A _ = Σ-contr-eqv (contr (lift tt) (λ _ → refl))

  Σ1A≅A : (x : Set ℓ) → (el! (Σ[ _ ∈ 𝟙ₜ ] ∣ x ∣)) ≅ₛ x
  Σ1A≅A x = equiv→iso (Σ1A≃A ∣ x ∣)

  rep-poly : Set ℓ → Poly.Ob ℓ ℓ
  rep-poly A = 𝟙ₛ , λ _ → A

  ident-on-P : (T T′ : Type ℓ) (x y : T) → (P : T → T′) → (x ≡ y) → (P x ≡ P y)
  ident-on-P _ _ x y P = ap P

  eqv-first : (x y : Type ℓ) → (P : Type ℓ → Type ℓ) → (x ≃ y) → (P x ≃ P y)
  eqv-first = ?

  -- TODO: the way this SHOULD work is that if we have A≡A′, then we should have PA≡PA′, but for some reason i can't find anything in 1Lab that says anything like that
  iso-first : A ≅ₛ A′ → ((A →ₛ B) ≃ (A′ →ₛ B))
  iso-first A≅A′ = {!!}

  -- TODO: if i use these, they'll need to have more consistent names
  1g→a≡g→a : (x y : Type ℓ) → ((Σ[ _ ∈ 𝟙ₜ ] x) → y) ≃ (x → y)
  1g→a≡g→a _ _ = {!!}
-- (funext (λ x → ua (Σ1A≃A x)))
  Fun : Type ℓ → Type ℓ → Type ℓ
  Fun x y = x → y

  x→1y≡x→y : (x y : Set ℓ) → Iso (x →ₛ (el! (Σ[ _ ∈ 𝟙ₜ ] ∣ y ∣))) (x →ₛ y)
  x→1y≡x→y x y = {!!} , {!!}
  -- NOTE: this DOES NOT use funext for the proof, because we're not proving that two specific functions can be identified, but that two function /types/ can be identified
  -- funext (λ x₁ → {!!}) {!!} {!!}
  -- subst {!Fun x!} (ua (Σ1A≃A y)) {!!}
  -- path→equiv (funext (λ x → {!ua!}) {!!} {!!})

  -- package curry and uncurry into an isomorphism
  module _ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : X → Type ℓ'} {Z : (x : X) → Y x → Type ℓ''} where
    curry-Iso : Iso ((p : Σ X Y) → Z (p .fst) (p .snd)) ((x : X) → (y : Y x) → Z x y)
    curry-Iso = curry , (iso uncurry (λ _ → refl) (λ _ → refl))

  -- uncurry

  fibre-rep : Polynomial-functor {ℓ} {ℓ} (rep-poly A) ≡ Hom-from (Sets ℓ) A
  fibre-rep {A} = Functor-path ob-path λ {x} {y} f → hom-path {x} {y} f
    where
      ob-path : (x : Set ℓ) →
                 F₀ (Polynomial-functor (rep-poly A)) x ≡ F₀ (Hom-from (Sets ℓ) A) x
      ob-path x = n-ua (Σ1A≃A (∣ A ∣ → ∣ x ∣))

      hom-path
        : {x y : Set ℓ} → (f : ∣ x ∣ → ∣ y ∣)
        → PathP (λ i → ∣ ob-path x i ∣ → ∣ ob-path y i ∣)
                (λ (lift tt , g) → lift tt , λ z → f (g z))
          (λ g z → f (g z))
      hom-path {x} {y} f = {!!}
      {-
        -- what gives me a PathP in all this?
        J-iso (λ b p → {! homs with domain varying over b, maybe where p gives the specific domain somehow !}) {!hom at id!} {!Σ1A≅A!}
        uncurry for Sets
        J-iso (λ b p → {! homs with codomain varying over b !}) {! hom at id !} {! Σ1A≅A!}
        -}

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
