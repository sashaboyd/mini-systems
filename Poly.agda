open import Cat.Prelude
open import Cat.Displayed.Instances.Family
open import Cat.Displayed.Total
open import Cat.Instances.Sets
open import Cat.Instances.Functor
open import Cat.Functor.Properties
open import 1Lab.Function.Embedding
import Cat.Functor.Hom
open import Cat.Functor.Base

module Poly {ℓ : Level} where

module ₛ = Univalent (Sets-is-category {ℓ})
open ₛ using () renaming (Hom to _→ₛ_ ; Hom-set to →ₛ-set)
open Functor
open Cat.Functor.Hom (Sets ℓ)

private
  variable
    A A′ B B′ p1 p′1 q1 q′1 : Set ℓ

𝟙ₜ : Type ℓ
𝟙ₜ = Lift ℓ ⊤

𝟙ₛ : Set ℓ
𝟙ₛ = el! 𝟙ₜ

[Sets,Sets] : Precategory _ _
[Sets,Sets] = Cat[ Sets ℓ , Sets ℓ ]

-- Representable polynomial functors
module Set where
  import Cat.Reasoning
  open Univalent (Sets-is-category {ℓ})
  open Cat.Reasoning (Sets ℓ) using (id-iso)
  open import Cat.Diagram.Limit.Finite
  open import Cat.Diagram.Limit.Terminal
  open import Cat.Diagram.Product
  open import Cat.CartesianClosed.Locally
  open import Cat.Instances.Sets.Complete
  open import Cat.Instances.Sets.CartesianClosed {ℓ}
  open Locally-cartesian-closed Sets-lcc
  open import Cat.Diagram.Exponential

  module _ where
    open Cartesian-closed
    open Exponential
    open is-exponential
    Sets-cc : Cartesian-closed (Sets ℓ) Sets-products Sets-terminal
    Sets-cc .has-exp A B .B^A = el! (∣ A ∣ → ∣ B ∣)
    Sets-cc .has-exp A B .ev (f , x) = f x
    Sets-cc .has-exp A B .has-is-exp .ƛ f cxt a = f (cxt , a)
    Sets-cc .has-exp A B .has-is-exp .commutes _ = refl
    Sets-cc .has-exp A B .has-is-exp .unique m' x = {!!}

  open Cartesian-closed (slices-cc 𝟙ₛ) renaming (has-exp to _^_)

  Sets[_,_] : Set ℓ → Set ℓ → Set ℓ
  Sets[_,_] A B = el (A →ₛ B) (→ₛ-set A B)

  Σ1A≃A : ∀{ℓ : Level} {x : Type ℓ} → (𝟙ₜ × x) ≃ x
  Σ1A≃A = Σ-contr-eqv (contr (lift tt) (λ _ → refl))

  ident-on-P : (T T′ : Type ℓ) (x y : T) → (P : T → T′) → (x ≡ y) → (P x ≡ P y)
  ident-on-P _ _ x y P = ap P

  ≅-ap : (F : Set ℓ → Set ℓ) → (A ≅ B) → (F A ≅ F B)
  ≅-ap {A = A} F s = J-iso (λ X _ → F A ≅ F X) id-iso s

  ≅-dom : (A ≅ A′) → Sets[ A , B ] ≅ Sets[ A′ , B ]
  ≅-dom {B = B} s = ≅-ap (λ X → el (X →ₛ B) (→ₛ-set X B)) s

  ≅-cod : (B ≅ B′) → Sets[ A , B ] ≅ Sets[ A , B′ ]
  ≅-cod {A = A} s = ≅-ap (λ X → el (A →ₛ X) (→ₛ-set A X)) s

  ≅Sets[_,_] : (A ≅ A′) → (B ≅ B′) → Sets[ A , B ] ≅ Sets[ A′ , B′ ]
  ≅Sets[_,_] {A = A} {B′ = B′} s t =
    ≅-ap (λ X → el (X →ₛ B′) (→ₛ-set X B′)) s
    ∘Iso
    ≅-ap (λ X → el (A →ₛ X) (→ₛ-set A X)) t

  -- package curry and uncurry into an isomorphism
  module _ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : X → Type ℓ'} {Z : (x : X) → Y x → Type ℓ''} where
    curry-Iso : Iso ((p : Σ X Y) → Z (p .fst) (p .snd)) ((x : X) → (y : Y x) → Z x y)
    curry-Iso = curry , (iso uncurry (λ _ → refl) (λ _ → refl))

  curry-≅ : (A B C : Set ℓ)
    → Sets[ el! (∣ A ∣ × ∣ B ∣) , C ] ≅ Sets[ A , Sets[ B , C ] ]
  curry-≅ A B C =
    record { to = curry ; from = uncurry
           ; inverses = record { invl = refl ; invr = refl } }

  -- stupid-iso
  --   : {A B : Set ℓ}
  --   → Sets[ el! (Σ[ _ ∈ 𝟙ₜ ] ∣ A ∣) , el! (Σ[ _ ∈ 𝟙ₜ ] ∣ B ∣) ] ≅ Sets[ A , B ]
  -- stupid-iso {A = A} {B = B} = -- ≅Sets[ Σ1A≅A A , Σ1A≅A B ]
  --   ≅-ap (Sets[_, B ]) Σ1A≅A
  --   ∘Iso
  --   ≅-ap (Sets[ el! (𝟙ₜ × ∣ A ∣) ,_]) Σ1A≅A {A = B}

  -- dumb-iso
  --   : (A B C : Set ℓ)
  --   → Sets[ el! (𝟙ₜ × ∣ A ∣) , Sets[ B , C ] ] ≅ Sets[ el! (∣ A ∣ × ∣ B ∣) , C ]
  -- dumb-iso A B C =
  --   ≅-ap (Sets[_, Sets[ B , C ] ]) Σ1A≅A
  --   ∙Iso
  --   curry-≅ A B C Iso⁻¹

  -- TODO: I'm gonna just have to figure out where × and stuff are defined for the actual category of sets, and make use of that
  -- obvious-iso
  --   : (A B C : Set ℓ)
  --   → Sets[ el! (𝟙ₜ × ∣ A ∣) , el! (𝟙ₜ × ∣ Sets[ B , C ] ∣) ] ≅ Sets[ el! (∣ A ∣ × ∣ B ∣) , C ]
  -- obvious-iso A B C =
  --   ≅-ap (Sets[_, el (Σ ⌞ 𝟙ₜ ⌟ (λ _ → ∣ Sets[ B , C ] ∣)) _ ]) (Σ1A≅A A)
  --   ₛ.∙Iso
  --   ≅-ap (Sets[ A ,_]) (Σ1A≅A Sets[ B , C ])
  --   ₛ.∙Iso
  --   curry-≅ A B C ₛ.Iso⁻¹


module F where
  open import Cat.Functor.Constant
  open import Cat.Instances.Shape.Terminal
  open import 1Lab.HLevel.Universe
  open import 1Lab.Path
  open import Cat.Instances.Poly
  open import Cat.Monoidal.Base
  open import Cat.Monoidal.Instances.Cartesian
  open Monoidal-category (Setsₓ {ℓ})
  open import Cat.Functor.Bifunctor -⊗-
  import Cat.Functor.Bifunctor as Bf
  open import Cat.Functor.Compose
  open import Cat.Bi.Base
  module C = Prebicategory (Cat (lsuc ℓ) ℓ)
  open Univalent (Functor-is-category {D = Sets ℓ} {C = Sets ℓ} Sets-is-category)
  open C using () renaming (_⊗_ to infixr 25 _◃_)

  𝟙 : Poly.Ob ℓ ℓ
  𝟙 .fst = 𝟙ₛ
  𝟙 .snd _ = 𝟙ₛ

  κ⊤ : Functor (Sets ℓ) (Sets ℓ)
  κ⊤ = Const 𝟙ₛ

  rep-poly : Set ℓ → Poly.Ob ℓ ℓ
  rep-poly A = Unit , λ _ → A

  ≅-rep-obs
    : (A B : Set ℓ)
    → el! (A →ₛ B)
    ₛ.≅ el! (𝟙ₜ × (A →ₛ B))
  ≅-rep-obs A B = λ≅

  ≅-test : Hom-from A ≅ Left Unit ◃ Hom-from A
  ≅-test = isoⁿ→iso C.unitor-l _ ∙Iso (unitor-r ◂ni _)

  -- Hom-from A ≅ Hom-from (1 × A)
  -- Hom-from is technically a functor, even though that's not part of the definition, so we might be able to use the fact that functors preserve isomorphisms
  -- alternatively, we can just use path->iso or whatever with ap, which seems like the simpler option

  new-test : (A : Set ℓ) → よcov # A ≅ よcov # (el! (𝟙ₜ × ∣ A ∣))
  new-test _ = F-map-iso よcov ((iso-op-invariant e⁻¹) # λ≅)

  ≅-rep-functor : Hom-from A ≅ Polynomial-functor {ℓ} {ℓ} (rep-poly A)
  ≅-rep-functor {A = A} = {!new-test A ∙Iso ≅-test!}

  fibre-rep : Polynomial-functor {ℓ} {ℓ} (rep-poly A) ≡ Hom-from A
  fibre-rep {A} = Functor-path ob-path λ {x} {y} f → hom-path {x} {y} f
    where
      ob-path : (x : Set ℓ) →
                 F₀ (Polynomial-functor (rep-poly A)) x ≡ F₀ (Hom-from A) x
      ob-path x = n-ua Set.Σ1A≃A

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
