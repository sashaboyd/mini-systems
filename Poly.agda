open import Cat.Prelude
open import Cat.Displayed.Instances.Family
open import Cat.Displayed.Total
open import Cat.Instances.Functor
open import Cat.Functor.Properties
open import 1Lab.Function.Embedding
import Cat.Functor.Hom
open import Cat.Functor.Base
import Cat.Reasoning as CR
import Cat.Morphism as CM

module Poly {ℓ : Level} where

open Functor

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
module ₛ where
  open import Cat.Instances.Sets public
  open Cat.Functor.Hom (Sets ℓ) public
  import Cat.Reasoning
  open Cat.Reasoning (Sets ℓ) using (id-iso)
  open Univalent (Sets-is-category {ℓ}) renaming (Hom to infixr 0 _⇾_) public
  open import Cat.Diagram.Limit.Finite
  open import Cat.Diagram.Limit.Terminal
  open import Cat.Diagram.Product
  open import Cat.CartesianClosed.Locally
  open import Cat.Instances.Sets.Complete
  open import Cat.Instances.Sets.CartesianClosed {ℓ}
  open Locally-cartesian-closed Sets-lcc
  open import Cat.Diagram.Exponential

  open import Cat.Monoidal.Base
  open import Cat.Monoidal.Instances.Cartesian
  open Monoidal-category (Setsₓ {ℓ}) public

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
  Sets[_,_] A B = el (A ⇾ B) (Hom-set A B)

  Σ1A≃A : ∀{ℓ : Level} {x : Type ℓ} → (𝟙ₜ × x) ≃ x
  Σ1A≃A = Σ-contr-eqv (contr (lift tt) (λ _ → refl))

  ident-on-P : (T T′ : Type ℓ) (x y : T) → (P : T → T′) → (x ≡ y) → (P x ≡ P y)
  ident-on-P _ _ x y P = ap P

  ≅-ap : (F : Set ℓ → Set ℓ) → (A ≅ B) → (F A ≅ F B)
  ≅-ap {A = A} F s = J-iso (λ X _ → F A ≅ F X) id-iso s

  ≅-dom : (A ≅ A′) → Sets[ A , B ] ≅ Sets[ A′ , B ]
  ≅-dom {B = B} s = ≅-ap (λ X → el (X ⇾ B) (Hom-set X B)) s

  ≅-cod : (B ≅ B′) → Sets[ A , B ] ≅ Sets[ A , B′ ]
  ≅-cod {A = A} s = ≅-ap (λ X → el (A ⇾ X) (Hom-set A X)) s

  ≅Sets[_,_] : (A ≅ A′) → (B ≅ B′) → Sets[ A , B ] ≅ Sets[ A′ , B′ ]
  ≅Sets[_,_] {A = A} {B′ = B′} s t =
    ≅-ap (λ X → el (X ⇾ B′) (Hom-set X B′)) s
    ∘Iso
    ≅-ap (λ X → el (A ⇾ X) (Hom-set A X)) t

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

  postulate
    nonsense : ⊥

  open ₛ using (_⇾_)
  open import Cat.Functor.Constant
  open import Cat.Instances.Shape.Terminal
  open import 1Lab.HLevel.Universe
  open import 1Lab.Path
  import Cat.Instances.Poly as Poly
  open import Cat.Monoidal.Base
  open import Cat.Monoidal.Instances.Cartesian
  open import Cat.Instances.Presheaf.Limits ℓ (Sets ℓ ^op)
  open Monoidal-category (Cartesian-monoidal PSh-products PSh-terminal)
  open import Cat.Functor.Bifunctor -⊗-
  import Cat.Functor.Bifunctor as Bf
  open import Cat.Functor.Compose
  open import Cat.Bi.Base
  module C = Prebicategory (Cat (lsuc ℓ) ℓ)
  PolyFun = Cat[ Sets ℓ , Sets ℓ ]
  open import Cat.Morphism PolyFun using (id-iso)
  open Univalent (Functor-is-category {D = Sets ℓ} {C = Sets ℓ} ₛ.Sets-is-category)
  open C using () renaming (_⊗_ to infixr 25 _◃₀_)
  open import 1Lab.Path

  module _ where
    import Cat.Morphism as CM
    module ₘ = CM (Cat[ PolyFun , PolyFun ])
    module ₚ = CR PolyFun
    open Monoidal-category
    open import Cat.Univalent

    open make-natural-iso
    lemma :
      ∀ F G φ → PathP (λ i → Hom (F∘-idl {F = F} i) (F∘-idl {F = G} i)) (id ◆ φ) φ
    lemma F G φ =
      Nat-pathp F∘-idl F∘-idl λ _ → refl

    lemma2 :
      ∀ F G φ → PathP (λ i → Hom (F∘-idr {F = F} i) (F∘-idr {F = G} i)) (φ ◆ id) φ
    lemma2 F G φ =
      -- I'm really not sure what to do here, but φ is being applied on the outside, while the inside is changing trivially
      Nat-pathp F∘-idr F∘-idr (λ A → {!!})

    ◃-monoidal : Monoidal-category (PSh ℓ (Sets ℓ ^op))
    ◃-monoidal .-⊗- = F∘-functor
    ◃-monoidal .Unit = Id
    ◃-monoidal .unitor-l =
      path→iso
        (Functor-path (λ _ → F∘-idl)
          (λ _ → Nat-pathp F∘-idl F∘-idl λ _ →  refl))
      ni⁻¹
    ◃-monoidal .unitor-r =
      path→iso
        (Functor-path (λ _ → F∘-idr)
          λ φ → Nat-pathp F∘-idr F∘-idr λ A → {!!})
      ni⁻¹
    ◃-monoidal .associator = absurd nonsense
    ◃-monoidal .triangle = absurd nonsense
    ◃-monoidal .pentagon = absurd nonsense

  𝟙 : Poly.Poly.Ob ℓ ℓ
  𝟙 .fst = 𝟙ₛ
  𝟙 .snd _ = 𝟙ₛ

  κ⊤ : Functor (Sets ℓ) (Sets ℓ)
  κ⊤ = Const 𝟙ₛ

  rep-poly : Set ℓ → Poly.Poly.Ob ℓ ℓ
  rep-poly A = 𝟙ₛ , λ _ → A

  -- ≅-rep-obs
  --   : (A B : Set ℓ)
  --   → el! (A →ₛ B)
  --   ₛ.≅ el! (𝟙ₜ × (A →ₛ B))
  -- ≅-rep-obs A B = λ≅

  -- TODO: so I guess the unit here is the presheaf into 1, but I need it to be just the set 1, but that doesn't make much sense
  ≅-test : ₛ.Hom-from A ≅ Unit ⊗ ₛ.Hom-from A
  ≅-test = λ≅ -- unitor-r -- ∙Iso (unitor-r ◂ni _)

  ≅-test2 : Id ◃₀ ₛ.Hom-from A ≅ (Bf.Right ₛ.-⊗- ₛ.Unit ◃₀ ₛ.Hom-from A)
  ≅-test2 = ₛ.unitor-l ◂ni _

  -- Hom-from A ≅ Hom-from (1 × A)
  -- Hom-from is technically a functor, even though that's not part of the definition, so we might be able to use the fact that functors preserve isomorphisms
  -- alternatively, we can just use path->iso or whatever with ap, which seems like the simpler option

  new-test : (A : Set ℓ) → ₛ.よcov · A ≅ ₛ.よcov · (el! (𝟙ₜ × ∣ A ∣))
  new-test _ = F-map-iso ₛ.よcov ((ₛ.iso-op-invariant e⁻¹) .fst ₛ.λ≅)

  -- ≅-rep-functor : Hom-from A ≅ Polynomial-functor {ℓ} {ℓ} (rep-poly A)
  -- ≅-rep-functor {A = A} = {!new-test A ∙Iso ≅-test2!}

  -- fibre-rep : Polynomial-functor {ℓ} {ℓ} (rep-poly A) ≡ Hom-from A
  -- fibre-rep {A} = Functor-path ob-path λ {x} {y} f → hom-path {x} {y} f
  --   where
  --     ob-path : (x : Set ℓ) →
  --                F₀ (Polynomial-functor (rep-poly A)) x ≡ F₀ (Hom-from A) x
  --     ob-path x = n-ua ₛ.Σ1A≃A

  --     hom-path
  --       : {x y : Set ℓ} → (f : ∣ x ∣ → ∣ y ∣)
  --       → PathP (λ i → ∣ ob-path x i ∣ → ∣ ob-path y i ∣)
  --               (λ (lift tt , g) → lift tt , λ z → f (g z))
  --         (λ g z → f (g z))
  --     hom-path {x} {y} f = {!!}
      {-
        -- what gives me a PathP in all this?
        J-iso (λ b p → {! homs with domain varying over b, maybe where p gives the specific domain somehow !}) {!hom at id!} {!Σ1A≅A!}
        uncurry for Sets
        J-iso (λ b p → {! homs with codomain varying over b !}) {! hom at id !} {! Σ1A≅A!}
        -}

  Poly→Functor : Functor (Poly.Poly ℓ ℓ) Cat[ Sets ℓ , Sets ℓ ]
  Poly→Functor .F₀ = Poly.Polynomial-functor
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
