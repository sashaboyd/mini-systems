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
    Sets-cc .has-exp A B .has-is-exp .unique _ = ap curry

  -- open Cartesian-closed (slices-cc 𝟙ₛ) renaming (has-exp to _^_)
  open Cartesian-closed (Sets-cc)

  Sets[_,_] : Set ℓ → Set ℓ → Set ℓ
  Sets[_,_] A B = el (A ⇾ B) (Hom-set A B)

  Σ1A≃A : ∀{ℓ : Level} {x : Type ℓ} → (𝟙ₜ × x) ≃ x
  Σ1A≃A = Σ-contr-eqv (contr (lift tt) (λ _ → refl))

  ≅-ap : (F : Set ℓ → Set ℓ) → (A ≅ B) → (F A ≅ F B)
  ≅-ap {A = A} F = J-iso (λ X _ → F A ≅ F X) id-iso

  -- package curry and uncurry into an isomorphism
  module _ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : X → Type ℓ'} {Z : (x : X) → Y x → Type ℓ''} where
    curry-Iso : Iso ((p : Σ X Y) → Z (p .fst) (p .snd)) ((x : X) → (y : Y x) → Z x y)
    curry-Iso = curry , (iso uncurry (λ _ → refl) (λ _ → refl))

  curry-≅ : (A B C : Set ℓ)
    → Sets[ el! (∣ A ∣ × ∣ B ∣) , C ] ≅ Sets[ A , Sets[ B , C ] ]
  curry-≅ A B C =
    record { to = curry ; from = uncurry
           ; inverses = record { invl = refl ; invr = refl } }

module F where

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
    open _=>_

    -- TODO: we're gonna need naturality here because ◆ has a particular ordering. Probably best to expand the definitions so that I can see exactly what ordering there is and what needs to be reordered

    -- lemma2 : ∀ (F F′ G G′ H H′ : Functor (Sets ℓ) (Sets ℓ)) (φ : F => F′) (γ : G => G′) (θ : H => H′)
    --   → ∀ A (x : ∣ F .F₀ (G .F₀ (H .F₀ A)) ∣) →
    --   F′ .F₁ (λ (y : ∣ G .F₀ (H .F₀ A) ∣) → G′ .F₁ (θ .η A) (γ .η (H .F₀ A) y)) (φ .η (G .F₀ (H .F₀ A)) x)
    --   ≡ (F′ F∘ G′) .F₁ (θ .η A) (F′ .F₁ (γ .η (H .F₀ A)) (φ .η (G .F₀ (H .F₀ A)) x))
    -- lemma2 F F′ G G′ H H′ φ γ θ A x i = F′ .F-∘ (G′ .F₁ (θ .η A)) (γ .η (F₀ H A)) i (φ .η (F₀ G (F₀ H A)) x)
    -- F′ (G′ θ ∘ γ) ∘ φ = F′ G′ θ ∘ F′ γ ∘ φ
    -- PathP
    --   (λ z → Functor.₀ (F∘-assoc z) A ⇾ Functor.₀ (F∘-assoc z) A)
    --   (F₁ F∘-functor (φ , F₁ F∘-functor (ψ , θ)) .η A)
    --   (F₁ F∘-functor (F₁ F∘-functor (φ , ψ) , θ) .η A)

    -- ρ← ◂ G ∘ α← ≡ F ▸ λ←
    -- F(1G) ↝ (F1)G ↝ FG ≡ F(1G) ↝ FG
    -- the morally correct answer is that the action of 1 on objects and morphisms is the identity... in fact, since we've implemented both the identity and associator laws in terms of equalities, they should just be equal by composition of equalities.

    -- so the plan is that we solve this, and then transport along id-iso or id-iso .to or whatever, and if that doesn't work, we try to use this to figure out how to apply the same reasoning at least.
    lemma2 : ∀ {F G : Functor (Sets ℓ) (Sets ℓ)} →
      F∘-assoc {F = Sets ℓ} {F = F} {G = Id {C = Sets ℓ}} {H = G} ∙ (ap₂ _F∘_ F∘-idr refl) ≡ ap₂ _F∘_ refl F∘-idl
    lemma2 {F} {G} i j = {!!}

    -- stuff that might be useful: uaβ and other stuff around there, Hom-transport (converts between path→iso and transport as an identity), Hom-pathp (as before but reversed)
    -- lemma2 : ∀ x →
    --   _◂_
    --      (CM.to
    --       (transport (isomorphism stuff) (id-iso C)
    --        (Functor-path (λ _ → F∘-idr)
    --         (λ φ →
    --            Nat-pathp F∘-idr F∘-idr (Poly.F.lemma φ)))
    --        )
    --       .η F
    --      .η A)
    --      (CM.to
    --       (path→iso
    --        (Functor-path (λ z → F∘-assoc)
    --         (λ (φ , (γ , ψ)) →
    --            Nat-pathp F∘-assoc F∘-assoc
    --            (Poly.F.lemma φ γ ψ))
    --        )
    --       .η (F , Id , G) .η A x))
    --   ≡
    --   _▸_
    --    (CM.to
    --    (path→iso
    --     (Functor-path (λ _ → F∘-idl)
    --      (λ z → Nat-pathp F∘-idl F∘-idl (λ _ → refl)))
    --     )
    --    .η G)
    --   .η A
    -- lemma2 = ?


    postulate
      nonsense : ⊥

    ◃-monoidal : Monoidal-category Cat[ Sets ℓ , Sets ℓ ]
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
          λ φ → Nat-pathp _ _ (lemma φ))
      ni⁻¹
      where
        lemma : ∀ {F G} (φ : F => G) →
          ∀ A → (φ ◆ id {Id}) .η A ≡ φ .η A
        lemma {G = G} φ A i x = G .F-id {x = A} i (φ .η A x)

    -- TODO: probably just go over the implicit arguments and see if an error occurs
    ◃-monoidal .associator =
      path→iso (
        Functor-path (λ _ → F∘-assoc)
        λ (φ , (γ , ψ)) → Nat-pathp F∘-assoc F∘-assoc (lemma φ γ ψ)
      )
      ni⁻¹
      where
        lemma : ∀ {F F′ G G′ H H′ : Functor (Sets ℓ) (Sets ℓ)} (φ : F => F′) (γ : G => G′) (ψ : H => H′)
          → ∀ A → (φ ◆ (γ ◆ ψ)) .η A ≡ ((φ ◆ γ) ◆ ψ) .η A
        lemma {F′ = F′} {G = G} {G′ = G′} {H = H} φ γ ψ A i x =
          F′ .F-∘ {y = G′ .F₀ _} (G′ .F₁ (ψ .η _)) (γ .η _) i (φ .η _ x)

    -- for this, we're trying to get rid of of the identity functor in the middle, I guess after reassociation, so I'm thinking it'll involve using one of the identity laws. What I'm confused by though is that because my associator and unitor definitions involve path→iso, that suggests I'm gonna need some transport identities, but I'm not sure how to introduce them into all this. I guess I'll try the usual method of coming up with something simpler to solve.
    ◃-monoidal .triangle {A = F} {B = G} = absurd nonsense

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
