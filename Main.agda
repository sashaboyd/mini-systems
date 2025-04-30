module Main where

open import 1Lab.Prelude
open import Data.Sum using (_⊎_ ; inl ; inr)

private variable
  ℓ ℓ′ ℴ ℴ′ 𝒽 𝒽′ : Level
  A A′ B B′ X Y : Type ℴ
  P Q P′ Q′ : Type ℴ → Type ℴ

record Functor (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  ob-action = F
  field ₁ : ∀ {A B : Type ℓ} → (A → B) → F A → F B

open Functor

const : A → X → A
const a _ = a

κ : ∀ (A : Type ℓ) → Functor (const A)
κ _ .₁ _ a = a

record _⇒_
  {F₀ G₀ : Type ℓ → Type ℓ}
  (F : Functor F₀) (G : Functor G₀)
  : Type (lsuc ℓ) where
  field
    trans : ∀ (A : Type ℓ) → F₀ A → G₀ A
    is-natural
      : ∀ {A B : Type ℓ}
      (f : A → B) (x : F₀ A)
      → trans B (F .₁ f x) ≡ (G .₁ f (trans A x))

open _⇒_
infixr 0 _⇒_

constTrans : {A B : Type ℓ} (f : A → B) → κ A ⇒ κ B
constTrans f .trans _ c = f c
constTrans f .is-natural g c = refl

-- A normalized polynomial functor
SomePoly : (p1 : Type ℓ) (p[_] : p1 → Type ℓ) (y : Type ℓ) → Type ℓ
SomePoly p1 p[_] y = Σ[ x ∈ p1 ] (p[ x ] → y)

PolyF : (p1 : Type ℓ) (p[_] : p1 → Type ℓ) → Functor (SomePoly p1 p[_])
PolyF _ _ .₁ f p .fst = p .fst
PolyF _ _ .₁ f p .snd y = f (p .snd y)

instance
  PolyFunctor
    : {p1 : Type ℓ} {p[_] : p1 → Type ℓ}
    → Functor (SomePoly {ℓ = ℓ} p1 p[_])
  PolyFunctor {p1 = p1} {p[_] = p[_]} = PolyF p1 p[_]

Lens
  : {p1 q1 : Type ℓ} {p[_] : p1 → Type ℓ} {q[_] : q1 → Type ℓ}
  → (f⃗ : p1 → q1)
  → (f↩ : {x : p1} → q[ f⃗ x ] → p[ x ])
  → PolyF p1 p[_] ⇒ PolyF q1 q[_]
Lens f⃗ f↩ .trans _ (x , p) =
  f⃗ x , λ x′ → p (f↩ x′)
Lens _ _ .is-natural {A = A} _ _ = refl

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

open Poly

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
  : ∀ (p1 q1 : Type ℓ) (p[_] : p1 → Type ℓ) (q[_] : q1 → Type ℓ) (y : Type ℓ)
  → (SomePoly p1 p[_] ⨰ SomePoly q1 q[_]) y
  ≃ SomePoly (p1 × q1) (λ (a , b) → p[ a ] ⊎ q[ b ]) y
⨰-Poly-distrib p1 q1 p[_] q[_] y =
  Iso→Equiv (⨰→Poly , (iso Poly→⨰ ⨰→Poly→⨰ λ _ → refl))
  where
    open import Data.Sum using ([_,_] ; []-η ; []-unique)
    open _⨰_
    ⨰→Poly : _
    ⨰→Poly (pair p q) =
      (p .fst , q .fst) , [ p .snd , q .snd ]
    Poly→⨰ : _
    Poly→⨰ (pos , dir) =
      pair
        (pos .fst , λ x → dir (inl x))
        (pos .snd , λ x → dir (inr x))

    -- Agda doesn't automatically reduce [ f ∘ inl , f ∘ inr ] → f, so we need
    -- to use []-unique explicitly
    ⨰→Poly→⨰ : (p : SomePoly (p1 × q1) _ y) → ⨰→Poly (Poly→⨰ p) ≡ p
    ⨰→Poly→⨰ (pos , _) =
      ap (pos ,_) ([]-unique refl refl)

module _
  {P Q : Type ℓ → Type ℓ}
  {p1 : Type ℴ} {q1 : Type ℴ′} {p[_] : p1 → Type 𝒽} {q[_] : q1 → Type 𝒽}
  ⦃ polyP@(poly p1 p[_] P-is-Poly) : Poly P ⦄
  ⦃ polyQ@(poly q1 q[_] Q-is-Poly) : Poly Q ⦄
  where
  open _⨰_

  f-P-is-Poly : ∀ (y : Type ℓ) → P y ≡ SomePoly p1 p[_] y
  f-P-is-Poly = happly P-is-Poly

  f-Q-is-Poly : ∀ (y : Type ℓ) → Q y ≡ SomePoly q1 q[_] y
  f-Q-is-Poly = happly Q-is-Poly

  ⨰≃Poly
    : (y : Type ℓ)
    → (P ⨰ Q) y ≃ SomePoly (p1 × q1) (λ (a , b) → (p[ a ] ⊎ q[ b ])) y
  ⨰≃Poly y =
    (P ⨰ Q) y                               ≃⟨ ⨰-ap y P≃Poly Q≃Poly ⟩
    (SomePoly p1 p[_] ⨰ SomePoly q1 q[_]) y ≃⟨ ⨰-Poly-distrib p1 q1 p[_] q[_] y ⟩
    SomePoly (p1 × q1)
      (λ (a , b) → p[ a ] ⊎ q[ b ]) y       ≃∎
    where
      P≃Poly : _
      P≃Poly = path→equiv (happly P-is-Poly y)
      Q≃Poly : _
      Q≃Poly = path→equiv (happly Q-is-Poly y)

  ⨰≡Poly : (P ⨰ Q) ≡ SomePoly (p1 × q1) (λ (a , b) → (p[ a ] ⊎ q[ b ]))
  ⨰≡Poly = funext (ua ∘ ⨰≃Poly)

  instance
    ⨰-Poly : Poly (P ⨰ Q)
    ⨰-Poly .is-Functor .₁ f pq .π₁ = polyP .₁ f (pq .π₁)
    ⨰-Poly .is-Functor .₁ f pq .π₂ = polyQ .₁ f (pq .π₂)
    ⨰-Poly .positions = p1 × q1
    ⨰-Poly .directions (a , b) = p[ a ] ⊎ q[ b ]
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

module _
  {P Q : Type ℓ → Type ℓ}
  {p1 : Type ℴ} {q1 : Type ℴ′} {p[_] : p1 → Type 𝒽} {q[_] : q1 → Type 𝒽′}
  ⦃ polyP@(poly p1 p[_] _) : Poly P ⦄ ⦃ polyQ@(poly q1 q[_] _) : Poly Q ⦄
  where
  open _⊗_

  ⊗≃Poly
    : (y : Type ℓ)
    → (P ⊗ Q) y ≃ SomePoly (p1 × q1) (λ (a , b) → (p[ a ] × q[ b ])) y
  ⊗≃Poly y = Iso→Equiv (⊗→Poly , (iso Poly→⊗ (λ _ → refl) λ _ → refl))
    where
      ⊗→Poly : _
      ⊗→Poly pq = (pq .p-positions , pq .q-positions) , pq .directions
      Poly→⊗ : _
      Poly→⊗ p .p-positions = p .fst .fst
      Poly→⊗ p .q-positions = p .fst .snd
      Poly→⊗ p .directions = p .snd

  ⊗≡Poly : (P ⊗ Q) ≡ SomePoly (p1 × q1) (λ (a , b) → p[ a ] × q[ b ])
  ⊗≡Poly = funext (ua ∘ ⊗≃Poly)

  instance
    ⊗-Poly : Poly (P ⊗ Q)
    ⊗-Poly .is-Functor .₁ f pq .p-positions = pq .p-positions
    ⊗-Poly .is-Functor .₁ f pq .q-positions = pq .q-positions
    ⊗-Poly .is-Functor .₁ f pq .directions y = f (pq .directions y)
    ⊗-Poly .positions = polyP .positions × polyQ .positions
    ⊗-Poly .directions pq =
      polyP .directions (fst pq) × polyQ .directions (snd pq)
    ⊗-Poly .is-Poly = ⊗≡Poly

record _◃_ (P Q : Type ℓ → Type ℓ) (y : Type ℓ) : Type ℓ where
  constructor composite
  field
    from-composite : P (Q y)

module _
  {P Q : Type ℓ → Type ℓ}
  {p1 : Type ℴ} {q1 : Type ℴ′} {p[_] : p1 → Type 𝒽} {q[_] : q1 → Type 𝒽′}
  ⦃ polyP@(poly p1 p[_] P-is-Poly) : Poly P ⦄
  ⦃ polyQ@(poly q1 q[_] Q-is-Poly) : Poly Q ⦄
  where
  open _◃_

  -- package curry and uncurry into an equivalence
  module _ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : X → Type ℓ'} {Z : (x : X) → Y x → Type ℓ''} where
    curry-≃ : ((p : Σ X Y) → Z (p .fst) (p .snd)) ≃ ((x : X) → (y : Y x) → Z x y)
    curry-≃ = Iso→Equiv (curry , (iso uncurry (λ _ → refl) (λ _ → refl)))

  -- given a type of the form ΣΠΣΠ, redistribute the inner ΠΣ to make the
  -- expression have the form ΣΣΠΠ so it can be turned into the normal form for
  -- polynomials
  inner-distrib
    : ∀ (y : Type ℓ)
    → (Σ[ a ∈ p1 ] (p[ a ] → Σ[ b ∈ q1 ] (q[ b ] → y)))
    ≃ (Σ[ (a , f) ∈ Σ[ a ∈ p1 ] (p[ a ] → q1) ]
      ((Σ[ b ∈ p[ a ] ] q[ f b ]) → y))
  inner-distrib y =
    (Σ[ a ∈ p1 ] (p[ a ] → Σ[ b ∈ q1 ] (q[ b ] → y)))
    ≃⟨ Σ-ap-snd (λ _ → Σ-Π-distrib) ⟩ -- distribute the inner ΠΣ to ΣΠ
    Σ[ a ∈ p1 ] (Σ[ f ∈ (p[ a ] → q1) ] ((b : p[ a ]) → q[ f b ] → y))
    ≃⟨ Σ-assoc ⟩                      -- reassociate the outer Σs
    (Σ[ (a , f) ∈ Σ[ a ∈ p1 ] (p[ a ] → q1) ] ((b : p[ a ]) → (c : q[ f b ]) → y))
    ≃˘⟨ Σ-ap-snd (λ _ → curry-≃) ⟩    -- uncurry the inner Πs
    (Σ[ (a , f) ∈ Σ[ a ∈ p1 ] (p[ a ] → q1) ] ((Σ[ b ∈ p[ a ] ] q[ f b ]) → y))
    ≃∎

  -- normalize a polynomial of polynomials into a single polynomial
  PolyPoly≃Poly
    : (y : Type ℓ)
    → SomePoly p1 p[_] (SomePoly q1 q[_] y)
    ≃ SomePoly (Σ[ a ∈ p1 ] (p[ a ] → q1))
               (λ (a , f) → Σ[ b ∈ p[ a ] ] q[ f b ]) y
  PolyPoly≃Poly y =
    SomePoly p1 p[_] (SomePoly q1 q[_] y)
    ≃⟨ inner-distrib y ⟩
    SomePoly (Σ[ a ∈ p1 ] (p[ a ] → q1))
             (λ (a , f) → Σ[ b ∈ p[ a ] ] q[ f b ]) y
    ≃∎

  P◃Qy≃PQy : (y : Type ℓ) → (P ◃ Q) y ≃ P (Q y)
  P◃Qy≃PQy y =
    Iso→Equiv ( from-composite , (iso composite (λ _ → refl) (λ _ → refl)))

  ◃≃Poly
    : (y : Type ℓ)
    → (P ◃ Q) y
    ≃ SomePoly (Σ[ a ∈ p1 ] (p[ a ] → q1))
               (λ (a , f) → Σ[ b ∈ p[ a ] ] q[ f b ]) y
  ◃≃Poly y =
    (P ◃ Q) y
    ≃⟨ P◃Qy≃PQy y ⟩
    P (Q y)
    ≃⟨ P≃Poly (Q y) ⟩
    SomePoly p1 p[_] (Q y)
    ≃⟨ Q≃Poly ⟩
    SomePoly p1 p[_] (SomePoly q1 q[_] y)
    ≃⟨ PolyPoly≃Poly y ⟩
    SomePoly (Σ[ a ∈ p1 ] (p[ a ] → q1))
             (λ (a , f) → Σ[ b ∈ p[ a ] ] q[ f b ]) y
    ≃∎
    where
      P≃Poly : (x : Type ℓ) → _
      P≃Poly x = path→equiv (happly P-is-Poly x)
      Q≃Poly : _
      Q≃Poly = path→equiv (ap (SomePoly p1 p[_]) (happly Q-is-Poly y))

  ◃≡Poly
    : P ◃ Q
    ≡ SomePoly (Σ[ a ∈ p1 ] (p[ a ] → q1))
               (λ (a , f) → Σ[ b ∈ p[ a ] ] q[ f b ])
  ◃≡Poly = funext (ua ∘ ◃≃Poly)

  instance
    ◃-Poly : Poly (P ◃ Q)
    ◃-Poly .is-Functor .₁ f = composite ∘ polyP .₁ (polyQ .₁ f) ∘ from-composite
    ◃-Poly .positions = Σ[ a ∈ p1 ] (p[ a ] → q1)
    ◃-Poly .directions (a , f) = Σ[ b ∈ p[ a ] ] q[ f b ]
    ◃-Poly .is-Poly = ◃≡Poly

record Comonad (P : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field
    ⦃ P-Functor ⦄ : Functor P
    ε : ∀ {A : Type ℓ} → P A → A
    δ : ∀ {A : Type ℓ} → P A → P (P A)

  open Functor P-Functor public

record LeftComodule {P : Type ℓ → Type ℓ} (𝒞 : Comonad P)
  (m : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  open Comonad 𝒞 renaming (ob-action to C₀ ; ₁ to C₁)
  field
    ⦃ M ⦄ : Functor m
    ƛ : ∀ {A : Type ℓ} → m A → C₀ (m A)
    ƛ-respects-ε : ∀ {x : m A} → ε (ƛ x) ≡ x
    ƛ-respects-δ : ∀ {x : m A} → C₁ ƛ (ƛ x) ≡ δ (ƛ x)

record RightComodule {P : Type ℓ → Type ℓ} (𝒞 : Comonad P)
  (m : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  open Comonad 𝒞 renaming (ob-action to C₀ ; ₁ to C₁)
  field
    ⦃ M ⦄ : Functor m
    ρ : ∀ {A : Type ℓ} → m A → m (C₀ A)
    ρ-respects-ε : ∀ {x : m A} → M .₁ ε (ρ x) ≡ x
    ρ-respects-δ : ∀ {x : m A} → ρ (ρ x) ≡ M .₁ δ (ρ x)

-- A bicomodule corresponds to a parametric right adjoint functor M : 𝒟 → 𝒞
record Bicomodule {P Q : Type ℓ → Type ℓ} (𝒞 : Comonad P) (𝒟 : Comonad Q)
  (m : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  private module C = Comonad 𝒞
  private module D = Comonad 𝒟
  field
    is-LCM : LeftComodule 𝒞 m
    is-RCM : RightComodule 𝒟 m

  open LeftComodule is-LCM public
  open RightComodule is-RCM public

  field
    coactions-commute : ∀ {x : m A} → C.₁ ρ (ƛ x) ≡ ƛ (ρ x)
