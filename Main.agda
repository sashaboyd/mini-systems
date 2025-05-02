module Main where

open import 1Lab.Prelude
open import Data.Sum using (_⊎_ ; inl ; inr)

private variable
  ℓ ℓ′ ℴ ℴ′ 𝒽 𝒽′ : Level
  A A′ B B′ X Y : Type ℴ
  P Q P′ Q′ : Type ℴ → Type ℴ

record Endofunctor (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  ob-action = F
  field ₁ : ∀ {A B : Type ℓ} → (A → B) → F A → F B

open Endofunctor

const : A → X → A
const a _ = a

Id : Endofunctor (id {A = Type ℓ})
Id .₁ f a = f a

κ : ∀ (A : Type ℓ) → Endofunctor (const A)
κ _ .₁ _ a = a

_○_ : {F G : Type ℓ → Type ℓ}
  → Endofunctor F → Endofunctor G → Endofunctor (F ∘ G)
(F ○ G) .₁ z = F .₁ (G .₁ z)

record _⇒_
  {F₀ G₀ : Type ℓ → Type ℓ}
  (F : Endofunctor F₀) (G : Endofunctor G₀)
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

PolyF : (p1 : Type ℓ) (p[_] : p1 → Type ℓ) → Endofunctor (SomePoly p1 p[_])
PolyF _ _ .₁ f p .fst = p .fst
PolyF _ _ .₁ f p .snd y = f (p .snd y)

instance
  PolyFunctor
    : {p1 : Type ℓ} {p[_] : p1 → Type ℓ}
    → Endofunctor (SomePoly {ℓ = ℓ} p1 p[_])
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
    ⦃ is-Functor ⦄ : Endofunctor F
    positions : Type ℓ
    directions : positions → Type ℓ
    is-Poly : F ≡ SomePoly positions directions

  open Endofunctor is-Functor public

open Poly

instance
  yₚ : Poly (id {A = Type ℓ})
  yₚ .is-Functor = Id
  yₚ {ℓ = ℓ} .positions = Lift ℓ ⊤
  yₚ {ℓ = ℓ} .directions _ = Lift ℓ ⊤
  yₚ .is-Poly =
    funext (λ x → Iso→Path ((λ y → lift tt , (λ tt → y))
           , (iso (λ (t , f) → f t)
             (λ _ → refl) (λ _ → refl))))

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

⨰-Endofunctor
  : {F G : Type ℓ → Type ℓ}
  → Endofunctor F → Endofunctor G → Endofunctor (F ⨰ G)
⨰-Endofunctor F G .₁ f (pair x y) =
  pair (F .₁ f x) (G .₁ f y)

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

fun≡→equiv : P ≡ Q → ∀ A → P A ≃ Q A
fun≡→equiv path = path→equiv ∘ happly path

module _
  {P Q : Type ℓ → Type ℓ}
  {p1 : Type ℴ} {q1 : Type ℴ′} {p[_] : p1 → Type 𝒽} {q[_] : q1 → Type 𝒽}
  ⦃ polyP@(poly p1 p[_] P-is-Poly) : Poly P ⦄
  ⦃ polyQ@(poly q1 q[_] Q-is-Poly) : Poly Q ⦄
  where
  open _⨰_

  private
    P≃Poly : ∀ (y : Type ℓ) → P y ≃ SomePoly p1 p[_] y
    P≃Poly y = path→equiv (happly P-is-Poly y)
    Q≃Poly : ∀ (y : Type ℓ) → Q y ≃ SomePoly q1 q[_] y
    Q≃Poly y = path→equiv (happly Q-is-Poly y)

  ⨰≃Poly
    : (y : Type ℓ)
    → (P ⨰ Q) y ≃ SomePoly (p1 × q1) (λ (a , b) → (p[ a ] ⊎ q[ b ])) y
  ⨰≃Poly y =
    (P ⨰ Q) y                               ≃⟨ ⨰-ap y (P≃Poly y) (Q≃Poly y) ⟩
    (SomePoly p1 p[_] ⨰ SomePoly q1 q[_]) y ≃⟨ ⨰-Poly-distrib p1 q1 p[_] q[_] y ⟩
    SomePoly (p1 × q1)
      (λ (a , b) → p[ a ] ⊎ q[ b ]) y       ≃∎

  ⨰≡Poly : (P ⨰ Q) ≡ SomePoly (p1 × q1) (λ (a , b) → (p[ a ] ⊎ q[ b ]))
  ⨰≡Poly = funext (ua ∘ ⨰≃Poly)

  instance
    ⨰-Poly : Poly (P ⨰ Q)
    ⨰-Poly .is-Functor =
      ⨰-Endofunctor (polyP .is-Functor)
                    (polyQ .is-Functor)
    ⨰-Poly .positions = p1 × q1
    ⨰-Poly .directions (a , b) = p[ a ] ⊎ q[ b ]
    ⨰-Poly .is-Poly = ⨰≡Poly

record _⊗_ (P Q : Type ℓ → Type ℓ)
  ⦃ p : Poly P ⦄ ⦃ q : Poly Q ⦄
  (y : Type ℓ)
  : Type ℓ where
  constructor mk-⊗
  private module p = Poly p
  private module q = Poly q
  field
    p-positions : p.positions
    q-positions : q.positions
    directions : p.directions p-positions × q.directions q-positions → y

yₚ⊗yₚ≃yₚ : ∀ (Y : Type ℓ) → (id ⊗ id) Y ≃ Y
yₚ⊗yₚ≃yₚ _ =
  Iso→Equiv
  ( (λ x → x ._⊗_.directions (lift tt , lift tt))
  , iso (λ x → mk-⊗ (lift tt) (lift tt) (λ tt → x))
        (λ _ → refl) (λ _ → refl))

⊗-map₂
  : ⦃ _ : Poly P ⦄ ⦃ _ : Poly P′ ⦄
    ⦃ _ : Poly Q ⦄ ⦃ _ : Poly Q′ ⦄
  → (∀ {X : Type ℓ} → P X → P′ X)
  → (∀ {X : Type ℓ} → Q X → Q′ X)
  → (P ⊗ Q) Y → (P′ ⊗ Q′) Y
⊗-map₂
  ⦃ polyP ⦄
  ⦃ polyP′ ⦄
  ⦃ polyQ ⦄
  ⦃ polyQ′ ⦄
  f g (mk-⊗ p1a q1b h) =
  mk-⊗ (newP .fst) (newQ .fst) (uncurry (flip (newQ .snd)))
  where
        fₚ : ∀ {X} → SomePoly _ _ X → SomePoly _ _ X
        fₚ px =
          transport (happly (polyP′ .is-Poly) _)
            (f (transport (happly (sym ( polyP .is-Poly)) _) px))
        gₚ : ∀ {X} → SomePoly _ _ X → SomePoly _ _ X
        gₚ qx =
          transport (happly (polyQ′ .is-Poly) _)
            (g (transport (happly (sym (polyQ .is-Poly)) _) qx))

        newP : _
        newP =
          fₚ (p1a , curry h)
        newQ : _
        newQ =
          gₚ (q1b , flip (newP .snd))

module _
  {P Q : Type ℓ → Type ℓ}
  {p1 : Type ℴ} {q1 : Type ℴ′}
  {p[_] : p1 → Type 𝒽} {q[_] : q1 → Type 𝒽′}
  ⦃ polyP@(poly p1 p[_] P-is-Poly) : Poly P ⦄
  ⦃ polyQ@(poly q1 q[_] Q-is-Poly) : Poly Q ⦄
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

  private
    P≃Poly : ∀ (y : Type ℓ) → P y ≃ SomePoly p1 p[_] y
    P≃Poly y = path→equiv (happly P-is-Poly y)
    Q≃Poly : ∀ (y : Type ℓ) → Q y ≃ SomePoly q1 q[_] y
    Q≃Poly y = path→equiv (happly Q-is-Poly y)

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
    ≃⟨ Q≃Poly-inner ⟩
    SomePoly p1 p[_] (SomePoly q1 q[_] y)
    ≃⟨ PolyPoly≃Poly y ⟩
    SomePoly (Σ[ a ∈ p1 ] (p[ a ] → q1))
             (λ (a , f) → Σ[ b ∈ p[ a ] ] q[ f b ]) y
    ≃∎
    where
      Q≃Poly-inner : _
      Q≃Poly-inner = path→equiv (ap (SomePoly p1 p[_]) (happly Q-is-Poly y))

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

module _
  {P Q P′ Q′ : Type ℓ → Type ℓ}
  {p1 : Type ℓ}
  {q1 : Type ℓ}
  {p′1 : Type ℓ}
  {q′1 : Type ℓ}
  {p[_] : p1 → Type ℓ}
  {p′[_] : p′1 → Type ℓ}
  {q[_] : q1 → Type ℓ}
  {q′[_] : q′1 → Type ℓ}
  {α β : Type ℓ}
  ⦃ polyP@(poly p1 p[_] P-is-Poly) : Poly P ⦄
  ⦃ polyP′@(poly p′1 p′[_] P′-is-Poly) : Poly P′ ⦄
  ⦃ polyQ@(poly q1 q[_] Q-is-Poly) : Poly Q ⦄
  ⦃ polyQ′@(poly q′1 q′[_] Q′-is-Poly) : Poly Q′ ⦄
  {Y : Type _}
  where
    -- also, ◃ has a duoidal relationship with ⊗
    -- sigh, more metavariable issues. I'm not sure I can resolve this without serious refactoring, since it seems like it can't figure out the values of the polynomial for the ◃ instance
    ⊗-◃-duoid : ((P ◃ P′) ⊗ (Q ◃ Q′)) Y → ((P ⊗ Q) ◃ (P′ ⊗ Q′)) Y
    ⊗-◃-duoid (mk-⊗ (p1x , f) (q1x , g) h) ._◃_.from-composite =
      mk-⊗ p1x q1x λ (x₁ , x₂) →
        mk-⊗ (f x₁) (g x₂) λ (u , v) →
          h ((x₁ , u) , (x₂ , v))

record Comonad (P : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field
    ⦃ ComonadFunctor ⦄ : Endofunctor P
    ε : ∀ {A : Type ℓ} → P A → A
    δ : ∀ {A : Type ℓ} → P A → P (P A)

  open Endofunctor ComonadFunctor public

record Category (𝔠 : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field
    ⦃ CatComonad ⦄ : Comonad 𝔠
    ⦃ CatPoly ⦄ : Poly 𝔠

  open Comonad CatComonad hiding (ob-action ; ₁) public
  open Poly CatPoly
    renaming ( positions to Ob
             ; directions to [_,-]
             )
    public

module _
  (𝔠 𝔡 : Type ℓ → Type ℓ)
  ⦃ 𝒞 : Category 𝔠 ⦄
  ⦃ 𝒟 : Category 𝔡 ⦄
  where
  private module 𝒞 = Category 𝒞
  private module 𝒟 = Category 𝒟
  open Category
  open Comonad
  open Poly
  open _⊗_

  ⊗-δ : (𝔠 ⊗ 𝔡) Y → (𝔠 ⊗ 𝔡) ((𝔠 ⊗ 𝔡) Y)
  ⊗-δ pq = _◃_.from-composite
    (⊗-◃-duoid (⊗-map₂ (composite ∘ 𝒞.δ) (composite ∘ 𝒟.δ) pq))

  ProductCategory : Category (𝔠 ⊗ 𝔡)
  ProductCategory .CatComonad .ComonadFunctor .₁ f (mk-⊗ p1 q1 dirs) =
    mk-⊗ p1 q1 (f ∘ dirs)
  ProductCategory .CatComonad .ε {A = A} pq =
    yₚ⊗yₚ≃yₚ A .fst (⊗-map₂ 𝒞.ε 𝒟.ε pq)
  ProductCategory .CatComonad .δ = ⊗-δ
  ProductCategory .CatPoly = ⊗-Poly

record LeftComodule {P : Type ℓ → Type ℓ} (𝒞 : Comonad P)
  (m : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  open Comonad 𝒞 renaming (ob-action to C₀ ; ₁ to C₁)
  field
    ⦃ M ⦄ : Endofunctor m
    ƛ : ∀ {A : Type ℓ} → m A → C₀ (m A)
    ƛ-respects-ε : ∀ {x : m A} → ε (ƛ x) ≡ x
    ƛ-respects-δ : ∀ {x : m A} → C₁ ƛ (ƛ x) ≡ δ (ƛ x)

record RightComodule {P : Type ℓ → Type ℓ} (𝒞 : Comonad P)
  (m : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  open Comonad 𝒞 renaming (ob-action to C₀ ; ₁ to C₁)
  field
    ⦃ M ⦄ : Endofunctor m
    ρ : ∀ {A : Type ℓ} → m A → m (C₀ A)
    ρ-respects-ε : ∀ {x : m A} → M .₁ ε (ρ x) ≡ x
    ρ-respects-δ : ∀ {x : m A} → ρ (ρ x) ≡ M .₁ δ (ρ x)

-- A bicomodule corresponds to a parametric right adjoint functor M : 𝒟 → 𝒞
record _⇾_ {P Q : Type ℓ → Type ℓ} (𝒞 : Comonad P) (𝒟 : Comonad Q)
  (m : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  private module C = Comonad 𝒞
  private module D = Comonad 𝒟
  field
    is-LCM : LeftComodule 𝒟 m
    is-RCM : RightComodule 𝒞 m

  open LeftComodule is-LCM public
  open RightComodule is-RCM public

  field
    coactions-commute : ∀ {x : m A} → D.₁ ρ (ƛ x) ≡ ƛ (ρ x)
