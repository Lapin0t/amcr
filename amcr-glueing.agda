{-# OPTIONS --rewriting #-}
module amcr-glueing where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

record UNIT : Set where constructor *
data VOID : Set where
data BOOL : Set where tt ff : BOOL
record SIGMA (A : Set) (B : A → Set) : Set where
  field
    proj₁ : A
    proj₂ : B proj₁
open SIGMA public

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
cong₂ f refl refl = refl

subst : {A : Set} (P : A → Set) {a₁ a₂ : A} → a₁ ≡ a₂ → P a₁ → P a₂ 
subst P refl p = p

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    π₀ : A
    π₁ : B
open _×_ public

infix 7 _⇒_
infixl 6 _▸_
infixl 5 _∙_ 
infix 5 _∋_ _⊇_
infix 4 _⊢_ _⊢ᵏ_ _⊢ᵛ_

data Ty : Set where
  𝔹 ⊥ : Ty
  _⇒_ _⊕_ _&_ : Ty → Ty → Ty

data Ty′ : Set where
  t⁺ t⁻ : Ty → Ty′

flip : Ty′ → Ty′
flip (t⁺ t) = t⁻ t
flip (t⁻ t) = t⁺ t

flip-flip : ∀ {σ′} → flip (flip σ′) ≡ σ′
flip-flip {t⁺ _} = refl
flip-flip {t⁻ _} = refl
{-# REWRITE flip-flip #-}

data Env : Set where
  ∅   : Env
  _▸_ : Env → Ty′ → Env

_▸+_ : Env → Env → Env
Γ ▸+ ∅       = Γ
Γ ▸+ (Δ ▸ σ) = (Γ ▸+ Δ) ▸ σ

private variable
  σ τ : Ty
  σ′ τ′ : Ty′
  Γ Δ Γ₁ Γ₂ Γ₃ : Env

-- well-type & well-scoped De-Bruijn indices
data _∋_ : Env → Ty′ → Set where
  top : (Γ ▸ σ′ ∋ σ′)
  pop : (Γ ∋ σ′) → (Γ ▸ τ′ ∋ σ′)

data _⊢_ : Env → Ty′ → Set
record state (Γ : Env) : Set

_⊢ᵛ_ : Env → Ty → Set
Γ ⊢ᵛ σ = Γ ⊢ t⁺ σ

_⊢ᵏ_ : Env → Ty → Set
Γ ⊢ᵏ σ = Γ ⊢ t⁻ σ

data _⊢_ where
  var   : (Γ ∋ σ′) → (Γ ⊢ σ′)

  -- values
  lam  : (Γ ▸ t⁺ σ ⊢ᵛ τ) → (Γ ⊢ᵛ (σ ⇒ τ))
  mu   : state (Γ ▸ t⁻ σ) → (Γ ⊢ᵛ σ)
  tt   : Γ ⊢ᵛ 𝔹
  ff   : Γ ⊢ᵛ 𝔹
  inl  : (Γ ⊢ᵛ σ) → (Γ ⊢ᵛ (σ ⊕ τ))
  inr  : (Γ ⊢ᵛ τ) → (Γ ⊢ᵛ (σ ⊕ τ))
  pair : (Γ ⊢ᵛ σ) → (Γ ⊢ᵛ τ) → (Γ ⊢ᵛ (σ & τ))

  -- continuations
  _∙_  : (Γ ⊢ᵛ σ) → (Γ ⊢ᵏ τ ) → (Γ ⊢ᵏ (σ ⇒ τ))
  ite  : state Γ → state Γ → (Γ ⊢ᵏ 𝔹)
  case : state (Γ ▸ t⁺ σ) → state (Γ ▸ t⁺ τ) → (Γ ⊢ᵏ (σ ⊕ τ))
  bot  : (Γ ⊢ᵏ ⊥)
  fst  : (Γ ⊢ᵏ σ) → (Γ ⊢ᵏ (σ & τ))
  snd  : (Γ ⊢ᵏ τ) → (Γ ⊢ᵏ (σ & τ))


record state Γ where
  inductive
  constructor ⟨_∥_⟩
  field
    {cur} : Ty
    foc : Γ ⊢ᵛ cur
    nxt : Γ ⊢ᵏ cur
open state public

DNE : Γ ⊢ᵛ (((σ ⇒ ⊥) ⇒ ⊥) ⇒ σ)
DNE = lam (mu ⟨ var (pop top) ∥ lam (mu ⟨ var (pop top) ∥ var (pop (pop top)) ⟩) ∙ bot ⟩)

data _⊇_ : Env → Env → Set where
  bot  : ∅ ⊇ ∅
  skip : (Γ ⊇ Δ) → (Γ ▸ σ′ ⊇ Δ)
  keep : Γ ⊇ Δ → (Γ ▸ σ′) ⊇ (Δ ▸ σ′)

⊇-refl : Γ ⊇ Γ
⊇-refl {∅}      = bot
⊇-refl {Γ ▸ _} = keep ⊇-refl

⊇-∅ : Γ ⊇ ∅
⊇-∅ {∅}    = bot
⊇-∅ {Γ ▸ x} = skip ⊇-∅

⊇-∘ : Γ₂ ⊇ Γ₁ → Γ₃ ⊇ Γ₂ → Γ₃ ⊇ Γ₁
⊇-∘ r        bot      = r
⊇-∘ r        (skip s) = skip (⊇-∘ r s)
⊇-∘ (skip r) (keep s) = skip (⊇-∘ r s)
⊇-∘ (keep r) (keep s) = keep (⊇-∘ r s)

⊇-idˡ : (r : Γ₂ ⊇ Γ₁) → ⊇-∘ ⊇-refl r ≡ r
⊇-idˡ bot      = refl
⊇-idˡ (skip r) = cong skip (⊇-idˡ r)
⊇-idˡ (keep r) = cong keep (⊇-idˡ r)

⊇-idʳ : (r : Γ₂ ⊇ Γ₁) → ⊇-∘ r ⊇-refl ≡ r
⊇-idʳ bot      = refl
⊇-idʳ (skip r) = cong skip (⊇-idʳ r)
⊇-idʳ (keep r) = cong keep (⊇-idʳ r)

⊇-keep : (Γ₂ ⊇ Γ₁) → (Γ₂ ▸+ Γ₃) ⊇ (Γ₁ ▸+ Γ₃)
⊇-keep {Γ₃ = ∅}     r = r
⊇-keep {Γ₃ = Γ₃ ▸ _} r = keep (⊇-keep r)

⊇+ˡ : Γ₁ ▸+ Γ₂ ⊇ Γ₁
⊇+ˡ {Γ₂ = ∅}       = ⊇-refl
⊇+ˡ {Γ₂ = Γ₂ ▸ _} = skip ⊇+ˡ

⊇+ʳ : Γ₁ ▸+ Γ₂ ⊇ Γ₂
⊇+ʳ {Γ₂ = ∅}       = ⊇-∅
⊇+ʳ {Γ₂ = Γ₂ ▸ _} = keep ⊇+ʳ

ren∋ : Γ₂ ⊇ Γ₁ → Γ₁ ∋ σ′ → Γ₂ ∋ σ′
ren∋ (skip r) i       = pop (ren∋ r i)
ren∋ (keep r) top     = top
ren∋ (keep r) (pop i) = pop (ren∋ r i)

ren∋-id : {x : Γ ∋ σ′} → ren∋ ⊇-refl x ≡ x
ren∋-id {_} {_} {top}   = refl
ren∋-id {_} {_} {pop x} = cong pop (ren∋-id {_} {_} {x})

ren∋-∘ : (r : Γ₂ ⊇ Γ₁) (s : Γ₃ ⊇ Γ₂) {x : Γ₁ ∋ σ′} → ren∋ s (ren∋ r x) ≡ ren∋ (⊇-∘ r s) x
ren∋-∘ bot      bot      {()}
ren∋-∘ r        (skip s) {i}     = cong pop (ren∋-∘ r s)
ren∋-∘ (skip r) (keep s) {i}     = cong pop (ren∋-∘ r s)
ren∋-∘ (keep r) (keep s) {top}   = refl
ren∋-∘ (keep r) (keep s) {pop i} = cong pop (ren∋-∘ r s)

case∋ : (Γ₁ ▸+ Γ₂) ∋ σ′ → (Γ₁ ∋ σ′) ⊎ (Γ₂ ∋ σ′)
case∋ {Γ₂ = ∅}       i = inl i
case∋ {Γ₂ = Γ₂ ▸ x} top     = inr top
case∋ {Γ₂ = Γ₂ ▸ x} (pop i) with case∋ i
... | inl j = inl j
... | inr j = inr (pop j)

case∋-inv : (Γ₁ ∋ σ′) ⊎ (Γ₂ ∋ σ′) → (Γ₁ ▸+ Γ₂) ∋ σ′
case∋-inv (inl j) = ren∋ ⊇+ˡ j
case∋-inv (inr j) = ren∋ ⊇+ʳ j

case∋-ren∋ : (i : (Γ₁ ▸+ Γ₂) ∋ σ′) → case∋-inv (case∋ {Γ₁} {Γ₂} i) ≡ i
case∋-ren∋ {Γ₂ = ∅} i = ren∋-id
case∋-ren∋ {Γ₂ = Γ₂ ▸ x} top = refl
case∋-ren∋ {Γ₂ = Γ₂ ▸ x} (pop i) with case∋ {Γ₂ = Γ₂} i in eq
... | inl j = cong pop (trans (sym (cong case∋-inv eq)) (case∋-ren∋ {Γ₂ = Γ₂} i))
... | inr j = cong pop (trans (sym (cong case∋-inv eq)) (case∋-ren∋ {Γ₂ = Γ₂} i))

ren : (Γ₂ ⊇ Γ₁) → Γ₁ ⊢ σ′ → Γ₂ ⊢ σ′
ren-cmd : (Γ₂ ⊇ Γ₁) → state Γ₁ → state Γ₂

ren r (var i)    = var (ren∋ (⊇-keep r) i)
ren r (lam a)    = lam (ren (keep r) a)
ren r (mu a)     = mu (ren-cmd (keep r) a)
ren r tt         = tt
ren r ff         = ff
ren r (inl a)    = inl (ren r a)
ren r (inr a)    = inr (ren r a)
ren r (pair a b) = pair (ren r a) (ren r b)
ren r (a ∙ b)    = ren r a ∙ ren r b
ren r (ite a b)  = ite (ren-cmd r a) (ren-cmd r b)
ren r (case a b) = case (ren-cmd (keep r) a) (ren-cmd (keep r) b)
ren r bot        = bot
ren r (fst a)    = fst (ren r a)
ren r (snd a)    = snd (ren r a)

ren-cmd r ⟨ v ∥ k ⟩ = ⟨ ren r v ∥ ren r k ⟩

ren-id : {x : Γ ⊢ σ′} → ren ⊇-refl x ≡ x
ren-cmd-id : {x : state Γ} → ren-cmd ⊇-refl x ≡ x

ren-id {x = var i} = cong var ren∋-id
ren-id {x = lam a} = cong lam ren-id
ren-id {x = mu a} = cong mu ren-cmd-id
ren-id {x = tt} = refl
ren-id {x = ff} = refl
ren-id {x = inl a} = cong inl ren-id
ren-id {x = inr a} = cong inr ren-id
ren-id {x = pair a b} = cong₂ pair ren-id ren-id
ren-id {x = a ∙ b} = cong₂ _∙_ ren-id ren-id
ren-id {x = ite a b} = cong₂ ite ren-cmd-id ren-cmd-id
ren-id {x = case a b} = cong₂ case ren-cmd-id ren-cmd-id
ren-id {x = bot} = refl
ren-id {x = fst a} = cong fst ren-id
ren-id {x = snd a} = cong snd ren-id
ren-cmd-id {x = ⟨ foc ∥ nxt ⟩} = cong₂ ⟨_∥_⟩ ren-id ren-id

ren-∘ : (r : Γ₂ ⊇ Γ₁) (s : Γ₃ ⊇ Γ₂) (x : Γ₁ ⊢ σ′) → ren (⊇-∘ r s) x ≡ ren s (ren r x)
ren-cmd-∘ : (r : Γ₂ ⊇ Γ₁) (s : Γ₃ ⊇ Γ₂) (x : state Γ₁) → ren-cmd (⊇-∘ r s) x ≡ ren-cmd s (ren-cmd r x)

ren-∘ r s (var i) = cong var (sym (ren∋-∘ r s))
ren-∘ r s (lam a) = cong lam (ren-∘ (keep r) (keep s) a)
ren-∘ r s (mu a) = cong mu (ren-cmd-∘ (keep r) (keep s) a)
ren-∘ r s tt = refl
ren-∘ r s ff = refl
ren-∘ r s (inl a) = cong inl (ren-∘ r s a)
ren-∘ r s (inr a) = cong inr (ren-∘ r s a)
ren-∘ r s (pair a b) = cong₂ pair (ren-∘ r s a) (ren-∘ r s b)
ren-∘ r s (a ∙ b) = cong₂ _∙_ (ren-∘ r s a) (ren-∘ r s b)
ren-∘ r s (ite a b) = cong₂ ite (ren-cmd-∘ r s a) (ren-cmd-∘ r s b)
ren-∘ r s (case a b) = cong₂ case (ren-cmd-∘ (keep r) (keep s) a) (ren-cmd-∘ (keep r) (keep s) b)
ren-∘ r s bot = refl
ren-∘ r s (fst a) = cong fst (ren-∘ r s a)
ren-∘ r s (snd a) = cong snd (ren-∘ r s a)

ren-cmd-∘ r s ⟨ v ∥ k ⟩ = cong₂ ⟨_∥_⟩ (ren-∘ r s v) (ren-∘ r s k)

∀[_] : (Env → Set) → Set
∀[ P ] = ∀ {Γ} → P Γ 

{-
_⊢ᵢ_ : (Env → Set) → (Env → Set) → (Env → Set)
(P ⊢ᵢ Q) Γ = P Γ → Q Γ
-}

record Sem₁ : Set₁ where
  field
    fam : Env → Set
    renᶠ : Γ₂ ⊇ Γ₁ → fam Γ₁ → fam Γ₂
open Sem₁ public

_⊢₁_ : Sem₁ → Sem₁ → (Env → Set)
(P ⊢₁ Q) Γ = fam P Γ → fam Q Γ

infix 4 _⊆₁_
_⊆₁_ : Sem₁ → Sem₁ → Set
P ⊆₁ Q = ∀[ P ⊢₁ Q ]

□_ : (Env → Set) → Sem₁
fam (□ P) Γ₁ = ∀ {Γ₂} → Γ₂ ⊇ Γ₁ → P Γ₂ 
renᶠ (□ P) r f r′ = f (⊇-∘ r r′)

_×₁_ : Sem₁ → Sem₁ → Sem₁
fam (P ×₁ Q) Γ = fam P Γ × fam Q Γ
renᶠ (P ×₁ Q) r p = renᶠ P r (π₀ p) , renᶠ Q r (π₁ p)

_+₁_ : Sem₁ → Sem₁ → Sem₁
fam (P +₁ Q) Γ = fam P Γ ⊎ fam Q Γ
renᶠ (P +₁ Q) r (inl p) = inl (renᶠ P r p)
renᶠ (P +₁ Q) r (inr p) = inr (renᶠ Q r p)

κ : Set → Sem₁
fam (κ A) _ = A
renᶠ (κ A) r a = a

record Sem₂ : Set₁ where
  field
    pos : Sem₁
    neg : Sem₁
open Sem₂ public

infix 4 _⊆₂_
_⊆₂_ : Sem₂ → Sem₂ → Set
P ⊆₂ Q = (pos P ⊆₁ pos Q) × (neg P ⊆₁ neg Q)

_≼₂_ : Sem₂ → Sem₂ → Set
P ≼₂ Q = (pos P ⊆₁ pos Q) × (neg Q ⊆₁ neg P)

swap : Sem₂ → Sem₂
pos (swap P) = neg P
neg (swap P) = pos P

module adequacy (paul : Sem₁) where

  infixl 8 _⫫
  _⫫ : Sem₁ → Sem₁
  fam (P ⫫) Γ₁ = ∀ {Γ₂} → Γ₂ ⊇ Γ₁ → fam P Γ₂ → fam paul Γ₂
  renᶠ (P ⫫) r f r′ = f (⊇-∘ r r′)

  contra : ∀ P Q → P ⊆₁ Q → Q ⫫ ⊆₁ P ⫫
  contra P Q f q r p = q r (f p)

  ⫫⫫ᵢ : ∀ P → P ⊆₁ P ⫫ ⫫
  ⫫⫫ᵢ P p r k = k ⊇-refl (renᶠ P r p)

  ⫫⫫⫫ₑ : ∀ P → P ⫫ ⫫ ⫫ ⊆₁ P ⫫
  ⫫⫫⫫ₑ P = contra P (P ⫫ ⫫) (⫫⫫ᵢ P)

  Sound : Sem₂ → Set
  Sound S = (pos S ×₁ neg S) ⊆₁ paul

  Complete : Sem₂ → Set
  Complete S = (neg S ⫫ ⊆₁ pos S) × (pos S ⫫ ⊆₁ neg S)

  swap-sound : ∀ P → Sound P → Sound (swap P)
  swap-sound P H (a , b) = H (b , a)

  swap-complete : ∀ P → Complete P → Complete (swap P)
  π₀ (swap-complete P H) = π₁ H
  π₁ (swap-complete P H) = π₀ H

  close : (P : Sem₁) → Sem₂
  pos (close P) = (P ⫫) ⫫
  neg (close P) = P ⫫

  close-sound : ∀ P → Sound (close P)
  close-sound P (k , p) = k ⊇-refl p

  close-complete : ∀ P → Complete (close P)
  close-complete P = (λ k → k) , ⫫⫫⫫ₑ P

  _⟦⇒⟧_ : Sem₂ → Sem₂ → Sem₂
  S ⟦⇒⟧ T = swap (close (pos S ×₁ neg T))

  _⟦&⟧_ : Sem₂ → Sem₂ → Sem₂
  S ⟦&⟧ T = swap (close (neg S +₁ neg T))

  _⟦⊕⟧_ : Sem₂ → Sem₂ → Sem₂
  S ⟦⊕⟧ T = close (pos S +₁ pos T)

  ⟦𝔹⟧ : Sem₂
  ⟦𝔹⟧ = close (κ BOOL)

  ⟦⊥⟧ : Sem₂
  ⟦⊥⟧ = swap (close (κ UNIT))

  ⟦_⟧T : Ty → Sem₂
  ⟦ 𝔹      ⟧T = ⟦𝔹⟧
  ⟦ ⊥      ⟧T = ⟦⊥⟧
  ⟦ σ ⇒ τ ⟧T = ⟦ σ ⟧T ⟦⇒⟧ ⟦ τ ⟧T
  ⟦ σ ⊕ τ  ⟧T = ⟦ σ ⟧T ⟦⊕⟧ ⟦ τ ⟧T
  ⟦ σ & τ  ⟧T = ⟦ σ ⟧T ⟦&⟧ ⟦ τ ⟧T

  ⟦_⟧T-sound : ∀ σ → Sound ⟦ σ ⟧T
  ⟦ 𝔹      ⟧T-sound = close-sound (κ BOOL)
  ⟦ ⊥      ⟧T-sound = swap-sound (close _) (close-sound (κ UNIT))
  ⟦ σ ⇒ τ ⟧T-sound = swap-sound (close (pos ⟦ σ ⟧T ×₁ neg ⟦ τ ⟧T)) (close-sound (pos ⟦ σ ⟧T ×₁ neg ⟦ τ ⟧T))
  ⟦ σ ⊕ τ  ⟧T-sound = close-sound (pos ⟦ σ ⟧T +₁ pos ⟦ τ ⟧T)
  ⟦ σ & τ  ⟧T-sound = swap-sound (close (neg ⟦ σ ⟧T +₁ neg ⟦ τ ⟧T)) (close-sound (neg ⟦ σ ⟧T +₁ neg ⟦ τ ⟧T))

  ⟦_⟧T-complete : ∀ σ → Complete ⟦ σ ⟧T
  ⟦ 𝔹      ⟧T-complete = close-complete (κ BOOL)
  ⟦ ⊥      ⟧T-complete = swap-complete (close _) (close-complete (κ UNIT))
  ⟦ σ ⇒ τ ⟧T-complete = swap-complete (close (pos ⟦ σ ⟧T ×₁ neg ⟦ τ ⟧T)) (close-complete (pos ⟦ σ ⟧T ×₁ neg ⟦ τ ⟧T))
  ⟦ σ ⊕ τ  ⟧T-complete = close-complete (pos ⟦ σ ⟧T +₁ pos ⟦ τ ⟧T)
  ⟦ σ & τ  ⟧T-complete = swap-complete (close (neg ⟦ σ ⟧T +₁ neg ⟦ τ ⟧T)) (close-complete (neg ⟦ σ ⟧T +₁ neg ⟦ τ ⟧T))

  ⟦_⟧T′ : Ty′ → Sem₁
  ⟦ t⁺ σ ⟧T′ = pos ⟦ σ ⟧T
  ⟦ t⁻ σ ⟧T′ = neg ⟦ σ ⟧T

  ⟦_⟧E : Env → Sem₁
  ⟦ ∅       ⟧E = κ UNIT
  ⟦ Γ ▸ σ′ ⟧E = ⟦ Γ ⟧E ×₁ ⟦ σ′ ⟧T′
  
  ⟦∋⟧ : Γ ∋ σ′ → ⟦ Γ ⟧E ⊆₁ ⟦ σ′ ⟧T′
  ⟦∋⟧ top     p = π₁ p
  ⟦∋⟧ (pop i) p = ⟦∋⟧ i (π₀ p)
  
  _⊩_ : Env → Ty′ → Set
  Γ ⊩ σ′ = ⟦ Γ ⟧E ⊆₁ ⟦ σ′ ⟧T′
  
  _⊩c : Env → Set
  Γ ⊩c = ⟦ Γ ⟧E ⊆₁ paul
  
  adequacy : Γ ⊢ σ′ → Γ ⊩ σ′
  adequacy-cmd : state Γ → Γ ⊩c

  adequacy {Γ} {σ′}          (var i)                = ⟦∋⟧ i
  adequacy {Γ} {t⁺ (σ ⇒ τ)} (lam a)    e r (v , k) = ⟦ τ ⟧T-sound (adequacy a (renᶠ ⟦ Γ ⟧E r e , v) , k)
  adequacy {Γ} {t⁺ σ}        (mu a)     e           = π₀ ⟦ σ ⟧T-complete (λ r k → adequacy-cmd a (renᶠ ⟦ Γ ⟧E r e , k))
  adequacy {Γ} {t⁺ 𝔹}        tt         e r k       = k ⊇-refl tt
  adequacy {Γ} {t⁺ 𝔹}        ff         e r k       = k ⊇-refl ff
  adequacy {Γ} {t⁺ (σ ⊕ τ)}  (inl a)    e r k       = k ⊇-refl (inl (adequacy a (renᶠ ⟦ Γ ⟧E r e)))
  adequacy {Γ} {t⁺ (σ ⊕ τ)}  (inr a)    e r k       = k ⊇-refl (inr (adequacy a (renᶠ ⟦ Γ ⟧E r e)))
  adequacy {Γ} {t⁺ (σ & τ)}  (pair a b) e r (inl k) = ⟦ σ ⟧T-sound (adequacy a (renᶠ ⟦ Γ ⟧E r e) , k)
  adequacy {Γ} {t⁺ (σ & τ)}  (pair a b) e r (inr k) = ⟦ τ ⟧T-sound (adequacy b (renᶠ ⟦ Γ ⟧E r e) , k)
  adequacy {Γ} {t⁻ (σ ⇒ τ)} (a ∙ b)    e r k       = k ⊇-refl (adequacy a (renᶠ ⟦ Γ ⟧E r e) , adequacy b (renᶠ ⟦ Γ ⟧E r e))
  adequacy {Γ} {t⁻ 𝔹}        (ite a b)  e r tt      = adequacy-cmd a (renᶠ ⟦ Γ ⟧E r e)
  adequacy {Γ} {t⁻ 𝔹}        (ite a b)  e r ff      = adequacy-cmd b (renᶠ ⟦ Γ ⟧E r e)
  adequacy {Γ} {t⁻ (σ ⊕ τ)}  (case a b) e r (inl k) = adequacy-cmd a (renᶠ ⟦ Γ ⟧E r e , k)
  adequacy {Γ} {t⁻ (σ ⊕ τ)}  (case a b) e r (inr k) = adequacy-cmd b (renᶠ ⟦ Γ ⟧E r e , k)
  adequacy {Γ} {t⁻ ⊥}        bot        e r k       = k ⊇-refl *
  adequacy {Γ} {t⁻ (σ & τ)}  (fst a)    e r k       = k ⊇-refl (inl (adequacy a (renᶠ ⟦ Γ ⟧E r e)))
  adequacy {Γ} {t⁻ (σ & τ)}  (snd a)    e r k       = k ⊇-refl (inr (adequacy a (renᶠ ⟦ Γ ⟧E r e)))

  adequacy-cmd c e = ⟦ cur c ⟧T-sound (adequacy (foc c) e , adequacy (nxt c) e)
