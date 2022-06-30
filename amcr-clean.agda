{-# OPTIONS --rewriting #-}
module amcr-clean where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

record UNIT : Set where constructor *
data VOID : Set where

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

_⟵_ : Env → Env → Set
Γ₂ ⟵ Γ₁ = ∀ {σ′} → Γ₁ ∋ σ′ → Γ₂ ⊢ σ′

sub₁ : Γ ⊢ σ′ → Γ ⟵ (Γ ▸ σ′)
sub₁ v top     = v
sub₁ v (pop i) = var i

sub : (Γ₂ ⟵ Γ₁) → (Γ₁ ▸+ Γ₃) ⊢ σ′ → (Γ₂ ▸+ Γ₃) ⊢ σ′
sub-cmd : (Γ₂ ⟵ Γ₁) → state (Γ₁ ▸+ Γ₃) → state (Γ₂ ▸+ Γ₃)

sub {Γ₃ = Γ₃} ρ (var i)    with case∋ {Γ₂ = Γ₃} i
... | inl j = ren (⊇+ˡ {Γ₂ = Γ₃}) (ρ j)
... | inr j = var (ren∋ ⊇+ʳ j)
sub ρ (lam a)    = lam (sub ρ a)
sub ρ (mu a)     = mu (sub-cmd ρ a)
sub ρ tt         = tt
sub ρ ff         = ff
sub ρ (inl a)    = inl (sub ρ a)
sub ρ (inr a)    = inr (sub ρ a)
sub ρ (pair a b) = pair (sub ρ a) (sub ρ b)
sub ρ (a ∙ b)    = sub ρ a ∙ sub ρ b
sub ρ (ite a b)  = ite (sub-cmd ρ a) (sub-cmd ρ b)
sub ρ (case a b) = case (sub-cmd ρ a) (sub-cmd ρ b)
sub ρ bot        = bot
sub ρ (fst a)    = fst (sub ρ a)
sub ρ (snd a)    = snd (sub ρ a)

sub-cmd ρ ⟨ v ∥ k ⟩ = ⟨ sub ρ v ∥ sub ρ k ⟩  

_,ₛ_ : Γ₂ ⟵ Γ₁ → Γ₂ ⊢ σ′ → Γ₂ ⟵ (Γ₁ ▸ σ′)
(ρ ,ₛ a) top     = a
(ρ ,ₛ a) (pop i) = ρ i

  {-
Goal: pole (sub-cmd (sub₁ k) (sub-cmd ρ a))
————————————————————————————————————————————————————————————
k  : Γ₂ ⊢ t⁻ σ
ρ  : Γ₂ ⟵ Γ
Γ₂ : Env   (not in scope)
a  : state (Γ ▸ t⁻ σ)


Goal: pole ⟨ sub (sub₁ v) (sub ρ a) ∥ k ⟩
————————————————————————————————————————————————————————————
k  : Γ₂ ⊢ᵏ τ
v  : Γ₂ ⊢ᵛ σ
ρ  : Γ₂ ⟵ Γ
Γ₂ : Env   (not in scope)
a  : Γ ▸ t⁺ σ ⊢ᵛ τ
-}


sub-ren : (ρ : Γ₂ ⟵ Γ₁) (x : Γ₁ ▸+ Γ₃ ⊢ σ′) →  {! x !} ≡ sub ρ x 
sub-ren ρ x = {!!}

{-
sub-sget : (ρ₁ : Γ₂ ⟵ Γ₁) (ρ₂ : Γ₃ ⟵ Γ₂) (i : (Γ₁ ▸+ Δ) ∋ σ′) → sext (λ j → sub ρ₂ (ρ₁ j)) i ≡ sub ρ₂ (sext ρ₁ i)
sub-sget {Δ = ∅} ρ₁ ρ₂ i = refl
sub-sget {Δ = Δ ▸ x} ρ₁ ρ₂ top = refl
sub-sget {Δ = ∅ ▸ x} ρ₁ ρ₂ (pop i) = {!!}
sub-sget {Δ = Δ ▸ x₁ ▸ x} ρ₁ ρ₂ (pop top) = refl
sub-sget {Δ = Δ ▸ x₁ ▸ x} ρ₁ ρ₂ (pop (pop i)) = {!!}
-}

sub-sub : (ρ₁ : Γ₂ ⟵ Γ₁) (ρ₂ : Γ₃ ⟵ Γ₂) (a : Γ₁ ▸+ Δ ⊢ σ′) →  sub (λ i → sub ρ₂ (ρ₁ i)) a ≡ sub ρ₂ (sub ρ₁ a)
sub-sub-cmd : (ρ₁ : Γ₂ ⟵ Γ₁) (ρ₂ : Γ₃ ⟵ Γ₂) (c : state (Γ₁ ▸+ Δ)) → sub-cmd (λ i → sub ρ₂ (ρ₁ i)) c ≡ sub-cmd ρ₂ (sub-cmd ρ₁ c)

sub-sub ρ₁ ρ₂ (var i) = {!!}
sub-sub ρ₁ ρ₂ (lam a) = cong lam (sub-sub ρ₁ ρ₂ a)
sub-sub ρ₁ ρ₂ (mu c) = cong mu (sub-sub-cmd ρ₁ ρ₂ c)
sub-sub ρ₁ ρ₂ tt = refl
sub-sub ρ₁ ρ₂ ff = refl
sub-sub ρ₁ ρ₂ (inl a) = cong inl (sub-sub ρ₁ ρ₂ a)
sub-sub ρ₁ ρ₂ (inr a) = cong inr (sub-sub ρ₁ ρ₂ a)
sub-sub ρ₁ ρ₂ (pair a b) = cong₂ pair (sub-sub ρ₁ ρ₂ a) (sub-sub ρ₁ ρ₂ b)
sub-sub ρ₁ ρ₂ (a ∙ b) = cong₂ _∙_ (sub-sub ρ₁ ρ₂ a) (sub-sub ρ₁ ρ₂ b)
sub-sub ρ₁ ρ₂ (ite a b) = cong₂ ite (sub-sub-cmd ρ₁ ρ₂ a) (sub-sub-cmd ρ₁ ρ₂ b)
sub-sub ρ₁ ρ₂ (case a b) = cong₂ case (sub-sub-cmd ρ₁ ρ₂ a) (sub-sub-cmd ρ₁ ρ₂ b)
sub-sub ρ₁ ρ₂ bot = refl
sub-sub ρ₁ ρ₂ (fst a) = cong fst (sub-sub ρ₁ ρ₂ a)
sub-sub ρ₁ ρ₂ (snd a) = cong snd (sub-sub ρ₁ ρ₂ a)

sub-sub-cmd ρ₁ ρ₂ ⟨ v ∥ k ⟩ = cong₂ ⟨_∥_⟩ (sub-sub ρ₁ ρ₂ v) (sub-sub ρ₁ ρ₂ k)

sub-sub₁ : (ρ : Γ₂ ⟵ Γ₁) (a : Γ₂ ⊢ σ′) (b : Γ₁ ▸ σ′ ⊢ τ′) → sub (ρ ,ₛ a) b ≡ sub {Γ₃ = ∅} (sub₁ a) (sub ρ b)
sub-sub₁-cmd : (ρ : Γ₂ ⟵ Γ₁) (a : Γ₂ ⊢ σ′) (b : state (Γ₁ ▸ σ′)) → sub-cmd (ρ ,ₛ a) b ≡ sub-cmd {Γ₃ = ∅} (sub₁ a) (sub-cmd ρ b)

sub-sub₁ ρ v x = {!sub₁ v!}

sub-sub₁-cmd ρ a ⟨ v ∥ k ⟩ = cong₂ ⟨_∥_⟩ (sub-sub₁ ρ a v) (sub-sub₁ ρ a k)

data _↦_ {Γ} : state Γ → state Γ → Set where
  ↦lam : ∀ {a : Γ ▸ t⁺ σ ⊢ᵛ τ} {v k}
         → ⟨ lam a    ∥ v ∙ k      ⟩ ↦ ⟨ sub (sub₁ v) a ∥ k ⟩
  ↦mu : ∀ {a : state (Γ ▸ t⁻ σ)} {k}
         → ⟨ mu a     ∥ k          ⟩ ↦ sub-cmd (sub₁ k) a
  ↦tt : ∀ {c₁ c₂ : state Γ}
         → ⟨ tt       ∥ ite c₁ c₂  ⟩ ↦ c₁
  ↦ff : ∀ {c₁ c₂ : state Γ}
         → ⟨ ff       ∥ ite c₁ c₂  ⟩ ↦ c₂
  ↦inl : ∀ {a} {c₁ : state (Γ ▸ t⁺ σ)} {c₂ : state (Γ ▸ t⁺ τ)}
         → ⟨ inl a    ∥ case c₁ c₂ ⟩ ↦ sub-cmd (sub₁ a) c₁
  ↦inr : ∀ {a} {c₁ : state (Γ ▸ t⁺ σ)} {c₂ : state (Γ ▸ t⁺ τ)}
         → ⟨ inr a    ∥ case c₁ c₂ ⟩ ↦ sub-cmd (sub₁ a) c₂
  ↦fst : ∀ {a : Γ ⊢ᵛ σ} {b : Γ ⊢ᵛ τ} {k}
         → ⟨ pair a b ∥ fst k      ⟩ ↦ ⟨ a ∥ k ⟩
  ↦snd : ∀ {a : Γ ⊢ᵛ σ} {b : Γ ⊢ᵛ τ} {k}
         → ⟨ pair a b ∥ snd k      ⟩ ↦ ⟨ b ∥ k ⟩

record ortho : Set₁ where
  field
    pole : state Γ → Set
    expand : ∀ {c₁ c₂ : state Γ} → c₁ ↦ c₂ → pole c₂ → pole c₁

  _⫫′_ : (Γ ⊢ σ′) → (Γ ⊢ flip σ′) → Set
  _⫫′_ {_} {t⁺ _} v k = pole ⟨ v ∥ k ⟩
  _⫫′_ {_} {t⁻ _} k v = pole ⟨ v ∥ k ⟩
  
  ⫫-flip : (σ′ : Ty′) {v : Γ ⊢ σ′} {k : Γ ⊢ flip σ′} → v ⫫′ k → k ⫫′ v
  ⫫-flip (t⁺ _) p = p
  ⫫-flip (t⁻ _) p = p


SUB : Ty′ → Set₁
SUB σ′ = ∀ {Γ} → Γ ⊢ σ′ → Set

_⊩_ : SUB σ′ → SUB σ′ → Set
P ⊩ Q = ∀ {Γ} {v : Γ ⊢ _} → P v → Q v

record biset (σ′ : Ty′) : Set₁ where
  constructor _,_
  field
    pos : SUB σ′
    neg : SUB (flip σ′)
open biset public

swap : biset σ′ → biset (flip σ′)
pos (swap P) = neg P
neg (swap P) = pos P

_⊑_ : biset σ′ → biset σ′ → Set
P ⊑ Q = (P .pos ⊩ Q .pos) × (P .neg ⊩ Q .neg)

-- subtyping order
_≼_ : biset σ′ → biset σ′ → Set
P ≼ Q = (P .pos ⊩ Q .pos) × (Q .neg ⊩ P .neg)

_⇔_ : biset σ′ → biset σ′ → Set
P ⇔ Q = (P ≼ Q) × (Q ≼ P)

module _ (O : ortho) where
  open ortho O

  _⫫ : SUB σ′ → SUB (flip σ′)
  (X ⫫) k = ∀ v → X v → v ⫫′ k

  _∗ : biset σ′ → biset σ′
  (X ∗) .pos = X .neg ⫫
  (X ∗) .neg = X .pos ⫫

  -- orthogonality ortho-candidate
  ortho-biset : biset σ′ → Set
  ortho-biset P = P ⇔ (P ∗)

  contra : {P Q : biset σ′} → (P ⊑ Q) → (Q ∗) ⊑ (P ∗)
  contra f .π₀ q k p = q k (f .π₁ p)
  contra f .π₁ q v p = q v (f .π₀ p)

  mono : {P Q : biset σ′} → (P ≼ Q) → (P ∗) ≼ (Q ∗)
  mono = contra

  ⫫⫫ᵢ : (P : biset σ′) → P ⊑ ((P ∗) ∗)
  ⫫⫫ᵢ {σ′} P .π₀ p k h = ⫫-flip σ′ (h _ p)
  ⫫⫫ᵢ {σ′} P .π₁ p v h = ⫫-flip (flip σ′) (h _ p)

  ⫫⫫⫫ₑ : (P : biset σ′) → (((P ∗) ∗) ∗) ⊑ (P ∗)
  ⫫⫫⫫ₑ P = contra (⫫⫫ᵢ P)

  ortho-sound : {P : biset σ′} (H : ortho-biset P) (v : Γ ⊢ σ′) (k : Γ ⊢ flip σ′) → P .pos v → P .neg k → v ⫫′ k
  ortho-sound {σ′} H _ k p q = ⫫-flip (flip σ′) (π₀ (π₀ H) p k q)

  completion : SUB σ′ → biset σ′
  completion P = (P , (P ⫫)) ∗

  completion⁺ : SUB (t⁺ σ) → biset (t⁺ σ)
  completion⁺ P = completion P

  completion⁻ : SUB (t⁻ σ) → biset (t⁺ σ)
  completion⁻ P = swap (completion P)

  completion-ortho : (P : SUB σ′) → ortho-biset (completion P)
  π₀ (π₀ (completion-ortho P)) = λ p → p
  π₁ (π₀ (completion-ortho P)) = π₁ (⫫⫫⫫ₑ (P , (P ⫫)))
  π₀ (π₁ (completion-ortho P)) = λ p → p
  π₁ (π₁ (completion-ortho P)) = π₁ (⫫⫫ᵢ (P , (P ⫫)))

  swap-ortho : {P : biset σ′} → ortho-biset P → ortho-biset (swap P)
  π₀ (π₀ (swap-ortho H)) = π₁ (π₁ H) 
  π₁ (π₀ (swap-ortho H)) = π₀ (π₁ H)
  π₀ (π₁ (swap-ortho H)) = π₁ (π₀ H)
  π₁ (π₁ (swap-ortho H)) = π₀ (π₀ H)

  ⟦_⟧T : (σ : Ty) → biset (t⁺ σ)
  ⟦ 𝔹      ⟧T = completion⁺ λ { tt → UNIT ; ff → UNIT ; _ → VOID }
  ⟦ ⊥      ⟧T = completion⁻ λ { bot → UNIT ; _ → VOID }
  ⟦ σ ⇒ τ ⟧T = completion⁻ λ { (v ∙ k) → ⟦ σ ⟧T .pos v × ⟦ τ ⟧T .neg k ; _ → VOID }
  ⟦ σ ⊕ τ  ⟧T = completion⁺ λ { (inl v) → ⟦ σ ⟧T .pos v ; (inr v) → ⟦ τ ⟧T .pos v ; _ → VOID }
  ⟦ σ & τ  ⟧T = completion⁻ λ { (fst k) → ⟦ σ ⟧T .neg k ; (snd k) → ⟦ τ ⟧T .neg k ; _ → VOID }

  ⟦_⟧E : Γ₂ ⟵ Γ₁ → Set
  ⟦_⟧T′ : (σ′ : Ty′) → biset σ′

  ⟦ ρ ⟧E = ∀ {σ′} (i : _ ∋ σ′) → ⟦ σ′ ⟧T′ .pos (ρ i)

  ⟦ t⁺ σ ⟧T′ = ⟦ σ ⟧T
  ⟦ t⁻ σ ⟧T′ = swap ⟦ σ ⟧T

  ⟦_⟧-ortho : (σ : Ty) → ortho-biset ⟦ σ ⟧T
  ⟦ 𝔹       ⟧-ortho = completion-ortho _
  ⟦ ⊥       ⟧-ortho = swap-ortho (completion-ortho _)
  ⟦ σ ⇒ σ₁ ⟧-ortho = swap-ortho (completion-ortho _)
  ⟦ σ ⊕ σ₁  ⟧-ortho = completion-ortho _
  ⟦ σ & σ₁  ⟧-ortho = swap-ortho (completion-ortho _)

  _⊨_ : ∀ {σ′} Γ → Γ ⊢ σ′ → Set
  _⊨c_ : ∀ Γ → state Γ → Set

  Γ ⊨ a          = ∀ {Γ₂} (ρ : Γ₂ ⟵ Γ) → ⟦ ρ ⟧E → ⟦ _ ⟧T′ .pos (sub ρ a)  
  Γ ⊨c ⟨ v ∥ k ⟩ = ∀ {Γ₂} (ρ : Γ₂ ⟵ Γ) → ⟦ ρ ⟧E → sub ρ v ⫫′ sub ρ k

  adequacy : (v : Γ ⊢ σ′) → Γ ⊨ v
  adequacy-cmd : (c : state Γ) → Γ ⊨c c

  adequacy (var i)    ρ x rewrite ren-id {x = ρ i} = x i
  adequacy (lam a)    ρ x (v ∙ k) h = expand ↦lam (π₀ (π₀ ⟦ _ ⟧-ortho) (subst (⟦ _ ⟧T .pos) (sub-sub₁ ρ v a) (adequacy a (ρ ,ₛ v) (λ { top → π₀ h ; (pop i) → x i }))) _ (π₁ h))
  adequacy (mu a)     ρ x = π₀ (π₁ ⟦ _ ⟧-ortho) λ k p → expand ↦mu (subst pole (sub-sub₁-cmd ρ k a) (adequacy-cmd a (ρ ,ₛ k) λ { top → p ; (pop i) → x i }))
  adequacy tt         ρ x k       h = h tt *
  adequacy ff         ρ x k       h = h ff *
  adequacy (inl a)    ρ x k       h = h (inl _) (adequacy a ρ x)
  adequacy (inr a)    ρ x k       h = h (inr _) (adequacy a ρ x) 
  adequacy (pair a b) ρ x (fst k) h = expand ↦fst (π₀ (π₀ ⟦ _ ⟧-ortho) (adequacy a ρ x) _ h)
  adequacy (pair a b) ρ x (snd k) h = expand ↦snd (π₀ (π₀ ⟦ _ ⟧-ortho) (adequacy b ρ x) _ h)
  adequacy (a ∙ b)    ρ x k       h = h (_ ∙ _) (adequacy a ρ x , adequacy b ρ x)
  adequacy (ite a b)  ρ x tt      h = expand ↦tt (adequacy-cmd a ρ x)
  adequacy (ite a b)  ρ x ff      h = expand ↦ff (adequacy-cmd b ρ x)
  adequacy (case a b) ρ x (inl c) h = expand ↦inl (subst pole (sub-sub₁-cmd ρ c a) (adequacy-cmd a (ρ ,ₛ c) λ { top → h ; (pop i) → x i}))
  adequacy (case a b) ρ x (inr c) h = expand ↦inr (subst pole (sub-sub₁-cmd ρ c b) (adequacy-cmd b (ρ ,ₛ c) λ { top → h ; (pop i) → x i}))
  adequacy bot        ρ x k       h = h bot *
  adequacy (fst a)    ρ x k       h = h (fst _) (adequacy a ρ x)
  adequacy (snd a)    ρ x k       h = h (snd _) (adequacy a ρ x)

  adequacy-cmd ⟨ v ∥ k ⟩ ρ x = π₀ (π₀ ⟦ _ ⟧-ortho) (adequacy v ρ x) _ (adequacy k ρ x)
