-- Parigot's λμ calculus formalization, along with a proof of Peirce.
-- Author: Matus Tejiscak <functor.sk@ziman>

module lambda-mu where

-- Some imports.
open import Data.String
open import Data.Product
open import Data.Unit
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

import Data.Empty

-- We name variables by strings.
Var : Set
Var = String

-- The set of types of λμ.
infixl 6 _⇒_
data Type : Set where
  LType : String → Type
  _⇒_ : Type → Type → Type
  ⊥ : Type

-- Mutually inductive set of terms/commands.
infixl 7 _$_
infixl 6 _:~_
mutual
        data Command : Set where
          _:~_ : Var → Term → Command

        data Term : Set where
          var : Var → Term
          Λ_∶_,_ : Var → Type → Term → Term
          μ_∶_,_ : Var → Type → Command → Term
          _$_ : Term → Term → Term

-- Type assignment judgments.
infix 5 _∷_
infix 5 _∷⊥⊥
data TypeAss : Set where
  _∷_ : Term → Type → TypeAss
  _∷⊥⊥ : Command → TypeAss

-- A variable-type assignment within a context.
infixl 5 _∶_
data CtxPair : Set where
  _∶_ : Var → Type → CtxPair

-- A context is a list of variable-type assignments.
infixl 4 _,_
data Context : Set where
  ∅ : Context
  _,_ : Context → CtxPair → Context

-- In lambda-mu, we have pairs of contexts.
infixl 3 _,,_
data Contexts : Set where
  _,,_ : Context → Context → Contexts

-- Occurrence of an assignment within a context.
infixl 3 _∈_
data _∈_ : CtxPair → Context → Set where
  enil : ∀ {Γ x σ} → x ∶ σ ∈ Γ , x ∶ σ
  esnoc : ∀ {Γ x σ y} → x ∶ σ ∈ Γ → x ∶ σ ∈ Γ , y

-- Injectivity of ⇒.
⇒-inj : ∀ {p q r s} → (p ⇒ q ≡ r ⇒ s) → (p ≡ r) × (q ≡ s)
⇒-inj refl = (refl , refl)

-- Injectivity of LType.
LType-inj : ∀ {p q} → (LType p ≡ LType q) → p ≡ q
LType-inj refl = refl

-- Decidable equality of λμ types.
decEqType : (σ : Type) → (τ : Type) → Dec (σ ≡ τ)
decEqType ⊥ ⊥ = yes refl
decEqType (p ⇒ q) (r ⇒ s) with decEqType p r | decEqType q s
... | yes pfL | yes pfR = yes (cong₂ _⇒_ pfL pfR)
... | no  pfL | yes pfR = no (pfL ∘ proj₁ ∘ ⇒-inj)
... | yes pfL | no  pfR = no (pfR ∘ proj₂ ∘ ⇒-inj)
... | no  pfL | no  pfR = no (pfL ∘ proj₁ ∘ ⇒-inj)
decEqType (LType σ) (LType τ) with Data.String._≟_ σ τ
... | yes pf = yes (cong LType pf)
... | no  pf = no (pf ∘ LType-inj)

-- booooooooring Agda cruft
decEqType ⊥ (LType _) = no (λ ())
decEqType (LType _) ⊥ = no (λ ())
decEqType (LType _) (_ ⇒ _) = no (λ ())
decEqType (_ ⇒ _) (LType _) = no (λ ())
decEqType (_ ⇒ _) ⊥ = no (λ ())
decEqType ⊥ (_ ⇒ _) = no (λ ())

-- If x:σ ∉ Γ and x≠y, then x:σ ∉ (Γ, y:τ)
neq-destr₁ : ∀ {x σ Γ y τ} → ¬ (x ∶ σ ∈ Γ) → ¬ (x ≡ y) → x ∶ σ ∈ Γ , y ∶ τ → Data.Empty.⊥
neq-destr₁ nl nr enil       = nr refl
neq-destr₁ nl nr (esnoc pf) = nl pf

-- If x:σ ∉ Γ and σ≠τ, then x:σ ∉ (Γ, y:τ)
neq-destr₂ : ∀ {x σ Γ y τ} → ¬ (x ∶ σ ∈ Γ) → ¬ (σ ≡ τ) → x ∶ σ ∈ Γ , y ∶ τ → Data.Empty.⊥
neq-destr₂ nl nr enil       = nr refl
neq-destr₂ nl nr (esnoc pf) = nl pf

-- Decide occurrence of a type assignment within a context.
edec : (Γ : Context) (x : Var) (σ : Type) → Dec (x ∶ σ ∈ Γ)
edec ∅ _ _ = no (λ ())
edec (Γ , y ∶ τ) x σ with Data.String._≟_ x y | decEqType σ τ | edec Γ x σ
... | yes pfL | yes pfR | _       = yes (subst₂ (λ y τ → x ∶ σ ∈ Γ , y ∶ τ) pfL pfR enil)
... | _       | _       | yes pfS = yes (esnoc pfS)
... | no  pfL | _       | no  pfS = no (neq-destr₁ pfS pfL)
... | _       | no  pfR | no  pfS = no (neq-destr₂ pfS pfR)

-- This is a type of an "existence token" of a proof of occurence.
lift : ∀ {a : Set} → Dec a → Set
lift (yes _) = ⊤
lift (no  _) = Data.Empty.⊥

-- Reconstruct proofs from its "existence token".
eprove : (Γ : Context) (x : Var) (σ : Type) → lift (edec Γ x σ) → x ∶ σ ∈ Γ
eprove ∅ _ _ ()
eprove (Γ , y ∶ τ) x σ p with Data.String._≟_ x y | decEqType σ τ | edec Γ x σ
... | yes pfL | yes pfR | _       = subst₂ (λ y τ → x ∶ σ ∈ Γ , y ∶ τ) pfL pfR enil
... | _       | _       | yes pfS = esnoc pfS 
eprove (Γ , y ∶ τ) x σ () | no  pfL | _      | no pfS
eprove (Γ , y ∶ τ) x σ () | yes _   | no pfR | no pfS

-- Typing judgments.
infixl 2 _⊢_
data _⊢_ : Contexts → TypeAss → Set where

  -- Assumption (needs a proof that x∶ρ ∈ Γ)
  Ass : ∀ {Γ Δ x ρ}
    → x ∶ ρ ∈ Γ
    → Γ ,, Δ ⊢ var x ∷ ρ

  -- Lambda
  Lam : ∀ {Γ Δ x ρ t σ}
    → Γ , x ∶ ρ ,, Δ ⊢ t ∷ σ
    → Γ ,, Δ ⊢ (Λ x ∶ ρ , t) ∷ ρ ⇒ σ

  -- Application
  App : ∀ {Γ Δ t ρ σ s}
    → Γ ,, Δ ⊢ t ∷ ρ ⇒ σ
    → Γ ,, Δ ⊢ s ∷ ρ
    → Γ ,, Δ ⊢ t $ s ∷ σ

  -- Activation
  Act : ∀ {Γ Δ α ρ c}
    → Γ ,, Δ , α ∶ ρ ⊢ c ∷⊥⊥
    → Γ ,, Δ ⊢ (μ α ∶ ρ , c) ∷ ρ

  -- Passivation (needs a proof that α∶ρ ∈ Δ)
  Pasv : ∀ {Γ Δ t ρ α}
    → α ∶ ρ ∈ Δ
    → Γ ,, Δ ⊢ t ∷ ρ
    → Γ ,, Δ ⊢ α :~ t ∷⊥⊥

-- Smart Assumption: infer the proof of occurence.
ass : ∀ {Γ Δ x ρ} → {pf : lift (edec Γ x ρ)} → Γ ,, Δ ⊢ var x ∷ ρ
ass {Γ} {Δ} {x} {ρ} {pf} = Ass (eprove Γ x ρ pf)

-- Smart Passivation: infer the proof of occurence.
-- Unfortunately we still need to provide the type ρ, which cannot be inferred.
pasv : ∀ {Γ Δ t α} → (ρ : Type) → {pf : lift (edec Δ α ρ)}
  → Γ ,, Δ ⊢ t ∷ ρ
  → Γ ,, Δ ⊢ α :~ t ∷⊥⊥
pasv {Γ} {Δ} {t} {α} ρ {pf} = Pasv (eprove Δ α ρ pf)

-- Peirce Theorem.
peirce : Type
peirce = ((ρ ⇒ σ) ⇒ ρ) ⇒ ρ
  where
    ρ = LType "ρ"
    σ = LType "σ"

-- Proof of Peirce in λμ.
peirceTerm : Term
peirceTerm = Λ t ∶ (ρ ⇒ σ) ⇒ ρ , (μ α ∶ ρ , (α :~ var t $ Λ x ∶ ρ , (μ β ∶ σ , (α :~ var x))))
  where
    t = "t"
    x = "x"
    α = "α"
    β = "β"
    ρ = LType "ρ"
    σ = LType "σ"

-- Proof that peirceTerm indeed proves peirce in λμ.
peirceCorrect : ∅ ,, ∅ ⊢ peirceTerm ∷ peirce
peirceCorrect = Lam (Act (pasv ρ (App ass (Lam (Act (pasv ρ ass))))))
  where
    ρ = LType "ρ"

