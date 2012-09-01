module dfa where

-- Deterministic Finite Automaton module.
--
-- Contains a proof that regular languages are closed under
-- both union and intersection.

open import Level
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product renaming (map to ×-map')
open import Data.Sum renaming (map to ⊎-map)
open import Data.List
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary hiding (Decidable; _⇒_)
open import Relation.Binary.PropositionalEquality

-- A bimap is a ternary predicate over A, B, and (A • B).
Bimap : ∀ {ℓ} → (_•_ : Set ℓ → Set ℓ → Set ℓ) → Set (suc ℓ)
Bimap _•_ = ∀ {a b c d} → (a → c) → (b → d) → a • b → c • d

-- η-expanded for consistency with ⊎-map
×-map : ∀ {ℓ} → Bimap {ℓ} _×_
×-map f g = ×-map' f g

module Subsets where

  -- A subset is an unary predicate
  Subset : ∀ {ℓ} → (a : Set ℓ) → Set (suc ℓ)
  Subset {ℓ} a = Pred a ℓ

  -- Decider for decidable subsets
  infix 4 _∈?_
  _∈?_ : ∀ {ℓ} {a : Set ℓ} → (x : a) → (P : Pred a ℓ) → {{dec : Decidable P}} → Dec (P x)
  (x ∈? P) {{dec}} = dec x

  -- Extensional equality of subsets
  _≈_ : ∀ {ℓ} {a : Set ℓ} → Subset a → Subset a → Set ℓ
  P ≈ Q = ∀ x → (P x → Q x) × (Q x → P x)

  ≈-isEquivalence : ∀ {ℓ} {a : Set ℓ} → IsEquivalence (_≈_ {ℓ} {a})
  ≈-isEquivalence = record
      { refl  = λ R → (id , id)
      ; sym   = λ R x → swap (R x)
      ; trans = λ R S x → (proj₁ (S x) ∘ proj₁ (R x)) , (proj₂ (R x) ∘ proj₂ (S x))
      }

open Subsets

-- Let us fix an alphabet for everything that follows.
module Automaton (Σ : Set) where
  
  -- A deterministic finite automaton
  record DFA : Set₁ where
    constructor dfa
    field
      Q  : Set
      q₀ : Q
      F  : Subset Q
      F? : Decidable F
      δ  : Σ → Q → Q

  -- Added for completeness
  record NFA : Set₁ where
    constructor nfa
    field
      Q  : Set
      q₀ : Subset Q
      F  : Subset Q
      F? : Decidable F
      δ  : Σ → Q → Subset Q

  -- A word is a (possibly empty) sequence of alphabet symbols
  Word : Set
  Word = List Σ

  -- A language is a set of words
  Language : Set₁
  Language = Subset Word

  module DFAProperties (A : DFA) where
    open DFA A

    -- Iteration of δ over the given word
    δ* : Word → Q → Q
    δ* []       = id
    δ* (x ∷ xs) = δ x ∘ δ* xs

    -- Iteration of δ from the starting state
    δ₀* : Word → Q
    δ₀* w = δ* w q₀

    -- The language accepted by the DFA
    language : Language
    language = F ∘ δ₀*

    -- This language is decidable
    decLanguage : Decidable language
    decLanguage = F? ∘ δ₀*

  open DFAProperties

  module DFAOps where

    -- Utilities for decidable sets
    _∨'_ : ∀ {ℓ} {P Q : Set ℓ} → Dec P → Dec Q → Dec (P ⊎ Q)
    yes p ∨' yes q = yes (inj₁ p)
    yes p ∨' no  _ = yes (inj₁ p)
    no  _ ∨' yes q = yes (inj₂ q)
    no ¬p ∨' no ¬q = no  [ ¬p , ¬q ]′

    _∧'_ : ∀ {ℓ} {P Q : Set ℓ} → Dec P → Dec Q → Dec (P × Q)
    yes p ∧' yes q = yes (p , q)
    yes _ ∧' no ¬q = no  (¬q ∘ proj₂)
    no ¬p ∧' yes _ = no  (¬p ∘ proj₁)
    no ¬p ∧' no  _ = no  (¬p ∘ proj₁)

    _→'_ : ∀ {ℓ} {P Q : Set ℓ} → Dec P → Dec Q → Dec (P → Q)
    yes p →' yes q = yes (λ _ → q)
    yes p →' no ¬q = no  (λ f → ¬q (f p))
    no ¬p →' yes q = yes (⊥-elim ∘ ¬p)
    no ¬p →' no ¬q = yes (⊥-elim ∘ ¬p)

    -- Parallel execution of two automata yields an automaton.
    parallel : (A B : DFA)
      → (_•_ : Set → Set → Set)
      → (_•?_ : ∀ {qA qB} → Dec (DFA.F A qA) → Dec (DFA.F B qB) → Dec (DFA.F A qA • DFA.F B qB))
      → DFA
    parallel A B _•_ _•?_ = record
        { Q  = Q A × Q B
        ; q₀ = q₀ A , q₀ B
        ; F  = uncurry λ qA qB → F A qA • F B qB
        ; F? = uncurry λ qA qB → F? A qA •? F? B qB
        ; δ  = λ x → ×-map (δ A x) (δ B x)
        }
      where
        open DFA

    -- Automaton disjunction
    infixr 6 _∪'_
    _∪'_ : DFA → DFA → DFA
    _∪'_ A B = parallel A B _⊎_ _∨'_

    -- Automaton conjunction
    infixr 7 _∩'_
    _∩'_ : DFA → DFA → DFA
    _∩'_ A B = parallel A B _×_ _∧'_

    -- A word decider for automata A and B and a combination predicate • is a function
    -- that takes deciders for A and B and produces a decider for (A • B).
    WordDecider : (A B : DFA) → (Set → Set → Set) → Set
    WordDecider A B _•_ = ∀ {qA qB} → Dec (DFA.F A qA) → Dec (DFA.F B qB) → Dec (DFA.F A qA • DFA.F B qB)

    -- Two automata executed in parallel give correct results.
    par-state : (A B : DFA)
      → (_•_ : Set → Set → Set)
      → (_•?_ : WordDecider A B _•_)
      → (w : Word)
      → δ₀* (parallel A B _•_ _•?_) w ≡ (δ₀* A w , δ₀* B w)
    par-state A B p p? [] = refl
    par-state A B p p? (x ∷ xs) rewrite par-state A B p p? xs = refl

    -- Lift a binary predicate on sets to operate on languages
    langop : (Set → Set → Set) → Language → Language → Language
    langop _•_ P Q x = (x ∈ P) • (x ∈ Q)

    -- The language function is distributive over (decidable) bimaps
    par-distr : (A B : DFA)
      → (_•_ : Set → Set → Set)
      → (_•?_ : WordDecider A B _•_)
      → (•-map : Bimap _•_)
      → let _•'_ = langop _•_ in
            language (parallel A B _•_ _•?_) ≈ (language A •' language B)
    par-distr A B _•_ _•?_ •-map = < P→Q , Q→P >
     where
       forth = cong proj₁ ∘ par-state A B _•_ _•?_
       back  = cong proj₂ ∘ par-state A B _•_ _•?_

       P→Q : (w : Word) → w ∈ language (parallel A B _•_ _•?_) → ((w ∈ language A) • (w ∈ language B))
       P→Q w = •-map (subst (DFA.F A) (forth w)) (subst (DFA.F B) (back w))

       Q→P : (w : Word) → ((w ∈ language A) • (w ∈ language B)) → w ∈ language (parallel A B _•_ _•?_)
       Q→P w = •-map (subst (DFA.F A) (sym (forth w))) (subst (DFA.F B) (sym (back w)))

    -- The language function is distributive over automaton disjunction
    ∪-lang-distr : ∀ A B → language (A ∪' B) ≈ (language A ∪ language B)
    ∪-lang-distr A B = par-distr A B _⊎_ _∨'_ ⊎-map

    -- The language function is distributive over automaton conjunction
    ∩-lang-distr : ∀ A B → language (A ∩' B) ≈ (language A ∩ language B)
    ∩-lang-distr A B = par-distr A B _×_ _∧'_ ×-map

  open DFAOps

  module Regularity where
  
    -- A regular language is a language that has an accepting automaton
    Regular : Subset Language
    Regular L = ∃ λ A →  L ≈ language A

    -- Regular languages are closed under (decidable) bimaps
    reg-preserve : ∀ (P Q : Language)
      → (rP : Regular P)
      → (rQ : Regular Q)
      → (_•_ : Set → Set → Set)
      → (_•?_ : WordDecider (proj₁ rP) (proj₁ rQ) _•_)
      → (•-map : Bimap _•_)
      → let _•'_ = langop _•_ in
            Regular (P •' Q)
    reg-preserve P Q (A , AdoesP) (B , BdoesQ) _•_ _•?_ •-map
        = parDFA , < PQ→AB , AB→PQ >
      where
        parDFA = parallel A B _•_ _•?_
        _•'_ = langop _•_

        PQ→AB : (w : Word) → w ∈ (P •' Q) → w ∈ language parDFA
        PQ→AB w = proj₂ (par-distr A B _•_ _•?_ •-map w) ∘ •-map (proj₁ (AdoesP w)) (proj₁ (BdoesQ w))

        AB→PQ : (w : Word) → w ∈ language parDFA → w ∈ (P •' Q)
        AB→PQ w = •-map (proj₂ (AdoesP w)) (proj₂ (BdoesQ w)) ∘ proj₁ (par-distr A B _•_ _•?_ •-map w)

    -- Regular languages are closed under union
    ∪-reg-preserve : ∀ (P Q : Language) → Regular P → Regular Q → Regular (P ∪ Q)
    ∪-reg-preserve P Q rP rQ = reg-preserve P Q rP rQ _⊎_ _∨'_ ⊎-map

    -- Regular languages are closed under intersection
    ∩-reg-preserve : ∀ (P Q : Language) → Regular P → Regular Q → Regular (P ∩ Q)
    ∩-reg-preserve P Q rP rQ = reg-preserve P Q rP rQ _×_ _∧'_ ×-map

{-  -- Because of the above reason, we cannot have a Bimap _⇒_.
    -- Probably a dumb encoding of the operator.

    _⇒_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
    P ⇒ Q = P → Q

    ⇒-map : Bimap _⇒_ → ⊥
    ⇒-map f = f (λ _ → tt) id id tt

    _⇒'_ : Language → Language → Language
    _⇒'_ = langop _⇒_

    →-reg-preserve : ∀ (P Q : Language) → Regular P → Regular Q → Regular (P ⇒' Q)
    →-reg-preserve P Q rP rQ = reg-preserve P Q rP rQ _⇒_ _→'_ {!!}
-}
