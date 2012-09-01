module mutate where

--------------------------------------------------------------------------------
-- Functional specification of mutable state à la Swierstra (2009)
--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Function
open import Data.Nat
open import Data.Nat.Properties as NatProp
open import Data.List
open import Data.List.Properties
open import Algebra.Structures
open import Category.Applicative.Indexed
open import Category.Monad
open import Category.Monad.Identity
open import Category.Monad.Indexed
open import Category.Monad.State
open import Relation.Nullary.Core
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality as PE

-- A decidable equality on the given set.
DecEq : Set → Set
DecEq U = Decidable {_} {_} {_} {U} {U} _≡_

-- Specification of mutable reference semantics.
module RefSpec (U : Set) (el : U → Set) (decEqU : DecEq U) where

    -- The shape of a heap.
    Shape : Set
    Shape = List U

    -- Shape-indexed heap, just a linear list of values.
    data Heap : Shape → Set where
      hnil  : Heap []
      hcons : ∀ {u s} → el u → Heap s → Heap (u ∷ s)  

    -- A reference into a heap of a specific shape.
    data Ref (u : U) : Shape → Set where
      rtop : ∀ {s} → Ref u (u ∷ s)
      rpop : ∀ {s v} → Ref u s → Ref u (v ∷ s)
    
    -- The representation of state/ref-mutating actions.
    data IOR (a : Set) : Shape → Shape → Set where
      Return : ∀ {s} → a → IOR a s s
      Read : ∀ {u s t} → Ref u s → (el u → IOR a s t) → IOR a s t
      Write : ∀ {u s t} → Ref u s → el u → IOR a s t → IOR a s t
      New : ∀ {u s t} → el u → (Ref u (u ∷ s) → IOR a (u ∷ s) t) → IOR a s t
    
    -- IOR is an indexed monad.
    MonadIOR : Set₁
    MonadIOR = RawIMonad (λ s t a → IOR a s t)

    MonadIOR' : MonadIOR
    MonadIOR' = record { return = Return ; _>>=_ = _>>=_ }
      where
        _>>=_ : ∀ {s t u a b} → IOR a s t → (a → IOR b t u) → IOR b s u
        Return a     >>= f = f a
        Read   r   g >>= f = Read r (λ v → g v >>= f)
        Write  r x g >>= f = Write r x (g >>= f)
        New      x g >>= f = New x (λ r → g r >>= f) 

    -- Smart constructor: new reference.
    newRef : ∀ {s u} → el u → IOR (Ref u (u ∷ s)) s (u ∷ s)
    newRef x = New x Return

    -- Dumb (shape-unaware) constructor: read a reference.
    readRef' : ∀ {s u} → Ref u s → IOR (el u) s s
    readRef' r = Read r Return

    -- Dumb (shape-unaware) constructor: write to a reference.
    writeRef' : ∀ {s u} → el u → Ref u s → IOR ⊤ s s
    writeRef' x r = Write r x (Return tt)

    ---------------------------------------------------------------------------- 
    -- In the following, we implement automatic weakening of references to be
    -- able to create smart read/write constructors.
    ----------------------------------------------------------------------------
 
    -- (Suffix s t) iff `s' is a suffix of `t'.
    data Suffix : Shape → Shape → Set where
      snil : ∀ {s} → Suffix s s
      scons : ∀ {s t u} → Suffix s t → Suffix s (u ∷ t)

    -- Given a proof that `s' is a suffix of `t', we can weaken the reference.
    weaken : ∀ {s t u} → Suffix s t → Ref u s → Ref u t
    weaken snil r = r
    weaken (scons pf) r = rpop (weaken pf r)

    -- Decidable equality of heap shapes.
    decEqShape : DecEq Shape
    decEqShape []       []       = yes refl
    decEqShape (x ∷ xs) []       = no (λ ())
    decEqShape []       (y ∷ ys) = no (λ ())
    decEqShape (x ∷ xs) (y ∷ ys) with decEqU x y | decEqShape xs ys
    ... | yes pfU | yes pfS = yes (cong₂ _∷_ pfU pfS)
    ... | yes pfU | no  pfS = no (pfS ∘ proj₂ ∘ ∷-injective)
    ... | no  pfU | yes pfS = no (pfU ∘ proj₁ ∘ ∷-injective)
    ... | no  pfU | no  pfS = no (pfU ∘ proj₁ ∘ ∷-injective)

    -- A function deciding the predicate `Suffix'.
    _≼_ : Shape → Shape → Bool
    []       ≼ _  = true
    (_ ∷ _ ) ≼ [] = false
    (x ∷ xs) ≼ (y ∷ ys) with decEqShape (x ∷ xs) (y ∷ ys)
    ... | yes pf = true
    ... | no  pf = (x ∷ xs) ≼ ys

    -- For cool automation, we want to map bools to the correspoding sets.
    lift : Bool → Set
    lift true  = ⊤
    lift false = ⊥

    -- Suffix index-weakening lemma.
    bump : {s t : Shape} → s ≡ t → Suffix s s → Suffix s t
    bump refl x = x

    -- For given shapes `s' and `t', generate the suffix proof.
    sufProof : (s t : Shape) → lift (s ≼ t) → Suffix s t
    sufProof []       []       tt = snil
    sufProof (x ∷ xs) []       ()
    sufProof []       (y ∷ ys) tt = scons (sufProof [] ys tt)
    sufProof (x ∷ xs) (y ∷ ys) p with decEqShape (x ∷ xs) (y ∷ ys)
    ... | yes pf = bump pf snil
    ... | no  pf = scons (sufProof (x ∷ xs) ys p)

    -- Note that the `lift (s ≼ t)' argument can be left implicit
    -- and will be inferred by Agda (since it is either ⊤ or ⊥).
    --
    -- Because it is plugged into `sufProof', this way we get automatic
    -- *proof inference*, yay.

    -- Finally, the smart reading constructor.
    readRef : ∀ {s t u} → {p : lift (s ≼ t)} → Ref u s → IOR (el u) t t
    readRef {s} {t} {u} {p} r = Read (weaken (sufProof s t p) r) Return

    -- Smart writing constructor.
    writeRef : ∀ {s t u} → {p : lift (s ≼ t)} → el u → Ref u s → IOR ⊤ t t
    writeRef {s} {t} {u} {p} x r = Write (weaken (sufProof s t p) r) x (Return tt)

    ---------------------------------------------------------------------------- 
    -- Interpretation of IOR as indexed State monad computation.
    ---------------------------------------------------------------------------- 
    
    open RawIMonadState (StateTIMonadState Heap IdentityMonad)
    
    -- Create a new reference on the top of the heap.
    allocate : ∀ {s u} → el u → IStateT Heap Identity s (u ∷ s) (Ref u (u ∷ s))
    allocate x = modify (hcons x) >> return rtop

    -- Descend into the heap and get the required value.
    readHeap : ∀ {s u} → Ref u s → Heap s → el u
    readHeap rtop     (hcons x _) = x
    readHeap (rpop r) (hcons _ h) = readHeap r h

    -- Descend into the heap and overwrite the referenced value.
    writeHeap : ∀ {s u} → el u → Ref u s → Heap s → Heap s
    writeHeap x rtop     (hcons _ h) = hcons x h
    writeHeap x (rpop r) (hcons y h) = hcons y (writeHeap x r h)

    -- Interpretation of IOR as State computation.
    interpret : ∀ {a s t} → IOR a s t → IStateT Heap Identity s t a
    interpret (Return  x  ) = return x
    interpret (New     x f) = allocate x >>= λ r → interpret (f r) 
    interpret (Read  r   f) = get >>= λ h → interpret (f (readHeap r h))
    interpret (Write r x f) = modify (writeHeap x r) >> interpret f

--------------------------------------------------------------------------------
-- Some testcases and usage of the specification defined above.
--------------------------------------------------------------------------------

-- The universe of types.
data U : Set where
  NAT : U

-- Denotation of the type representants.
el : U → Set
el NAT = ℕ

-- Decidable equality on the universe.
decEqU : DecEq U
decEqU NAT NAT = yes refl

-- Open the specification + the IOR monad from within the spec.
open RefSpec U el decEqU
open RawIMonad MonadIOR'

-- A sample IOR computation.
tfun : IOR ℕ [] (NAT ∷ NAT ∷ [])
tfun =
    newRef 5 >>= λ ref₁ →
    newRef 3 >>= λ ref₂ →
    writeRef 1 ref₁ >>
    readRef ref₂ >>= λ x₂ →
    readRef ref₁ >>= λ x₁ →
    return (x₁ + x₂)

-- A short-hand notation.
run : ∀ {a s t} → Heap s → IOR a s t → a
run h f = proj₁ (interpret f h)

-- A proof of correctness of the computation above.
tfun-correct : run hnil tfun ≡ 4
tfun-correct = refl

-- A more interesting example: a sum function.
tsum-go : List ℕ → Ref NAT (NAT ∷ []) → IOR ℕ (NAT ∷ []) (NAT ∷ [])
tsum : List ℕ → IOR ℕ [] (NAT ∷ [])
tsum xs = newRef 0 >>= tsum-go xs

tsum-go []       r = readRef r
tsum-go (x ∷ xs) r =
  readRef r >>= λ sum →
  writeRef (sum + x) r >>
  tsum-go xs r

-- Some auxiliary definitions follow.
suml : List ℕ → ℕ
suml = foldl _+_ 0

x+0=x : ∀ n → n + 0 ≡ n
x+0=x 0       = refl
x+0=x (suc n) = cong suc (x+0=x n)

tsum-lemma₁ : ∀ x xs → proj₁ (interpret (tsum-go xs rtop) (hcons x hnil)) ≡ foldl _+_ x xs
tsum-lemma₁ x [] = refl
tsum-lemma₁ x (y ∷ ys) = begin
    proj₁ (interpret (tsum-go (y ∷ ys) rtop) (hcons x hnil))
      ≡⟨ refl ⟩
    proj₁ (interpret (tsum-go ys rtop) (hcons (x + y) hnil))
      ≡⟨ tsum-lemma₁ (x + y) ys ⟩
    foldl _+_ (x + y) ys
      ≡⟨ refl ⟩
    foldl _+_ x (y ∷ ys)
      ∎
  where
    open ≡-Reasoning

tsum-lemma₂ : ∀ xs → run hnil (tsum xs) ≡ suml xs
tsum-lemma₂ [] = refl
tsum-lemma₂ (x ∷ xs) = tsum-lemma₁ x xs

suml-plus : ∀ x xs → suml (x ∷ xs) ≡ x + suml xs
suml-plus x [] = sym (x+0=x x)
suml-plus x (y ∷ ys) = begin
    suml (x ∷ y ∷ ys)    ≡⟨ _≡_.refl ⟩
    suml ((x + y) ∷ ys)  ≡⟨ suml-plus (x + y) ys ⟩
    (x + y) + suml ys    ≡⟨ assoc x y (suml ys) ⟩ 
    x + (y + suml ys)    ≡⟨ cong (_+_ x) (PE.sym (suml-plus y ys)) ⟩
    x + suml (y ∷ ys)    ∎
  where
    open ≡-Reasoning
    open IsCommutativeSemiring isCommutativeSemiring
    open IsCommutativeMonoid +-isCommutativeMonoid

suml=sumr : ∀ xs → suml xs ≡ sum xs
suml=sumr [] = refl
suml=sumr (x ∷ xs) = begin
    suml (x ∷ xs)  ≡⟨ suml-plus x xs ⟩
    x + suml xs    ≡⟨ cong (_+_ x) (suml=sumr xs) ⟩
    x + sum  xs    ≡⟨ refl ⟩
    sum (x ∷ xs)   ∎
  where
    open ≡-Reasoning

-- Goal theorem: proof of correctness of tsum.
tsum-correct : ∀ xs → run hnil (tsum xs) ≡ sum xs
tsum-correct xs = begin
  run hnil (tsum xs)
    ≡⟨ tsum-lemma₂ xs ⟩
  suml xs
    ≡⟨ suml=sumr xs ⟩
  sum xs
    ∎
  where
    open ≡-Reasoning
    
    
    
