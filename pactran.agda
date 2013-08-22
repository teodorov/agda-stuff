-- Package transform, as proposed  by Rivest (1997).

module pactran where

-- Bits and XOR utilities.
module Xor where

  open import Function
  open import Data.Vec
  open import Data.Nat

  data Bit : Set where
    O I : Bit

  Block : ℕ → Set
  Block = Vec Bit

  -- All zeroes.
  zeroBlock : ∀ {n} → Block n
  zeroBlock = replicate O

  -- XOR on bits.
  infixr 4 _⊕_
  _⊕_ : Bit → Bit → Bit
  O ⊕ O = O
  O ⊕ I = I
  I ⊕ O = I
  I ⊕ I = O

  -- XOR on blocks, prefix.
  xor : ∀ {n} → Block n → Block n → Block n
  xor = zipWith _⊕_

  -- XOR on blocks, infix.
  infixr 4 _⊕⊕_
  _⊕⊕_ : ∀ {n} → Block n → Block n → Block n
  _⊕⊕_ = xor

  -- XOR all blocks together.
  xorfold : ∀ {n k} → Vec (Block n) k → Block n
  xorfold = foldr (const $ Block _) xor zeroBlock

open import Data.Nat

module PackageTransform (blockSize : ℕ) (blockCount : ℕ) where

  open Xor
  open import Data.Vec

  Block' : Set
  Block' = Block blockSize

  Plaintext : Set
  Plaintext = Vec Block' blockCount

  Package : Set
  Package = Vec Block' (1 + blockCount)

  encode : (key : Block') → Plaintext → Package
  encode key blocks = keyBlock ∷ encBlocks
    where
      encBlocks = map (xor key) blocks
      keyBlock  = xorfold (key ∷ encBlocks)

  decode : Package → Plaintext
  decode (keyBlock ∷ encBlocks) = blocks
    where
      key    = xorfold (keyBlock ∷ encBlocks)
      blocks = map (xor key) encBlocks

module Correctness (blockSize : ℕ) (blockCount : ℕ) where

  open import Data.Vec
  open import Relation.Binary.PropositionalEquality

  open Xor
  open PackageTransform blockSize blockCount
                     
  module Lemmas where

    -- Double XOR is identity, on bits.
    dxor₁ : ∀ k x → k ⊕ k ⊕ x ≡ x
    dxor₁ O O = refl
    dxor₁ O I = refl
    dxor₁ I O = refl
    dxor₁ I I = refl

    -- Double XOR is identity, on blocks.
    dxor₂ : ∀ {n} (k x : Block n) → k ⊕⊕ k ⊕⊕ x ≡ x
    dxor₂ [] [] = refl
    dxor₂ (k ∷ ks) (x ∷ xs) = cong₂ _∷_ (dxor₁ k x) (dxor₂ ks xs)

    -- Double (map xor) is identity, on sequences of blocks.
    dxor₃ : ∀ {n k} (key : Block n) (pt : Vec (Block n) k)
      → map (xor key) (map (xor key) pt) ≡ pt
    dxor₃ key []       = refl
    dxor₃ key (b ∷ bs) = cong₂ _∷_ (dxor₂ key b) (dxor₃ key bs)

    -- Self-XOR yields zero, on bits.
    sxor₁ : ∀ x → x ⊕ x ≡ O
    sxor₁ O = refl
    sxor₁ I = refl

    -- Self-XOR yields zero, on blocks.
    sxor₂ : ∀ {n} (xs : Block n) → xs ⊕⊕ xs ≡ zeroBlock
    sxor₂ [] = refl
    sxor₂ (x ∷ xs) = cong₂ _∷_ (sxor₁ x) (sxor₂ xs)

    z⊕x₁ : ∀ x → O ⊕ x ≡ x
    z⊕x₁ O = refl
    z⊕x₁ I = refl

    z⊕x₂ : ∀ {n} (xs : Block n) → zeroBlock ⊕⊕ xs ≡ xs
    z⊕x₂ []       = refl
    z⊕x₂ (x ∷ xs) = cong₂ _∷_ (z⊕x₁ x) (z⊕x₂ xs)

    x⊕z₁ : ∀ x → x ⊕ O ≡ x
    x⊕z₁ O = refl
    x⊕z₁ I = refl

    x⊕z₂ : ∀ {n} (xs : Block n) → xs ⊕⊕ zeroBlock ≡ xs
    x⊕z₂ []       = refl
    x⊕z₂ (x ∷ xs) = cong₂ _∷_ (x⊕z₁ x) (x⊕z₂ xs)

    -- XOR is associative, on bits.
    xor-assoc₁ : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ y ⊕ z
    xor-assoc₁ O O O = refl
    xor-assoc₁ O O I = refl
    xor-assoc₁ O I O = refl
    xor-assoc₁ O I I = refl
    xor-assoc₁ I O O = refl
    xor-assoc₁ I O I = refl
    xor-assoc₁ I I O = refl
    xor-assoc₁ I I I = refl

    -- XOR is associative, on blocks.
    xor-assoc₂ : ∀ {n} (x y z : Block n) → (x ⊕⊕ y) ⊕⊕ z ≡ x ⊕⊕ y ⊕⊕ z
    xor-assoc₂ [] [] [] = refl
    xor-assoc₂ (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_ (xor-assoc₁ x y z) (xor-assoc₂ xs ys zs)

    -- XOR distributes with respect to _∷_.
    xor-distr-∷ : ∀ {n kx ky} (xs : Vec (Block n) kx) (ys : Vec (Block n) ky)
      → xorfold (xorfold xs ∷ ys) ≡ xorfold (xs ++ ys)
    xor-distr-∷ []       ys = z⊕x₂ _
    xor-distr-∷ (x ∷ xs) ys rewrite sym (xor-distr-∷ xs ys) = xor-assoc₂ _ _ _

    -- XOR distributes with respect to _++_.
    xor-distr-++ : ∀ {n kx ky} (xs : Vec (Block n) kx) (ys : Vec (Block n) ky)
      → xorfold (xs ++ ys) ≡ xorfold xs ⊕⊕ xorfold ys
    xor-distr-++ []       ys rewrite z⊕x₂ (xorfold ys) = refl
    xor-distr-++ (x ∷ xs) ys rewrite xor-distr-++ xs ys = sym (xor-assoc₂ _ _ _)

    -- XOR-fold of a doubled sequence is always zero.
    xor-vain : ∀ {n k} (bs : Vec (Block n) k) → xorfold (bs ++ bs) ≡ zeroBlock
    xor-vain bs = trans (xor-distr-++ bs bs) (sxor₂ _)

    -- The decoding function calculates the correct key.
    key-lemma : ∀ {n k} (key : Block n) (encBlocks : Vec (Block n) k)
      → xorfold (xorfold (key ∷ encBlocks) ∷ encBlocks) ≡ key
    key-lemma key bs = begin
      xorfold (xorfold (key ∷ bs) ∷ bs)
        ≡⟨ xor-distr-∷ (key ∷ bs) bs ⟩
      xorfold (key ∷ bs ++ bs)
        ≡⟨ refl ⟩
      key ⊕⊕ xorfold (bs ++ bs)
        ≡⟨ cong (_⊕⊕_ key) (xor-vain bs) ⟩
      key ⊕⊕ zeroBlock
        ≡⟨ x⊕z₂ key ⟩
      key
        ∎
      where
        open ≡-Reasoning

  -- Correctness of the package transform.
  correct : ∀ key plaintext → decode (encode key plaintext) ≡ plaintext
  correct key plaintext rewrite Lemmas.key-lemma key (map (xor key) plaintext)
    = Lemmas.dxor₃ key plaintext


module Test where

  open Xor public
  open PackageTransform 4 2 public
  open import Data.Vec public
  
  -- C-c C-n test
  test : Plaintext
  test = decode (encode key plaintext)
    where
      key = O ∷ I ∷ O ∷ I ∷ []
      plaintext = (I ∷ O ∷ O ∷ I ∷ []) ∷ (I ∷ O ∷ I ∷ O ∷ []) ∷ []

open Test

  

  
