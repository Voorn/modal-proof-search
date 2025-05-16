module Modal where

open import Data.Bool
open import Data.Maybe
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality

-- This module specifies K4-style multimodal axiom schemes
-- The general axiomatic relation will be generated given the following three constructors.

-- 1) A relation for specifying direct implications of modalities, that is: M X => N X axioms.
ERel : (A : Set) → Set
ERel A = A → A → Bool

-- 2) A function specifying for each M and N at most one R for asserting that: M X => N R X
-- We write this R as (M-N).
Split : (A : Set) → Set
Split A = A → A → Maybe A

-- 3) A proposition specifying for which modalities we have the co-unit axioms, that is: M X => X
DProp : (A : Set) → Set
DProp A = (a : A) → Bool


private
  variable
    X Y Z : Set

Yes : Bool → Set
Yes b = b ≡ true

-- We have given a set of modalities X, and one of each of the above specifications.
-- We formulate the properties on these which we need them to satsify.

-- ERel needs to be reflexive
Refl : ERel X → Set
Refl {X} R = {x : X} → R x x ≡ true

-- ERel needs to be transitive
Tran : ERel X → Set
Tran {X} R = {x y z : X} → R x y ≡ true → R y z ≡ true → R x z ≡ true

-- If M' => M, and M => N (M-N), and N => N', then M' => N'(M'-N') and (M'-N') => (M-N)
RelSplit : ERel X → Split X → Set
RelSplit {X} R S = {x x' y y' x-y : X}
  → S x y ≡ just x-y
  → R x' x ≡ true
  → R y y' ≡ true
  → Σ X λ x'-y' → S x' y' ≡ just x'-y' × R x'-y' x-y ≡ true

-- If M => N(M-N) and N => R(N-R), then M => R(M-R) and (M-R) => (N-R)((M-R)-(N-R)) and ((M-R)-(N-R)) => (M-N)
SplitCom : ERel X → Split X → Set
SplitCom {X} R S = {x y z x-y y-z : X}
  → S x y ≡ just x-y
  → S y z ≡ just y-z
  → Σ X λ x-z
  → Σ X λ c
  → S x z ≡ just x-z
  × S x-z y-z ≡ just c
  × R c x-y ≡ true

-- If M => N and N => ·, then M => · 
RelPro : ERel X → DProp X → Set
RelPro {X} R C = {x y : X}
  → R x y ≡ true
  → C y ≡ true
  → C x ≡ true

-- If M => N(M-N) and N => · , then M => (M-N) 
DipSplitL : ERel X → Split X → DProp X → Set
DipSplitL {X} R S C = {x y z : X}
  → S x y ≡ just z
  → C y ≡ true
  → R x z ≡ true

-- If M => N(M-N) and (M-N) => · , then M => N
DipSplitR : ERel X → Split X → DProp X → Set
DipSplitR {X} R S C = {x y z : X}
  → S x y ≡ just z
  → C z ≡ true
  → R x y ≡ true


-- All properties wrapped together
record Preo {A : Set} (R : ERel A) : Set where
  field
    PRefl : Refl R
    PTran : Tran R

record MProp {A : Set} (R : ERel A) (S : Split A) (Q : DProp A) : Set where
  field
    MRefl : Refl R
    MTran : Tran R
    MRS : RelSplit R S
    MSC : SplitCom R S
    MZip : RelPro R Q
    MDipL : DipSplitL R S Q
    MDipR : DipSplitR R S Q


-- The full implication relation from modalities to lists of modalities
data Full {X : Set} (R : ERel X) (S : Split X) (Q : DProp X) : X → List X → Set where
  Pop : (M : X) → (M▸ : Q M ≡ true) → Full R S Q M []
  Tra : (M N : X) → (M▸N : R M N ≡ true) → Full R S Q M (N ∷ [])
  Spl : (M N T : X) → (M▸NT : S M N ≡ just T) → (α : List X) → Full R S Q T α → Full R S Q M (N ∷ α)  

FullRel : {X : Set} (R : ERel X) (S : Split X) (Q : DProp X) → (MProp R S Q)
  → (M N : X) → (α : List X) → (R M N ≡ true) → Full R S Q N α → Full R S Q M α
FullRel R S Q MP M N [] M▸N (Pop .N M▸) = Pop M (MProp.MZip MP M▸N M▸)
FullRel R S Q MP M N (T ∷ .[]) M▸N (Tra .N .T N▸T) = Tra M T (MProp.MTran MP M▸N N▸T)
FullRel R S Q MP M N (T ∷ α) M▸N (Spl .N .T K N▸TK .α K▸α) with MProp.MRS MP N▸TK M▸N (MProp.MRefl MP)
... | K' , M▸TK' , K'▸K = Spl M T K' M▸TK' α (FullRel R S Q MP K' K α K'▸K K▸α)

FullSplit : {X : Set} (R : ERel X) (S : Split X) (Q : DProp X) → (MProp R S Q) → (M N T : X) → (α β : List X)
  → (S M N ≡ just T) → Full R S Q N α → Full R S Q T β → Full R S Q M (α ++ β)
FullSplit R S Q MP M N T [] β M▸NT (Pop .N N▸) T▸β = FullRel R S Q MP M T β (MProp.MDipL MP M▸NT N▸) T▸β
FullSplit R S Q MP M N T (K ∷ .[]) [] M▸NT (Tra .N .K N▸K) (Pop .T T▸) = Tra M K (MProp.MTran MP (MProp.MDipR MP M▸NT T▸) N▸K)
FullSplit R S Q MP M N T (K ∷ .[]) β M▸NT (Tra .N .K N▸K) T▸Uβ with MProp.MRS MP M▸NT (MProp.MRefl MP) N▸K
... | (T' , M▸KT' , T'▸T) = Spl M K T' M▸KT' β (FullRel R S Q MP T' T β T'▸T T▸Uβ) 
FullSplit R S Q MP M N T (K ∷ α) β M▸NT (Spl .N .K V N▸KV .α V▸α) T▸β with MProp.MSC MP M▸NT N▸KV
... | M-K , M-K-V , M▸K- , M-K▸V- , p = Spl M K M-K M▸K- (α ++ β) (FullSplit R S Q MP M-K V M-K-V α β M-K▸V- V▸α (FullRel R S Q MP M-K-V T β p T▸β))
--FullRel R S Q MP M N (T ∷ K ∷ α) M▸N N▸α = {!!}

data FullT (R : ERel X) (S : Split X) (Q : DProp X) : List X → List (List X) → Set where
  Non : FullT R S Q [] []
  Ano : (M : X) → (α β : List X) → (σ : List (List X)) → Full R S Q M α → FullT R S Q β σ → FullT R S Q (M ∷ β) (α ∷ σ)

FullEmp : (R : ERel X) (S : Split X) (Q : DProp X) → (α : List X) → FullT R S Q α [] → α ≡ []
FullEmp R S Q [] Non = refl
FullEmp R S Q (x ∷ α) ()

FullEnd : (R : ERel X) (S : Split X) (Q : DProp X) → (M : X) → (α β : List X) → (σ : List (List X))
  → FullT R S Q α σ → Full R S Q M β
  → FullT R S Q (α ++ (M ∷ [])) (σ ++ (β ∷ []))
FullEnd R S Q M [] β [] Non M>β = Ano _ _ _ _ M>β Non 
FullEnd R S Q M (x ∷ α) β .(α₁ ∷ σ) (Ano .x α₁ .α σ x₁ α>σ) M>β = Ano x α₁ (α ++ M ∷ []) (σ ++ β ∷ []) x₁ (FullEnd R S Q M α β σ α>σ M>β)

FullTail : (R : ERel X) (S : Split X) (Q : DProp X) → (M : X) → (α β : List X) → (σ : List (List X))
  → FullT R S Q (α ++ (M ∷ [])) (σ ++ (β ∷ []))
  → FullT R S Q α σ × Full R S Q M β
FullTail R S Q M [] β [] (Ano .M .β .[] .[] x prop) = Non , x
FullTail R S Q M [] β (σ ∷ []) (Ano .M .σ .[] .([] ++ β ∷ []) x ())
FullTail R S Q M [] β (σ ∷ σ₁ ∷ σ₂) (Ano .M .σ .[] .((σ₁ ∷ σ₂) ++ β ∷ []) x ())
FullTail R S Q M (x ∷ []) β [] (Ano .x .β .([] ++ M ∷ []) .[] x₁ ())
FullTail R S Q M (x ∷ x₂ ∷ α) β [] (Ano .x .β .((x₂ ∷ α) ++ M ∷ []) .[] x₁ prop)  with FullEmp R S Q _ prop
... | ()
FullTail R S Q M (x ∷ α) β (γ ∷ τ) (Ano .x .γ .(α ++ M ∷ []) .(τ ++ β ∷ []) x₁ prop) with FullTail R S Q M α β τ prop
... | fst , snd = (Ano _ _ _ _ x₁ fst) , snd

RuniList : {X : Set} → (α : List X) → (α ++ [] ≡ α)
RuniList [] = refl
RuniList (x ∷ α) = cong (λ z → x ∷ z) (RuniList α)

FTra : {X : Set} (R : ERel X) (S : Split X) (Q : DProp X) → (MProp R S Q) → (M : X) → (α : List X) → (σ : List (List X)) → Full R S Q M α → FullT R S Q α σ → Full R S Q M (concat σ) 
FTra R S Q MP M [] .[] (Pop .M M▸) Non = Pop M M▸
FTra R S Q MP M (N ∷ .[]) .(α ∷ []) (Tra .M .N M▸N) (Ano .N α .[] .[] N▸α Non) rewrite RuniList α = FullRel R S Q MP M N α M▸N N▸α
FTra R S Q MP M (N ∷ α) .(β ∷ σ) (Spl .M .N T M▸NT .α T▸α) (Ano .N β .α σ N▸β α▸σ) = FullSplit R S Q MP M N T β (concat σ) M▸NT N▸β (FTra R S Q MP T α σ T▸α α▸σ)


Ona : (R : ERel X) (S : Split X) (Q : DProp X) (M : X) → (α β : List X) → (σ : List (List X)) → Full R S Q M β → FullT R S Q α σ → FullT R S Q (α ++ M ∷ []) (σ ++ β ∷ [])
Ona R S Q M [] β .[] M▸β Non = Ano M β [] [] M▸β Non
Ona R S Q M (N ∷ α) β .(γ ∷ σ) M▸β (Ano .N γ .α σ N▸γ α▸σ) = Ano N γ (α ++ M ∷ []) (σ ++ β ∷ []) N▸γ (Ona R S Q M α β σ M▸β α▸σ)
