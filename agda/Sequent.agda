open import Modal

module Sequent (Atom : Set) (Modal : Set) (ModR : ERel Modal) (ModS : Split Modal) (ModQ : DProp Modal) (MP : MProp ModR ModS ModQ) where


open import Formula Atom Modal
open import Ctx Atom Modal ModR ModS ModQ MP

open import Data.Bool
open import Data.Maybe
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

infix 1 _⊢_^_


private
  variable
    P : Atom
    A B C D : Form
    Γ Δ : Ctx
    m n : Size
    M N S : Modal


data _⊢_^_ : Ctx → Form → Size → Set where
  Var   :  sato P ∈ Γ
        → Γ ⊢ sato P ^ init 
  ⇒R    :  Γ ,, A ⊢ B ^ m
        → Γ ⊢ A s⇒ B ^ step m
  ⇒L    :  (A s⇒ B) ∈ Γ
        → Γ ⊢ A ^ m
        → Γ ,, B ⊢ C ^ n
        → Γ ⊢ C ^ fork m n
  ∧R    :  Γ ⊢ A ^ m
        → Γ ⊢ B ^ n
        → Γ ⊢ A s∧ B ^ fork m n
  ∧L1   :  A s∧ B ∈ Γ
        → Γ ,, A ⊢ C ^ m
        → Γ ⊢ C ^ step m
  ∧L2   :  A s∧ B ∈ Γ
        → Γ ,, B ⊢ C ^ m
        → Γ ⊢ C ^ step m
  ∨R1   :  Γ ⊢ A ^ m
        → Γ ⊢ A s∨ B ^ step m
  
  ∨R2   :  Γ ⊢ B ^ m
        → Γ ⊢ A s∨ B ^ step m
  ∨L    :  A s∨ B ∈ Γ
        → Γ ,, A ⊢ C ^ m
        → Γ ,, B ⊢ C ^ n
        → Γ ⊢ C ^ fork m n
  ⊤R    :  Γ ⊢ s⊤ ^ init
  ⊥L    :  s⊥ ∈ Γ
        → Γ ⊢ A ^ init
  Mod   :  Shift M Γ ⊢ A ^ m
        → Γ ⊢ sMod M A ^ (step m)
  Pop   :  Yes (ModQ M)
        → sMod M A ∈ Γ
        → Γ ,, A ⊢ C ^ m
        → Γ ⊢ C ^ (step m)


weak :  Γ ⊆ Δ
     → Γ ⊢ C ^ m
     → Δ ⊢ C ^ m
weak Γ⊆Δ (Var i) = Var (Γ⊆Δ i)
weak Γ⊆Δ (⇒R a) = ⇒R (weak (⊆S Γ⊆Δ) a)
weak Γ⊆Δ (⇒L i a b) = ⇒L (Γ⊆Δ i) (weak Γ⊆Δ a) (weak (⊆S Γ⊆Δ) b)
weak Γ⊆Δ (∧R a b) = ∧R (weak Γ⊆Δ a) (weak Γ⊆Δ b)
weak Γ⊆Δ (∧L1 i a) = ∧L1 (Γ⊆Δ i) (weak (⊆S Γ⊆Δ) a)
weak Γ⊆Δ (∧L2 i a) = ∧L2 (Γ⊆Δ i) (weak (⊆S Γ⊆Δ) a)
weak Γ⊆Δ (∨R1 a) = ∨R1 (weak Γ⊆Δ a)
weak Γ⊆Δ (∨R2 a) = ∨R2 (weak Γ⊆Δ a)
weak Γ⊆Δ (∨L i a b) = ∨L (Γ⊆Δ i) (weak (⊆S Γ⊆Δ) a) (weak (⊆S Γ⊆Δ) b)
weak Γ⊆Δ ⊤R = ⊤R
weak Γ⊆Δ (⊥L i) = ⊥L (Γ⊆Δ i)
weak Γ⊆Δ (Mod a) = Mod (weak (Shift⊆ Γ⊆Δ _) a)
weak Γ⊆Δ (Pop q i a) = Pop q (Γ⊆Δ i) (weak (⊆S Γ⊆Δ) a)


weak0 : Γ ⊢ C ^ m → Γ ,, A ⊢ C ^ m
weak0 x = weak ∈S x

weak1 : Γ ,, A ⊢ C ^ m → Γ ,, B ,, A ⊢ C ^ m
weak1 x = weak (λ { ∈Z → ∈Z ; (∈S i) → ∈S (∈S i)}) x

exch : Γ ,, A ,, B ⊢ C ^ m → Γ ,, B ,, A ⊢ C ^ m
exch x = weak ((λ { ∈Z → ∈S ∈Z ; (∈S ∈Z) → ∈Z ; (∈S (∈S i)) → ∈S (∈S i) })) x


-- virtual weakening is structurally possible
veak :  Γ ⊑ Δ
     → Γ ⊢ C ^ m
     → Δ ⊢ C ^ m
veak Γ⊑Δ (Var i) with Γ⊑Δ i
... | inj₁ j = Var j
veak Γ⊑Δ (⇒R a) = ⇒R (veak (⊑S Γ⊑Δ) a)
veak Γ⊑Δ (⇒L i a b) with Γ⊑Δ i
... | inj₁ j =  ⇒L j (veak Γ⊑Δ a) (veak (⊑S Γ⊑Δ) b)
veak Γ⊑Δ (∧R a b) =  ∧R (veak Γ⊑Δ a) (veak Γ⊑Δ b)
veak Γ⊑Δ (∧L1 i a) with Γ⊑Δ i
... | inj₁ j =  ∧L1 j (veak (⊑S Γ⊑Δ) a)
veak Γ⊑Δ (∧L2 i a) with Γ⊑Δ i
... | inj₁ j =  ∧L2 j (veak (⊑S Γ⊑Δ) a)
veak Γ⊑Δ (∨R1 a) =  ∨R1 (veak Γ⊑Δ a)
veak Γ⊑Δ (∨R2 a) =  ∨R2 (veak Γ⊑Δ a)
veak Γ⊑Δ (∨L i a b) with Γ⊑Δ i
... | inj₁ j =  ∨L j (veak (⊑S Γ⊑Δ) a) (veak (⊑S Γ⊑Δ) b)
veak Γ⊑Δ ⊤R = ⊤R
veak Γ⊑Δ (⊥L i) with Γ⊑Δ i
... | inj₁ j =  ⊥L j
veak Γ⊑Δ (Mod a) = Mod (veak (Shift⊑ Γ⊑Δ _) a)
veak Γ⊑Δ (Pop {M = M} M◂ i a) with Γ⊑Δ i
... | inj₁ j = Pop M◂ j (veak (⊑S Γ⊑Δ) a)
... | inj₂ ((M , (N , A)) , (refl , N◂M , j)) = Pop (MProp.MZip MP N◂M M◂) j (veak (⊑S Γ⊑Δ) a)

-- Mod left rule is now admissible
ModL : (sMod M A ∈ Γ) → (M ◂ N) → Γ ,, sMod N A ⊢ B ^ m → Γ ⊢ B ^ m
ModL {M} {A} {Γ} {N} i M◂N a = veak (λ {
  ∈Z → inj₂ ((N , M , A) , refl , M◂N , i) ;
  (∈S j) → inj₁ j}) a

id : A ∈ Γ → ∃ (λ q → (Γ ⊢ A ^ q))
id {_ , atom x} i = init , (Var i)
id {_ , A f⇒ B} {Γ} i =
  let (m , a) = id {_ , A} {Γ ,, (_ , A)} ∈Z in
  let (n , b) = id {_ , B} {Γ ,, (_ , A) ,, (_ , B)} ∈Z in
  step (fork m n) , ⇒R (⇒L (∈S i) a b)
id {_ , A f∧ B} {Γ} i =
  let (m , a) = id {_ , A} {Γ ,, (_ , A)} ∈Z in
  let (n , b) = id {_ , B} {Γ ,, (_ , B)} ∈Z in
  fork (step m) (step n) , ∧R (∧L1 i a) (∧L2 i b)
id {_ , A f∨ B} {Γ} i =
  let (m , a) = id {_ , A} {Γ ,, (_ , A)} ∈Z in
  let (n , b) = id {_ , B} {Γ ,, (_ , B)} ∈Z in
 fork (step m) (step n) , ∨L i (∨R1 a) (∨R2 b)
id {_ , f⊤} {Γ} i = init , ⊤R
id {_ , f⊥} {Γ} i = init , (⊥L i)
id {_ , fMod M A} {Γ} i =
  let (m , a) = id {_ , A} {Shift M Γ} (Shift∋ i (MProp.MRefl MP)) in
  step m , (Mod a)



-- the logic is consistent, that is we cannot proof false from nothing
consistent : · ⊢ s⊥ ^ m → ⊥
consistent (⇒L () p i)
consistent (∧L1 () a)
consistent (∧L2 () a)
consistent (⊥L ())

Pops : PopSeq Γ Δ → (Δ ⊢ A ^ m) → (∃ λ q → Γ ⊢ A ^ q) 
Pops {Γ} {.Γ} {A} {m} End P = m , P
Pops {Γ} {Δ} {A} {m} (Nex {Γ} {Δ} {M} {B} q i σ) P =
  let (v , a) = Pops σ P in
  (step v) , (Pop q i a)

Popa : (AllPop Γ · ⊢ A ^ m) → (∃ λ q → Γ ⊢ A ^ q)
Popa {Γ} P = Pops (AllPopSeq {Γ} {·}) P

qeak : Yes (ModQ M) → Shift M Γ ⊢ A ^ m → (∃ λ q → Γ ⊢ A ^ q)  
qeak {M} {Γ} M◂ P = Popa (veak {Shift M Γ} {AllPop Γ ·} (APS {M} {Γ} {Γ} M◂ (λ i → i)) P)

