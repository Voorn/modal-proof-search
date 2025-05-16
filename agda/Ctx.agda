open import Modal

open import Data.Bool

module Ctx (Atom : Set) (Modal : Set) (ModR : ERel Modal) (ModS : Split Modal) (ModQ : DProp Modal) (MP : MProp ModR ModS ModQ) where

open import Formula Atom Modal 

open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

infixl 32 _,,_
infix 31 _∈_
infix 31 _⊆_


BI : (b : Bool) → (b ≡ false) ⊎ (b ≡ true)
BI false = inj₁ refl
BI true = inj₂ refl

MI : (M N : Modal) →  (ModS M N ≡ nothing ⊎ Σ Modal λ M-N → ModS M N ≡ just M-N)
MI M N with (ModS M N)
... | nothing = inj₁ refl
... | just M-N = (inj₂ (M-N , refl))

_◂_ : Modal → Modal → Set
M ◂ N = (ModR M N) ≡ true

_◃_ : Modal → Modal → Set
M ◃ N = (ModR M N) ≡ false

ModInfo : (M N : Modal) → ((M ◃ N) ⊎ (M ◂ N)) × (ModS M N ≡ nothing ⊎ Σ Modal λ M-N → ModS M N ≡ just M-N)
ModInfo M N with (ModS M N)
... | nothing = BI (ModR M N) , inj₁ refl
... | just M-N = (BI (ModR M N)) , (inj₂ (M-N , refl))


data Ctx : Set where
  · : Ctx
  _,,_ : Ctx → Form → Ctx

conc : Ctx → Ctx → Ctx
conc Γ · = Γ
conc Γ (Δ ,, x) = conc Γ Δ ,, x

·conc : {Γ : Ctx} → conc · Γ ≡ Γ
·conc {·} = refl
·conc {Γ ,, x} = cong (λ z → z ,, x) ·conc

dda : Form → Ctx → Ctx
dda A Γ = conc (· ,, A) Γ

concdda≡ : {Γ Δ : Ctx} → {A : Form} → (conc (Γ ,, A) Δ ≡ conc Γ (dda A Δ))
concdda≡ {Γ} {·} {A} = refl
concdda≡ {Γ} {Δ ,, B} {A} = cong (λ z → z ,, B) (concdda≡ {Γ} {Δ} {A})

private
  variable
    A B C D : Form
    Γ Δ Θ Λ : Ctx
    M N S : Modal
    m n k : Size


data _∈_ : Form → Ctx → Set where
  ∈Z : {A : Form} → {Γ : Ctx} → A ∈ (Γ ,, A)
  ∈S : {A B : Form} → {Γ : Ctx} → (A ∈ Γ) → (A ∈ Γ ,, B)

-- Literal inclusion
_⊆_ : Ctx → Ctx → Set
Γ ⊆ Δ = {A : Form} → A ∈ Γ → A ∈ Δ

conc⊆ : {Γ Δ : Ctx} → Γ ⊆ conc Γ Δ
conc⊆ {Γ} {·} i = i
conc⊆ {Γ} {Δ ,, x} i = ∈S (conc⊆ i)

conc⊆2 : {Γ Δ : Ctx} → Δ ⊆ conc Γ Δ
conc⊆2 {Γ} {·} ()
conc⊆2 {Γ} {Δ ,, x} ∈Z = ∈Z
conc⊆2 {Γ} {Δ ,, x} (∈S i) = ∈S (conc⊆2 i)

-- Virtual inclusion
_⊑_ : Ctx → Ctx → Set
Γ ⊑ Δ = {A : Form} → A ∈ Γ → A ∈ Δ ⊎ Σ (Modal × Modal × Form) λ (N , M , B) → A ≡ sMod N B × M ◂ N × sMod M B ∈ Δ

⊆S : Γ ⊆ Δ → Γ ,, A ⊆ Δ ,, A
⊆S Γ⊆Δ ∈Z = ∈Z
⊆S Γ⊆Δ (∈S p) = ∈S (Γ⊆Δ p)


⊑S : Γ ⊑ Δ → Γ ,, A ⊑ Δ ,, A
⊑S Γ⊑Δ ∈Z = inj₁ ∈Z
⊑S Γ⊑Δ (∈S p) with Γ⊑Δ p
... | inj₁ i = inj₁ (∈S i)
... | inj₂ (MNA , refl , N◂M , i) = inj₂ (MNA , refl , N◂M , (∈S i))

⊆⊑ : Γ ⊆ Δ → Γ ⊑ Δ 
⊆⊑ Γ⊆Δ i = inj₁ (Γ⊆Δ i)

⊑tran : Γ ⊑ Δ → Δ ⊑ Θ → Γ ⊑ Θ
⊑tran  Γ⊑Δ Δ⊑Θ i with  Γ⊑Δ i 
⊑tran Γ⊑Δ Δ⊑Θ i | inj₁ j = Δ⊑Θ j
⊑tran Γ⊑Δ Δ⊑Θ i | inj₂ ((M , N , A) , refl , N◂M , j) with  Δ⊑Θ j
⊑tran Γ⊑Δ Δ⊑Θ i | inj₂ ((M , N , A) , refl , N◂M , j) | inj₁ k =
  inj₂ ((M , N , A) , refl , N◂M , k)
⊑tran Γ⊑Δ Δ⊑Θ i | inj₂ ((M , N , A) , refl , N◂M , j) | inj₂ ((N , R , A) , refl , R◂N , k) =
  inj₂ ((M , R , A) , refl , MProp.MTran MP R◂N N◂M , k)

Shift : Modal → Ctx → Ctx
Shift1 : Modal → Ctx → Modal → Form → Ctx
Shift2 : Modal → Ctx → Modal → Form → Ctx

Shift N · = ·
Shift N (Γ ,, (_ , atom x)) = Shift N Γ
Shift N (Γ ,, (_ , A f⇒ B)) = Shift N Γ
Shift N (Γ ,, (_ , A f∧ B)) = Shift N Γ
Shift N (Γ ,, (_ , A f∨ B)) = Shift N Γ
Shift N (Γ ,, (_ , f⊤)) = Shift N Γ
Shift N (Γ ,, (_ , f⊥)) = Shift N Γ
Shift N (Γ ,, (step k , fMod M A)) = Shift1 N Γ M (k , A)

Shift1 M Γ N A with (ModR N M)
... | false = Shift2 M Γ N A
... | true = Shift2 M Γ N A ,, A
Shift2 M Γ N A with (ModS N M)
... | nothing = Shift M Γ
... | just N-M = Shift M Γ ,, sMod N-M A


prot : (A : Form) → (M : Modal) → (Γ : Ctx) → Set
prot A M Γ = (Σ Modal λ N → (sMod N A ∈ Γ × N ◂ M)) ⊎
  (Σ (Modal × Modal × Form) λ (N , N-M , B) → (sMod N B ∈ Γ × A ≡ sMod N-M B × ModS N M ≡ just N-M))

wkprot : prot A M Γ → prot A M (Γ ,, B)
wkprot (inj₁ (N , i , N◂M)) = inj₁ (N , ∈S i , N◂M)
wkprot (inj₂ (det , i , eqs)) = inj₂ (det , (∈S i , eqs))

Shift∈ : (A ∈ (Shift M Γ)) → prot A M Γ
Shift∈ {A} {M} {Γ ,, (_ , atom x)} p = wkprot (Shift∈ p)
Shift∈ {A} {M} {Γ ,, (_ , B f⇒ C)} p = wkprot (Shift∈ p)
Shift∈ {A} {M} {Γ ,, (_ , B f∧ C)} p = wkprot (Shift∈ p)
Shift∈ {A} {M} {Γ ,, (_ , B f∨ C)} p = wkprot (Shift∈ p)
Shift∈ {A} {M} {Γ ,, (_ , f⊤)} p = wkprot (Shift∈ p)
Shift∈ {A} {M} {Γ ,, (_ , f⊥)} p = wkprot (Shift∈ p)
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p with ModInfo N M
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p | inj₁ N◃M , inj₁ N□M rewrite N◃M | N□M = wkprot (Shift∈ p) --let (R , i , rest) = Shift∈ p in R , (∈S i , rest)
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p | inj₁ N◃M , inj₂ (N-M , N■M) rewrite N◃M | N■M with p
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p | inj₁ N◃M , inj₂ (N-M , N■M) | ∈Z = inj₂ ((N , N-M , (k , B)) , (∈Z , refl , N■M)) --N-M , ({!∈Z!} , {!!})
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p | inj₁ N◃M , inj₂ (N-M , N■M) | (∈S i) = wkprot (Shift∈ i)
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p | inj₂ N◂M , inj₁ N□M rewrite N◂M | N□M with p
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p | inj₂ N◂M , inj₁ N□M | ∈Z = inj₁ (N , ∈Z , N◂M) --N , (∈Z , inj₁ N◂M)
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p | inj₂ N◂M , inj₁ N□M | (∈S i) = wkprot (Shift∈ i) --let (R , j , rest) = Shift∈ {Γ = Γ} i in R , (∈S j , rest)
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p | inj₂ N◂M , inj₂ (N-M , N■M) rewrite N◂M | N■M with p
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p | inj₂ N◂M , inj₂ (N-M , N■M) | ∈Z = inj₁ (N , ∈Z , N◂M)
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p | inj₂ N◂M , inj₂ (N-M , N■M) | ∈S ∈Z = inj₂ ((N , N-M , (k , B)) , (∈Z , refl , N■M))
Shift∈ {A} {M} {Γ ,, (step k , fMod N B)} p | inj₂ N◂M , inj₂ (N-M , N■M) | ∈S (∈S i) = wkprot (Shift∈ i)


Shift∋ : {A : Forms m} → ((step m , fMod M A) ∈ Γ) → (M ◂ N) → ((m , A) ∈ (Shift N Γ))
Shift∋ {m} {M} {Γ ,, (_ , atom x)} (∈S p) eqt = Shift∋ p eqt 
Shift∋ {m} {M} {Γ ,, (_ , B f⇒ C)} (∈S p) eqt = Shift∋ p eqt
Shift∋ {m} {M} {Γ ,, (_ , B f∧ C)} (∈S p) eqt = Shift∋ p eqt 
Shift∋ {m} {M} {Γ ,, (_ , B f∨ C)} (∈S p) eqt = Shift∋ p eqt 
Shift∋ {m} {M} {Γ ,, (_ , f⊤)} (∈S p) eqt = Shift∋ p eqt 
Shift∋ {m} {M} {Γ ,, (_ , f⊥)} (∈S p) eqt = Shift∋ p eqt 
Shift∋ {m} {M} {Γ ,, (_ , fMod M B)} {N} ∈Z eqt rewrite eqt = ∈Z
Shift∋ {m} {M} {Γ ,, (_ , fMod R B)} {N} (∈S i) eqt with ModR R N
Shift∋ {m} {M} {Γ ,, (_ , fMod R B)} {N} (∈S i) eqt | false with ModS R N
Shift∋ {m} {M} {Γ ,, (_ , fMod R B)} {N} (∈S i) eqt | false | nothing = Shift∋ i eqt 
Shift∋ {m} {M} {Γ ,, (_ , fMod R B)} {N} (∈S i) eqt | false | just R-N = ∈S (Shift∋ i eqt)
Shift∋ {m} {M} {Γ ,, (_ , fMod R B)} {N} (∈S i) eqt | true with ModS R N
Shift∋ {m} {M} {Γ ,, (_ , fMod R B)} {N} (∈S i) eqt | true | nothing = ∈S (Shift∋ i eqt) 
Shift∋ {m} {M} {Γ ,, (_ , fMod R B)} {N} (∈S i) eqt | true | just R-N = ∈S (∈S (Shift∋ i eqt))

Shift∋2 : {A : Forms m} → ((step m , fMod M A) ∈ Γ) → (ModS M N ≡ just S) → ((step m , fMod S A) ∈ (Shift N Γ))
Shift∋2 {m} {M} {Γ ,, (_ , fMod M A)} {N} {M-N} ∈Z eqs with ModR M N
... | false rewrite eqs = ∈Z
... | true rewrite eqs = ∈S ∈Z
Shift∋2 {m} {M} {Γ ,, (_ , atom x)} {N} {M-N} (∈S i) eqs = Shift∋2 i eqs
Shift∋2 {m} {M} {Γ ,, (_ , B f⇒ B₁)} {N} {M-N} (∈S i) eqs = Shift∋2 i eqs
Shift∋2 {m} {M} {Γ ,, (_ , B f∧ B₁)} {N} {M-N} (∈S i) eqs = Shift∋2 i eqs
Shift∋2 {m} {M} {Γ ,, (_ , B f∨ B₁)} {N} {M-N} (∈S i) eqs = Shift∋2 i eqs
Shift∋2 {m} {M} {Γ ,, (_ , f⊤)} {N} {M-N} (∈S i) eqs = Shift∋2 i eqs
Shift∋2 {m} {M} {Γ ,, (_ , f⊥)} {N} {M-N} (∈S i) eqs = Shift∋2 i eqs
Shift∋2 {m} {M} {Γ ,, (_ , fMod R B)} {N} {M-N} (∈S i) eqs with ModR R N
Shift∋2 {m} {M} {Γ ,, (_ , fMod R B)} {N} {M-N} (∈S i) eqs | false with ModS R N
Shift∋2 {m} {M} {Γ ,, (_ , fMod R B)} {N} {M-N} (∈S i) eqs | false | nothing = Shift∋2 i eqs
Shift∋2 {m} {M} {Γ ,, (_ , fMod R B)} {N} {M-N} (∈S i) eqs | false | just R-N = ∈S (Shift∋2 i eqs)
Shift∋2 {M} {A} {Γ ,, (_ , fMod R B)} {N} {M-N} (∈S i) eqs | true with ModS R N
Shift∋2 {M} {A} {Γ ,, (_ , fMod R B)} {N} {M-N} (∈S i) eqs | true  | nothing = ∈S (Shift∋2 i eqs)
Shift∋2 {M} {A} {Γ ,, (_ , fMod R B)} {N} {M-N} (∈S i) eqs | true  | just R-N = ∈S (∈S (Shift∋2 i eqs))

Shift⊆ : (Γ ⊆ Δ) → (M : Modal) → (Shift M Γ ⊆ Shift M Δ)
Shift⊆ {Γ} Γ⊆Δ M i with Shift∈ {_} {M} {Γ} i
... | inj₁ (N , i , N◂M) = Shift∋ (Γ⊆Δ i) N◂M
... | inj₂ ((N , N-M , B) , (i , eq , N■M)) rewrite eq = Shift∋2 (Γ⊆Δ i) N■M
-- -- ... | N , eq , p = Shift∋ (Γ⊆Δ p) eq

Shift⊑ : (Γ ⊑ Δ) → (M : Modal) → (Shift M Γ ⊑ Shift M Δ)
Shift⊑ {Γ} Γ⊑Δ M i with Shift∈ {_} {M} {Γ} i
Shift⊑ {Γ} Γ⊑Δ M i | inj₁ (N , j , N◂M) with Γ⊑Δ j
Shift⊑ {Γ} Γ⊑Δ M i | inj₁ (N , j , N◂M) | inj₁ k = inj₁ (Shift∋ k N◂M)
Shift⊑ {Γ} Γ⊑Δ M i | inj₁ (N , j , N◂M) | inj₂ ((.N , R , A) , (refl , R◂N , k)) = inj₁ (Shift∋ k (MProp.MTran MP R◂N N◂M) )
Shift⊑ {Γ} Γ⊑Δ M i | inj₂ ((N , N-M , B) , (j , refl , N■M)) with Γ⊑Δ j
Shift⊑ {Γ} Γ⊑Δ M i | inj₂ ((N , N-M , B) , (j , refl , N■M)) | inj₁ k = inj₁ (Shift∋2 k N■M) --Shift∋2 (Γ⊆Δ i) N■M
Shift⊑ {Γ} Γ⊑Δ M i | inj₂ ((N , N-M , B) , (j , refl , N■M)) |  inj₂ ((.N , R , A) , (refl , R◂N , k))
  with MProp.MRS MP N■M R◂N (MProp.MRefl MP) 
... | (R-M , R■M , R-M◂N-M) =  inj₂ ((N-M , R-M , B) , (refl , R-M◂N-M , Shift∋2 k R■M))

Shift◂ : (M ◂ N) → (Γ : Ctx) → (Shift M Γ ⊑ Shift N Γ)
Shift◂ {M} {N} M◂N Γ i with Shift∈ {Γ = Γ} i
Shift◂ {M} {N} M◂N Γ i | inj₁ (R , j , R◂M) = inj₁ (Shift∋ j (MProp.MTran MP R◂M M◂N))
Shift◂ {M} {N} M◂N Γ i | inj₂  ((R , R-M , B) , (j , eq , R■M)) rewrite eq with  MProp.MRS MP R■M (MProp.MRefl MP) M◂N
... | (R-N , R■N , R-N◂R-M) =  inj₂ ((R-M , R-N , B) , refl , R-N◂R-M , Shift∋2 j R■N)


Shift■ : (ModS M N ≡ just S) → (Γ : Ctx) → Shift M Γ ⊑ (Shift S (Shift N Γ))
Shift■ {M} {N} {M-N} M■N Γ i with Shift∈ {Γ = Γ} i
... | inj₁ (R , j , R◂M) =
  let (R-N , R■N , R-N◂M-N) = MProp.MRS MP M■N R◂M (MProp.MRefl MP) in
  inj₁ (Shift∋ (Shift∋2 j R■N) R-N◂M-N)
... | inj₂ ((R , R-M , D) , (j , refl , R■M)) =
  let ( R-N , RN-MN , R■N , R-N■M-N , RN-MN◂RM ) = MProp.MSC MP R■M M■N in
  inj₂ ((R-M , RN-MN , D) , refl , RN-MN◂RM , Shift∋2 (Shift∋2 j R■N) R-N■M-N)


-- De Bruijn Indices Stuff
data Cloc : Ctx → Set where
  Last : {A : Form} → {Γ : Ctx} → Cloc (Γ ,, A)
  Befo : {A : Form} → {Γ : Ctx} → Cloc Γ → Cloc (Γ ,, A)

data Cbet : Ctx → Set where
  Last : {Γ : Ctx} → Cbet (Γ)
  Befo : {A : Form} → {Γ : Ctx} → Cbet Γ → Cbet (Γ ,, A)
  
ClocA : {Γ : Ctx} → Cloc Γ → Form
ClocA {Γ ,, A} Last = A
ClocA {Γ} (Befo i) = ClocA i

ClocCut : {Γ : Ctx} → Cloc Γ → Ctx
ClocCut {Γ ,, A} Last = Γ
ClocCut {Γ ,, A} (Befo p) = ClocCut p ,, A

ClocBef : {Γ : Ctx} → Cloc Γ → Ctx
ClocBef {Γ ,, A} Last = Γ
ClocBef {Γ ,, A} (Befo p) = ClocBef p

CIns : {Γ : Ctx} → Cbet Γ → Form → Ctx
CIns {Γ} Last B = Γ ,, B
CIns {Γ ,, A} (Befo p) B = CIns p B ,, A

CInsP : {Γ : Ctx} → {B : Form} → (i : Cbet Γ) → (j : Cloc Γ) → Cloc (CIns i B)
CInsP Last j = Befo j
CInsP (Befo i) Last = Last
CInsP (Befo i) (Befo j) = Befo (CInsP i j)

CInsP≡ :  {Γ : Ctx} → {B : Form} → (i : Cbet Γ) → (j : Cloc Γ) → (ClocA j) ≡ (ClocA (CInsP {Γ} {B} i j))
CInsP≡ Last j = refl
CInsP≡ (Befo i) Last = refl
CInsP≡ (Befo i) (Befo j) = CInsP≡ i j

Cloc∈ : (i : Cloc Γ) → (ClocA i ∈ Γ)
Cloc∈ Last = ∈Z
Cloc∈ (Befo i) = ∈S (Cloc∈ i)

∈Cloc : (A ∈ Γ) → Cloc Γ
∈Cloc ∈Z = Last
∈Cloc (∈S i) = Befo (∈Cloc i)

∈Cloc≡ : (i : A ∈ Γ) → (ClocA (∈Cloc i) ≡ A)
∈Cloc≡ ∈Z = refl
∈Cloc≡ (∈S i) = ∈Cloc≡ i

Cloc⊆ : (s : Γ ⊆ Δ) → (i : Cloc Γ) → (ClocA i ≡ ClocA (∈Cloc (s (Cloc∈ i))))
Cloc⊆ s i = sym (∈Cloc≡ (s (Cloc∈ i)))

-- Merry Poppins
AllPop : Ctx → Ctx → Ctx
AllPop' : Ctx → Form → Ctx → Ctx

AllPop · Γ' = Γ'
AllPop (Γ ,, x) Γ' = AllPop' Γ x Γ'

AllPop' Γ (k , atom p) Γ' = AllPop Γ (dda (k , atom p) Γ')
AllPop' Γ (k , (A f⇒ B)) Γ' = AllPop Γ (dda (k , (A f⇒ B)) Γ') 
AllPop' Γ (k , (A f∧ B)) Γ' = AllPop Γ (dda (k , (A f∧ B)) Γ') 
AllPop' Γ (k , (A f∨ B)) Γ' = AllPop Γ (dda (k , (A f∨ B)) Γ') 
AllPop' Γ (k , f⊤) Γ' = AllPop Γ (dda (k , f⊤) Γ') 
AllPop' Γ (k , f⊥) Γ' = AllPop Γ (dda (k , f⊥) Γ') 
AllPop' Γ (step k1 , fMod M A) Γ' with ModQ M
... | false = AllPop Γ (dda (step k1 , fMod M A) Γ') 
... | true = AllPop Γ (dda (step k1 , fMod M A) Γ'  ,,  (k1 , A)) 


∈D : {A : Form} → {Γ : Ctx} → (A ∈ dda A Γ)
∈D {A} {·} = ∈Z
∈D {A} {Γ ,, B} = ∈S (∈D {A} {Γ})

∈A : {A B : Form} → {Γ : Ctx} → (A ∈ Γ) → (A ∈ dda B Γ)
∈A ∈Z = ∈Z
∈A (∈S i) = ∈S (∈A i)

∈M : {A : Form} → {Γ Γ' : Ctx} → (A ∈ (conc (Γ ,, A) Γ'))
∈M {A} {Γ} {·} = ∈Z
∈M {A} {Γ} {Γ' ,, B} = ∈S ∈M

∈M' : {A : Form} → {Γ Γ' : Ctx} → (A ∈ (conc Γ (dda A Γ')))
∈M' {A} {Γ} {·} = ∈Z
∈M' {A} {Γ} {Γ' ,, B} = ∈S (∈M' {A} {Γ} {Γ'})

≡M : {A : Form} → {Γ Γ' : Ctx} → (conc (Γ ,, A) Γ' ≡ conc Γ (dda A Γ'))
≡M {Γ' = ·} = refl
≡M {Γ' = Γ' ,, A} = cong (λ z → z ,, A) ≡M


data PopSeq : Ctx → Ctx → Set where
  End : {Γ : Ctx} → PopSeq Γ Γ
  Nex : {Γ Γ' : Ctx} → {M : Modal} → {A : Form} → Yes (ModQ M) → sMod M A ∈ Γ → PopSeq (Γ ,, A) Γ' → PopSeq Γ Γ'

AllPopSeq : {Γ Γ' : Ctx} → PopSeq (conc Γ Γ') (AllPop Γ Γ')
AllPopSeq {·} {Γ'} rewrite ·conc {Γ'} = End {Γ'}
AllPopSeq {Γ ,, (k , atom p)} {Γ'} rewrite ≡M {k , atom p} {Γ} {Γ'} = AllPopSeq {Γ} {dda (k , atom p) Γ'}
AllPopSeq  {Γ ,, (k , (B f⇒ C))} {Γ'} rewrite ≡M {k , (B f⇒ C)} {Γ} {Γ'} = AllPopSeq {Γ} {dda (k , (B f⇒ C)) Γ'}
AllPopSeq  {Γ ,, (k , (B f∧ C))} {Γ'} rewrite ≡M {k , (B f∧ C)} {Γ} {Γ'} = AllPopSeq {Γ} {dda (k ,  (B f∧ C)) Γ'}
AllPopSeq  {Γ ,, (k , (B f∨ C))} {Γ'} rewrite ≡M {k , (B f∨ C)} {Γ} {Γ'} = AllPopSeq {Γ} {dda (k ,  (B f∨ C)) Γ'}
AllPopSeq  {Γ ,, (k , f⊤)} {Γ'} rewrite ≡M {k , f⊤} {Γ} {Γ'} = AllPopSeq {Γ} {dda (k , f⊤) Γ'}
AllPopSeq  {Γ ,, (k , f⊥)} {Γ'} rewrite ≡M {k , f⊥} {Γ} {Γ'} = AllPopSeq {Γ} {dda (k , f⊥) Γ'}
AllPopSeq  {Γ ,, (step k1 , fMod M B)} {Γ'} with BI (ModQ M)
... | inj₁ eq rewrite eq | ≡M {step k1 , fMod M B} {Γ} {Γ'} = AllPopSeq {Γ} {dda (step k1 , fMod M B) Γ'}
... | inj₂ eq rewrite eq | ≡M {step k1 , fMod M B} {Γ} {Γ'} = Nex {M = M} eq (∈M' {step k1 , fMod M B} {Γ} {Γ'}) (AllPopSeq {Γ} {dda (step k1 , fMod M B) (Γ' ,, (k1 , B))})

--NextPop : (Γ Γ' : Ctx) → (AllPop Γ Γ' ≡ conc Γ Γ') ⊎ (Σ Modal λ M → Σ Form λ A → (Yes (ModQ M) × (Mod M A ∈ Γ) ×   ))



∈AlpR : {A : Form} → {Γ Γ' : Ctx} → (A ∈ Γ') → (A ∈ AllPop Γ Γ')
∈AlpR {A} {·} {Γ'} i = i
∈AlpR {A} {Γ ,, (k , atom p)} {Γ'} i = ∈AlpR {Γ = Γ} (∈A i)
∈AlpR {A} {Γ ,, (k , (B f⇒ C))} {Γ'} i = ∈AlpR {Γ = Γ} (∈A i)
∈AlpR {A} {Γ ,, (k , (B f∧ C))} {Γ'} i = ∈AlpR {Γ = Γ} (∈A i)
∈AlpR {A} {Γ ,, (k , (B f∨ C))} {Γ'} i = ∈AlpR {Γ = Γ} (∈A i)
∈AlpR {A} {Γ ,, (k , f⊤)} {Γ'} i = ∈AlpR {Γ = Γ} (∈A i)
∈AlpR {A} {Γ ,, (k , f⊥)} {Γ'} i = ∈AlpR {Γ = Γ} (∈A i)
∈AlpR {A} {Γ ,, (step k1 , fMod M B)} {Γ'} i with ModQ M
... | false = ∈AlpR {Γ = Γ} (∈A i)
... | true = (∈AlpR {Γ = Γ} (∈S (∈A i)))

∈AlpL : {A : Form} → {Γ Γ' : Ctx} → (A ∈ Γ) → (A ∈ AllPop Γ Γ')
∈AlpL {A} {Γ ,, (k , atom p)} {Γ'} ∈Z = ∈AlpR {Γ = Γ} ∈D
∈AlpL {A} {Γ ,, (k , (B f⇒ C))} {Γ'}  ∈Z = ∈AlpR {Γ = Γ} ∈D
∈AlpL {A} {Γ ,, (k , (B f∧ C))} {Γ'}  ∈Z = ∈AlpR {Γ = Γ} ∈D
∈AlpL {A} {Γ ,, (k , (B f∨ C))} {Γ'}  ∈Z = ∈AlpR {Γ = Γ} ∈D
∈AlpL {A} {Γ ,, (k , f⊤)} {Γ'}  ∈Z = ∈AlpR {Γ = Γ} ∈D
∈AlpL {A} {Γ ,, (k , f⊥)} {Γ'}  ∈Z = ∈AlpR {Γ = Γ} ∈D
∈AlpL {A} {Γ ,, (step k1 , fMod M B)} {Γ'} ∈Z with ModQ M
... | false =  ∈AlpR {Γ = Γ} ∈D
... | true =  (∈AlpR {Γ = Γ} (∈D {Γ = Γ' ,, _ }))
∈AlpL {A} {Γ ,, (k , atom p)} {Γ'} (∈S i) = ∈AlpL {Γ = Γ} i
∈AlpL {A} {Γ ,, (k , (B f⇒ C))} {Γ'}  (∈S i) = ∈AlpL {Γ = Γ} i
∈AlpL {A} {Γ ,, (k , (B f∧ C))} {Γ'}  (∈S i) = ∈AlpL {Γ = Γ} i
∈AlpL {A} {Γ ,, (k , (B f∨ C))} {Γ'}  (∈S i) = ∈AlpL {Γ = Γ} i
∈AlpL {A} {Γ ,, (k , f⊤)} {Γ'}  (∈S i) = ∈AlpL {Γ = Γ} i
∈AlpL {A} {Γ ,, (k , f⊥)} {Γ'}  (∈S i) = ∈AlpL {Γ = Γ} i
∈AlpL {A} {Γ ,, (step k1 , fMod M B)} {Γ'} (∈S i) with ModQ M
... | false =  ∈AlpL {Γ = Γ} i
... | true =  (∈AlpL {Γ = Γ} i)

∈AlpM : Yes (ModQ M) → sMod M A ∈ Γ → A ∈ AllPop Γ Δ
∈AlpM {M} {A} {Γ ,, (k , atom x)} q (∈S i) = ∈AlpM {M} {A} {Γ} q i
∈AlpM {M} {A} {Γ ,, (k , (B f⇒ C))} q (∈S i) = ∈AlpM {M} {A} {Γ} q i
∈AlpM {M} {A} {Γ ,, (k , (B f∧ C))} q (∈S i) = ∈AlpM {M} {A} {Γ} q i
∈AlpM {M} {A} {Γ ,, (k , (B f∨ C))} q (∈S i) = ∈AlpM {M} {A} {Γ} q i
∈AlpM {M} {A} {Γ ,, (k , f⊤)} q (∈S i) = ∈AlpM {M} {A} {Γ} q i
∈AlpM {M} {A} {Γ ,, (k , f⊥)} q (∈S i) = ∈AlpM {M} {A} {Γ} q i
∈AlpM {M} {k1 , A} {Γ ,, (step k1 , fMod M A)} M◂ ∈Z rewrite M◂ = ∈AlpR {k1 , A} {Γ} {dda _ _ ,, (k1 , A)} ∈Z 
∈AlpM {M} {A} {Γ ,, (step k1 , fMod N B)} M◂ (∈S i) with ModQ N
... | false =  ∈AlpM {M} {A} {Γ} M◂ i
... | true =  ∈AlpM {M} {A} {Γ} M◂ i

⊆Alp : Γ ⊆ AllPop Γ ·
⊆Alp i = ∈AlpL i

APS : Yes (ModQ M) → Γ ⊆ Δ → Shift M Γ ⊑ AllPop Δ · 
APS {M} {Γ ,, (k , atom x)} q Γ⊆Δ i = APS {M} {Γ} q (λ i → Γ⊆Δ (∈S i) ) i
APS {M} {Γ ,, (k , (A f⇒ B))} q Γ⊆Δ i =  APS {M} {Γ} q (λ i → Γ⊆Δ (∈S i) ) i
APS {M} {Γ ,, (k , (A f∧ B))} q Γ⊆Δ i =  APS {M} {Γ} q (λ i → Γ⊆Δ (∈S i) ) i
APS {M} {Γ ,, (k , (A f∨ B))}  q Γ⊆Δ i =  APS {M} {Γ} q (λ i → Γ⊆Δ (∈S i) ) i
APS {M} {Γ ,, (k , f⊤)} {Δ}  q Γ⊆Δ i =  APS {M} {Γ} q (λ i → Γ⊆Δ (∈S i) ) i
APS {M} {Γ ,, (k , f⊥)} {Δ} q Γ⊆Δ i =  APS {M} {Γ} q (λ i → Γ⊆Δ (∈S i) ) i
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i with BI (ModR N M) | MI N M
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i | inj₁ N◃M | inj₁ N□M rewrite N◃M | N□M = APS {M} {Γ} {Δ} M◂ (λ t → Γ⊆Δ (∈S t)) i
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i | inj₁ N◃M | inj₂ (R , N■M) rewrite N◃M | N■M with i
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i | inj₁ N◃M | inj₂ (R , N■M) | ∈Z = inj₂ ((R , N , k1 , A) , refl , MProp.MDipL MP N■M M◂  , ∈AlpL (Γ⊆Δ ∈Z))
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i | inj₁ N◃M | inj₂ (R , N■M) | ∈S j =  APS {M} {Γ} {Δ} M◂ (λ t → Γ⊆Δ (∈S t)) j
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i | inj₂ N◂M | inj₁ N□M rewrite N◂M | N□M with i
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i | inj₂ N◂M | inj₁ N□M | ∈Z = inj₁ (∈AlpM {N} {k1 , A} {Δ} {·} (MProp.MZip MP N◂M M◂) (Γ⊆Δ ∈Z))
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i | inj₂ N◂M | inj₁ N□M | ∈S j =  APS {M} {Γ} {Δ} M◂ (λ t → Γ⊆Δ (∈S t)) j
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i | inj₂ N◂M | inj₂ (R , N■M) rewrite N◂M | N■M with i
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i | inj₂ N◂M | inj₂ (R , N■M) | ∈Z =  inj₁ (∈AlpM {N} {k1 , A} {Δ} {·} (MProp.MZip MP N◂M M◂) (Γ⊆Δ ∈Z))
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i | inj₂ N◂M | inj₂ (R , N■M) | ∈S ∈Z =  inj₂ ((R , N , k1 , A) , refl , MProp.MDipL MP N■M M◂  , ∈AlpL (Γ⊆Δ ∈Z))
APS {M} {Γ ,, (step k1 , fMod N A)} {Δ} M◂ Γ⊆Δ i | inj₂ N◂M | inj₂ (R , N■M) | ∈S (∈S j) = APS {M} {Γ} {Δ} M◂ (λ t → Γ⊆Δ (∈S t)) j
