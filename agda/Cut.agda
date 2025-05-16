open import Modal

module Cut (Atom : Set) (Modal : Set) (ModR : ERel Modal) (ModS : Split Modal) (ModQ : DProp Modal) (MP : MProp ModR ModS ModQ) where


open import Formula Atom Modal
open import Ctx Atom Modal ModR ModS ModQ MP
open import Sequent Atom Modal ModR ModS ModQ MP

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Relation.Binary.PropositionalEquality


private
  variable
    P : Atom
    A B C D : Form
    Γ Δ : Ctx
    m n k : Size
    M N S : Modal


-- Cut elimination is forced to do an initial case distinction of size on formula to be cut
-- This is only to satisfy Agda's termination checker, and duplicates lots of cases.
-- Perhaps another solution is possible, but so be it.

-- cut elimination on all formulas
cut : (k m n : Size) →  {A' : Forms k} → {Γ : Ctx} → {B : Form}
  → Γ ⊢ (k , A') ^ m
  →   Γ ,, (k , A') ⊢ B ^ n
  → ∃ λ q → Γ ⊢ B ^ q
  
-- cut elimination on formulas with no premises, that is: atomic, top and bottom
cuti : (m n : Size) →  {A' : Forms init} → {Γ : Ctx} → {B : Form}
  → Γ ⊢ (init , A') ^ m
  →   Γ ,, (init , A') ⊢ B ^ n
  → ∃ λ q → Γ ⊢ B ^ q

-- cut elimination on formulas with a single premise, that is: modal
cuts : (k m n : Size) →  {A' : Forms (step k)} → {Γ : Ctx} → {B : Form}
  → Γ ⊢ (step k , A') ^ m
  →   Γ ,, (step k , A') ⊢ B ^ n
  → ∃ λ q → Γ ⊢ B ^ q

-- cut elimination on formulas with two premises, that is: conjunctions, disjunctions and implications
cutf : (k k' m n : Size) →  {A' : Forms (fork k k')} → {Γ : Ctx} → {B : Form}
  → Γ ⊢ (fork k k' , A') ^ m
  →   Γ ,, (fork k k' , A') ⊢ B ^ n
  → ∃ λ q → Γ ⊢ B ^ q

-- case distinction on size of formula
cut init m n D E = cuti m n D E
cut (step k) m n D E = cuts k m n D E
cut (fork k k₁) m n D E = cutf k k₁ m n D E

-- ==============================
-- initialisers
-- ==============================
cuti init n (Var i) pE = _ , weak (λ { ∈Z → i ; (∈S j) → j}) pE
cuti m init pD (Var ∈Z) = _ , pD
cuti m init pD (Var (∈S i)) = _ , Var i
-- ==============================
-- Left + Any
-- ==============================
cuti (fork m1 m2) n (⇒L i D1 D2) E =
  let (v , F1) = cuti m2 n D2 (weak1 E) in
  fork m1 v , ⇒L i D1 F1
cuti (step m1) n (∧L1 i D1) E =
  let (v1 , F1) = cuti m1 n D1 (weak1 E) in
  step v1 , ∧L1 i F1
cuti (step m1) n (∧L2 i D1) E = 
  let (v1 , F1) = cuti m1 n D1 (weak1 E) in
  step v1 , ∧L2 i F1
cuti (fork m1 m2) n (∨L i D1 D2) E =
  let (v1 , F1) = cuti m1 n D1 (weak1 E) in
  let (v2 , F2) = cuti m2 n D2 (weak1 E) in
  fork v1 v2 , ∨L i F1 F2
cuti init n (⊥L i) E = init , ⊥L i
cuti (step m1) n (Pop M◂ i D1) E =
  let (v1 , F1) = cuti m1 n D1 (weak1 E) in
  step v1 , Pop M◂ i F1
-- ==============================
-- Any  + Right
-- ==============================
cuti m (step n1) D (⇒R E1) =
  let (v1 , F1) = cuti m n1 (weak0 D) (exch E1) in
  step v1 , ⇒R F1
cuti m (fork n1 n2) D (∧R E1 E2) =
  let (v1 , F1) = cuti m n1 D E1 in
  let (v2 , F2) = cuti m n2 D E2 in
  fork v1 v2 , ∧R F1 F2
cuti m (step n1) D (∨R1 E1) =
  let (v1 , F1) = cuti m n1 D E1 in
  step v1 , ∨R1 F1
cuti m (step n1) D (∨R2 E1) =
  let (v1 , F1) = cuti m n1 D E1 in
  step v1 , ∨R2 F1
cuti m init D ⊤R = init , ⊤R
-- =============================
-- Right + Left (non-principal)
-- =============================
-- ⇒ Left
cuti m@init (fork n1 n2) D@⊤R (⇒L (∈S i) E1 E2) =
  let (v1 , F1) = cuti init n1 D E1 in
  let (v2 , F2) = cuti init n2 (weak0 D) (exch E2) in
  fork v1 v2 , ⇒L i F1 F2
-- ∧ Left 1
cuti m@init (step n1) D@⊤R (∧L1 (∈S i) E1) =
  let (v1 , F1) = cuti init n1 (weak0 D) (exch E1) in
  step v1 , ∧L1 i F1
-- ∧ Left 2
cuti m@init (step n1) D@⊤R (∧L2 (∈S i) E1) =
  let (v1 , F1) = cuti init n1 (weak0 D) (exch E1) in
  step v1 , ∧L2 i F1
-- ∨ Left
cuti m@init (fork n1 n2) D@⊤R (∨L (∈S i) E1 E2) =
  let (v1 , F1) = cuti m n1 (weak0 D) (exch E1) in
  let (v2 , F2) = cuti m n2 (weak0 D) (exch E2) in
  fork v1 v2 , ∨L i F1 F2 
-- ⊥ Left
cuti m@init init D@⊤R (⊥L (∈S i)) = init , ⊥L i
-- Mod (Left)
cuti m@init (step n1) ⊤R (Mod E1) = step n1 , Mod E1
-- Pop
cuti m@init (step n1) D@⊤R (Pop M◂ (∈S i) E1) =
  let (v1 , F1) = cuti m n1 (weak0 D) (exch E1) in
  step v1 , Pop M◂ i F1 
-- ==============================
-- Right + Left (principal)
-- ==============================


-- ==============================
-- initialisers
-- ==============================
cuts k m init pD (Var (∈S i)) = _ , Var i
-- ==============================
-- Left + Any
-- ==============================
cuts k (fork m1 m2) n (⇒L i D1 D2) E =
  let (v , F1) = cuts k m2 n D2 (weak1 E) in
  fork m1 v , ⇒L i D1 F1
cuts k (step m1) n (∧L1 i D1) E =
  let (v1 , F1) = cuts k m1 n D1 (weak1 E) in
  step v1 , ∧L1 i F1
cuts k (step m1) n (∧L2 i D1) E = 
  let (v1 , F1) = cuts k m1 n D1 (weak1 E) in
  step v1 , ∧L2 i F1
cuts k (fork m1 m2) n (∨L i D1 D2) E =
  let (v1 , F1) = cuts k m1 n D1 (weak1 E) in
  let (v2 , F2) = cuts k m2 n D2 (weak1 E) in
  fork v1 v2 , ∨L i F1 F2
cuts k init n (⊥L i) E = init , ⊥L i
cuts k (step m1) n (Pop M◂ i D1) E =
  let (v1 , F1) = cuts k m1 n D1 (weak1 E) in
  step v1 , Pop M◂ i F1
-- ==============================
-- Any  + Right
-- ==============================
cuts k m (step n1) D (⇒R E1) =
  let (v1 , F1) = cuts k m n1 (weak0 D) (exch E1) in
  step v1 , ⇒R F1
cuts k m (fork n1 n2) D (∧R E1 E2) =
  let (v1 , F1) = cuts k m n1 D E1 in
  let (v2 , F2) = cuts k m n2 D E2 in
  fork v1 v2 , ∧R F1 F2
cuts k m (step n1) D (∨R1 E1) =
  let (v1 , F1) = cuts k m n1 D E1 in
  step v1 , ∨R1 F1
cuts k m (step n1) D (∨R2 E1) =
  let (v1 , F1) = cuts k m n1 D E1 in
  step v1 , ∨R2 F1
cuts k m init D ⊤R = init , ⊤R
-- =============================
-- Right + Left (non-principal)
-- =============================
-- ⇒ Left
cuts k m@(step m1) (fork n1 n2) D@(Mod D1) (⇒L (∈S i) E1 E2) =
  let (v1 , F1) = cuts k m n1 D E1 in
  let (v2 , F2) = cuts k m n2 (weak0 D) (exch E2) in
  fork v1 v2 , ⇒L i F1 F2
-- ∧ Left 1
cuts k m@(step m1) (step n1) D@(Mod D1) (∧L1 (∈S i) E1) =
  let (v1 , F1) = cuts k m n1 (weak0 D) (exch E1) in
  step v1 , ∧L1 i F1
-- ∧ Left 2
cuts k m@(step m1) (step n1) D@(Mod D1) (∧L2 (∈S i) E1) =
  let (v1 , F1) = cuts k m n1 (weak0 D) (exch E1) in
  step v1 , ∧L2 i F1
-- ∨ Left
cuts k m@(step m1) (fork n1 n2) D@(Mod D1) (∨L (∈S i) E1 E2) =
  let (v1 , F1) = cuts k m n1 (weak0 D) (exch E1) in
  let (v2 , F2) = cuts k m n2 (weak0 D) (exch E2) in
  fork v1 v2 , ∨L i F1 F2 
-- ⊥ Left
cuts k m@(step m1) init D@(Mod D1) (⊥L (∈S i)) = init , ⊥L i
-- Mod (Left)
-- Pop
cuts k m@(step m1) (step n1) D@(Mod D1) (Pop M◂ (∈S i) E1) =
  let (v1 , F1) = cuts k m n1 (weak0 D) (exch E1) in
  step v1 , Pop M◂ i F1
-- ==============================
-- Right + Left (principal)
-- ==============================
cuts k m@(step m1) n@(step n1) (Mod {M} D1) (Mod {N} {Γ ,, (step k , fMod M A')} E1) with BI (ModR M N)
cuts k m@(step m1) n@(step n1) (Mod {M} D1) (Mod {N} {Γ ,, (step k , fMod M A')} E1) | inj₁ M◃N rewrite M◃N with MI M N
cuts k m@(step m1) n@(step n1) (Mod {M} D1) (Mod {N} {Γ ,, (step k , fMod M A')} E1) | inj₁ M◃N | inj₁ M□N rewrite M□N = n , Mod E1
cuts k m@(step m1) n@(step n1) D@(Mod {M} D1) (Mod {N} {Γ ,, (step k , fMod M A')} E1) | inj₁ M◃N | inj₂ (M-N , M■N) rewrite M■N = 
  let (v1 , F1) = cuts k m n1 ( Mod (veak (Shift■ M■N Γ) D1)) E1 in step v1 , Mod {N} F1
cuts k m@(step m1) n@(step n1) (Mod {M} D1) (Mod {N} {Γ ,, (step k , fMod M A')} E1) | inj₂ M◂N rewrite M◂N with MI M N
cuts k m@(step m1) n@(step n1) (Mod {M} D1) (Mod {N} {Γ ,, (step k , fMod M A')} E1) | inj₂ M◂N | inj₁ M□N rewrite M□N =
  let (v1 , F1) = cut k m1 n1 (veak (Shift◂ M◂N Γ) D1) E1 in
  step v1 , Mod F1
cuts k m@(step m1) n@(step n1) (Mod {M} D1) (Mod {N} {Γ ,, (step k , fMod M A)} E1) | inj₂ M◂N | inj₂ (M-N , M■N) rewrite M■N =
  let (v1 , F1) = cuts k m n1 (weak (λ x → ∈S x) (Mod (veak (Shift■ M■N Γ) D1))) (exch E1) in
  let (v2 , F2) = cut k m1 v1 (veak (Shift◂ M◂N Γ) D1) F1 in
  step v2 , Mod F2
cuts k m@(step m1) n@(step n1) D@(Mod {M} D1) (Pop {M} {k , A} {Γ ,, (step k , fMod M A)} M◂ ∈Z E1) =
  let (v1 , F1) = cuts k m n1 (weak0 D) (exch E1) in
  let (v2 , F2) = qeak {M} {Γ} {k , A} {m1} M◂ D1 in
  cut k v2 v1 {A} {Γ} F2 F1

-- ==============================
-- initialisers
-- ==============================
cutf k k' m init pD (Var (∈S i)) = _ , Var i
-- ==============================
-- Left + Any
-- ==============================
cutf k k' (fork m1 m2) n (⇒L i D1 D2) E =
  let (v , F1) = cutf k k' m2 n D2 (weak1 E) in
  fork m1 v , ⇒L i D1 F1
cutf k k' (step m1) n (∧L1 i D1) E =
  let (v1 , F1) = cutf k k' m1 n D1 (weak1 E) in
  step v1 , ∧L1 i F1
cutf k k' (step m1) n (∧L2 i D1) E = 
  let (v1 , F1) = cutf k k' m1 n D1 (weak1 E) in
  step v1 , ∧L2 i F1
cutf k k' (fork m1 m2) n (∨L i D1 D2) E =
  let (v1 , F1) = cutf k k' m1 n D1 (weak1 E) in
  let (v2 , F2) = cutf k k' m2 n D2 (weak1 E) in
  fork v1 v2 , ∨L i F1 F2
cutf k k' init n (⊥L i) E = init , ⊥L i
cutf k k' (step m1) n (Pop M◂ i D1) E =
  let (v1 , F1) = cutf k k' m1 n D1 (weak1 E) in
  step v1 , Pop M◂ i F1
-- ==============================
-- Any  + Right
-- ==============================
cutf k k' m (step n1) D (⇒R E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , ⇒R F1
cutf k k' m (fork n1 n2) D (∧R E1 E2) =
  let (v1 , F1) = cutf k k' m n1 D E1 in
  let (v2 , F2) = cutf k k' m n2 D E2 in
  fork v1 v2 , ∧R F1 F2
cutf k k' m (step n1) D (∨R1 E1) =
  let (v1 , F1) = cutf k k' m n1 D E1 in
  step v1 , ∨R1 F1
cutf k k' m (step n1) D (∨R2 E1) =
  let (v1 , F1) = cutf k k' m n1 D E1 in
  step v1 , ∨R2 F1
cutf k k' m init D ⊤R = init , ⊤R
-- =============================
-- Right + Left (non-principal)
-- =============================
-- ⇒ Left
cutf k k' m@(step m1) (fork n1 n2) D@(⇒R D1) (⇒L (∈S i) E1 E2) =
  let (v1 , F1) = cutf k k' m n1 D E1 in
  let (v2 , F2) = cutf k k' m n2 (weak0 D) (exch E2) in
  fork v1 v2 , ⇒L i F1 F2
cutf k k' m@(fork m1 m2) (fork n1 n2) D@(∧R D1 D2) (⇒L (∈S i) E1 E2) =
  let (v1 , F1) = cutf k k' m n1 D E1 in
  let (v2 , F2) = cutf k k' m n2 (weak0 D) (exch E2) in
  fork v1 v2 , ⇒L i F1 F2
cutf k k' m@(step m1) (fork n1 n2) D@(∨R1 D1) (⇒L (∈S i) E1 E2) =
  let (v1 , F1) = cutf k k' m n1 D E1 in
  let (v2 , F2) = cutf k k' m n2 (weak0 D) (exch E2) in
  fork v1 v2 , ⇒L i F1 F2
cutf k k' m@(step m1) (fork n1 n2) D@(∨R2 D1) (⇒L (∈S i) E1 E2) =
  let (v1 , F1) = cutf k k' m n1 D E1 in
  let (v2 , F2) = cutf k k' m n2 (weak0 D) (exch E2) in
  fork v1 v2 , ⇒L i F1 F2
-- ∧ Left 1
cutf k k' m@(step m1) (step n1) D@(⇒R D1) (∧L1 (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , ∧L1 i F1
cutf k k' m@(fork m1 m2) (step n1) D@(∧R D1 D2) (∧L1 (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , ∧L1 i F1
cutf k k' m@(step m1) (step n1) D@(∨R1 D1) (∧L1 (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , ∧L1 i F1
cutf k k' m@(step m1) (step n1) D@(∨R2 D1) (∧L1 (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , ∧L1 i F1
-- ∧ Left 2
cutf k k' m@(step m1) (step n1) D@(⇒R D1) (∧L2 (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , ∧L2 i F1
cutf k k' m@(fork m1 n2) (step n1) D@(∧R D1 D2) (∧L2 (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , ∧L2 i F1
cutf k k' m@(step m1) (step n1) D@(∨R1 D1) (∧L2 (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , ∧L2 i F1
cutf k k' m@(step m1) (step n1) D@(∨R2 D1) (∧L2 (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , ∧L2 i F1
-- ∨ Left
cutf k k' m@(step m1) (fork n1 n2) D@(⇒R D1) (∨L (∈S i) E1 E2) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  let (v2 , F2) = cutf k k' m n2 (weak0 D) (exch E2) in
  fork v1 v2 , ∨L i F1 F2 
cutf k k' m@(fork m1 m2) (fork n1 n2) D@(∧R D1 D2) (∨L (∈S i) E1 E2) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  let (v2 , F2) = cutf k k' m n2 (weak0 D) (exch E2) in
  fork v1 v2 , ∨L i F1 F2 
cutf k k' m@(step m1) (fork n1 n2) D@(∨R1 D1) (∨L (∈S i) E1 E2) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  let (v2 , F2) = cutf k k' m n2 (weak0 D) (exch E2) in
  fork v1 v2 , ∨L i F1 F2 
cutf k k' m@(step m1) (fork n1 n2) D@(∨R2 D1) (∨L (∈S i) E1 E2) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  let (v2 , F2) = cutf k k' m n2 (weak0 D) (exch E2) in
  fork v1 v2 , ∨L i F1 F2 
-- ⊥ Left
cutf k k' m@(step m1) init D@(⇒R D1) (⊥L (∈S i)) = init , ⊥L i
cutf k k' m@(fork m1 m2) init D@(∧R D1 D2) (⊥L (∈S i)) = init , ⊥L i
cutf k k' m@(step m1) init D@(∨R1 D1) (⊥L (∈S i)) = init , ⊥L i
cutf k k' m@(step m1) init D@(∨R2 D1) (⊥L (∈S i)) = init , ⊥L i
-- Mod (Left)
cutf k k' m@(step m1) (step n1) (⇒R D1) (Mod E1) = step n1 , Mod E1
cutf k k' m@(step m1) (step n1) (∨R1 D1) (Mod E1) = step n1 , Mod E1
cutf k k' m@(step m1) (step n1) (∨R2 D1) (Mod E1) = step n1 , Mod E1
cutf k k' m@(fork m1 m2) (step n1) (∧R D1 D2) (Mod E1) = step n1 , Mod E1
-- Pop
cutf k k' m@(step m1) (step n1) D@(⇒R D1) (Pop M◂ (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , Pop M◂ i F1 
cutf k k' m@(fork m1 m2) (step n1) D@(∧R D1 D2) (Pop M◂ (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , Pop M◂ i F1
cutf k k' m@(step m1) (step n1) D@(∨R1 D1) (Pop M◂ (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , Pop M◂ i F1
cutf k k' m@(step m1) (step n1) D@(∨R2 D1) (Pop M◂ (∈S i) E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  step v1 , Pop M◂ i F1
-- ==============================
-- Right + Left (principal)
-- ==============================
cutf k k' m@(step m1) (fork n1 n2) D@(⇒R D1) (⇒L ∈Z E1 E2) =
  let (v1 , F1) = cutf k k' m n1 D E1 in
  let (v2 , F2) = cut k v1 m1 F1 D1 in
  let (v3 , F3) = cutf k k' m n2 (weak0 D) (exch E2) in
  cut k' v2 v3 F2 F3
cutf k k' m@(fork m1 m2) (step n1) D@(∧R D1 D2) (∧L1 ∈Z E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  cut k m1 v1 D1 F1
cutf k k' m@(fork m1 m2) (step n1) D@(∧R D1 D2) (∧L2 ∈Z E1) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  cut k' m2 v1 D2 F1
cutf k k' m@(step m1) (fork n1 n2) D@(∨R1 D1) (∨L ∈Z E1 E2) =
  let (v1 , F1) = cutf k k' m n1 (weak0 D) (exch E1) in
  cut k m1 v1 D1 F1
cutf k k' m@(step m1) (fork n1 n2) D@(∨R2 D1) (∨L ∈Z E1 E2) =
  let (v1 , F1) = cutf k k' m n2 (weak0 D) (exch E2) in
  cut k' m1 v1 D1 F1
