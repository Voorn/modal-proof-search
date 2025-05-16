module Formula (Atom : Set) (Modal : Set) where

open import Data.Product

infixr 100 _f⇒_
infixr 100 _f∧_
infixr 100 _f∨_

infixr 100 _s⇒_
infixr 100 _s∧_
infixr 100 _s∨_

data Size : Set where
  init : Size
  step : Size → Size
  fork : Size → Size → Size


private
  variable
    m n : Size

data Forms : Size → Set where
  atom : Atom → Forms init
  _f⇒_ : Forms m → Forms n → Forms (fork m n)
  _f∧_ : Forms m → Forms n → Forms (fork m n)
  _f∨_ : Forms m → Forms n → Forms (fork m n)
  f⊤ : Forms init 
  f⊥ : Forms init 
  fMod : Modal → Forms m → Forms (step m)

Form : Set
Form = Σ Size λ k → Forms k

sato : Atom → Form
sato p = (init , atom p)

_s⇒_ : Form → Form → Form
(m , A) s⇒ (n , B) = (fork m n) , (A f⇒ B)

_s∧_ : Form → Form → Form
(m , A) s∧ (n , B) = (fork m n) , (A f∧ B)

_s∨_ : Form → Form → Form
(m , A) s∨ (n , B) = (fork m n) , (A f∨ B)

s⊤ : Form
s⊤ = (init , f⊤)

s⊥ : Form
s⊥ = (init , f⊥)

sMod : Modal → Form → Form
sMod M (m , A) = (step m , fMod M A)
