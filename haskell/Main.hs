module Main where

import MForm
import MExample

basic :: String -> MForm Flat
basic = Ba

main :: IO ()

-- Uncomment a "main" line to run example. 
-- Alternatively, make your own example. 
-- Make list of (Formula , Boolean), Boolean designates whether you want to assume the formula (True) or want to prove it (False)
-- The following asks: A∨B , A⇒B ⊢ B 
--main = drunner [(Or [basic "A" , basic "B"] , True) , (Im (basic "A") (basic "B") , True) , (basic "B" , False) ]

-- ==========================================
-- Non-modal conjunction disjunction examples
-- ==========================================

-- Alex = (A∨B)∧(B∨C)∧(C∨A) , Bertha = (A∧B)∨(B∧C)∨(C∧A), from one you can derive the other
--main = drunner testbag23

-- (A∧B)∨(B∧C)∨(C∧A))⇔((A∨B)∧(B∨C)∧(C∨A)))
--main = drunner testbagIff23

-- From basic formulas A,B,C,D,E, each subset of three is associated to a name, either via conjunction or disjunction. Derive all dependencies.
--main = drunner testbagNames 

-- Stress test: (A∧B∧C)∨(A∧B∧D)∨(A∧B∧E)∨(A∧C∧D)∨(A∧C∧E)∨(A∧D∧E)∨(B∧C∧D)∨(B∧C∧E)∨(B∧D∧E)∨(C∧D∧E)⇔(A∨B∨C)∧(A∨B∨D)∧(A∨B∨E)∧(A∨C∨D)∧(A∨C∨E)∧(A∨D∨E)∧(B∨C∨D)∧(B∨C∨E)∧(B∨D∨E)∧(C∨D∨E)
--main = drunner testbagIff35 


-- ==========================================
-- Non-modal multiple implications examples
-- ==========================================

-- 8 programmers verify different sections of a code. Here A represents correct input, and E represents correct output. B,C,D are correct intermediate states.
--main = drunner testbagComp 

-- Stress test: All basic implication between A,B,C,D,E
--main = drunner testbagImp 

-- ==========================================
-- Non-modal negation formulas
-- ==========================================

-- (A∧B) ⊢ ¬(¬A∨¬B)
--main = drunner  [(An [basic "A" , basic "B"] , True) , (notF (Or [notF (basic "A") , notF (basic "B")]) , False)]

-- (¬¬¬A⇒¬A) 
--main = drunner [(Im (notF (notF (notF (basic "A")))) (notF (basic "A")) , False)]

-- (A∨¬A) and ¬¬(A∨¬A)
main = drunner  [(Or [basic "A" , notF (basic "A")] , False) , (notF (notF (Or [basic "A" , notF (basic "A")])) , False)]

-- =========================
-- Necessity (Box) examples
-- =========================

-- ☐(☐(A)) as assumption and question
--main = drunner testbagBoxA 

-- Generating from ☐(A) a large composite statement
--main = drunner testbagBBB 


-- ==========================
-- Basic Multimodal K + N
-- ==========================

-- Assuming and deriving: M(A)∧M(B), M(A)∨M(B), M(A∧B), M(A∨B)
--main = drunner testbagOne 

-- Simple check for Necessity: ⊢ M((X⇒X))
--main = drunner testbagNecc 


-- ================================
-- Communication and Trust examples
-- ================================

-- Validity composes
--main = drunner testbagValid 

-- Validity composes 2
--main = drunner testbagValidimp 

-- Trust composes
--main = drunner testbagTrust 
--main = drunner testbagTrustimp  

-- Stress test (takes a long time): Trust double composition
--main = drunner testbagTrust2 


-- ================================
-- Lattice of modalities
-- ================================

-- We have three sources: a , b , c, contributing different pieces of evidence. 
-- We combine into a: 2-out-of-3 sources composite modality, to verify that result is correct even if one source is faulty.
--main = drunner testbagSourcesCont 

-- We show that the 2-out-of-3 sources composite modality satisfies axiom K
--main = drunner testbagSourcesComp 

