{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use >=>" #-}
{-# HLINT ignore "Use forM_" #-}
module MLambda where

import Modal
import MForm

import Control.Monad


data Concon m =
    Cfor (MForm m)
    |   Cmod m
    deriving Show

type MCont m = [Concon m]

flatC :: [MForm m] -> MCont m
flatC = fmap Cfor

listLook :: [a] -> Int -> Maybe a
listLook [] i            = Nothing
listLook (a : l) i
    |   i <= 0          =   Just a
    |   otherwise       =   listLook l (i-1)

listAll :: [Maybe a] -> Maybe [a]
listAll [] = Just []
listAll (Nothing : l) = Nothing
listAll (Just a : l) = fmap (a :) (listAll l)

listZip :: (a -> b -> Maybe c) -> [a] -> [b] -> Maybe [c]
listZip f [] [] = Just []
listZip f (a : l) (b : r) =  f a b >>= \c ->  fmap (c :) (listZip f l r)
listZip f l r = Nothing

listCling :: Eq c => (a -> b -> Maybe c) -> c -> [a] -> [b] -> Bool
listCling f c [] [] = True
listCling f c (a : l) (b : r) = case f a b of
    Just c'     ->  c == c' && listCling f c l r
    Nothing     ->  False
listCling f c l r = False

extAn :: MForm m -> Maybe [MForm m]
extAn (An l) = Just l
extAn a = Nothing

extOr :: MForm m -> Maybe [MForm m]
extOr (Or l) = Just l
extOr a = Nothing

extIm :: MForm m -> Maybe (MForm m , MForm m)
extIm (Im a b) = Just (a , b)
extIm a = Nothing

extMo :: MForm m -> Maybe (m , MForm m)
extMo (Mo a b) = Just (a , b)
extMo a = Nothing

data Term m =
    Vari Int
    |   Lamb (MForm m) (Term m)
    |   Appl (Term m) (Term m)
    |   Tupl [Term m]
    |   Proj Int (Term m)
    |   Inje Int [MForm m] (Term m)
    |   Case (MForm m) (Term m) [Term m]
    |   Lock m (Term m)
    |   Unlo Int m m (Term m)
    |   Popm m (Term m)
    |   Peal Int m m m (Term m)


instance Show m => Show (Term m) where 
    show :: Show m => Term m -> String
    show (Vari i)       =   "<" ++ show i ++ ">"
    show (Lamb a t)     =   "λ" ++ show a ++ "." ++ show t 
    show (Appl t r)     =   "(" ++ show t ++ "@" ++ show r ++ ")"
    show (Tupl lt)      =   "(" ++ interleave "," (fmap show lt) ++ ")"
    show (Proj i t)     =   "π" ++ show i ++ " " ++ show t
    show (Inje i la t)  =   "σ" ++ show i ++ " " ++ show t
    show (Case a t lr)  =   "C(" ++ show t ++ "){" ++ interleave ";" (fmap show lr) ++ "}"
    show (Lock m t)     =   "L" ++ show m ++ " " ++  show t 
    show (Unlo i m n t) =   "[" ++ show m ++ "-" ++ show n ++ "→⋅|" ++ show i ++ "] " ++ show t 
    show (Popm m t)     =   "[" ++ show m ++ "→⋅] " ++ show t 
    show (Peal i m n r t)   =   "[" ++ show m ++ "-" ++ show n ++ "→" ++ show r ++ "|" ++ show i ++ "] " ++ show t 


conLook :: MCont m -> Int -> Maybe (MForm m)
conLook [] i            = Nothing
conLook (Cfor a : l) i
    |   i <= 0          =   Just a
    |   otherwise       =   conLook l (i-1)
conLook (Cmod m : l) i  = conLook l i

conUnlock :: MCont m -> Maybe (m , MCont m , Int)
conUnlock [] = Nothing
conUnlock (Cfor a : l) = fmap (\(m , c , i) -> (m , c , i+1)) (conUnlock l)
conUnlock (Cmod m : l) = Just (m , l , 0)

conSplit :: m -> m -> Int -> MCont m -> MCont m
conSplit n r i [] = []
conSplit n r i (Cfor a : con) = Cfor a : conSplit n r i con
conSplit n r i (Cmod m : con)
    |   i <= 0      =   Cmod r : Cmod n : con
    |   otherwise   =   Cmod m : conSplit n r (i-1) con

conPop :: Int -> MCont m -> MCont m 
conPop i [] = []
--conPop i 



-- Infer type of term in a context. Fails if no such type exists.
typeInfer :: Eq m => Lat m => MCont m -> Term m -> Maybe (MForm m)
typeInfer con (Vari i)      =   conLook con i
typeInfer con (Lamb a t)    =   fmap (Im a) (typeInfer (Cfor a : con) t)
typeInfer con (Appl t r)    =   typeInfer con t >>= \a
                            ->  extIm a >>= \(a1 , a2)
                            ->  typeInfer con r >>= \ b
                            ->  if a1 == b then Just a2 else Nothing
typeInfer con (Tupl lt)     =   listAll (fmap (typeInfer con) lt) >>= \la
                            ->  Just (An la)
typeInfer con (Proj i t)    =   typeInfer con t >>= \a
                            ->  extAn a >>= \lb
                            ->  listLook lb i
typeInfer con (Inje i la t) =   listLook la i >>= \a
                            ->  typeInfer con t >>= \b
                            ->  if a == b then Just (Or la) else Nothing
typeInfer con (Case c t lr) =   typeInfer con t >>= \a
                            ->  extOr a >>= \lb
                            ->  if listCling typeInfer c [Cfor b : con | b <- lb] lr then Just c else Nothing
typeInfer con (Lock m t)    =   typeInfer (Cmod m : con) t >>= \a
                            ->  Just (Mo m a)
typeInfer con (Unlo i m n t)    
                            =   conUnlock con >>= \(n' , con' , j)
                            ->   typeInfer con' t >>= \a
                            ->  extMo a >>= \(m' , b)
                            ->  if m == m' && n == n' && i == j && imp m n then Just b else Nothing
typeInfer con (Popm m t)    =   typeInfer con t >>= \a
                            ->  extMo a >>= \(m' , b)
                            ->  if m == m' && cou m then Just b else Nothing
typeInfer con (Peal i m n r t)  
                            =   conUnlock con >>= \(n' , con' , j)
                            ->  typeInfer con' t >>= \a
                            ->  extMo a >>= \(m' , b)
                            ->  if n == n' && m == m' && i == j && latSplit m n r then Just (Mo r b) else Nothing


useVar :: Int -> Term m -> Bool 
useVar i (Vari j)           =   i == j
useVar i (Lamb a t)         =   useVar (i+1) t 
useVar i (Appl t r)         =   useVar i t || useVar i r 
useVar i (Tupl [])          =   False 
useVar i (Tupl (t : l))     =   useVar i t || useVar i (Tupl l)
useVar i (Proj j t)         =   useVar i t 
useVar i (Inje j la t)      =   useVar i t
useVar i (Case a t [])      =   useVar i t
useVar i (Case a t (r : l)) =   useVar i r || useVar i (Case a t l)
useVar i (Lock m t)         =   useVar i t 
useVar i (Unlo j m n t)     =   useVar (i+j) t 
useVar i (Popm m t)         =   useVar i t 
useVar i (Peal j m n r t)   =   useVar (i+j) t


-- Insert at location j number of variable indices k
weakTerm :: Int -> Int -> Term m -> Term m
weakTerm j k (Vari i)
    |   i >= j              =   Vari (i+k)
    |   otherwise           =   Vari i
weakTerm j k (Lamb a t)     =   Lamb a (weakTerm (j+1) k t)
weakTerm j k (Appl t r)     =   Appl (weakTerm j k t) (weakTerm j k r)
weakTerm j k (Tupl lt)      =   Tupl (fmap (weakTerm j k) lt)
weakTerm j k (Proj i t)     =   Proj i (weakTerm j k t)
weakTerm j k (Inje i la t)  =   Inje i la (weakTerm j k t)
weakTerm j k (Case a t lr)  =   Case a (weakTerm j k t) (fmap (weakTerm j k) lr)
weakTerm j k (Lock m t)     =   Lock m (weakTerm j k t)
weakTerm j k (Unlo i m n t)
    |   j <= i              =   Unlo (i+k) m n t
    |   otherwise           =   Unlo i m n (weakTerm (j-i-1) k t)
weakTerm j k (Popm m t)     =   Popm m (weakTerm j k t)
weakTerm j k (Peal i m n r t)
    |   j <= i              =   Peal (i+k) m n r t
    |   otherwise           =   Peal i m n r (weakTerm (j-i-1) k t)

-- Substitute s at location j in term
substTerm :: Term m -> Int -> Term m -> Term m
substTerm s j (Vari i)
    |   i == j              =   s
    |   i < j               =   Vari i
    |   otherwise           =   Vari (i-1)
substTerm s j (Lamb a t)    =   Lamb a (substTerm (weakTerm 0 1 s) (j+1) t)
substTerm s j (Appl t r)    =   Appl (substTerm s j t) (substTerm s j r)
substTerm s j (Tupl lt)     =   Tupl (fmap (substTerm s j) lt)
substTerm s j (Proj i t)    =   Proj i (substTerm s j t)
substTerm s j (Inje i la t) =   Inje i la (substTerm s j t)
substTerm s j (Case a t lr) =   Case a (substTerm s j t) (fmap (substTerm (weakTerm 0 1 s) (j+1)) lr)
substTerm s j (Lock m t)    =   Lock m (substTerm s j t)
substTerm s j (Unlo i m n t)
    |   j < i               =   Unlo (i-1) m n t
    |   otherwise           =   Unlo i m n (substTerm s (j-i) t)
substTerm s j (Popm m t)    =   Popm m (substTerm s j t)
substTerm s j (Peal i m n r t)
    |   j < i               =   Peal (i-1) m n r t
    |   otherwise           =   Peal i m n r (substTerm s (j-1) t)


-- Shift the value of a modality in context
shiftCon :: m -> Int -> MCont m -> MCont m
shiftCon m i [] = []
shiftCon m i (Cfor a : con) = Cfor a : shiftCon m i con 
shiftCon m i (Cmod n : con)
    |   i <= 0      =   Cmod m : con 
    |   otherwise   =   Cmod n : shiftCon m (i-1) con

shiftTerm :: Eq m => Lat m => m -> Int -> Term m -> Term m
shiftTerm n i (Vari j)          =   Vari j
shiftTerm n i (Lamb a t)        =   Lamb a (shiftTerm n i t)
shiftTerm n i (Appl t s)        =   Appl (shiftTerm n i t) (shiftTerm n i s)
shiftTerm n i (Tupl lt)         =   Tupl (fmap (shiftTerm n i) lt)
shiftTerm n i (Proj j t)        =   Proj j (shiftTerm n i t)
shiftTerm n i (Inje j la t)     =   Inje j la (shiftTerm n i t)
shiftTerm n i (Case a t lr)     =   Case a (shiftTerm n i t) (fmap (shiftTerm n i) lr)
shiftTerm n i (Lock m t)        =   Lock m (shiftTerm n (i+1) t)
shiftTerm n i (Unlo j m' m t) 
    |   i <= 0                  =   Unlo j m' n t
    |   otherwise               =   Unlo j m' m (shiftTerm n (i-1) t)
shiftTerm n i (Popm m t)        =   Popm m (shiftTerm n i t)
shiftTerm n i (Peal j m' m s t)    
    |   i <= 0                  =   Peal j m' n s t 
    |   otherwise               =   Peal j m' m s (shiftTerm n (i-1) t)


-- Split a modality in context into two modalities. 
splitCon :: m -> m -> Int -> MCont m -> MCont m
splitCon n r i [] = []
splitCon n r i (Cfor a : con) = Cfor a : conSplit n r i con
splitCon n r i (Cmod m : con)
    |   i <= 0      =   Cmod r : Cmod n : con
    |   otherwise   =   Cmod m : conSplit n r (i-1) con


-- This is unsafe, as in it should only be applied if the term is well-typed and context is splittable.
splitTerm :: Eq m => Lat m => m -> m -> Int -> Term m -> Term m
splitTerm n r i (Vari j)        =   Vari j
splitTerm n r i (Lamb a t)      =   Lamb a (splitTerm n r i t)
splitTerm n r i (Appl t s)      =   Appl (splitTerm n r i t) (splitTerm n r i s)
splitTerm n r i (Tupl lt)       =   Tupl (fmap (splitTerm n r i) lt)
splitTerm n r i (Proj j t)      =   Proj j (splitTerm n r i t)
splitTerm n r i (Inje j la t)   =   Inje j la (splitTerm n r i t)
splitTerm n r i (Case a t lr)   =   Case a (splitTerm n r i t) (fmap (splitTerm n r i) lr)
splitTerm n r i (Lock m t)      =   Lock m (splitTerm n r (i+1) t)
splitTerm n r i (Unlo j m' m t) 
    |   i <= 0                  =   Unlo j r r (Peal 0 m' n r t)
    |   otherwise               =   Unlo j m' m (splitTerm n r (i-1) t)
splitTerm n r i (Popm m t)      =   Popm m (splitTerm n r i t)
splitTerm n r i (Peal j m' m s t)    
    |   i <= 0                  =   let mn = omiU m n in Peal j mn r s (Peal 0 m' n (omiU m n) t)
    |   otherwise               =   Peal j m' m s (splitTerm n r (i-1) t)

-- 
-- Remove modality from context
counCon :: Int -> MCont m -> MCont m
counCon i [] = []
counCon i (Cfor a : con) = Cfor a : counCon i con 
counCon i (Cmod n : con)
    |   i <= 0      =   con 
    |   otherwise   =   Cmod n : counCon (i-1) con

counTerm :: Eq m => Lat m => Int -> Term m -> Term m
counTerm i (Vari j)             =   Vari j
counTerm i (Lamb a t)           =   Lamb a (counTerm i t)
counTerm i (Appl t s)           =   Appl (counTerm i t) (counTerm i s)
counTerm i (Tupl lt)            =   Tupl (fmap (counTerm i) lt)
counTerm i (Proj j t)           =   Proj j (counTerm i t)
counTerm i (Inje j la t)        =   Inje j la (counTerm i t)
counTerm i (Case a t lr)        =   Case a (counTerm i t) (fmap (counTerm i) lr)
counTerm i (Lock m t)           =   Lock m (counTerm (i+1) t)
counTerm i (Unlo j m' m t) 
    |   i <= 0                  =   Popm m' (weakTerm 0 j t)
    |   otherwise               =   Unlo j m' m (counTerm (i-1) t)
counTerm i (Popm m t)           =   Popm m (counTerm i t)
counTerm i (Peal j m' m s t)    
    |   i <= 0                  =   Lock s (Unlo j m' s t)
    |   otherwise               =   Peal j m' m s (counTerm (i-1) t)


eval :: Eq m => Lat m => Term m -> Maybe (Term m)

-- Beta rules
eval (Appl (Lamb a t) r)        =   Just (substTerm r 0 t)
eval (Proj i (Tupl lt))         =   listLook lt i
eval (Case a (Inje i la t) lr)  =   fmap (substTerm t 0) (listLook lr i)
eval (Unlo j m' n (Lock m t))   =   Just (weakTerm 0 j (shiftTerm n 0 t))
eval (Popm m (Lock m' t))       =   Just (counTerm 0 t)
eval (Peal j m n r (Lock m' t)) =   Just (Lock r (weakTerm 1 j (splitTerm n r 0 t)))

-- special 
eval (Lock s (Unlo i r s' (Peal j m n r' t)))
                                =   Just (Peal j m s r' t)
eval (Popm r (Peal i m n r' t)) =   Just (Unlo 0 m n (weakTerm 0 i t))

-- Eta rules
eval (Lamb a (Appl t (Vari i)))
    |   i <= 0 && not (useVar 0 t)  =   Just (substTerm (Vari 99) 0 t) 
    |   otherwise                   =   fmap (Lamb a) (eval (Appl t (Vari i)))
-- Tupl Proj
eval (Lock m (Unlo i n m' t))
    |   m == n                  =   Just t
    |   otherwise               =   fmap (Lock m) (eval (Unlo i n m' t))


-- Congruent calls
eval (Lamb a t)                 =   fmap (Lamb a) (eval t)
eval (Appl t r)                 =   case eval t of 
                Just t'     ->  Just (Appl t' r)
                Nothing     ->  fmap (Appl t) (eval r)
eval (Tupl lt)                  =   fmap Tupl (evalTup lt)      
eval (Proj i t)                 =   fmap (Proj i) (eval t)
eval (Inje i la t)              =   fmap (Inje i la) (eval t)
eval (Case a t lr)              =   case eval t of 
                Just t'         ->  Just (Case a t' lr)
                Nothing         ->  fmap (Case a t) (evalTup lr)
eval (Lock m t)                 =   fmap (Lock m) (eval t)
eval (Unlo j m n t)             =   fmap (Unlo j m n) (eval t)
eval (Popm m t)                 =   fmap (Popm m) (eval t)
eval (Peal j m n r t)           =   fmap (Peal j m n r) (eval t)

eval t                          =   Nothing

evalTup :: Eq m => Lat m => [Term m] -> Maybe [Term m] 
evalTup []                =   Nothing 
evalTup (t : l)     =   case eval t of 
    Just t'     ->  Just (t' : l)
    Nothing     ->  fmap (t :) (evalTup l)


evalIO :: Eq m => Show m => Lat m => Term m -> IO ()
evalIO t = do {print t ; case eval t of 
    Just t' -> evalIO t' 
    Nothing -> return ()
    }

data Bm =
    Box
    deriving (Eq , Ord)

instance Show Bm where
    show :: Bm -> String
    show Box = "☐"

instance Lat Bm where
    -- Box X => Box X
    imp :: Bm -> Bm -> Bool
    imp Box Box = True

    lat :: Bm -> Bm -> Maybe Bm
    lat Box Box = Just Box

    -- Box X => X
    cou :: Bm -> Bool
    cou Box = True

    -- Box X => Box (Box X)
    awa :: Bm -> [(Bm , Bm)]
    awa Box = [(Box , Box)]

    omi :: Bm -> Bm -> Maybe Bm
    omi Box Box = Just Box

    def :: Bm 
    def = Box


exCompCon :: MCont Bm 
exCompCon = [Cfor (Im (Ba "A") (Ba "B")) , Cfor (Im (Ba "B") (Ba "C"))]

exCompTerm :: Term Bm
exCompTerm = Lamb (Ba "A") (Appl (Lamb (Ba "A") (Appl (Vari 3) (Appl (Vari 2) (Vari 0)))) (Vari 0))

exPealBoxCon :: MCont Bm 
exPealBoxCon = [Cfor (Mo Box (Ba "A"))]

exPealBox :: Term Bm 
exPealBox = Peal 0 Box Box Box (Lock Box (Popm Box (Peal 0 Box Box Box (Vari 0))))

main :: IO ()
--main = print (typeInfer exPealBoxCon exPealBox)
main = evalIO exPealBox