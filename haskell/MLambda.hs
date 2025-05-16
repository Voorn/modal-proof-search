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
    |   Unlo Int (Term m)
    |   Popm (Term m)
    |   Peal Int m (Term m)
    deriving Show

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
typeInfer con (Unlo i t)    =   conUnlock con >>= \(m , con' , j)
                            ->   typeInfer con' t >>= \a
                            ->  extMo a >>= \(n , b)
                            ->  if i == j && imp n m then Just b else Nothing
typeInfer con (Popm t)      =   typeInfer con t >>= \a
                            ->  extMo a >>= \(m , b)
                            ->  if cou m then Just b else Nothing
typeInfer con (Peal i r t)  =   conUnlock con >>= \(n , con' , j)
                            ->  typeInfer con' t >>= \a
                            ->  extMo a >>= \(m , b)
                            ->  if i == j && latSplit m n r then Just (Mo r b) else Nothing

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
weakTerm j k (Unlo i t)
    |   j <= i              =   Unlo (i+k) t
    |   otherwise           =   Unlo i (weakTerm (j-i-1) k t)
weakTerm j k (Popm t)       =   Popm (weakTerm j k t)
weakTerm j k (Peal i m t)
    |   j <= i              =   Peal (i+k) m t
    |   otherwise           =   Peal i m (weakTerm (j-i-1) k t)

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
substTerm s j (Unlo i t)
    |   j < i               =   Unlo (i-1) t
    |   otherwise           =   Unlo i (substTerm s (j-i) t)
substTerm s j (Popm t)      =   Popm (substTerm s j t)
substTerm s j (Peal i m t)
    |   j < i               =   Peal (i-1) m t
    |   otherwise           =   Peal i m (substTerm s (j-1) t)

-- Split a modality in context into two modalities. 
-- This is unsafe, as in it should only be applied if the term is well-typed and context is splittable.
splitTerm :: Eq m => Lat m => MCont m -> m -> m -> Int -> Term m -> Maybe (Term m)
splitTerm con n r i (Vari j)        =   Just (Vari j)
splitTerm con n r i (Lamb a t)      =   fmap (Lamb a) (splitTerm (Cfor a : con) n r i t)
splitTerm con n r i (Appl t s)      =   splitTerm con n r i t >>= \t' 
                                    ->  fmap (Appl t') (splitTerm con n r i s)
splitTerm con n r i (Tupl lt)       =   fmap Tupl (listAll (fmap (splitTerm con n r i) lt))
splitTerm con n r i (Proj j t)      =   fmap (Proj j) (splitTerm con n r i t)
splitTerm con n r i (Inje j la t)   =   fmap (Inje j la) (splitTerm con n r i t)
splitTerm con n r i (Case a t lr)   =   typeInfer con t >>= \a
                                    ->  extOr a >>= \lb
                                    ->  splitTerm con n r i t >>= \t'
                                    ->  fmap (Case a t') (listZip (\ x y -> splitTerm (Cfor x : con) n r i y) lb lr)
splitTerm con n r i (Lock m t)      =   fmap (Lock m) (splitTerm con n r (i+1) t)
splitTerm con n r i (Unlo j t)      =   Just (Unlo j (Peal 0 r t))
splitTerm con n r i (Popm t)        =   fmap Popm (splitTerm con n r i t)
splitTerm con n r i (Peal j s t)    =   case typeInfer con t >>= \a -> extMo a of
    Just (m , b)        ->  Just (Peal j s (Peal 0 (omiU m n) t)) 
    _                   ->  Nothing



eval :: Eq m => Lat m => MCont m -> Term m -> Maybe (Term m)
-- Beta steps
eval con (Appl (Lamb a t) r)        =   Just (substTerm r 0 t)
eval con (Proj i (Tupl lt))         =   listLook lt i
eval con (Case a (Inje i la t) lr)  =   fmap (substTerm t 0) (listLook lr i)
eval con (Unlo j (Lock m t))        =   Just (weakTerm 0 j t)
eval con (Peal j r (Lock m t))      =   conUnlock con >>= \(m , con' , i) 
                                    ->  typeInfer (Cmod m : con') t >>= \a 
                                    ->  extMo a >>= \(n , b)
                                    ->  splitTerm con n r 0 t >>= \t' 
                                    ->  Just (Lock r (weakTerm 1 j t'))
-- Congruent calls
eval con (Lamb a t)                 =   fmap (Lamb a) (eval (Cfor a : con) t)
eval con (Appl t r)                 =   case eval con t of 
                Just t'     ->  Just (Appl t' r)
                Nothing     ->  fmap (Appl t) (eval con r)
eval con (Tupl lt)                  =   fmap Tupl (evalTup [con | i <- lt] lt)      
eval con (Proj i t)                 =   fmap (Proj i) (eval con t)
eval con (Inje i la t)              =   fmap (Inje i la) (eval con t)
eval con (Case a t lr)              =   case eval con t of 
                Just t'     ->  Just (Case a t' lr)
                Nothing     ->  typeInfer con t >>= \b -> extOr b >>= \lb -> fmap (Case a t) (evalTup [Cfor i : con | i <- lb] lr)
eval con (Lock m t)                 =   fmap (Lock m) (eval (Cmod m : con) t)
eval con (Unlo j t)                 =   conUnlock con >>= \(m , con' , i) -> fmap (Unlo j) (eval con' t)
eval con (Popm t)                   =   fmap Popm (eval con t)
eval con (Peal j s t)               =   conUnlock con >>= \(m , con' , i) -> fmap (Peal j s) (eval con' t)
eval con t                          =   Nothing

evalTup :: Eq m => Lat m => [MCont m] -> [Term m] -> Maybe [Term m] 
evalTup l []                =   Nothing 
evalTup [] r                =   Nothing 
evalTup (a : c) (t : l)     =   case eval a t of 
    Just t'     ->  Just (t' : l)
    Nothing     ->  fmap (t :) (evalTup c l)


evalIO :: Eq m => Show m => Lat m => MCont m -> Term m -> IO ()
evalIO con t = do {print t ; case eval con t of 
    Just t' -> evalIO con t' 
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

main :: IO ()
main = evalIO exCompCon exCompTerm