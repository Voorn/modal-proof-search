{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
module MForm where

import Knowledge
import Modal

-- Contains definition of formulas and forward search algorithm

data MForm m =
    Ba String
    |   Bo
    |   An [MForm m]
    |   Or [MForm m]
    |   Im (MForm m) (MForm m)
    |   Mo m (MForm m)
    |   Nam String (MForm m)
    deriving (Eq , Ord)

notF :: MForm m -> MForm m
notF f = Im f Bo

interleave :: [a] -> [[a]] ->  [a]
interleave i [] = []
interleave i [l] = l
interleave i (a : ll) = a ++ i ++ interleave i ll

instance Show m => Show (MForm m) where
    show :: MForm m -> String
    show (Ba s) = s
    show Bo = "⊥"
    show (An lf) = "(" ++ interleave "∧" (fmap show lf) ++ ")"
    show (Or lf) = "(" ++ interleave "∨" (fmap show lf) ++ ")"
    show (Im f Bo) = "¬" ++ show f
    show (Im f g) = "(" ++ show f ++ "⇒" ++ show g ++ ")"
    show (Mo m f) = show m ++ "(" ++ show f ++ ")"
    show (Nam s f) = s

-- ========================================
-- The Catch Rules and catching
-- ========================================


-- The Squeezer: or catcher, generating new sequents by catch rules

-- The Boolean determines whether we can have modal formulas separating contexts, while not having a relevant consequence. 
-- This should be True for initiation formulas at least. Can be False for cut formulas, but this does not work well with further queries
-- Apparantly not cleaning the Bowties at this stage (that is, removing redundant ones) is slightly quicker? Will be cleaned anyway, 
--      but also compared with knowledge base in the meantime.
squeezeM :: Show m => Ord m => Lat m => Bool -> [(m , [MForm m])] -> [MBowtie m (MForm m) Proof] -> [MBowtie m (MForm m) Proof]
squeezeM v catch =    concatMap (foldForm v catch)

incatch :: Ord m => Lat m => [(m , [MForm m])] -> m -> MForm m -> Bool
incatch [] m f = False
incatch ((n , r) : l) m f   =   (imp m n && inSet f r) || incatch l m f

-- Specific catch rule checker
foldForm :: Show m => Ord m => Lat m => Bool -> [(m , [MForm m])] -> MBowtie m (MForm m) Proof -> [MBowtie m (MForm m) Proof]
foldForm v catch (MBas bow) = let (a , b , c) = tranBowSeq bow in case (a , b) of
    ([] , [f])      ->  MBas bow : foldNecc catch catch f c
    (_ , [Im l r])  ->  let s = sieveBow bow l in
                            if s == bow then [MBas s] else MBas s : foldForm v catch (MBas s)
    (_ , _)         ->  [MBas bow]
foldForm v catch (MBin l m bow) = let (a , b , c) = tranBowSeq bow in case (a , b) of
    ([] , [d])  ->  if v || incatch catch m d then MBin l m bow : foldMod catch l m d c else []
    (t , [d])   ->  if v || incatch catch m d then [MBin l m bow] else []
    _           ->  [MBin l m bow]

-- Modal catch rule
foldMod :: Show m => Ord m => Lat m => [(m , [MForm m])] -> [MForm m] -> m -> MForm m -> Proof -> [MBowtie m (MForm m) Proof]
foldMod [] la m a p = []
foldMod ((n , r) : ta) la m a p
    |   imp m n && inSet a r && not (inSet (Mo n a) la)
                                =   MBas (cleanBow ((Mo n a , False) : fmap (\x -> (x , True)) la , Cat ("MI:"++ show m) ("Mod Introduction " ++ show m) p)) : foldMod ta la m a p
    |   otherwise               =   foldMod ta la m a p

-- Modal catch rule for necessity
foldNecc :: Show m => Ord m => [(m , [MForm m])] -> [(m , [MForm m])] -> MForm m -> Proof -> [MBowtie m (MForm m) Proof]
foldNecc his [] f p = []
foldNecc his ((m , s) : l) f p
    |   inSet f s   =   MBas ([(Mo m f , False)] , Cat ("MI:"++ show m) ("Mod Introduction " ++ show m) p) : foldNecc his his (Mo m f) p ++ foldNecc his l f p
    |   otherwise   =   foldNecc his l f p

-- =================================
-- The cut rule process
-- =================================

-- The cutmachine: Go through stack of all new sequents, find cuts with existing database. 
-- New cuts are added to the stack, and the sequent itself to the database

-- cutmachine: Producing new cuts.
cutmachineM :: Show m => Ord m => Lat m => [(m , [MForm m])] -> MKnow m (MForm m) Proof -> MBowtie m (MForm m) Proof -> [MBowtie m (MForm m) Proof]
    -> (MKnow m (MForm m) Proof , [MBowtie m (MForm m) Proof])
cutmachineM catch k b l = if inMKnow b k then (k , l) else
  let cuts = squeezeM False catch (cutMKnowMBowSimple Cut k b)  in cutmachineM2 catch (addMKnow b k) l cuts
--  let cuts = squeezeM catch (cutMKnowMBow Cut k b)  in cutmachineM2 catch (addMKnow b k) l cuts

-- cutmachine: Add new cuts to stack of sequents
cutmachineM2 :: Ord m => Lat m => [(m , [MForm m])] -> MKnow m (MForm m) Proof -> [MBowtie m (MForm m) Proof] -> [MBowtie m (MForm m) Proof]
    -> (MKnow m (MForm m) Proof , [MBowtie m (MForm m) Proof])
cutmachineM2 catch k his [] = (k , his)
cutmachineM2 catch k his (b : l) =
    if inMKnow b k then cutmachineM2 catch k his l else
--        cutmachineM2 catch (filterMKnow b k) (b : his) l
        cutmachineM2 catch (filterMKnow b k) (filteraddMBowties' b his) l

-- Cutmachine Output Initialiser
cutmachineMIterIOinit :: Ord m => Lat m => Show m => [(m , [MForm m])] -> MKnow m (MForm m) Proof -> [MBowtie m (MForm m) Proof] -> ([MForm m] , [MForm m]) -> IO ()
cutmachineMIterIOinit catch k l = cutmachineMIterIO catch k (squeezeM True catch l)

-- Cutmachine Output main iterator and finalizer. Pop sequent from stack and start cut
cutmachineMIterIO :: Ord m => Lat m => Show m => [(m , [MForm m])] -> MKnow m (MForm m) Proof -> [MBowtie m (MForm m) Proof] -> ([MForm m] , [MForm m]) -> IO ()
cutmachineMIterIO catch k [] (x , y) = putStr
    ("Done:\n===============\n"
    ++ stringMKnow k
    ++ "RESULTS\n"
    ++ "Assumptions: " ++ show x ++ "\n"
    ++ "Questions: " ++ show y ++ "\n\n"
    ++ "Minimal true sequents:\n"
    ++ interleave "\n" (fmap stringBowtieNP (trivialSeq (fst k) (capList x y) ++ tranKnowBow (extractKnow x y (fst k)))))
cutmachineMIterIO catch k (b : l) q = do {print b ; --print (cutMKnowMBow Cut k b) ; 
    putStrLn "-----" ;
    let (k' , l') = cutmachineM catch k b l in cutmachineMIterIO catch k' l' q}

-- find trivial sequents
trivialSeq :: Ord m => Lat m => Show m => Know (MForm m) Proof -> [MForm m] -> [Bowtie (MForm m) Proof]
trivialSeq know [] = []
trivialSeq know (x : l)
    |   inKnow ([(x, False)] , Axiom "" "") know   =   trivialSeq know l
    |   otherwise       =   ([(x , True) , (x, False)] , Axiom "Trivial" "") : trivialSeq know l


-- ===================================
-- Initiation Rules: Unfolding queries
-- ===================================

-- Add catch-rule for modal formula
addCatch :: Ord m => [(m , [MForm m])] -> m -> MForm m -> [(m , [MForm m])]
addCatch [] m f = [(m , [f])]
addCatch ((n , s) : t) m f
    |   n < m       =   (n , s) : addCatch t m f
    |   m == n      =   (n , addSet f s) : t
    |   otherwise   =   (m , [f]) : (n , s) : t

-- Check if this is a base formula
baseForm :: MForm m -> Bool
baseForm (Ba s) = True
baseForm Bo = True
baseForm f = False

-- Remove redundant queries
addForms :: Eq m => [(MForm m , Bool)] -> [(MForm m , Bool)] -> [(MForm m , Bool)]
addForms [] r = r
addForms (x : l) r = x : filList x (addForms l r)

-- unfold investigates queries and produces small sequents without focussing

-- Go through all queries and initate unfolding
--          assumptions -> questions -> modal catchers    -> current knowledge       -> tautologies                 -> new formulas       
unfoldForm :: Show m => Ord m => Lat m => [MForm m] -> [MForm m] -> [(m , [MForm m])] -> MKnow m (MForm m) Proof -> [MBowtie m (MForm m) Proof] -> [(MForm m , Bool)]
    -> ([MForm m] , [MForm m] , [(m , [MForm m])] , [MBowtie m (MForm m) Proof])
unfoldForm assu ques catch know bows [] = (assu  , ques , catch , bows)
unfoldForm assu ques catch know bows ((f , True) : lis) = if baseForm f || inList f assu
    then unfoldForm assu ques catch know bows lis
    else unfoldAssu assu ques catch know bows lis f
unfoldForm assu ques catch know bows ((f , False) : lis) = if baseForm f || inList f ques
    then unfoldForm assu ques catch know bows lis
    else unfoldQues assu ques catch know bows lis f

-- Unfold the assumptions
unfoldAssu :: Show m => Ord m => Lat m => [MForm m] -> [MForm m] -> [(m , [MForm m])] -> MKnow m (MForm m) Proof -> [MBowtie m (MForm m) Proof] -> [(MForm m , Bool)] -> MForm m
    -> ([MForm m] , [MForm m] , [(m , [MForm m])] , [MBowtie m (MForm m) Proof])
unfoldAssu assu ques catch know bows lis (Ba a)     = unfoldForm assu ques catch know bows lis
unfoldAssu assu ques catch know bows lis Bo         = unfoldForm assu ques catch know bows lis
unfoldAssu assu ques catch know bows lis (An lf)    =
    unfoldForm (addSet (An lf) assu) ques catch know (filteraddMBowtiesAll [MBas (cleanBow ([(An lf , True) , (f , False)] , Axiom "AE" ("And Elimination " ++ show lf ++ " => " ++ show f))) | f <- lf] bows)
        (addForms (fmap (\x -> (x , True)) lf) lis)
unfoldAssu assu ques catch know bows lis (Or lf)    =
    unfoldForm (addSet (Or lf) assu) ques catch know (filteraddMBowties (MBas (cleanBow ((Or lf , True) : [(f , False) | f <- lf] , Axiom "OE" ("Or Elimination " ++ show lf))))  bows)
        (addForms (fmap (\x -> (x , True)) lf) lis)
unfoldAssu assu ques catch know bows lis (Im f g)   =
    unfoldForm (addSet (Im f g) assu) ques catch know (filteraddMBowties (MBas (cleanBow ([(f , True) , (Im f g , True) , (g , False)] , Axiom "IE" ("Implication Elimination " ++ show (Im f g))))) bows)
        (addForms [(f , False) , (g , True)] lis)
unfoldAssu assu ques catch know bows lis (Mo m f)   =
    unfoldForm (addSet (Mo m f) assu) ques catch know (filteraddMBowtiesAll
        (MBin [Mo m f] m ([(f , False)] , Axiom "ME" ("Mod Elimination " ++ show (Mo m f))) :
        [MBas (cleanBow ([(Mo m f , True) , (f , False)] , Axiom "MC" ("Mod Counit " ++ show (Mo m f)))) |   cou m] ++
        [MBin [Mo m f] i ([(Mo j f , False)] , Axiom "MS" ("Mod Split " ++  show (Mo m f) ++ " => " ++ show i ++ " " ++ show j))  | (i , j) <- awa m]
        ) bows)
        (addForms ((f , True) : fmap (\(x , y) -> (Mo y f , True)) (awa m)) lis)
unfoldAssu assu ques catch know bows lis (Nam s f)   =
    unfoldForm (addSet (Nam s f) assu) ques catch know (filteraddMBowties (MBas (cleanBow ([(Nam s f , True) , (f , False)] , Axiom "NE" "Name Elimination")))  bows)
        (addForms [(f , True)] lis)

-- unfold the questions
unfoldQues :: Show m => Ord m => Lat m => [MForm m] -> [MForm m] -> [(m , [MForm m])] -> MKnow m (MForm m) Proof -> [MBowtie m (MForm m) Proof] -> [(MForm m , Bool)] -> MForm m
    -> ([MForm m] , [MForm m] , [(m , [MForm m])] , [MBowtie m (MForm m) Proof])
unfoldQues assu ques catch know bows lis (Ba a)     = unfoldForm assu ques catch know bows lis
unfoldQues assu ques catch know bows lis Bo         = unfoldForm assu ques catch know bows lis
unfoldQues assu ques catch know bows lis (An lf)    =
    unfoldForm assu (addSet (An lf) ques)  catch know (filteraddMBowties (MBas (cleanBow ((An lf , False) : [(f , True) | f <- lf] , Axiom "AI" ("And Introduction " ++ show lf))))  bows)
        (addForms (fmap (\x -> (x , False)) lf) lis)
unfoldQues assu ques catch know bows lis (Or lf)    =
    unfoldForm assu (addSet (Or lf) ques) catch know (filteraddMBowtiesAll [MBas (cleanBow ([(Or lf , False) , (f , True)] , Axiom "OI" ("Or Introduction " ++ show f ++ " => " ++ show lf))) | f <- lf] bows)
        (addForms (fmap (\x -> (x , False)) lf) lis)
unfoldQues assu ques catch know bows lis (Im f g)   =
    unfoldForm assu (addSet (Im f g) ques) catch know (filteraddMBowties (MBas (cleanBow ([(g , True) , (Im f g , False)] , Axiom "II" ("Implication Introduction " ++ show (Im f g))))) bows)
        (addForms [(f , True) , (g , False)] lis)
unfoldQues assu ques catch know bows lis (Mo m f)   =
    unfoldForm assu (addSet (Mo m f) ques) (addCatch catch m f) know bows (addForms [(f , False)] lis)
unfoldQues assu ques catch know bows lis (Nam s f)   =
    unfoldForm assu (addSet (Nam s f) ques) catch know (filteraddMBowties (MBas (cleanBow ([(Nam s f , False) , (f , True)] , Axiom "NI" "Name Introduction")))  bows)
        (addForms [(f , False)] lis)


-- dunfold is deep unfold. They unfold queries using focussing. Major speed up.

-- deep unfold main operation
dunfoldForm :: Show m => Ord m => Lat m => [MForm m] -> [MForm m] -> [(m , [MForm m])] -> MKnow m (MForm m) Proof -> [MBowtie m (MForm m) Proof] -> [(MForm m , Bool)]
    -> ([MForm m] , [MForm m] , [(m , [MForm m])] , [MBowtie m (MForm m) Proof])
dunfoldForm assu ques catch know bows [] = (assu  , ques , catch , bows)
dunfoldForm assu ques catch know bows ((f , True) : lis) = if inList f assu
    then dunfoldForm assu ques catch know bows lis
    else dunfoldAssu assu ques catch know bows lis f
dunfoldForm assu ques catch know bows ((f , False) : lis)
  | inList f ques   = dunfoldForm assu ques catch know bows lis
  | f == Bo         = dunfoldForm assu ques catch know bows lis
  | otherwise       = dunfoldQues assu ques catch know (filteraddMBowties (MBas (cleanBow ([(f , False) , (Bo , True)] , Axiom "BE" "Bottom Elimination"))) bows) lis f

-- deep unfold assumptions. Requires additional function
-- Note: we have already added the formula to the questions, we are just processing consequences
dunfoldAssu :: Show m => Ord m => Lat m => [MForm m] -> [MForm m] -> [(m , [MForm m])] -> MKnow m (MForm m) Proof -> [MBowtie m (MForm m) Proof] -> [(MForm m , Bool)] -> MForm m
    -> ([MForm m] , [MForm m] , [(m , [MForm m])] , [MBowtie m (MForm m) Proof])
dunfoldAssu assu ques catch know bows cont (Ba f) = dunfoldForm assu ques catch know bows cont
dunfoldAssu assu ques catch know bows cont Bo = dunfoldForm assu ques catch know bows cont
dunfoldAssu assu ques catch know bows cont (Mo m f)  =
    dunfoldForm (addSet (Mo m f) assu) ques catch know
        (filteraddMBowtiesAll
            (   MBin [Mo m f] m ([(f , False)] , Axiom "ME" ("Mod Elimination " ++ show (Mo m f))) :
                [MBas (cleanBow ([(Mo m f , True) , (f , False)] , Axiom "MC" ("Mod Counit " ++ show (Mo m f)))) |   cou m] ++
                [MBin [Mo m f] i ([(Mo j f , False)] , Axiom "MS" ("Mod Split " ++  show (Mo m f) ++ " => " ++ show i ++ " " ++ show j))  | (i , j) <- awa m]
            ) bows)
        (addForms ((f , True) : fmap (\(x , y) -> (Mo y f , True)) (awa m)) cont)
dunfoldAssu assu ques catch know bows cont f =
    let assu1 = addSet f assu in
    let (cont1 , skel1) = deepAssu assu1 ques cont f in
        dunfoldForm assu1 ques catch know (filteraddMBowtiesAll
            [MBas (cleanBow ((f , True) : fmap (\x -> (x , True)) i1 ++ fmap (\x -> (x , False)) i2 , Axiom "FE" ("Focussed Elimination " ++ show f)))  | (i1 , i2) <- skel1 , difSet i1 i2]
            bows)
        cont1

-- Deep unfold questions. Requires additional function
dunfoldQues :: Show m => Ord m => Lat m => [MForm m] -> [MForm m] -> [(m , [MForm m])] -> MKnow m (MForm m) Proof -> [MBowtie m (MForm m) Proof] -> [(MForm m , Bool)] -> MForm m
    -> ([MForm m] , [MForm m] , [(m , [MForm m])] , [MBowtie m (MForm m) Proof])
dunfoldQues assu ques catch know bows cont (Ba f) = dunfoldForm assu ques catch know bows cont
dunfoldQues assu ques catch know bows lis Bo         = dunfoldForm assu ques catch know bows lis
dunfoldQues assu ques catch know bows lis (Im f g)   =
    dunfoldForm assu (addSet (Im f g) ques) catch know (filteraddMBowties (MBas (cleanBow ([(g , True) , (Im f g , False)] , Axiom "II" ("Implication Introduction " ++ show (Im f g))))) bows)
        (addForms [(f , True) , (g , False)] lis)
dunfoldQues assu ques catch know bows lis (Mo m f)   =
    dunfoldForm assu (addSet (Mo m f) ques) (addCatch catch m f) know bows (addForms [(f , False)] lis)
dunfoldQues assu ques catch know bows cont f =
    let ques1 = addSet f ques in
    let (cont1 , skel1) = deepQues assu ques1 cont f in
        dunfoldForm assu ques1 catch know (filteraddMBowtiesAll
            [MBas (cleanBow ((f , False) : fmap (\x -> (x , True)) i1 ++ fmap (\x -> (x , False)) i2 , Axiom "FI" ("Focussed Introduction " ++ show f)))  | (i1 , i2) <- skel1 , difSet i1 i2]
            bows)
        cont1

-- The following functions facilitate deep unfolding\focussing

weave :: Ord a => [[([a] , [a])]] -> [([a] , [a])]
weave [] = [([] , [])]
weave (a : l) = let r = weave l in
    [(joinSet i1 j1 , joinSet i2 j2) | (i1 , i2) <- a , (j1 , j2) <- r]


-- Important Note: This treats the next to be added queries as a Set, not a list
deepAssu :: Ord m => [MForm m] -> [MForm m] -> [(MForm m , Bool)] -> MForm m -> ([(MForm m , Bool)] , [([MForm m] , [MForm m])])
deepAssu assu ques open (An lf) = let (open1 , bow1) = deepAssuLis assu ques open lf in (open1 , concat bow1)
deepAssu assu ques open (Or lf) = let (open1 , bow1) = deepAssuLis assu ques open lf in (open1 , weave bow1)
deepAssu assu ques open (Im f g) =   let (open1 , bow1) = deepQues assu ques open f in
                                let (open2 , bow2) = deepAssu assu ques open1 g in
                                    (open2 , weave [bow1 , bow2])
deepAssu assu ques open (Mo m f) = let open1 = if inSet (Mo m f) assu || inList (Mo m f , True) open then open else addForms [(Mo m f , True)] open in
        (open1 , [([] , [Mo m f])])
deepAssu assu ques open (Nam s f) = deepAssu assu ques open f
deepAssu assu ques open f = (open , [([] , [f])])

deepAssuLis :: Ord m => [MForm m] -> [MForm m] -> [(MForm m , Bool)] -> [MForm m] -> ([(MForm m , Bool)] , [[([MForm m] , [MForm m])]])
deepAssuLis as qu open [] = (open , [])
deepAssuLis as qu open (b : l) =
    let (open1 , k1) = deepAssu as qu open b in
    let (open2 , k2) = deepAssuLis as qu open1 l in (open2 , k1 : k2)

deepQues :: Ord m => [MForm m] -> [MForm m] -> [(MForm m , Bool)] -> MForm m -> ([(MForm m , Bool)] , [([MForm m] , [MForm m])])
deepQues assu ques open (An lf) = let (open1 , bow1) = deepQuesLis assu ques open lf in (open1 , weave bow1)
deepQues assu ques open (Or lf) = let (open1 , bow1) = deepQuesLis assu ques open lf in (open1 , concat bow1)
deepQues assu ques open (Im f g) = let open1 = if inSet (Im f g) ques || inList (Im f g , False) open then open else addForms [(Im f g, False)] open in
        (open1 , [([Im f g] , [])])
deepQues assu ques open (Mo m f) = let open1 = if inSet (Mo m f) ques || inList (Mo m f , False) open then open else addForms [(Mo m f , False)] open in
        (open1 , [([Mo m f] , [])])
deepQues assu ques open (Nam s f) = deepQues assu ques open f
deepQues assu ques open f = (open , [([f] , [])])

deepQuesLis :: Ord m => [MForm m] -> [MForm m] -> [(MForm m , Bool)] -> [MForm m] -> ([(MForm m , Bool)] , [[([MForm m] , [MForm m])]])
deepQuesLis as qu open [] = (open , [])
deepQuesLis as qu open (b : l) =
    let (open1 , k1) = deepQues as qu open b in
    let (open2 , k2) = deepQuesLis as qu open1 l in (open2 , k1 : k2)

-- ===============================================================
-- The runners, the whole forward search process into one function
-- ===============================================================

-- * Empty knowledge database
empM :: MKnow m (MForm m) Proof
empM = (Knowledge.No , [])

-- * Shallow Runner: Perform the full forward search, using one-step sequents only.
runner :: Ord m => Show m => Lat m => [(MForm m , Bool)]  -> IO ()
runner lis =
    let query = extractQuery lis in
    let (assu , ques , catch , bow) = unfoldForm [] [] [] empM [] lis in
        cutmachineMIterIOinit catch empM bow query

-- * Deep Runner: Perform the full forward search, using focussing.
drunner :: Ord m => Show m => Lat m => [(MForm m , Bool)]  -> IO ()
drunner lis =
    let query = extractQuery lis in
    let (assu , ques , catch , bow) = dunfoldForm [] [] [] empM [] lis in
        do {print catch ;
        cutmachineMIterIOinit catch empM bow query}


