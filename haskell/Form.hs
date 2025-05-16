module Form where

import Knowledge

-- Formulas
data Form =
    Base String
    |   Bot
    |   And [Form]
    |   Ore [Form]
    |   Imp Form Form
    deriving (Eq , Ord)



instance Show Form where
    show :: Form -> String
    show (Base s) = s
    show Bot = "⊥"
    show (And l) = stringCol "⊤" "∧" show l
    show (Ore l) = stringCol "*" "∨" show l
    show (Imp l r) = "(" ++ show l ++ "⇒" ++ show r ++ ")"

botBow :: Form -> Bowtie Form Proof
botBow a = cleanBow ([(Bot  , True) , (a , False)] , Axiom "BE" "Bottom Elimination")

assuBow :: Form -> ([Form] , [Form] , [Bowtie Form Proof])
assuBow (And l) = (l , [] , [cleanBow ([(And l , True) , (a , False)] , Axiom "AE" "And Elimination") | a <- l])
assuBow (Ore l) = (l , [] , [cleanBow ((Ore l , True) : fmap (\p -> (p , False)) l , Axiom "OE" "Or Elimination")])
assuBow (Imp l r) = ([r] , [l] , [cleanBow ([(Imp l r , True) , (l , True) , (r , False)] , Axiom "IE" "Implication Elimination") | l /= r])
assuBow a = ([] , [] , [])

quesBow :: Form -> ([Form] , [Form] , [Bowtie Form Proof])
quesBow (And l) = ([] , l , botBow (And l) : [cleanBow ((And l , False) : fmap (\p -> (p , True)) l , Axiom "AI" "And Introduction")])
quesBow (Ore l) = ([] , l , botBow (Ore l) : [cleanBow ([(Ore l , False) , (a , True)] , Axiom "OI" "Or Introduction") | a <- l])
quesBow (Imp l r) = ([l] , [r] , botBow (Imp l r) : [cleanBow ([(Imp l r , False) , (r , True)] , Axiom "II" "Implication Introduction")])
quesBow Bot = ([] , [] , [])
quesBow a = ([] , [] , [botBow a])

mergebute :: Ord a => [a] -> [a] -> [[a]]
mergebute [] r = []
mergebute l [] = [l]
mergebute (a : l) (b : r)
    |   a < b       =   (a : b : r) : mergebute l (b : r)
    |   a == b      =   (a : r) : mergebute l r
    |   otherwise   =   fmap (b :) (mergebute (a : l) r)

joinmerge :: Ord a => [a] -> [a] -> [a]
joinmerge [] r = r
joinmerge l [] = l
joinmerge (a : l) (b : r)
    |   a < b       =   a : joinmerge l (b : r)
    |   b < a       =   b : joinmerge (a : l) r
    |   otherwise   =   a : joinmerge l r

concmerge :: Ord a => [[a]] -> [a]
concmerge = foldr joinmerge []

distribute :: Ord a => [[a]] -> [[a]]
distribute [] = [[]]
distribute ([] : lx) = []
distribute (l : xl) = concatMap (mergebute l) (distribute xl)

concers :: [([Form] , [Form])] -> ([Form] , [Form])
concers [] = ([] , [])
concers ((a , b) : l) = let (xa , xb) = concers l in (a ++ xa , b ++ xb)


disForm :: Form -> Bool -> [[(Form , Bool)]]
disForm (And l) True = fmap concat (distribute [disForm i True | i <- l])
disForm (Ore l) True = concat [disForm i True | i <- l]
disForm Bot True = [[]]
disForm (Base a) True = [[(Base a , False)]]

useForm :: Form -> [([Form] , [Form])]
useForm (And l) = fmap concers (distribute [useForm i  | i <- l])

starter :: [Form] -> [Form] -> [Bowtie Form Proof] -> [Form] -> [Form] -> ([Form] , [Form] , [Bowtie Form Proof])
starter assu ques bows [] [] = (assu , ques , bows)
starter assu ques bows [] (a : r) = if inSet a ques
    then starter assu ques bows [] r
    else let (l' , r' , b') = quesBow a in starter assu (addSet a ques) (b' ++ bows) l' (r ++ r')
starter assu ques bows (a : l) r = if inSet a assu
    then starter assu ques bows l r
    else let (l' , r' , b') = assuBow a in starter (addSet a assu) ques (b' ++ bows) (l ++ l') (r ++ r')




impreduce :: Bowtie Form b -> Bowtie Form b
impreduce bow = let (a , b , c) = tranBowSeq bow in case b of
    [Imp l r]   ->  sieveBow bow l
    _           ->  bow



-- Squeeze does all automatic derivations
squeeze :: [Bowtie Form b] -> [Bowtie Form b]
squeeze b = cleanBowties (fmap impreduce b)

-- cutmachine (we assume k is not in Knowledge nor in bowties)
cutmachine :: Ord a => Ord b => Bool -> (b -> b -> b) -> ([Bowtie a b] -> [Bowtie a b]) -> Know a b -> Bowtie a b -> [Bowtie a b] -> (Know a b , [Bowtie a b])
cutmachine v step fun k b l = if inKnow b k then (k , l) else let cuts = fun (cutKnowBowSimple step k b) in cutmachine2 v (addKnow b k) l cuts

cutmachine2 :: Ord a => Ord b => Bool -> Know a b -> [Bowtie a b] -> [Bowtie a b] -> (Know a b , [Bowtie a b])
cutmachine2 v k his [] = (k , his)
cutmachine2 v k his (b : l) =
    if inKnow b k then cutmachine2 v k his l else
        cutmachine2 v (filterKnow b k) (if v then filteraddBowties' b his else
            filteraddsortBowties b his) l

cutmachineIterIO :: Show a => Show b => Ord a => Ord b => Bool -> (b -> b -> b) -> ([Bowtie a b] -> [Bowtie a b]) -> Know a b -> [Bowtie a b] -> IO ()
cutmachineIterIO v step fun k [] = putStr ("Done:\n===============\n" ++ fstringKnow "" k)
cutmachineIterIO v step fun k (b : l) = do {putStrLn (stringSeq (tranBowSeq b)) ; putStrLn "-----" ; let (k' , l') = cutmachine v step fun k b l in cutmachineIterIO v step fun k' l'}

--fullcutmachineIO :: Show a => Show b => Ord a => Ord b => Bool -> (b -> b -> b) -> ([Bowtie a b] -> [Bowtie a b]) -> Know a b -> [Bowtie a b] -> IO ()

-- alternative
putmachine :: Ord a => (b -> b -> b) -> ([Bowtie a b] -> [Bowtie a b]) -> Know a b -> Bowtie a b -> Know a b -> (Know a b , Know a b)
putmachine step fun k b q = let cuts = fun (cutKnowBow step k b) in putmachine2 (addKnow b k) q cuts

putmachine2 :: Ord a => Know a b -> Know a b -> [Bowtie a b] -> (Know a b , Know a b)
putmachine2 k his [] = (k , his)
putmachine2 k his (b : l) =
    if inKnow b k || inKnow b his then putmachine2 k his l else
        putmachine2 (filterKnow b k) (addKnow b his) l

putmachineIterIO :: Show a => Show b => Ord a => (b -> b -> b) -> ([Bowtie a b] -> [Bowtie a b]) -> Know a b -> Know a b-> IO ()
putmachineIterIO step fun k q = case popKnow q of
    Just (b , q')   ->  do {putStrLn (stringSeq (tranBowSeq b)) ; putStrLn "-----" ; let (k' , q'') = putmachine step fun k b q' in putmachineIterIO step fun k' q''}
    Nothing         ->  putStr ("Done:\n===============\n" ++ stringKnow k)




-- Modalities 



-- const 
neg :: Form -> Form
neg a = Imp a (Base "B")

equiv :: Form -> Form -> Form
equiv a b = And [Imp a b , Imp b a]

-- Examples 

empt :: Know Int Int
empt = No

full :: Know Int Int
full = Yes 0

ex012 :: Know Int Int
ex012 = Node 0 (Node 1 No (Node 2 No No (Yes 9)) (Yes 9)) (Node 1 (Node 2 No No (Yes 9)) No No) No

exlis :: [Bowtie Int Int]
exlis = [([(i*2 , True) , (i*2+1 , False)] , 1) | i <- [0..19]] ++ [([(i*2+1 , True) , (i*2+2 , False)] , 1) | i <- [0..18]]

orand :: Form
orand = Ore [And [Base "A" , Base "B"] , And [Base "B" , Base "C"] , And [Base "C" , Base "A"]]

andor :: Form
andor = And [Ore [Base "A" , Base "B"] , Ore [Base "B" , Base "C"] , Ore [Base "C" , Base "A"]]

eximp1 :: Form
eximp1 = Imp orand andor

eximp2 :: Form
eximp2 = Imp andor orand

eximp3 :: Form
eximp3 = equiv orand andor

orandbig :: Form
orandbig = Ore [And [Base a , Base b , Base c] | a <- ["A" , "B" , "C"] , b <- ["B" , "C" , "D"] , c <- ["C" , "D" , "E"] , a < b , b < c]

andorbig :: Form
andorbig = And [Ore [Base a , Base b , Base c] | a <- ["A" , "B" , "C"] , b <- ["B" , "C" , "D"] , c <- ["C" , "D" , "E"] , a < b , b < c]

eximp1big :: Form
eximp1big = Imp orandbig andorbig

eximp2big :: Form
eximp2big = Imp andorbig orandbig

eximp3big :: Form
eximp3big = equiv orandbig andorbig

knowtest :: Know Form Proof
knowtest = let (a , q , bows) = starter [] [] [] [andorbig] [orandbig]   in (tranBowKnow bows)

popper :: Know Form Proof -> IO ()
popper k = do {print "----" ; print k ; print "----" ; case popKnow k of
    Just (b, k') -> do {print b ; popper k'}}

runner :: Bool -> [Form] -> [Form] -> IO ()
runner p assu ques = let (a , q , bows) = starter [] [] [] assu ques   in cutmachineIterIO p Cut squeeze No (squeeze bows)

fullrunner :: [Form] -> [Form] -> IO ()
fullrunner assu ques = 
    let (a , q , bows) = starter [] [] [] assu ques   in 
    fullrunnerIter No (tranBowKnow bows)

fullrunnerIter :: Know Form Proof -> Know Form Proof -> IO ()
fullrunnerIter know No = return () 
fullrunnerIter know cut = do {putStr (fstringKnow "" cut) ; putStrLn "=============" ;
                        let know' = joinKnow know cut in 
                        let cut' =  filter2Know know' (ocutKnow' Cut know') in
                                    --cutKnowKnow Cut know' cut in
                                    --filter2Know know' (cutKnowKnow' Cut know' cut) in 
                        fullrunnerIter know' cut'}


eximps :: [Form]
eximps = [Imp (Base i) (Base j) | i <- ["A" , "B" , "C"] , j <- ["A" , "B" , "C"]]

eximpsbig :: [Form]
eximpsbig = [Imp (Base i) (Base j) | i <- ["A" , "B" , "C" , "D" , "E"] , j <- ["A" , "B" , "C" , "D" , "E"]]

doubnegelim :: Form
doubnegelim = Imp (neg (neg (neg (Base "A")))) (neg (Base "A"))

doubnegintro :: Form
doubnegintro = Imp (Base "A") (neg (neg (Base "A")))

debugS :: Bowtie Form Proof
debugS = cleanBow ([(Base "A" , True) , (Imp (Imp (Base "A") (Base "B")) (Base "B") , False)] , Axiom "Debug" "")

debugK :: Know Form Proof
debugK = Node (Base "A")
    (Node (Base "B") No (Node (Imp (Imp (Base "A") (Base "B")) (Base "B")) No No (Yes (Axiom "Debug" ""))) (Node (Imp (Base "A") (Base "B")) (Yes (Axiom "Debug" "")) No No)) (Node (Base "B") (Node (Imp (Base "A") (Imp (Imp (Base "A") (Base "B")) (Base "B"))) No (Node (Imp (Imp (Base "A") (Base "B")) (Base "B")) No No (Yes (Axiom "Debug" ""))) (Yes (Axiom "Debug" ""))) (Node Bot (Node (Imp (Base "A") (Imp (Imp (Base "A") (Base "B")) (Base "B"))) No (Node (Imp (Imp (Base "A") (Base "B")) (Base "B")) No No (Yes (Axiom "Debug" ""))) (Yes (Axiom "Debug" ""))) (Node (Imp (Base "A") (Base "B")) (Node (Imp (Base "A") (Imp (Imp (Base "A") (Base "B")) (Base "B"))) No No (Yes (Axiom "Debug" ""))) (Node (Imp (Base "A") (Imp (Imp (Base "A") (Base "B")) (Base "B"))) No No (Node (Imp (Imp (Base "A") (Base "B")) (Base "B")) (Yes (Axiom "Debug" "")) No No)) No) No) (Node Bot (Yes (Axiom "Debug" "")) No No)) (Node Bot (Yes (Axiom "Debug" "")) No No)

debugK1 :: Know Form Proof
debugK1 = Yes (Axiom "Debug" "")

exImperA :: [Form]
exImperA = [Imp (And [Base "A" , Base "B"]) (Base "C") , Imp (Base "A") (Ore [Base "B" , Base "C"])]

exImperQ :: [Form]
exImperQ = [Imp (Base "A") (Base "C")]


main :: IO ()
--main = --print (mergeKnowBow (+) (debugK1) ([] , 1))
--    print (cutKnowBow (+) debugK debugS)

-- 391 seconds
-- orandbig => andorbig, depth-first: 34.886, breadth: too long
-- andorbif => orandbig, depth-first: 14.867, breadh: 18.924
--main = let (a , q , bows) = starter [] [] [] [andorbig] [orandbig]   in cutmachineIterIO False (+) squeeze No bows
--main = let (a , q , bows) = starter [] [] [] [andorbig , orandbig] [orandbig]   in putmachineIterIO (+) No (tranBowKnow bows)

--main = popper knowtest

--main = let (a , q , bows) = starter [] [] [] [andor , orand] [andor , orand]   in cutmachineIterIO False (+) squeeze No bows

-- Just introduced simple cuts, time tests

-- eximp1big :  depth-first,    simple-cuts:    35.761 sec
--              depth-first,    all-cuts:       41.942 sec

-- eximp2big :  depth-first,    all-cuts:       40.144 sec
--              depth-first,    simple-cuts:    3.84 sec
--              breadth-first,  simple-cuts:    129.33 sec/141.509

-- eximp3big : depth-first,     simple-cuts:    621.787 sec

--main = runner True [] [eximp1big]

main = fullrunner [] [eximp2]

--main = runner True exImperA exImperQ

--main = print (disForm andorbig True)

-- eximp1big : 19.026, eximp2big : 10.502
--main = runner True [] [eximp1big]

--main = runner True eximps eximps

--main = runner True [] [doubnegelim]

--main = cutmachineIterIO (+) No exlis
--main = putStr (stringKnow ex012)
--main = putStr (stringBowties (cutKnowBow (+) ex012 ([(0 , False) , (2 , True) , (3 , False) , (4 , True)] , 7)))