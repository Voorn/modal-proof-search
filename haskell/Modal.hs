module Modal where

import SetList
import Knowledge

-- These specify the modal axioms. They need to satisfy certain properties in order to admit a terminating and exhaustive proof search. 
-- a) imp M N = true stands for M => N, and must be a transitive and reflexive relation.
-- b) lat M N = R means M => R, N => R and for any S where M => S and N => S, then R => S 
--      lat M N is defined if a common upper bound exists (which hence needs to be a smallest upper bound)
-- c) cou M = true means M => (). Must be compatible with Imp, that is, if M => N and N => () then M => (). 
-- d) awa M -> (N , R) means M => N R. This needs to satisfy the following properties:
--      d1) compatibility with cou, if M => N R and N => () then M => R. And if M => N R and R => () then M => N 
--      d2) semicompatibility with imp. If M' => M and M => N R, then there must be an N' and R' such that M' => N' R' and N' => N and R' => R
--      d3) selfcomaptivbility. If M => N R and N => S T, then there are K, S', T', R' such that M => S' K and K => T' R' and S' => S and T' => T and R' => R
class Lat m where
    imp :: m -> m -> Bool
    lat :: m -> m -> Maybe m
    cou :: m -> Bool
    awa :: m -> [(m , m)]
    omi :: m -> m -> Maybe m 
    def :: m

latSplit :: Eq m => Lat m => m -> m -> m -> Bool
latSplit m n r
  = foldr ((||) . (\ (n', r') -> imp r' r && imp n' n)) False (awa m)

omiU :: Lat m => m -> m -> m 
omiU m n = case omi m n of 
    Just r      ->  r 
    _           ->  def


instance Ord a => Top (Know a b) where
    is1 :: Know a b -> Bool
    is1 = isyesKnow

    fil2 :: Know a b -> Know a b -> Maybe (Know a b)
    fil2 x y = let k = filter2Know x y in if isnoKnow k then Nothing else Just k

    joi :: Know a b -> Know a b -> Know a b
    joi = joinKnow

instance Ord a => Struct (Bowtie a b) (Know a b) where
    emb :: Bowtie a b -> Know a b
    emb = newKnow

    ind :: Bowtie a b -> Know a b -> Bool
    ind = inKnow

    fil :: Bowtie a b -> Know a b -> Maybe (Know a b)
    fil b x =  let k = filterKnow b x in if isnoKnow k then Nothing else Just k

    add :: Ord a => Bowtie a b -> Know a b -> Know a b
    add = addKnow

    pop :: Ord a => Know a b -> Maybe (Bowtie a b, Maybe (Know a b))
    pop k = popKnow k >>= \(x , y) -> Just (x , if isnoKnow y then Nothing else Just y)

    weak :: Bowtie a b -> Know a b -> Know a b
    weak b k = tranBowKnow (mergeKnowBow const k b)


data MBowtie m a b =
    MBas (Bowtie a b)
    |   MBin [a] m (Bowtie a b)

instance (Eq m , Eq a) => Eq (MBowtie m a b) where 
  (==) :: (Eq m, Eq a) => MBowtie m a b -> MBowtie m a b -> Bool
  (==) (MBas (r , b)) (MBas (r' , b'))              =   r == r' 
  (==) (MBin l m (r , b)) (MBin l' m' (r' , b'))    =   l == l' && m == m' && r == r'
  (==) x y                                          =   False  

instance (Ord m , Ord a) => Ord (MBowtie m a b) where 
  (<=) :: (Ord m, Ord a) => MBowtie m a b -> MBowtie m a b -> Bool
  (<=) (MBas (r , b)) (MBas (r' , b'))              =   r <= r' 
  (<=) (MBas x) (MBin l m y)                        =   True
  (<=) (MBin l m (r , b)) (MBin l' m' (r' , b'))    =   m < m' || (m == m' && (r < r' || (r == r' && l <= l'))) 
  (<=) x y                                          =   False  


instance (Show m , Show a , Show b) => Show (MBowtie m a b) where
    show :: MBowtie m a b -> String
    show (MBas bow) = stringBowtie bow
    show (MBin a m bow) = stringList a ++ "[" ++ show m ++ "] " ++ stringBowtie bow

impMBowtie :: Ord a => Lat m => MBowtie m a b -> MBowtie m a b -> Bool
impMBowtie (MBas b1) (MBas b2) = impBowtie b1 b2
impMBowtie (MBin l1 m1 b1) (MBin l2 m2 b2) = imp m1 m2 && subSet l1 l2 && impBowtie b1 b2
impMBowtie x y = False

filteraddMBowties :: Ord a => Lat m => MBowtie m a b -> [MBowtie m a b] -> [MBowtie m a b]
filteraddMBowties b [] = [b]
filteraddMBowties b (c : l)
    |   impMBowtie c b   =   c : l
    |   impMBowtie b c   =   filteraddMBowties b l
    |   otherwise       =   c : filteraddMBowties b l

filteraddMBowtiesAll :: Lat m => Ord a => [MBowtie m a b] -> [MBowtie m a b] -> [MBowtie m a b]
filteraddMBowtiesAll l r = foldl (flip filteraddMBowties) r l

filterMBowties :: Lat m => Ord a => MBowtie m a b -> [MBowtie m a b] -> Maybe [MBowtie m a b]
filterMBowties b [] = Just []
filterMBowties b (c : l)
    |   impMBowtie b c   =   filterMBowties b l
    |   impMBowtie c b   =   Nothing
    |   otherwise       =   fmap (c :) (filterMBowties b l)

filteraddMBowties' :: Lat m => Ord a => MBowtie m a b -> [MBowtie m a b] -> [MBowtie m a b]
filteraddMBowties' b l = case filterMBowties b l of
    Just l'     ->  b : l'
    _           ->  l

filteraddMBowtiesAll' :: Lat m => Ord a => [MBowtie m a b] -> [MBowtie m a b] -> [MBowtie m a b]
filteraddMBowtiesAll' l r = foldr filteraddMBowties' r l

filteraddMBowtiesSort :: Ord m => Lat m => Ord a => MBowtie m a b -> [MBowtie m a b] -> [MBowtie m a b]
filteraddMBowtiesSort b [] = [b]
filteraddMBowtiesSort b (c : l)
    |   b < c           =   filteraddMBowties' b (c : l)
    |   impMBowtie b c  =   filteraddMBowtiesSort b l 
    |   impMBowtie c b  =   c : l 
    |   otherwise       =   c : filteraddMBowtiesSort b l

filteraddMBowtiesSortAll :: Ord m => Lat m => Ord a => [MBowtie m a b] -> [MBowtie m a b] -> [MBowtie m a b]
filteraddMBowtiesSortAll l r = foldr filteraddMBowtiesSort r l

cleanMBowties :: Ord a => Lat m => [MBowtie m a b] -> [MBowtie m a b]
cleanMBowties = foldr filteraddMBowties' []

cleanMBow :: Ord a => MBowtie m a b -> MBowtie m a b
cleanMBow (MBas bow) = MBas (cleanBow bow)
cleanMBow (MBin a m bow) = MBin (sortSet a) m (cleanBow bow)

type MKnow m a b = (Know a b , [(m , Data a (Know a b))])

fstringDataKnow :: Show a => Show b => String -> String -> Data a (Know a b) -> String
fstringDataKnow s m (SetList.Yes b) = fstringKnow (s ++ m) b
fstringDataKnow s m SetList.No = ""
fstringDataKnow s m (Bran a l r) = s ++ show a ++ "\n" ++ fstringDataKnow (s ++ "+ ") m l ++ fstringDataKnow s m r

stringMKnow :: Show m => Show a => Show b => MKnow m a b -> String
stringMKnow (Knowledge.No , []) = ""
stringMKnow (Knowledge.No , (m , k) : t) = show m ++ "\n" ++ fstringDataKnow "" ("[" ++ show m ++ "] ") k ++ "\n\n" ++ stringMKnow (Knowledge.No , t)
stringMKnow (k , t) = fstringKnow "" k ++ "\n" ++ stringMKnow (Knowledge.No , t)

filterMKnow :: Ord a => Lat m => MBowtie m a b -> MKnow m a b -> MKnow m a b
filterMKnow (MBas bow) (know , list) = (filterKnow bow know , list)
filterMKnow (MBin l m bow) (know , list) = (know , maybeList (fmap (\(n , dat) ->
    if imp m n then
        filterData (\ x y -> let p = filterKnow x y in if isnoKnow p then Nothing else Just p) (l , bow) dat >>= \x -> Just (n , x)
    else Just (n , dat)) list))

inMKnow :: Ord a => Lat m => MBowtie m a b -> MKnow m a b -> Bool
inMKnow (MBas bow) (know , list) = inKnow bow know
inMKnow (MBin l m bow) (know , []) = inKnow bow know
inMKnow (MBin l m bow) (know , (n , dat) : t)
    |   imp n m         =   inData inKnow (l , bow) dat || inMKnow (MBin l m bow) (know , t)
    |   otherwise       =   inMKnow (MBin l m bow) (know , t)

addMKnow :: Ord a => Ord m => Lat m => MBowtie m a b -> MKnow m a b -> MKnow m a b
addMKnow (MBas bow) (know , lis) = (addKnow bow know , lis >>= \(m , dat) ->
    case filterData (\ x y -> let z = filterKnow x y in if isnoKnow z then Nothing else Just z ) ([] , bow) dat of
        Nothing     ->  []
        Just dat'   ->  [(m , dat')])
addMKnow (MBin l m bow) (know , t) = addMKnow2 True (know , []) l m bow t


addMKnow2 :: Ord a => Ord m => Lat m => Bool -> MKnow m a b -> [a] -> m -> Bowtie a b -> [(m , Data a (Know a b))] -> MKnow m a b
addMKnow2 b (hknow , hlis) l m bow [] = if b then (hknow , hlis ++ [(m , sinData newKnow (l , bow))]) else (hknow , hlis)
addMKnow2 b (hknow , hlis) l m bow ((n , dat) : t)
    |   m == n      =   addMKnow2 False (hknow , hlis ++ [(m , addData addKnow
                                                                (\ x y -> let p = filterKnow x y in if isnoKnow p then Nothing else Just p)
                                                                newKnow (l , bow) dat)]) l m bow t
    |   m < n && b  =   addMKnow2 False (hknow , hlis ++ [(m , sinData newKnow (l , bow))]) l m bow ((n , dat) : t)
    |   imp m n     =
        case filterData (\ x y -> let p = filterKnow x y in if isnoKnow p then Nothing else Just p) (l , bow) dat of
            Nothing     ->  addMKnow2 b (hknow , hlis) l m bow t
            Just x    ->  addMKnow2 b (hknow , hlis ++ [(n , x)]) l m bow t
    |   otherwise   =   addMKnow2 b (hknow , hlis ++ [(n , dat)]) l m bow t

cutMKnowMBow :: Ord a => Lat m => (b -> b -> b) -> MKnow m a b -> MBowtie m a b -> [MBowtie m a b]
cutMKnowMBow step (know , t) (MBas bow) = fmap MBas (cutKnowBow step know bow) ++ cutMKnowMBowBasMod step t bow
cutMKnowMBow step (know , t) (MBin l m bow) = (cutKnowBow step know bow >>= \cut -> [MBin l m cut]) ++ cutMKnowMBowBinMod step t l m bow

cutMKnowMBowBasMod :: Ord a => Lat m => (b -> b -> b) -> [(m , Data a (Know a b))] -> Bowtie a b -> [MBowtie m a b]
cutMKnowMBowBasMod step [] bow = []
cutMKnowMBowBasMod step ((n , dat) : t) bow =
    (opperData (flip (cutKnowBow step)) ([] , bow) dat  >>= \(ml , mbow) -> [MBin ml n mbow]) ++ cutMKnowMBowBasMod step t bow

cutMKnowMBowBinMod :: Ord a => Lat m => (b -> b -> b) -> [(m , Data a (Know a b))] -> [a] -> m -> Bowtie a b -> [MBowtie m a b]
cutMKnowMBowBinMod step [] l m bow = []
cutMKnowMBowBinMod step ((n , dat) : t) l m bow = case lat m n of
    Just mn         ->  (opperData (flip (cutKnowBow step)) (l , bow) dat  >>= \(ml , mbow) -> [MBin ml mn mbow]) ++ cutMKnowMBowBinMod step t l m bow
    Nothing         ->  cutMKnowMBowBinMod step t l m bow


-- simple version
cutMKnowMBowS :: Ord a => Lat m => (b -> b -> b) -> Bool -> MKnow m a b -> MBowtie m a b -> [MBowtie m a b]
cutMKnowMBowS step b (know , t) (MBas bow) = fmap MBas (cutKnowBowS step b know bow) -- ++ cutMKnowMBowBasModS step b t bow
cutMKnowMBowS step b (know , t) (MBin l m bow) = (cutKnowBowS step b know bow >>= \cut -> [MBin l m cut]) ++ cutMKnowMBowBinModS step b t l m bow

cutMKnowMBowBasModS :: Ord a => Lat m => (b -> b -> b) -> Bool -> [(m , Data a (Know a b))] -> Bowtie a b -> [MBowtie m a b]
cutMKnowMBowBasModS step b [] bow = []
cutMKnowMBowBasModS step b ((n , dat) : t) bow =
    (opperData (flip (cutKnowBowS step b)) ([] , bow) dat  >>= \(ml , mbow) -> [MBin ml n mbow]) ++ cutMKnowMBowBasModS step b t bow

cutMKnowMBowBinModS :: Ord a => Lat m => (b -> b -> b) -> Bool -> [(m , Data a (Know a b))] -> [a] -> m -> Bowtie a b -> [MBowtie m a b]
cutMKnowMBowBinModS step b [] l m bow = []
cutMKnowMBowBinModS step b ((n , dat) : t) l m bow = case lat m n of
    Just mn         ->  (opperData (flip (cutKnowBowS step b)) (l , bow) dat  >>= \(ml , mbow) -> [MBin ml mn mbow]) ++ cutMKnowMBowBinModS step b t l m bow
    Nothing         ->  cutMKnowMBowBinModS step b t l m bow

complexM :: MBowtie m a b -> Bool
complexM (MBas f) = countCons f > 1
complexM f = True

cutMKnowMBowSimple :: Lat m => Ord a => (b -> b -> b) -> MKnow m a b -> MBowtie m a b -> [MBowtie m a b]
cutMKnowMBowSimple step mknow  bow
    |   complexM bow            =   cutMKnowMBowS step True mknow bow
    |   otherwise               =   cutMKnowMBow step mknow bow