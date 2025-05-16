module SetList where

class Top a where
    is1 :: a -> Bool
    fil2 :: a -> a -> Maybe a
    joi :: a -> a -> a

-- Structure has datapoint type a and data collection type b
class Struct a b where
    -- generate structure b from single datapoint a
    emb :: a -> b
    -- check if datapoint a is covered by b
    ind :: a -> b -> Bool
    -- remove anything covered by a from b, returning Nothing if result is empty
    fil :: a -> b -> Maybe b
    -- add new data point a to database b
    add :: a -> b -> b
    -- pop data point a from database b. Return Nothing if database was empty.
    pop :: b -> Maybe (a , Maybe b)
    -- weaken all datapoints in data base b by datapoint a 
    weak :: a -> b -> b

type Info = String

instance Top Info where
    is1 :: Info -> Bool
    is1 p = True

    fil2 :: Info -> Info -> Maybe Info
    fil2 m r = Nothing

    joi :: Info -> Info -> Info
    joi m n = m

instance Struct Info Info where
    emb :: Info -> Info
    emb m = m

    ind :: Info -> Info -> Bool
    ind a b = True

    fil :: Info -> Info -> Maybe a
    fil a b = Nothing

    add :: Info -> Info -> Info
    add a b = a

    pop :: Info -> Maybe (Info , Maybe Info)
    pop m = Just (m , Nothing)

    weak :: Info -> Info -> Info 
    weak m n = n





-- A chain is a sorted list together with a continuation
type Chain a b = ([a] , b)

-- whether one chain is contained in another
subChain :: Ord a => (b -> b -> Bool) -> Chain a b -> Chain a b -> Bool
subChain rel ([] , b) (l' , b') =   rel b b'
subChain rel (l , b) ([] , b')  =   False
subChain rel (a : l , b) (a' : l' , b')
    |   a < a'      =   False
    |   a == a'     =   subChain rel (l , b) (l' , b')
    |   otherwise   =   subChain rel (l , b) (a' : l' , b')

-- Data is supposed to collect minimal sets of chains.
--      End b           denotes the end of a Chain, with associated continuation.
--      Node a cy cn    separates chains with a to those without a.
data Data a b =
    Yes b
    |   No
    |   Bran a (Data a b) (Data a b)
    deriving Show
-- Properties it should satisfy:
-- 1) if y : a occurs within a branching of Bran x, then x < y 
-- 2) Yes cannot contain no data
-- 3) the left branch cannot be No
-- 4) Nothing in the right branch may cover the left branch

wrapData :: Maybe (Data a b) -> Data a b
wrapData Nothing = No
wrapData (Just t) = t

noData :: Data a b -> Bool
noData No = True
noData d = False

allData :: (b -> Bool) -> Data a b -> Bool
allData is1 (Yes b) = is1 b
allData is1 t = False



filterData2 :: Ord a => (b -> b -> Maybe b) -> Data a b -> Data a b -> Maybe (Data a b)
filterData2 fil No t                    =   Just t
filterData2 fil t No                    =   Just No
filterData2 fil (Yes b) (Yes c)         =   fil b c >>= \d -> Just (Yes d)
filterData2 fil (Yes b) (Bran a l r)    =   case filterData2 fil (Yes b) l of
    Nothing ->  filterData2 fil (Yes b) r
    Just nl ->  Just (Bran a nl (wrapData (filterData2 fil (Yes b) l)))
filterData2 fil (Bran a l r) (Bran a' l' r')
    |   a == a'     =   case filterData2 fil l (wrapData (filterData2 fil r l')) of
            Nothing     ->  filterData2 fil r r'
            Just nl     ->  Just (Bran a nl (wrapData (filterData2 fil r r')))
    |   a < a'      =   case filterData2 fil r l' of
            Nothing     ->  filterData2 fil r r'
            Just nl     ->  Just (Bran a nl (wrapData (filterData2 fil r r')))
    |   otherwise   =   case filterData2 fil (Bran a l r) l' of
            Nothing     ->  filterData2 fil (Bran a l r) r'
            Just nl     ->  Just (Bran a nl (wrapData (filterData2 fil (Bran a l r) r')))

joinData :: Ord a => (b -> b -> Maybe b) -> (b -> b -> b) -> Data a b -> Data a b -> Data a b
joinData fil vee No t = t
joinData fil vee t No = t
joinData fil vee (Yes b) (Yes b') = Yes (vee b b')
joinData fil vee (Yes b) (Bran a l r) =
    let nr = joinData fil vee (Yes b) r in case filterData2 fil nr l of
        Nothing -> nr
        Just nl -> Bran a nl nr
joinData fil vee (Bran a l r) (Yes b) =
    let nr = joinData fil vee r (Yes b) in case filterData2 fil nr l of
        Nothing -> nr
        Just nl -> Bran a nl nr
joinData fil vee (Bran a l r) (Bran a' l' r')
    |   a == a'     =   let (nl , nr) = (joinData fil vee l l' , joinData fil vee r r') in
            case filterData2 fil nr nl of
                Nothing     ->  nr
                Just nl'    ->  Bran a nl' nr
    |   a < a'      =   case filterData2 fil (Bran a' l' r') l of
            Nothing     ->  joinData fil vee r (Bran a' l' r')
            Just nl     ->  Bran a nl (joinData fil vee r (Bran a' l' r'))
    |   otherwise   =   case filterData2 fil (Bran a l r) l' of
            Nothing     ->  joinData fil vee (Bran a l r) r'
            Just nl     ->  Bran a' nl (joinData fil vee (Bran a l r) r')



instance (Top b , Ord a) =>  Top (Data a b) where
    is1 :: Data a b -> Bool
    is1 (Yes b) = is1 b
    is1 t = False

    fil2 :: Data a b -> Data a b -> Maybe (Data a b)
    fil2 = filterData2 fil2

    joi :: Data a b -> Data a b -> Data a b
    joi = joinData fil2 joi

-- Whether a Chain is covered by the data set
sinData :: (b -> c) -> Chain a b -> Data a c
sinData em ([] , b)        =   Yes (em b)
sinData em (a : l , b)     =   Bran a (sinData em (l , b)) No

inData :: Ord a => (b -> c -> Bool) -> Chain a b -> Data a c -> Bool
inData rel (l , b)  (Yes c)             =   rel b c
inData rel (l , b) No                   =   False
inData rel ([] , b) (Bran a' cy cn)     =   inData rel ([] , b) cn
inData rel (a : l , b) (Bran a' cy cn)
    |   a < a'      =   inData rel (l , b) (Bran a' cy cn)
    |   a == a'     =   inData rel (l , b) cy || inData rel (l , b) cn
    |   otherwise   =   inData rel (a : l , b) cn

-- Cut everything covered by the chain from the Data set 
filterData :: Ord a => (b -> c -> Maybe c) -> Chain a b -> Data a c -> Maybe (Data a c)
filterData fil ([] , b) (Yes c) = case fil b c of
    Nothing -> Nothing
    Just c' -> Just (Yes c')
filterData fil (a : l , b) (Yes c) = Just (Yes c)
filterData fil (l , b) No = Nothing
filterData fil ([] , b) (Bran a' l r) = 
    case (filterData fil ([] , b) l , filterData fil ([] , b) r) of
        (Nothing , Nothing) ->  Nothing
        (Nothing , Just nr) ->  Just nr
        (Just nl , Nothing) ->  Just (Bran a' nl No)
        (Just nl , Just nr) ->  Just (Bran a' nl nr)
filterData fil (a : l , b) (Bran a' l' r')
    |   a < a'          =   Just (Bran a' l' r')
    |   a == a'         =   case  filterData fil (l , b) l' of
            Nothing     ->  Just r'
            Just nl     ->  Just (Bran a' nl r')
    |   otherwise       =   
            case (filterData fil (a : l , b) l' , filterData fil (a : l , b) r') of
                (Nothing , Nothing) ->  Nothing
                (Nothing , Just nr) ->  Just nr
                (Just nl , Nothing) ->  Just (Bran a' nl No)
                (Just nl , Just nr) ->  Just (Bran a' nl nr)


addData :: Ord a => (b -> c -> c) -> (b -> c -> Maybe c) -> (b -> c) -> Chain a b -> Data a c -> Data a c
addData add fil em ([] , b) (Yes c)         =   Yes (add b c)
addData add fil em (a : l , b) (Yes c)      =   Bran a (sinData em (l , b)) (Yes c)
    --if inD b c then Yes c else Bran a (addData add inD fil em (l , b) No) (Yes c)
addData add fil em (l , b) No               =   sinData em (l , b)
addData add fil em ([] , b) (Bran a' l r)   =   let nr = addData add fil em ([] , b) r in
                                                    case filterData fil ([] , b) l of
                                                    Nothing     ->  nr
                                                    Just nl     ->  Bran a' nl nr
addData add fil em (a : t , b) (Bran a' l r)
    |   a < a'      =   Bran a (sinData em (t , b)) (Bran a' l r)
    |   a == a'     =   Bran a (addData add fil em (t , b) l) r
    |   otherwise   =   case filterData fil (a : t , b) l of
            Nothing     ->  addData add fil em (a : t , b) r
            Just nl     ->  Bran a' nl (addData add fil em (a : t , b) r )

popData :: Ord a => (c -> Maybe (b , Maybe c)) -> Data a c -> Maybe (Chain a b , Maybe (Data a c))
popData po No = Nothing
popData po (Yes b) = po b >>= \(b' , k) -> case k of
    Nothing     ->  Just (([] , b') , Nothing)
    Just nb     ->  Just (([] , b') , Just (Yes nb))
popData po (Bran a l r) =   case popData po l of
    Nothing                     ->  popData po r
    Just ((t , b) , Nothing)    ->  Just ((a : t , b) , if noData r then Nothing else Just r)
    Just ((t , b) , Just k)     ->  Just ((a : t , b) , Just (Bran a k r))

mergeData :: Ord a => (b -> c -> c) -> (c -> c -> Maybe c) -> (c -> c -> c) -> Chain a b -> Data a c -> Data a c
mergeData mer fil joi s No = No
mergeData mer fil joi (l , b) (Yes c) = sinData (`mer` c) (l , b)
mergeData mer fil joi ([] , b) (Bran a l r) = 
    let (nl , nr) = (mergeData mer fil joi ([] , b) l , mergeData mer fil joi ([] , b) r) in 
        case filterData2 fil nr nl of 
            Nothing     ->  nr 
            Just nl'    ->  Bran a nl' nr 
mergeData mer fil joi (a : t , b) (Bran a' l r)
    |   a == a'     =   let k = joinData fil joi l r in Bran a (mergeData mer fil joi (t , b) k) No
    |   a < a'      =   Bran a (mergeData mer fil joi (t , b) (Bran a' l r)) No 
    |   otherwise   =   let (nl , nr) = (mergeData mer fil joi (a : t , b) l , mergeData mer fil joi (a : t , b) r) in 
            case filterData2 fil nr nl of 
                Nothing     ->  nr 
                Just nl'    ->  Bran a' nl' nr 

opperData :: Ord a => (b -> c -> [d]) -> Chain a b -> Data a c -> [Chain a d]
opperData op chain No = []
opperData op ([] , b) (Yes c) = op b c >>= \nb -> [([] , nb)]
opperData op (a : la , b) (Yes c) = opperData op (la , b) (Yes c) >>= \(nla , nb) -> [(a : nla , nb)]
opperData op ([] , b) (Bran a' l' r') = (opperData op ([] , b) l' >>= \(nla , nb) -> [(a' : nla , nb)])
                                        ++ opperData op ([] , b) r'
opperData op (a : la , b) (Bran a' l' r') 
    |   a == a'     =   (opperData op (la , b) l' >>= \(nla , nb) -> [(a : nla , nb)])
                        ++ (opperData op (la , b) r' >>= \(nla , nb) -> [(a : nla , nb)])
    |   a < a'      =   opperData op (la , b) (Bran a' l' r')  >>= \(nla , nb) -> [(a : nla , nb)]
    |   otherwise   =   (opperData op (a : la , b) l' >>= \(nla , nb) -> [(a' : nla , nb)])
                        ++ opperData op (a : la , b) r'


instance (Top c , Struct b c , Ord a) => Struct (Chain a b) (Data a c) where
    emb :: Chain a b -> Data a c
    emb = sinData emb

    ind :: Chain a b -> Data a c -> Bool
    ind = inData ind

    fil :: Chain a b -> Data a c -> Maybe (Data a c)
    fil = filterData fil

    add :: Chain a b -> Data a c -> Data a c
    add = addData add fil emb

    pop :: Data a c -> Maybe (Chain a b, Maybe (Data a c))
    pop = popData pop

    weak :: (Struct b c, Ord a) => Chain a b -> Data a c -> Data a c
    weak = mergeData weak fil2 joi 


type Sequent a = Chain a (Chain a Info)

type Base a = Data a (Data a Info)



cutBase :: Ord a => [a] -> [a] -> Sequent a -> Base a -> Maybe (Base a)
cutBase h1 h2 ([] , ([] , r)) t = Nothing
cutBase h1 h2 s No = Nothing
cutBase h1 h2 ([] , (c2 , p)) (Yes b) = cutBase2 (h1 , (h2 , p)) b >>= \k -> Just (Yes k)
cutBase h1 h2 (a : t , (c2 , p)) (Yes b) = cutBase (h1 ++ [a]) h2 (t , (c2 , p)) (Yes b) >>= \k -> Just (Bran a k No)

cutBase2 :: Ord a => Sequent a -> Data a Info -> Maybe (Data a Info)
cutBase2 l t = Nothing
