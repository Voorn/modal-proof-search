{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use first" #-}
{-# HLINT ignore "Use tuple-section" #-}
module Knowledge where


maybeList :: [Maybe a] -> [a]
maybeList [] = []
maybeList (Nothing : l) = maybeList l
maybeList (Just a : l) = a : maybeList l


-- Proof type: Consists of basic axioms, cut applications, and unary rule
-- The Axioms will include introduction and elimination rules for the basic proof constructors
-- The unary cat rules will include implication-sieve and modal lock

data Proof =
    Axiom String String
    |   Cut Proof Proof
    |   Cat String String Proof

instance Show Proof where
    show :: Proof -> String
    --show s = show (measProof s)
    show (Axiom s z) = s
    show (Cut a b) = "(" ++ show a ++ ")" ++ show b
    show (Cat s z a) = s ++ "{" ++ show a ++ "}"

-- The size of a proof
measProof :: Proof -> Int
measProof (Axiom s z) = 0
measProof (Cut a b) = 1 + measProof a + measProof b
measProof (Cat s z a) = 1 + measProof a

instance Eq Proof where
    (==) :: Proof -> Proof -> Bool
    a == b = measProof a == measProof b

instance Ord Proof where
    (<=) :: Proof -> Proof -> Bool
    a <= b = measProof a <= measProof b

stringCol :: String -> String -> (a -> String) -> [a] -> String
stringCol emp bet f [] = emp
stringCol emp bet f [a] = f a
stringCol emp bet f l = "(" ++ stringCol' bet f l ++ ")"

stringCol' :: String -> (a -> String) -> [a] -> String
stringCol' bet f [a] = f a
stringCol' bet f (a : l) = f a ++ bet ++ stringCol' bet f l


-- Some basic operations. Lists are considered unsorted, whereas Sets are sorted non-repeating lists.
-- Sets have some more efficient operations.

-- Check if an element is contained in a list
inList :: Eq a => a -> [ a ] -> Bool
inList a [] = False
inList a (b : l)
    |   a == b      =   True
    |   otherwise   =   inList a l

-- Filter the List: Remove all instances of an element from a list
filList :: Eq a => a -> [ a ] -> [ a ]
filList a [] = []
filList a (b : r)
    |   a == b      =   filList a r
    |   otherwise   =   b : filList a r

difList :: Ord a => [ a ] -> [ a ] -> Bool
difList [] r = True 
difList (a : l) r = not (inList a r) && difList l r

-- Check if an element is contained in a set
inSet :: Ord a => a -> [ a ] -> Bool
inSet a [] = False
inSet a (b : l)
    |   a > b       =   inSet a l
    |   otherwise   =   a == b

-- Check if all elements of one set are contained in another
subSet :: Ord a => [a] -> [a] -> Bool
subSet [] r = True
subSet l [] = False
subSet (a : l) (b : r)
    |   a < b       =   False
    |   a == b      =   subSet l r
    |   otherwise   =   subSet (a : l) r

-- Check if two sets are disjoint
difSet :: Ord a => [ a ] -> [ a ] -> Bool
difSet l [] = True
difSet [] r = True 
difSet (a : l) (b : r)
    |   a == b      =   False 
    |   a <  b      =   difSet l (b : r)
    |   otherwise   =   difSet (a : l) r

-- Add an element to a set
addSet :: Ord a => a -> [ a ] -> [ a ]
addSet a [] = [a]
addSet a (b : l)
    |   a > b       =   b : addSet a l
    |   a == b      =   b : l
    |   otherwise   =   a : b : l

-- Take the union of two sets
joinSet :: Ord a => [a] -> [a] -> [a]
joinSet [] r = r 
joinSet l [] = l 
joinSet (a : l) (b : r) 
    |   a == b      =   a : joinSet l r 
    |   a < b       =   a : joinSet l (b : r)
    |   otherwise   =   b : joinSet (a : l) r

-- Take a list and turn it into a set
sortSet :: Ord a => [ a ] -> [ a ]
sortSet = foldr addSet []


-- The Bowtie type represent a proven sequent.
-- It has a list of elements of a, with Boolean to determine whether it is an assumption "True", or a consequence "False"
-- List is sorted on a, and does not contain repeats. 
-- Further information, such as the proof, can be stored in b. 
type Bowtie a b = ([(a , Bool)] , b)

-- Add a new element to a Bowtie
addBow :: Ord a => (a , Bool) -> Bowtie a b -> Bowtie a b
addBow (a , k) ([] , f) = ([(a , k)] , f)
addBow (a , k) ((b , v) : l , f)
    |   a < b       =   ((a , k) : (b , v) : l , f)
    |   a == b      =   ((b , v) : l , f)
    |   otherwise   =   let (l' , f') = addBow (a , k) (l , f) in ((b , v) : l' , f')

-- Take a disorganized bowtie, sort it and remove duplicates.
-- This is partially unsafe: when input has an a as both assumption and consequence, result will not be a bowtie
cleanBow :: Ord a => Bowtie a b -> Bowtie a b
cleanBow ([] , f) = ([] , f)
cleanBow ((a , k) : l , f) = addBow (a , k) (cleanBow (l , f))

-- Whether one bowtie implies the other
impBowtie :: Ord a => Bowtie a b -> Bowtie a b -> Bool
impBowtie ([] , f) r = True
impBowtie l ([] , g) = False
impBowtie ((a , v) : l , f) ((b , w) : r , g)
    |   a < b       =   False
    |   a == b      =   (v == w) && impBowtie (l , f) (r , g)
    |   otherwise   =   impBowtie ((a , v) : l , f) (r , g)

--compBowtie :: Ord a => Bowtie a b -> Bowtie a b -> Comp 
--compBowtie ([] , f) ([] , g) = Same 
--compBowtie ([] , f) (r , g) = Better 
--compBowtie (l , f) ([] , g) = Worse 
--compBowtie ((a , v) : l , f) ((b , w) : r , g) 
--    |   a < b       =   

-- Whether the bowties is implied by any of the other bowties
inBowties :: Ord a => Bowtie a b -> [Bowtie a b] -> Bool
inBowties b = foldr (\ c -> (||) (impBowtie c b)) False

-- Add bowtie to bowties, filtering out any already covered, O(n+sum m)
filteraddBowties :: Ord a => Bowtie a b -> [Bowtie a b] -> [Bowtie a b]
filteraddBowties b [] = [b]
filteraddBowties b (c : l)
    |   impBowtie c b   =   c : l
    |   impBowtie b c   =   filteraddBowties b l
    |   otherwise       =   c : filteraddBowties b l

filterBowties :: Ord a => Bowtie a b -> [Bowtie a b] -> Maybe [Bowtie a b]
filterBowties b [] = Just []
filterBowties b (c : l)
    |   impBowtie c b   =   Nothing
    |   impBowtie b c   =   filterBowties b l
    |   otherwise       =   fmap (c :) (filterBowties b l)

filteraddBowties' :: Ord a => Bowtie a b -> [Bowtie a b] -> [Bowtie a b]
filteraddBowties' b l = case filterBowties b l of
    Just l'     ->  b : l'
    _           ->  l


filterBowties' :: Ord a => Bowtie a b -> [Bowtie a b] -> [Bowtie a b]
filterBowties' b [] = []
filterBowties' b (c : l)
    |   impBowtie b c   =   filterBowties' b l
    |   otherwise       =   c : filterBowties' b l

filteraddsortBowties :: Ord a => Ord b => Bowtie a b -> [Bowtie a b] -> [Bowtie a b]
filteraddsortBowties b [] = [b]
filteraddsortBowties b (c : l)
    |   impBowtie c b   =   c : l
    |   impBowtie b c   =   filteraddsortBowties b l
    |   snd b < snd c   =   b : c : filterBowties' b l
    |   otherwise       =   c : filteraddsortBowties b l

-- Make sure none of the bowties imply eachother O((sum m)^2)
cleanBowties :: Ord a => [Bowtie a b] -> [Bowtie a b]
cleanBowties = foldr filteraddBowties []


-- Knowledge structure: Bowties wrapped into a tree
-- Nodes have instance of a, with three branches telling whether it is: assumed, not considered, or concluded.
-- Leaves with Yes b confirm existence of sequent, with further information stored in b
-- Leaves with No denote the inexistence of the sequent
data Know a b =
    Yes b
    |   No
    |   Node a (Know a b) (Know a b) (Know a b)
    deriving Show

isyesKnow :: Know a b -> Bool
isyesKnow (Yes b) = True
isyesKnow t = False

-- normal form details, which are to be maintained:
-- 1) The a's in the nodes are sorted
-- 2) "Node a No m No" cannot exist, this is "m" (a does not determine truth)
-- 3) "Node a x (Yes b) y" cannot exist, this is "Yes b" (truth is regardless of a)

-- Fancy way of displaying knowledge
fstringKnow :: Show a => Show b => String -> Know a b -> String
fstringKnow s No = ""
fstringKnow s (Yes f) = s ++ show f ++ "\n"
fstringKnow s (Node a x m y) = s ++ show a ++ "\n" ++ fstringKnow (s ++ "+ ") x ++ fstringKnow (s ++ "- ") y ++ fstringKnow s m

-- Whether we have no knowledge
isnoKnow :: Know a b -> Bool
isnoKnow No = True
isnoKnow t = False

-- Remove everything from Know which is covered by the Bowtie
filterKnow :: Ord a => Bowtie a b -> Know a b -> Know a b
filterKnow ([] , f) t = No
filterKnow (l , f) No = No
filterKnow ((a , t) : l , f) (Yes b) = Yes b
filterKnow ((a , t) : l , f) (Node b x m y)
    |   a < b       =   Node b x m y
    |   a == b      =
            if t then let x' = filterKnow (l , f) x in
                if isnoKnow x' && isnoKnow y then m else Node b x' m y
            else let y' = filterKnow (l , f) y in
                if isnoKnow y' && isnoKnow x then m else Node b x m y'
    |   otherwise   =   let (x' , y') = (filterKnow ((a , t) : l , f) x , filterKnow ((a , t) : l , f) y) in
            if isnoKnow x' && isnoKnow y' then filterKnow ((a , t) : l , f) m else Node b x' (filterKnow ((a , t) : l , f) m) y'

-- Remove everything from the second data implied by the first data
filter2Know :: Ord a => Know a b -> Know a b -> Know a b
filter2Know (Yes s) t = No
filter2Know No t = t
filter2Know l No = No
filter2Know (Node a x m y) (Yes b) = Yes b      -- Note that "m" cannot simply be a Yes, since the node exists. Hence there is no filter needed
filter2Know (Node a ax am ay) (Node b bx bm by)
    |   a < b       =   filter2Know am (Node b bx bm by)
    |   a == b      =   let (bx' , by') = (filter2Know am (filter2Know ax bx) , filter2Know am (filter2Know ay by)) in
                if isnoKnow bx' && isnoKnow by' then filter2Know am bm else Node b bx' (filter2Know am bm) by'
    |   otherwise   =   let (bx' , by') = (filter2Know (Node a ax am ay) bx , filter2Know (Node a ax am ay) by) in
            if isnoKnow bx' && isnoKnow by' then filter2Know am bm else Node b bx' (filter2Know (Node a ax am ay) bm) by'

joinKnow :: Ord a => Know a b -> Know a b -> Know a b
joinKnow No t = t
joinKnow (Yes b) t = Yes b
joinKnow t No = t
joinKnow t (Yes b) = Yes b
joinKnow (Node a l m r) (Node a' l' m' r')
    |   a == a'     =   let (nl , nm , nr) = (joinKnow (filter2Know m' l) (filter2Know m l') , joinKnow m m' , joinKnow (filter2Know m' r) (filter2Know m r')) in
                        if isnoKnow nl && isnoKnow nr then nm else Node a nl nm nr
    |   a < a'      =   let (nl , nr) = (filter2Know (Node a' l' m' r') l , filter2Know (Node a' l' m' r') r) in
                        if isnoKnow nl && isnoKnow nr then joinKnow m (Node a' l' m' r') else Node a nl (joinKnow m (Node a' l' m' r')) nr
    |   otherwise   =   let (nl , nr) = (filter2Know (Node a l m r) l' , filter2Know (Node a l m r) r') in
                        if isnoKnow nl && isnoKnow nr then joinKnow (Node a l m r) m' else Node a' nl (joinKnow (Node a l m r) m') nr

-- Is bowtie covered by Know
inKnow :: Ord a => Bowtie a b -> Know a b -> Bool
inKnow l (Yes b) = True
inKnow l No = False
inKnow ([] , f) t = False
inKnow ((a , k) : l , f) (Node b x m y)
    |   a < b       =   inKnow (l , f) (Node b x m y)
    |   a == b      =   inKnow (l , f) m || if k then inKnow (l , f) x else inKnow (l , f) y
    |   otherwise   =   inKnow ((a , k) : l , f) m

-- Generate new Know from a bowtie
newKnow :: Bowtie a b -> Know a b
newKnow ([] , f) = Yes f
newKnow ((a , k) : l , f) = if k then Node a (newKnow (l , f)) No No else Node a No No (newKnow (l , f))

-- Add Bowtie to Know
-- !!! Unsafe, output may not be a proper Know. Only apply if Bowtie is not in Know
addKnow :: Ord a => Bowtie a b -> Know a b -> Know a b
addKnow l (Yes f) = Yes f
addKnow l No = newKnow l
addKnow ([] , f) t = Yes f
addKnow ((a , k) : l , f) (Node b x m y)
    |   a < b       =
            if k then   Node a (newKnow (l , f)) (Node b x m y) No
            else        Node a No (Node b x m y) (newKnow (l , f))
    |   a == b      =
            if k then   Node a (addKnow (l , f) x) m y
            else        Node a x m (addKnow (l , f) y)
    |   otherwise   =   let (x' , y') = (filterKnow ((a , k) : l , f) x , filterKnow ((a , k) : l , f) y) in
            if isnoKnow x' && isnoKnow y' then addKnow ((a , k) : l , f) m else Node b x' (addKnow ((a , k) : l , f) m) y'

popKnow :: Ord a => Know a b -> Maybe (Bowtie a b , Know a b)
popKnow No = Nothing
popKnow (Yes f) = Just (([] , f) , No)
popKnow (Node a No m y) = case popKnow y of
        Just ((l , f) , No) ->  Just (((a , False) : l , f) , m)
        Just ((l , f) , y') ->  Just (((a , False) : l , f) , Node a No m y')
popKnow (Node a x m No) = case popKnow x of
    Just ((l , f) , No) ->  Just (((a , True) : l , f) , m)
    Just ((l , f) , x') ->  Just (((a , True) : l , f) , Node a x' m No)
popKnow (Node a x m y) =    case popKnow x of
    Just ((l , f) , x') ->  Just (((a , True) : l , f) , Node a x' m y)

filterBowtiesKnow :: Ord a => [Bowtie a b] -> Know a b -> ([Bowtie a b] , Know a b)
filterBowtiesKnow [] k = ([] , k)
filterBowtiesKnow (b : l) k = let (l' , k') = filterBowtiesKnow l k in if inKnow b k' then (l' , k') else (b : l' , filterKnow b k')

-- Add Bowtie to Know
-- Slower, but safe
addKnowSafe :: Ord a => Bowtie a b -> Know a b -> Know a b
addKnowSafe b t = if inKnow b t then t else addKnow b t


tranKnowBow :: Know a b -> [Bowtie a b]
tranKnowBow (Yes b) = [([] , b)]
tranKnowBow No = []
tranKnowBow (Node a x m y) =
    fmap (\(l , f) -> ((a , True) : l , f)) (tranKnowBow x) ++ fmap (\(l , f) -> ((a , False) : l , f)) (tranKnowBow y) ++ tranKnowBow m

tranBowKnow :: Ord a => [Bowtie a b] -> Know a b
tranBowKnow = foldr addKnowSafe No

type Seq a b = ([a] , [a] , b)

tranBowSeq :: Bowtie a b -> Seq a b
tranBowSeq ([] , f) = ([] , [] , f)
tranBowSeq ((a , k) : l , f) = let (x , y , f') = tranBowSeq (l , f) in
    if k then (a : x , y , f') else (x , a : y , f')

stringList :: Show a => [a] -> String
stringList [] = " "
stringList [a] = show a ++ " "
stringList (a : l) = show a ++ ", " ++ stringList l

stringSeq :: Show a => Show b => Seq a b -> String
stringSeq (l , r , f) = show f ++ "\n" ++ stringList l ++ "⊢ " ++ stringList r

stringBowtie :: Show a => Show b => Bowtie a b -> String
stringBowtie bow = let (l , r , f) = tranBowSeq bow in stringList l ++ "⊢ " ++ stringList r ++ "\n" ++ show f

stringBowties :: Show a => Show b => [Bowtie a b] -> String
stringBowties [] = ""
stringBowties (b : l) = stringSeq (tranBowSeq b) ++ "\n" ++ stringBowties l

stringKnow :: Show a => Show b => Know a b -> String
stringKnow k = stringBowties (tranKnowBow k)

-- cuts 
mergeKnowBow :: Ord a => (b -> b -> b) -> Know a b -> Bowtie a b -> [Bowtie a b]
mergeKnowBow step No b = []
mergeKnowBow step (Yes f) (l , g) = [(l , step f g)]
mergeKnowBow step t ([] , g) = fmap (\(l , f) -> (l , step f g)) (tranKnowBow t)
mergeKnowBow step (Node a x m y) ((b , k) : l , g)
    |   a < b       =
            fmap (\(r , f) -> ((a , True) : r , f)) (mergeKnowBow step x ((b , k) : l , g))
            ++  fmap (\(r , f) -> ((a , False) : r , f)) (mergeKnowBow step y ((b , k) : l , g))
            ++  mergeKnowBow step m ((b , k) : l , g)
    |   a == b      =
            fmap (\(r , f) -> ((b , k) : r , f)) (
                (if k then mergeKnowBow step x (l , g) else mergeKnowBow step y (l , g))
                ++ mergeKnowBow step m (l , g))
    |   otherwise   =   fmap (\(r , f) -> ((b , k) : r , f)) (mergeKnowBow step (Node a x m y) (l , g))

cutKnowBow :: Ord a => (b -> b -> b) -> Know a b -> Bowtie a b -> [Bowtie a b]
cutKnowBow step No b = []
cutKnowBow step (Yes f) (l , g) = []
cutKnowBow step t ([] , g) = []
cutKnowBow step (Node a x m y) ((b , k) : l , g)
    |   a < b       =
            fmap (\(r , f) -> ((a , True) : r , f)) (cutKnowBow step x ((b , k) : l , g))
            ++  fmap (\(r , f) -> ((a , False) : r , f)) (cutKnowBow step y ((b , k) : l , g))
            ++  cutKnowBow step m ((b , k) : l , g)
    |   a == b      =
            (if k then
                fmap (\(r , f) -> ((b , k) : r , f)) (cutKnowBow step x (l , g))
                ++  mergeKnowBow step y (l , g)
            else
                fmap (\(r , f) -> ((b , k) : r , f)) (cutKnowBow step y (l , g))
                ++  mergeKnowBow (flip step) x (l , g))
            ++ fmap (\(r , f) -> ((b , k) : r , f)) (cutKnowBow step m (l , g))
    |   otherwise   =   fmap (\(r , f) -> ((b , k) : r , f)) (cutKnowBow step (Node a x m y) (l , g))

-- version which limits to 1 consequent in knowledge base
tranKnowBowS :: Bool -> Know a b -> [Bowtie a b]
tranKnowBowS i (Yes b) = [([] , b)]
tranKnowBowS i No = []
tranKnowBowS i (Node a x m y)
    |   i           =   fmap (\(l , f) -> ((a , True) : l , f)) (tranKnowBowS i x) ++ fmap (\(l , f) -> ((a , False) : l , f)) (tranKnowBowS False y) ++ tranKnowBowS i m
    |   otherwise   =   fmap (\(l , f) -> ((a , True) : l , f)) (tranKnowBowS i x) ++ tranKnowBowS i m

mergeKnowBowS :: Ord a => (b -> b -> b) -> Bool -> Know a b -> Bowtie a b -> [Bowtie a b]
mergeKnowBowS step i No b = []
mergeKnowBowS step i (Yes f) (l , g) = [(l , step f g)]
mergeKnowBowS step i t ([] , g) = fmap (\(l , f) -> (l , step f g)) (tranKnowBowS i t)
mergeKnowBowS step i (Node a x m y) ((b , k) : l , g)
    |   a < b       =
            fmap (\(r , f) -> ((a , True) : r , f)) (mergeKnowBowS step i x ((b , k) : l , g))
            ++  (if i then fmap (\(r , f) -> ((a , False) : r , f)) (mergeKnowBowS step False y ((b , k) : l , g)) else [])
            ++  mergeKnowBowS step i m ((b , k) : l , g)
    |   a == b      =
            fmap (\(r , f) -> ((b , k) : r , f)) (
                (if k then mergeKnowBowS step i x (l , g) else (if i then mergeKnowBowS step False y (l , g) else []))
                ++ mergeKnowBowS step i m (l , g))
    |   otherwise   =   fmap (\(r , f) -> ((b , k) : r , f)) (mergeKnowBowS step i (Node a x m y) (l , g))

cutKnowBowS :: Ord a => (b -> b -> b) -> Bool -> Know a b -> Bowtie a b -> [Bowtie a b]
cutKnowBowS step i No b = []
cutKnowBowS step i (Yes f) (l , g) = []
cutKnowBowS step i t ([] , g) = []
cutKnowBowS step i (Node a x m y) ((b , k) : l , g)
    |   a < b       =
            fmap (\(r , f) -> ((a , True) : r , f)) (cutKnowBowS step i x ((b , k) : l , g))
            ++  (if i then fmap (\(r , f) -> ((a , False) : r , f)) (cutKnowBowS step False y ((b , k) : l , g)) else [])
            ++  cutKnowBowS step i m ((b , k) : l , g)
    |   a == b      =
            (if k then
                fmap (\(r , f) -> ((b , k) : r , f)) (cutKnowBowS step i x (l , g))
                ++  (if i then mergeKnowBowS step False y (l , g) else [])
            else
                fmap (\(r , f) -> ((b , k) : r , f)) (if i then cutKnowBowS step False y (l , g) else [])
                ++  mergeKnowBowS (flip step) i x (l , g))
            ++ fmap (\(r , f) -> ((b , k) : r , f)) (cutKnowBowS step i m (l , g))
    |   otherwise   =   fmap (\(r , f) -> ((b , k) : r , f)) (cutKnowBowS step i (Node a x m y) (l , g))

countCons :: Bowtie a b -> Int
countCons ([] , f) = 0
countCons ((a , True) : l , f) = countCons (l , f)
countCons ((a , False) : l , f) = 1 + countCons (l , f)

cutKnowBowSimple :: Ord a => (b -> b -> b) -> Know a b -> Bowtie a b -> [Bowtie a b]
cutKnowBowSimple step know bow
    |   countCons bow <= 1      =   cutKnowBow step know bow
    |   otherwise               =   cutKnowBowS step True know bow

-- The big ones:
--mergeKnowKnow :: Ord a => Know a b -> Know a b -> Know a b 
--mergeKnowKnow (Yes f) r = Yes f 
--mergeKnowKnow No r = r
--mergeKnowKnow t (Yes g) = Yes g
--mergeKnowKnow t No = t 
--mergeKnowKnow (Node a ax am ay) (Node b bx bm by)
--    |   a == b      =   let cx = 

-- Auotmatic rule applications 
sieveBow :: Eq a => Bowtie a b -> a -> Bowtie a b
sieveBow ([] , f) l = ([] , f)
sieveBow ((a , k) : l , f) r = let (l' , f') = sieveBow (l , f) r in
    if k && (a == r) then (l' , f') else ((a , k) : l' , f')


extractKnow :: Ord a => [a] -> [a] -> Know a b -> Know a b 
extractKnow assu ques (Yes f) = Yes f 
extractKnow assu ques No = No 
extractKnow [] [] (Node a l m r) = extractKnow [] [] m 
extractKnow (b : assu) [] (Node a l m r) 
    |   b < a       =   extractKnow assu [] (Node a l m r) 
    |   b == a      =   let nl = extractKnow assu [] l in if isnoKnow nl then extractKnow assu [] m else Node a nl (extractKnow assu [] m) No
    |   otherwise   =   extractKnow (b : assu) [] m 
extractKnow [] (c : ques) (Node a l m r) 
    |   c < a       =   extractKnow [] ques (Node a l m r) 
    |   c == a      =   let nr = extractKnow [] ques r in if isnoKnow nr then extractKnow [] ques m else Node a No (extractKnow [] ques m) nr
    |   otherwise   =   extractKnow [] (c : ques) m 
extractKnow (b : assu) (c : ques) (Node a l m r) 
    |   b < a               =   extractKnow assu (c : ques) (Node a l m r) 
    |   c < a               =   extractKnow (b : assu) ques (Node a l m r) 
    |   b == a && c == a    =   let nl = extractKnow assu ques l in 
                                let nr = extractKnow assu ques r in  
                                if isnoKnow nl && isnoKnow nr then extractKnow assu ques m else Node a nl (extractKnow assu ques m) nr
    |   b == a              =   let nl = extractKnow assu (c : ques) l in if isnoKnow nl then extractKnow assu (c : ques) m else Node a nl (extractKnow assu (c : ques) m) No
    |   c == a              =   let nr = extractKnow (b : assu)  ques r in if isnoKnow nr then extractKnow (b : assu)  ques m else Node a No (extractKnow (b : assu)  ques m) nr
    |   otherwise           =   extractKnow (b : assu) (c : ques) m


extractQuery :: Ord a => [(a , Bool)] -> ([a] , [a])
extractQuery [] = ([] , [])
extractQuery ((a , True) : l) = let (x , y) = extractQuery l in (addSet a x , y)
extractQuery ((a , False) : l) = let (x , y) = extractQuery l in (x , addSet a y) 

-- merge two knowledge sets, as in pair all sequents
mergeKnowKnow :: Ord a => (b -> b -> b) -> Know a b -> Know a b -> Know a b 
mergeKnowKnow f No t'                       =   No 
mergeKnowKnow f t No                        =   No
mergeKnowKnow f (Yes b) (Yes b')            =   Yes (f b b')
mergeKnowKnow f (Yes b) (Node a' l' m' r')  =   Node a' (mergeKnowKnow f (Yes b) l') (mergeKnowKnow f (Yes b) m') (mergeKnowKnow f (Yes b) r')
mergeKnowKnow f (Node a l m r) (Yes b')     =   Node a (mergeKnowKnow f l (Yes b')) (mergeKnowKnow f m (Yes b')) (mergeKnowKnow f r (Yes b'))
mergeKnowKnow f (Node a l m r) (Node a' l' m' r')   
    |   a < a'                              =   let nm = mergeKnowKnow f m (Node a' l' m' r') in 
                                                let nl = filter2Know nm (mergeKnowKnow f l (Node a' l' m' r')) in 
                                                let nr = filter2Know nm (mergeKnowKnow f r (Node a' l' m' r')) in 
                                                if isnoKnow nl  && isnoKnow nr then nm else Node a nl nm nr
    |   a' < a                              =   let nm = mergeKnowKnow f (Node a l m r) m' in 
                                                let nl = filter2Know nm (mergeKnowKnow f (Node a l m r) l') in 
                                                let nr = filter2Know nm (mergeKnowKnow f (Node a l m r) r') in 
                                                if isnoKnow nl  && isnoKnow nr then nm else Node a' nl nm nr
    |   otherwise                           =   let nm = mergeKnowKnow f m m' in 
                                                let nl = filter2Know nm (joinKnow (mergeKnowKnow f l l') (joinKnow (mergeKnowKnow f l m') (mergeKnowKnow f m l'))) in 
                                                let nr = filter2Know nm (joinKnow (mergeKnowKnow f r r') (joinKnow (mergeKnowKnow f r m') (mergeKnowKnow f m r'))) in 
                                                if isnoKnow nl && isnoKnow nr then nm else Node a nl nm nr 




-- Make sure that a knowledge database has all its own cuts
fullcutKnow :: Ord a  => (b -> b -> b) -> Know a b -> Know a b 
fullcutKnow f No = No 
fullcutKnow f (Yes b) = Yes b 
fullcutKnow f (Node a l m r) =  let m' = fullcutKnow f m in 
                                let l' = filter2Know m' (fullcutKnow f (joinKnow l m')) in 
                                let r' = filter2Know m' (fullcutKnow f (joinKnow r m')) in 
                                let m'' = joinKnow m' (mergeKnowKnow f l' r') in 
                                let l'' = filter2Know m'' l'' in 
                                let r'' = filter2Know m'' r'' in 
                                if isnoKnow l'' && isnoKnow r'' then m'' else Node a l'' m'' r''

-- find all cuts between knowledge bases, not covered by either
cutKnowKnow :: Ord a => (b -> b -> b) -> Know a b -> Know a b -> Know a b 
cutKnowKnow f No t'                         =   No 
cutKnowKnow f (Yes b) t'                    =   No
cutKnowKnow f t No                          =   No 
cutKnowKnow f t (Yes b')                    =   No
cutKnowKnow f (Node a l m r) (Node a' l' m' r')  
    |   a < a'                              =   let nm = cutKnowKnow f m (Node a' l' m' r') in 
                                                let nl = filter2Know m (filter2Know nm (cutKnowKnow f l (Node a' l' m' r'))) in 
                                                let nr = filter2Know m (filter2Know nm (cutKnowKnow f r (Node a' l' m' r'))) in 
                                                if isnoKnow nl  && isnoKnow nr then nm else Node a nl nm nr
    |   a' < a                              =   let nm = cutKnowKnow f (Node a l m r) m' in 
                                                let nl = filter2Know m' (filter2Know nm (cutKnowKnow f (Node a l m r) l')) in 
                                                let nr = filter2Know m' (filter2Know nm (cutKnowKnow f (Node a l m r) r')) in 
                                                if isnoKnow nl  && isnoKnow nr then nm else Node a' nl nm nr
    |   otherwise                           =   let jm = joinKnow m m' in
                                                let nm = joinKnow   (cutKnowKnow f m m') 
                                                                    (filter2Know m (filter2Know m' (joinKnow (mergeKnowKnow f r' l) (mergeKnowKnow f r l')))) in 
                                                let nl = filter2Know nm (joinKnow (filter2Know m (filter2Know m' (cutKnowKnow f l l'))) (joinKnow (filter2Know m (filter2Know l' (cutKnowKnow f l m'))) (filter2Know l (filter2Know m' (cutKnowKnow f m l'))))) in 
                                                let nr = filter2Know nm (joinKnow (filter2Know m (filter2Know m' (cutKnowKnow f r r'))) (joinKnow (filter2Know m (filter2Know r' (cutKnowKnow f r m'))) (filter2Know r (filter2Know m' (cutKnowKnow f m r'))))) in 
                                                if isnoKnow nl && isnoKnow nr then nm else Node a nl nm nr 

cutKnowKnow' :: Ord a => (b -> b -> b) -> Know a b -> Know a b -> Know a b 
cutKnowKnow' f No t'                         =   No 
cutKnowKnow' f (Yes b) t'                    =   No
cutKnowKnow' f t No                          =   No 
cutKnowKnow' f t (Yes b')                    =   No
cutKnowKnow' f (Node a l m r) (Node a' l' m' r')  
    |   a < a'                              =   let nm = cutKnowKnow' f m (Node a' l' m' r') in 
                                                let nl = filter2Know nm (cutKnowKnow' f l (Node a' l' m' r')) in 
                                                let nr = filter2Know nm (cutKnowKnow' f r (Node a' l' m' r')) in 
                                                if isnoKnow nl  && isnoKnow nr then nm else Node a nl nm nr
    |   a' < a                              =   let nm = cutKnowKnow f (Node a l m r) m' in 
                                                let nl = filter2Know nm (cutKnowKnow' f (Node a l m r) l') in 
                                                let nr = filter2Know nm (cutKnowKnow' f (Node a l m r) r') in 
                                                if isnoKnow nl  && isnoKnow nr then nm else Node a' nl nm nr
    |   otherwise                           =   let jm = joinKnow m m' in
                                                let nm = joinKnow   (cutKnowKnow' f m m') 
                                                                    (filter2Know m (joinKnow (mergeKnowKnow f r' l) (mergeKnowKnow f r l'))) in 
                                                let nl = filter2Know nm (joinKnow (cutKnowKnow' f l l') (joinKnow (cutKnowKnow f l m') (cutKnowKnow f m l'))) in 
                                                let nr = filter2Know nm (joinKnow (cutKnowKnow' f r r') (joinKnow (cutKnowKnow f r m') (cutKnowKnow f m r'))) in 
                                                if isnoKnow nl && isnoKnow nr then nm else Node a nl nm nr 

ocutKnow :: Ord a => (b -> b -> b) -> Know a b -> Know a b 
ocutKnow f No = No 
ocutKnow f (Yes b) = No 
ocutKnow f (Node a l m r) = 
    let nm = joinKnow (ocutKnow f m) (filter2Know m (mergeKnowKnow f r l)) in 
    let nl = filter2Know nm (joinKnow (filter2Know m (ocutKnow f l)) (filter2Know m (cutKnowKnow f l m))) in 
    let nr = filter2Know nm (joinKnow (filter2Know m (ocutKnow f r)) (filter2Know m (cutKnowKnow f r m))) in 
    if isnoKnow nl && isnoKnow nr then nm else Node a nl nm nr 

ocutKnow' :: Ord a => (b -> b -> b) -> Know a b -> Know a b 
ocutKnow' f No = No 
ocutKnow' f (Yes b) = No 
ocutKnow' f (Node a l m r) = 
    let nm = joinKnow (ocutKnow' f m) (mergeKnowKnow f r l) in 
    let nl = filter2Know nm (joinKnow (ocutKnow' f l) (cutKnowKnow' f l m)) in 
    let nr = filter2Know nm (joinKnow (ocutKnow' f r) (cutKnowKnow' f r m)) in 
    if isnoKnow nl && isnoKnow nr then nm else Node a nl nm nr 