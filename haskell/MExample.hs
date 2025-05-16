module MExample where

import Knowledge
import Modal
import MForm


-- EXAMPLE SYSTEM 1:    Necessity ☐
-- ☐ X => ☐ ☐ X
-- ☐ X => X 
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


-- EXAMPLE SYSTEM 2:    Multimodal K and N without additional axioms

newtype Flat =  Flat String
    deriving (Eq , Ord)

instance Show Flat where
    show :: Flat -> String
    show (Flat s) = s

instance Lat Flat where
    imp :: Flat -> Flat -> Bool
    imp m n = m == n

    lat :: Flat -> Flat -> Maybe Flat
    lat m n = if m == n then Just m else Nothing

    cou :: Flat -> Bool
    cou m = False
  
    awa :: Flat -> [(Flat, Flat)]
    awa m = []

    omi :: Flat -> Flat -> Maybe Flat
    omi m n = Nothing

    def :: Flat
    def = Flat ""


-- EXAMPLE SYSTEM 3:    Belief and Communication
-- B(a) is belief of agent a 
-- I(a,b) is communication from b to a 
-- Axioms
-- B(a) X => B(a) B(a) X 
-- I(a,b) X => B(a) I(a,b) X
-- I(a,b) X => B(b) I(a,b) X
-- I(a,b) X => I(a,b) B(b) X
data Comm =
    Belief String
    |   Inter String String
    deriving (Eq , Ord)

instance Show Comm where
    show :: Comm -> String
    show (Belief a) = a
    show (Inter a b) = a ++ "<" ++ b

instance Lat Comm where
  imp :: Comm -> Comm -> Bool
  imp m n = m == n

  lat :: Comm -> Comm -> Maybe Comm
  lat m n = if m == n then Just m else Nothing

  cou :: Comm -> Bool
  cou m = False

  awa :: Comm -> [(Comm , Comm)]
  awa (Belief a) = [(Belief a , Belief a)]
  awa (Inter a b) = [(Belief a , Inter a b) , (Belief b , Inter a b) , (Inter a b , Belief b)]

  omi :: Comm -> Comm -> Maybe Comm
  omi (Belief a) (Belief b) = if a == b then Just (Belief a) else Nothing
  omi (Inter a b) (Belief c) = if a == c || b == c then Just (Inter a b) else Nothing 
  omi (Inter a b) (Inter c d) = if a == c && b == d then Just (Belief b) else Nothing 
  omi m n = Nothing 

  def :: Comm
  def = Belief ""

-- EXAMPLE SYSTEM 4:    Lattice of knowledge domains 
-- Modality is given by a subset of domains, combining statements of all domains
-- Axiom: S(A) X => S(B) X if A a subset of B
newtype Source = From [String]
    deriving (Eq , Ord)

instance Show Source where
  show :: Source -> String
  show (From a) = "<" ++ interleave "," a ++ ">"

instance Lat Source where
  imp :: Source -> Source -> Bool
  imp (From a) (From b) = subSet a b
  
  lat :: Source -> Source -> Maybe Source
  lat (From a) (From b) = --if a == b then Just (From a) else Nothing 
    Just (From (joinSet a b))
  
  cou :: Source -> Bool
  cou (From a) = False
  
  awa :: Source -> [(Source, Source)]
  awa (From a) = []
  
  omi :: Source -> Source -> Maybe Source
  omi (From a) (From b) = Nothing
  
  def :: Source
  def = From []



iff :: MForm m -> MForm m -> MForm m
iff f g = An [Im f g , Im g f]

-- threhsold examples
thresh23 :: MForm m -> MForm m -> MForm m -> MForm m
thresh23 f g h = Or [An [f , g] , An [g , h] , An [h , f]]

thresh23' :: MForm m -> MForm m -> MForm m -> MForm m
thresh23' f g h = Or [An [f , g] , An [g , h] , An [h , f]]

-- and and ors
twoThree :: MForm Bm
twoThree = Or [An [Ba "A" , Ba "B"] , An [Ba "B" , Ba "C"] , An [Ba "C" ,  Ba "A"]]

threeTwo :: MForm Bm
threeTwo = An [Or [Ba "A" , Ba "B"] , Or [Ba "B" , Ba "C"] , Or [Ba "C" ,  Ba "A"]]

testbag23 :: [(MForm Bm , Bool)]
testbag23 = [(Nam "Alex" twoThree , True) , (Nam "Alex" twoThree , False) , (Nam "Bertha" threeTwo , True) , (Nam "Bertha" threeTwo , False)]

testbagIff23 :: [(MForm Bm , Bool)]
testbagIff23 = [(iff twoThree threeTwo , False)]

-- 
namesCol :: [MForm Bm] 
namesCol =     [Nam "Alex" (An [Ba "A" , Ba "B" , Ba "C"]) , 
                Nam "Ben" (An [Ba "A" , Ba "B" , Ba "D"]) , 
                Nam "Charlie" (An [Ba "A" , Ba "B" , Ba "E"]) , 
                Nam "Danny" (An [Ba "A" , Ba "C" , Ba "D"]) , 
                Nam "Emma" (An [Ba "A" , Ba "C" , Ba "E"]),
                Nam "Fred" (An [Ba "A" , Ba "D" , Ba "E"]) , 
                Nam "Ginna" (An [Ba "B" , Ba "C" , Ba "D"]) , 
                Nam "Hank" (An [Ba "B" , Ba "C" , Ba "E"]) , 
                Nam "Ivonne" (An [Ba "B" , Ba "D" , Ba "E"]) , 
                Nam "Joker" (An [Ba "C" , Ba "D" , Ba "E"]) ,
                Nam "Kevin" (Or [Ba "A" , Ba "B" , Ba "C"]) , 
                Nam "Leo" (Or [Ba "A" , Ba "B" , Ba "D"]) , 
                Nam "Marlene" (Or [Ba "A" , Ba "B" , Ba "E"]) , 
                Nam "Niels" (Or [Ba "A" , Ba "C" , Ba "D"]) , 
                Nam "Oliver" (Or [Ba "A" , Ba "C" , Ba "E"]),
                Nam "Pear" (Or [Ba "A" , Ba "D" , Ba "E"]) , 
                Nam "Quirkle" (Or [Ba "B" , Ba "C" , Ba "D"]) , 
                Nam "Ratat" (Or [Ba "B" , Ba "C" , Ba "E"]) , 
                Nam "Selvin" (Or [Ba "B" , Ba "D" , Ba "E"]) , 
                Nam "Tantastic" (Or [Ba "C" , Ba "D" , Ba "E"]) ]

testbagNames :: [(MForm Bm , Bool)]
testbagNames = fmap (\x -> (x , True)) namesCol ++ fmap (\x -> (x , False)) namesCol

threeFive :: MForm Bm
threeFive = Or [An [Ba "A" , Ba "B" , Ba "C"] , An [Ba "A" , Ba "B" , Ba "D"] , An [Ba "A" , Ba "B" , Ba "E"] , An [Ba "A" , Ba "C" , Ba "D"] , An [Ba "A" , Ba "C" , Ba "E"],
                An [Ba "A" , Ba "D" , Ba "E"] , An [Ba "B" , Ba "C" , Ba "D"] , An [Ba "B" , Ba "C" , Ba "E"] , An [Ba "B" , Ba "D" , Ba "E"] , An [Ba "C" , Ba "D" , Ba "E"] ]

fiveThree :: MForm Bm
fiveThree = An [Or [Ba "A" , Ba "B" , Ba "C"] , Or [Ba "A" , Ba "B" , Ba "D"] , Or [Ba "A" , Ba "B" , Ba "E"] , Or [Ba "A" , Ba "C" , Ba "D"] , Or [Ba "A" , Ba "C" , Ba "E"],
                Or [Ba "A" , Ba "D" , Ba "E"] , Or [Ba "B" , Ba "C" , Ba "D"] , Or [Ba "B" , Ba "C" , Ba "E"] , Or [Ba "B" , Ba "D" , Ba "E"] , Or [Ba "C" , Ba "D" , Ba "E"] ]

testbagIff35 :: [(MForm Bm , Bool)]
testbagIff35 = [(iff threeFive fiveThree , False)]

testbagtest :: [(MForm Bm , Bool)]
testbagtest = [(Im (Or [Ba "A" , Ba "B"]) (An [Ba "C" , Ba "D"]) , True)]

testbagImp :: [(MForm Bm , Bool)]
testbagImp = [(Im (Ba [i]) (Ba [j]) , True) | i <- "ABCDE", j <- "ABCDE"] ++
    [(Im (Ba [i]) (Ba [j]) , False) | i <- "ABCDE", j <- "ABCDE"]

proof :: Proof
proof = Axiom " " "Place Holder"

-- box
mA :: MForm Bm
mA = Ba "A"

mBoA :: MForm Bm
mBoA = Mo Box (Mo Box (Ba "A"))

testbagBoxA :: [(MForm Bm, Bool)]
testbagBoxA = [(mBoA, False) , (mBoA, True)]

iterBox :: MForm Bm -> MForm Bm
iterBox f = An [Mo Box f , f]

mBBB :: MForm Bm
mBBB = Im (Mo Box (Ba "A")) (iterBox (iterBox (iterBox (iterBox (iterBox (Ba "A"))))))

testbagBBB :: [(MForm Bm, Bool)]
testbagBBB = [(mBBB , False)]

testbagOne :: [(MForm Flat, Bool)]
testbagOne = [  (Mo (Flat "M") (An [Ba "A" , Ba "B"]) , True) ,
                (Mo (Flat "M") (An [Ba "A" , Ba "B"]) , False),
                (An [Mo (Flat "M") (Ba "A") , Mo (Flat "M") (Ba "B")] , True) ,
                (An [Mo (Flat "M") (Ba "A") , Mo (Flat "M") (Ba "B")] , False),
                (Mo (Flat "M") (Or [Ba "A" , Ba "B"]) , True) ,
                (Mo (Flat "M") (Or [Ba "A" , Ba "B"]) , False),
                (Or [Mo (Flat "M") (Ba "A") , Mo (Flat "M") (Ba "B")] , True) ,
                (Or [Mo (Flat "M") (Ba "A") , Mo (Flat "M") (Ba "B")] , False)]

catchA :: [(Bm , [MForm Bm])]
catchA = [(Box , [Ba "A" , Mo Box (Ba "A") , Mo Box (Mo Box (Ba "A"))])]

-- trust 
commchain :: String -> [String] -> String -> MForm Comm -> MForm Comm
commchain a [] c f = Mo (Inter a c) f
commchain a (b : l) c f = Mo (Inter a b) (commchain b l c f)

val :: m -> MForm m -> MForm m 
val m f = Im (Mo m f) f

validity :: MForm Comm -> String -> [String] -> String -> MForm Comm
validity f a l b = Im (commchain a l b f) f

validity2 ::  String -> [String] -> String -> MForm Comm -> MForm Comm
validity2 a l b f = Nam ("val{" ++ a ++ "<" ++ interleave "," l ++ "-" ++ b ++ "}(" ++ show f ++ ")") 
    (An [Im (commchain a l b f) (Mo (Belief b) f) , Im (Mo (Belief b) f) f])

trust :: String -> [String] -> String -> MForm Comm -> MForm Comm
trust a l b f = Mo (Belief a) (validity2 a l b f)

testbagTrust :: [(MForm Comm, Bool)]
testbagTrust = [(Mo (Inter "a" "b") (validity2 "b" [] "c" (Ba "X")) , True) ,
                (trust "a" [] "b"   (validity2 "b" [] "c" (Ba "X")) , True) ,
                (trust "a" [] "b"   (Mo (Inter "b" "c") (Ba "X")) , True) ,
                (trust "a" ["b"] "c" (Ba "X") , False)]

testbagTrustimp :: [(MForm Comm, Bool)]
testbagTrustimp = [(Im (An [ Mo (Inter "a" "b") (validity2 "b" [] "c" (Ba "X")) ,
                            trust "a" [] "b"   (validity2 "b" [] "c" (Ba "X")) ,
                            trust "a" [] "b"   (Mo (Inter "b" "c") (Ba "X")) ])
                        (trust "a" ["b"] "c" (Ba "X")) , False)]

testbagTrust2 :: [(MForm Comm, Bool)]
testbagTrust2 = [
    (Mo (Inter "a" "b") (Mo (Inter "b" "c") (validity2 "c" [] "d" (Ba "X"))) , True) ,
    (Mo (Inter "a" "b") (validity2 "b" [] "c"   (validity2 "c" [] "d" (Ba "X"))) , True) ,
    (Mo (Inter "a" "b") (validity2 "b" [] "c"   (Mo (Inter "c" "d") (Ba "X"))) , True) ,
--    (Mo (Inter "a" "b") (validity2 "b" ["c"] "d" (Ba "X")) , True) ,
    (trust "a" [] "b"   (validity2 "b" ["c"] "d" (Ba "X")) , True) ,
    (trust "a" [] "b"   (Mo (Inter "b" "c") (Mo (Inter "c" "d") (Ba "X"))) , True) ,
    (trust "a" ["b" , "c"] "d" (Ba "X") , False)
    ]

testbagValid :: [(MForm Comm, Bool)]
testbagValid = [(Mo (Inter "a" "b") (validity (Ba "X") "b" [] "c") , True) ,
                (validity (Ba "X") "a" [] "b" , True) ,
                --(validity (validity (Ba "X") "b" [] "c") "a" [] "b" , True) ,
                --(validity (Ba "X") "b" [] "c" , True) ,
                (validity (Ba "X") "a" ["b"] "c" , False)]

testbagValidimp :: [(MForm Comm, Bool)]
testbagValidimp = [(Im  (An [Mo (Inter "a" "b") (validity (Ba "X") "b" [] "c"),
                                thresh23   (validity (Ba "X") "a" [] "b")
                                            (validity (validity (Ba "X") "b" [] "c") "a" [] "b")
                                            (validity (Mo (Inter "b" "c") (Ba "X")) "a" [] "b")])
                        (validity (Ba "X") "a" ["b"] "c") , False)]

testbagNecc :: [(MForm Flat , Bool)]
testbagNecc = [(Mo (Flat "M") (Im (Ba "X") (Ba "X")) , False)]

-- composition example

testbagComp :: [(MForm Flat , Bool)]
testbagComp = [
    (Nam "Alex" (Im (Ba "A") (Ba "B")) , True) ,
    (Nam "Bertha" (Im (Ba "A") (Ba "C")) , True) ,
    (Nam "Charly" (Im (Ba "A") (Ba "D")) , True) ,
    (Nam "Danny" (Im (Ba "B") (Ba "C")) , True) ,
    (Nam "Eduardo" (Im (Ba "B") (Ba "D")) , True) , 
    (Nam "Fred" (Im (Ba "B") (Ba "E")) , True) , 
    (Nam "Gerald" (Im (Ba "C") (Ba "E")) , True) , 
    (Nam "Harriet" (Im (Ba "D") (Ba "E")) , True) , 
    (Nam "Program Correctness" (Im (Ba "A") (Ba "E")) , False)
    ]


-- two out of three sources
sources23 :: MForm Source -> MForm Source
sources23 f = Nam ("23[" ++ show f ++ "]") (An [Mo (From ["a","b"]) f , Mo (From ["a","c"]) f , Mo (From ["b","c"]) f])

testbagSourcesComp :: [(MForm Source , Bool)]
testbagSourcesComp = [(sources23 (Im (Ba "A") (Ba "B")) , True) , (sources23 (Im (Ba "B") (Ba "C")) , True) , (sources23 (Im (Ba "A") (Ba "C")) , False)]

testbagSourcesCont :: [(MForm Source , Bool)]
testbagSourcesCont = [
    (Mo (From ["a"]) (Im (Ba "A") (Ba "B")) , True) , 
    (Mo (From ["a"]) (Im (Ba "C") (Ba "D")) , True) ,
    (Mo (From ["b"]) (Im (Ba "A") (Ba "B")) , True) ,
    (Mo (From ["b"]) (Im (Ba "B") (Ba "C")) , True) ,
    (Mo (From ["c"]) (Im (Ba "B") (Ba "D")) , True) ,
    (sources23 (Im (Ba "A") (Ba "D")) , False)]

