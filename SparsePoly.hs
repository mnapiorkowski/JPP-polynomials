module SparsePoly(fromDP, toDP, qrP) where
import PolyClass
import Representation

reverseAcc :: [a] -> [a] -> [a]
reverseAcc [] acc = acc
reverseAcc (h:t) acc = reverseAcc t (h:acc)

fromDPAcc :: (Eq a, Num a) => [a] -> Int -> [(Int, a)] -> [(Int, a)]
fromDPAcc [] _ acc = acc
fromDPAcc (h:t) exp acc 
    | h /= 0 = fromDPAcc t (exp+1) ((exp, h):acc)
    | otherwise = fromDPAcc t (exp+1) acc

fromDP :: (Eq a, Num a) => DensePoly a -> SparsePoly a
fromDP (P p) = S (fromDPAcc p 0 [])

toDPAcc :: (Eq a, Num a) => [(Int, a)] -> Int -> [a] -> [a]
toDPAcc [] (-1) acc = acc
toDPAcc [] exp acc = toDPAcc [] (exp-1) (0:acc)
toDPAcc (h:t) exp acc
    | exp == fst h = toDPAcc t (exp-1) ((snd h):acc)
    | otherwise = toDPAcc (h:t) (exp-1) (0:acc)

toDP :: (Eq a, Num a) => SparsePoly a -> DensePoly a
toDP (S p) = P (toDPAcc p (degree (S p)) [])

first :: (a -> a') -> (a, b) -> (a', b)
first f (x,y) = (f x, y)
second :: (b -> b') -> (a, b) -> (a, b')
second f (x,y) = (x, f y)

instance Functor SparsePoly where
    fmap f (S p) = S (fmap (second f) p)

evalAcc :: (Num a) => [(Int, a)] -> a -> a -> a
evalAcc [] _ acc = acc
evalAcc (h:t) x acc = evalAcc t x (acc + (snd h) * x^(fst h))

shiftAcc :: Int -> [(Int, a)] -> [(Int, a)] -> [(Int, a)]
shiftAcc _ [] acc = reverseAcc acc []
shiftAcc n (h:t) acc = shiftAcc n t ((n + fst h, snd h):acc)

instance Polynomial SparsePoly where
    zeroP = S []
    constP 0 = zeroP
    constP c = S [(0,c)]
    varP = S [(1,1)]
    evalP (S p) x = evalAcc p x 0
    shiftP n (S p) = S (shiftAcc n p [])
    degree (S []) = -1
    degree (S ((_,0):t)) = degree (S t)
    degree (S (h:t)) = fst h

addAcc :: (Eq a, Num a) => [(Int, a)] -> [(Int, a)] -> [(Int, a)] -> [(Int, a)]
addAcc [] [] acc = reverseAcc acc []
addAcc [] (h:t) acc = addAcc [] t (h:acc)
addAcc (h:t) [] acc = addAcc t [] (h:acc)
addAcc (hp:tp) (hq:tq) acc
    | fst hp > fst hq = addAcc tp (hq:tq) (hp:acc)
    | fst hp < fst hq = addAcc (hp:tp) tq (hq:acc)
    | coeffsSum /= 0 = addAcc tp tq ((fst hp, coeffsSum):acc)
    | otherwise = addAcc tp tq acc
        where coeffsSum = (snd hp + snd hq)

mulCoeffsAcc :: (Eq a, Num a) => a -> [(Int, a)] -> [(Int, a)] -> [(Int, a)]
mulCoeffsAcc _ [] acc = reverseAcc acc []
mulCoeffsAcc c (h:t) acc
    | coeffsProduct /= 0 = mulCoeffsAcc c t ((fst h, coeffsProduct):acc)
    | otherwise = mulCoeffsAcc c t acc
        where coeffsProduct = (c * snd h)

mulAcc :: (Eq a, Num a) => [(Int, a)] -> [(Int, a)] -> [(Int, a)] -> [(Int, a)]
mulAcc [] _ acc = acc
mulAcc (h:t) q acc = mulAcc t q (addAcc acc multiplied [])
    where multiplied = mulCoeffsAcc (snd h) (shiftAcc (fst h) q []) []

instance (Eq a, Num a) => Num (SparsePoly a) where
    S p + S q = S (addAcc p q [])
    S p * S q = S (mulAcc p q [])
    negate (S p) = fmap negate (S p)
    fromInteger x = constP (fromInteger x)
    abs = undefined
    signum = undefined

instance (Eq a, Num a) => Eq (SparsePoly a) where
    S p == S q = nullP(S p - S q)

qrAcc :: (Eq a, Fractional a) => [(Int, a)] -> [(Int, a)] -> [(Int, a)] -> ([(Int, a)], [(Int, a)])
qrAcc [] _ acc = (reverseAcc acc [], [])
qrAcc (hp:tp) (hq:tq) acc
    | degree (S (hp:tp)) < degree (S (hq:tq)) = (reverseAcc acc [], (hp:tp))
    | otherwise = qrAcc re (hq:tq) (qu:acc)
        where 
            qu = ((fst hp - fst hq), (snd hp / snd hq))
            S re = (S(hp:tp)) - (S(hq:tq) * S [qu])

qrP :: (Eq a, Fractional a) => SparsePoly a -> SparsePoly a -> (SparsePoly a, SparsePoly a)
qrP (S p) (S q) = (S qu, S re) 
    where (qu, re) = qrAcc p q []

-- | fromDP example
-- >>> fromDP sampleDP
-- S {unS = [(3,1),(0,-1)]}

-- | Division example
-- >>> qrP (x^2 - 1) (x -1) == ((x + 1), 0)
-- True
