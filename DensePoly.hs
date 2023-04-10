module DensePoly() where
import PolyClass
import Representation

reverseAcc :: [a] -> [a] -> [a]
reverseAcc [] acc = acc
reverseAcc (h:t) acc = reverseAcc t (h:acc)

removeLeadingZeroes :: (Eq a, Num a) => [a] -> [a]
removeLeadingZeroes [] = []
removeLeadingZeroes (0:t) = removeLeadingZeroes t
removeLeadingZeroes p = p

removeTrailingZeroes :: (Eq a, Num a) => [a] -> [a]
removeTrailingZeroes p = reverseAcc (removeLeadingZeroes (reverseAcc p [])) []

toCanonical :: (Eq a, Num a) => DensePoly a -> DensePoly a
toCanonical (P p) = P (removeTrailingZeroes p)

instance Functor DensePoly where
    fmap f (P p) = P (fmap f p)

evalAcc :: (Num a) => [a] -> a -> Int -> a -> a
evalAcc [] _ _ acc = acc
evalAcc (h:t) x exp acc = evalAcc t x (exp + 1) (acc + (h * x^exp))

instance Polynomial DensePoly where
    zeroP = P []
    constP 0 = zeroP
    constP c = P [c]
    varP = P [0,1]
    evalP (P p) x = evalAcc p x 0 0
    shiftP n (P p)
        | n > 0 = shiftP (n-1) (P (0:p))
        | otherwise = toCanonical (P p)
    degree (P p) = (length (removeTrailingZeroes p)) - 1

addAcc :: (Num a) => [a] -> [a] -> [a] -> [a]
addAcc [] [] acc = reverseAcc acc []
addAcc [] (h:t) acc = addAcc [] t (h:acc)
addAcc (h:t) [] acc = addAcc t [] (h:acc)
addAcc (hp:tp) (hq:tq) acc = addAcc tp tq ((hp + hq):acc)

mulAcc :: (Num a) => [a] -> [a] -> [a] -> [a]
mulAcc [] _ acc = acc
mulAcc (h:t) q acc = mulAcc t q (addAcc (0:acc) (fmap (*h) q) [])

instance (Eq a, Num a) => Num (DensePoly a) where
    P p + P q = toCanonical $ P (addAcc p q [])
    P p * P q = toCanonical $ P (mulAcc (reverseAcc p []) q [])
    negate (P p) = toCanonical $ fmap (negate) (P p)
    fromInteger x = constP (fromInteger x)
    abs = undefined
    signum = undefined

instance (Eq a, Num a) => Eq (DensePoly a) where
    P p == P q = nullP(P p - P q)

-- |
-- >>> x^3 - 1 :: DensePoly Integer 
-- P {unP = [-1,0,0,1]}

-- | Num operations give canonical results:
-- >>> isCanonicalDP (sampleDP - sampleDP)
-- True

-- |
-- >>>  P [1,2] == P [1,2]
-- True

-- |
-- >>> fromInteger 0 == (zeroP :: DensePoly Int)
-- True

-- |
-- >>>  P [0,1] == P [1,0]
-- False

-- | Degree examples
-- >>> degree (zeroP :: DensePoly Int)
-- -1
-- >>> degree (constP 1 :: DensePoly Int)
-- 0
