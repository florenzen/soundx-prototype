module Utils where

import Control.Monad
-- import Debug.Trace
import Prelude hiding (repeat)

fromRight :: Either a b -> b
fromRight (Right x) = x

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither a Nothing = Left a
maybeToEither a (Just b) = Right b

isLeft :: Either a b -> Bool
isLeft (Left x) = True
isLeft (Right x) = False

isRight :: Either a b -> Bool
isRight = not . isLeft

(+%+) :: String -> String -> String
str1 +%+ str2 = str1 ++ "\n" ++ str2

-- | Maps [x1,..,xi,...,xn] to Just [x1,...,fromJust (f xi),...,xn] where
-- xi is the leftmost element of the list for which f xi /= Nothing.
-- If f xj = Nothing for all j=1..n, return Nothing
mapLeftmost :: (a -> Maybe a) -> [a] -> Maybe [a]
mapLeftmost f [] = Nothing
mapLeftmost f (x:xs) =
    (do x' <- f x
        return (x':xs)) `mplus`
    (do xs' <- mapLeftmost f xs
        return (x:xs'))

-- | Maps [x1,...,xi,...,xn] to Just (f xi) where
-- xi is the leftmost element of the list for which f xi /= Nothing.
-- If f xj = Nothing for all j=1..n, return Nothing.
transformLeftmost :: (a -> Maybe b) -> [a] -> Maybe b
transformLeftmost f [] = Nothing
transformLeftmost f (x:xs) = f x `mplus` transformLeftmost f xs

-- | Apply f to x until Nothing is reached and return the input x'
-- which triggered Nothing.
repeat :: Show a => (a -> Maybe a) -> a -> a
repeat f x =
    let result = -- trace ("EX: " ++ show x ++ " --> " ++ show (f x))$
                 f x
    in case result of
         Nothing -> x
         Just x' -> repeat f x'
