module OL1.Internal where

import Data.Vec.Lazy        (Vec (..))
import Data.Type.Equality

equalLength' :: Vec n a -> Vec m b -> Maybe (n :~: m)
equalLength' VNil VNil = Just Refl
equalLength' (_ ::: xs) (_ ::: ys) = do
    Refl <- equalLength' xs ys
    return Refl
equalLength' _ _ = Nothing

equalLength :: [a] -> Vec n b -> Maybe (Vec n a)
equalLength []     VNil       = Just VNil
equalLength (x:xs) (_ ::: ys) = do
    xs' <- equalLength xs ys
    return (x ::: xs')
equalLength _ _ = Nothing
