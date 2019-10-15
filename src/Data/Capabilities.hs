module Data.Capabilities 
    ( Apply(..)
    , Capabilities
    , HasCapability
    , getCapability
    , Cap(..)
    , apply
    ) where

import Data.Kind
import Data.Vinyl
import Data.Vinyl.ARec
import Data.Vinyl.TypeLevel
import Data.Vinyl.XRec

--

newtype Apply a f = Apply { unApply :: f a }

instance IsoHKD (Apply a) f where
    type HKD (Apply a) f = f a

    unHKD = Apply
    toHKD = unApply

--

type Capabilities cs a = ARec (Apply a) cs
type HasCapability c cs = IndexableField cs c

getCapability :: (HasCapability c cs) => Capabilities cs a -> c a
getCapability r = unApply (aget r)
{-# INLINE getCapability #-}

newtype Cap caps a = Cap { runCap :: forall m. Capabilities caps m -> m a }

apply :: a -> (a -> b) -> b
apply x f = f x
