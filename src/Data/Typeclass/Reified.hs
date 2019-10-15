module Data.Typeclass.Reified ( module Data.Capabilities, module Data.Typeclass.Reified.Internal ) where

import Control.Applicative
import Control.Monad
import Data.Capabilities
import Data.Typeclass.Reified.Internal

thReifiable ''Eq
thReifiable ''Functor
thReifiable ''Applicative
thReifiable ''Alternative
thReifiable ''Monad
thReifiable ''MonadFail
thReifiable ''MonadPlus
