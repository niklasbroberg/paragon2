module Language.Java.Paragon.Monad.Uniq
    ( Uniq, initUniq, getUniq ) where

import Data.IORef

-- |Type used for generating unique identifiers for actors etc
newtype Uniq = Uniq (IORef Int)

-- |Get a unique number generator
initUniq :: IO Uniq
initUniq = Uniq <$> newIORef 0

-- |Get next unique identifier from generator
getUniq :: Uniq -> IO Int
getUniq (Uniq u) = do i <- readIORef u
                      writeIORef u (i+1)
                      return i

