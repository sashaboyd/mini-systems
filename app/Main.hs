{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeAbstractions #-}
module Main where

-- import Control.Monad
import Control.Comonad
-- import Control.Comonad.Cofree
import Control.Comonad.Env
--import Control.Monad.Free hiding (unfold)
--import Control.Arrow ((&&&))
import Data.Functor.Const
import Data.Void

main :: IO ()
main = do
  pure ()

class (Comonad c, Functor m) ⇒ LeftComodule c m | m → c where
  leftAction :: m a → c (m a)

law_extract_leftAction :: LeftComodule c m ⇒ Eq (m a) ⇒ m a → Bool
law_extract_leftAction m = m == extract (leftAction m)

law_duplicate_leftAction :: LeftComodule c m ⇒ Eq (c (c (m a))) ⇒ m a → Bool
law_duplicate_leftAction m = duplicate (leftAction m) == (leftAction <$> leftAction m)

class (Comonad c, Functor m) ⇒ RightComodule c m | m → c where
  rightAction :: m a → m (c a)

law_extract_rightAction :: RightComodule c m ⇒ Eq (m a) ⇒ m a → Bool
law_extract_rightAction m = m == (extract <$> rightAction m)

law_duplicate_rightAction :: RightComodule c m ⇒ Eq (m (c (c a))) ⇒ m a → Bool
law_duplicate_rightAction m = (duplicate <$> rightAction m) == rightAction (rightAction m)

class (LeftComodule l m, RightComodule r m) ⇒ Bicomodule l r m | m → r, m → l where
  biAction :: m a → l (m (r a))
  biAction = leftAction . rightAction

law_biAction_compat :: Bicomodule l r m ⇒ Eq (l (m (r a))) ⇒ m a → Bool
law_biAction_compat m = leftAction (rightAction m) == (rightAction <$> leftAction m)

law_LeftComodule_morphism :: LeftComodule c m ⇒ LeftComodule c n ⇒ Eq (m a → c (n a)) ⇒ (m a → n a) → Bool
law_LeftComodule_morphism f = leftAction . f == fmap f . leftAction

-- law_RightComodule_morphism :: RightComodule c m ⇒ RightComodule c n ⇒ Eq (m a → n (c a)) ⇒ (forall x. m x → n x) → Bool
-- law_RightComodule_morphism @c @_ @_ @a f = rightAction . (f @a) == (f @(c a)) . rightAction

data Nodes = V1 | V2 | V3

data Update a =
  U1 a a
  | U2 a
  | U3 a
  deriving (Functor)

instance LeftComodule (Env Nodes) Update where
  leftAction v@(U1 _ _) = env V1 v
  leftAction v@(U2 _) = env V2 v
  leftAction v@(U3 _) = env V3 v

-- instance Bicomodule (Env Nodes) (Env Nodes) Update where
--   rightAction (U1 x y) = U1 (env V2 x) (env V3 y)
--   rightAction (U2 x) = U2 (env V3 x)
--   rightAction (U3 x) = U3 (env V1 x)

-- data GraphInit a = I1 Bool | I2 Bool | I3 Bool
--   deriving (Functor)

-- instance Comonad (Const Void) where
--   extract = absurd . getConst
--   duplicate (Const x) = Const x

-- instance Bicomodule (Env Nodes) (Const Void) GraphInit where
--   leftAction i@(I1 _) = env V1 i
--   leftAction i@(I2 _) = env V2 i
--   leftAction i@(I3 _) = env V3 i
--   rightAction (I1 x) = I1 x
--   rightAction (I2 x) = I2 x
--   rightAction (I3 x) = I3 x
