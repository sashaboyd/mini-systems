{-# LANGUAGE UndecidableInstances #-}

module Main where

import Prelude hiding (zipWith, Num (..), repeat)

import Control.Comonad.Cofree
import Control.Comonad
import Control.Arrow (Kleisli (..))
import Control.Applicative
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

-- | A wrapper for Maybe that implements the Alternative instance as an ‘xor’
-- operation rather than the default
newtype Unique a = U { fromU :: Maybe a }
  deriving newtype (Functor, Applicative, Monad)

{-# COMPLETE Failed, Single #-}
pattern Failed :: Unique a
pattern Failed = U Nothing

pattern Single :: a -> Unique a
pattern Single x = U (Just x)

instance Alternative Unique where
  empty = Failed
  -- ‘xor’
  Failed <|> Failed = Failed
  Single _ <|> Single _ = Failed
  Single x <|> _ = Single x
  _ <|> Single y = Single y

newtype PrefixTree m a =
  PT { fromPT :: Cofree (Kleisli m Char) a }
  deriving newtype (Functor, Applicative, Monad)

instance Functor m => Comonad (PrefixTree m) where
  extract = extract . fromPT
  duplicate = PT . fmap PT . duplicate . fromPT

newtype Lang' a = L { fromL :: PrefixTree Unique a }
  deriving newtype (Functor, Applicative, Monad)

type Lang = Lang' (Unique String)

{-# COMPLETE (:>:) #-}
pattern (:>:) :: a -> (Char -> Unique (Cofree (Kleisli Unique Char) a)) -> Lang' a
pattern x :>: xs = L (PT (x :< Kleisli xs))

parse :: Lang' (Unique a) -> (Seq Char -> Maybe a)
parse (x :>:  _) Seq.Empty = fromU x
parse (_ :>: xs) (k Seq.:<| ks) =
  fromU do
    y <- xs k
    U (parse (L (PT y)) ks)

fromParser :: (Seq Char -> Maybe a) -> Lang' (Unique a)
fromParser f = U (f Seq.Empty) :>: step
  where
    step c = Single (fromPT (fromL (fromParser (f . (c Seq.:<|)))))

-- The empty language, unit of ⊕
nil :: Lang
nil = pure Failed

zipWith' :: Applicative f => (a -> b -> c) -> (Cofree f a -> Cofree f b -> Cofree f c)
zipWith' f (x :< xs) (y :< ys) =
  f x y :< (zipWith' f <$> xs <*> ys)

zipWith :: (a -> b -> c) -> (Lang' a -> Lang' b -> Lang' c)
zipWith f (L (PT t₁)) (L (PT t₂)) = L (PT (zipWith' f t₁ t₂))

-- | A variant of + that fails if its variants overlap
(⊕) :: Lang -> Lang -> Lang
(⊕) = zipWith (<|>)

infixl 6 ⊕

-- | ‘Unambiguous’ concatenation of languages
(·) :: Lang -> Lang -> Lang
l₁ · l₂ = do
  v₁ <- l₁
  v₂ <- l₂
  pure ((<>) <$> v₁ <*> v₂)

infixl 7 ·

-- | ‘Unambiguous’ repetition
(*) :: Lang -> Lang
(*) l = l ⊕ l·(l*)

main :: IO ()
main = pure ()
