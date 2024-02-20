{-# LANGUAGE UndecidableInstances #-}

module Types where

import qualified Control.Comonad.Cofree as C
import Data.Functor.Rep
import Control.Comonad
import Data.Distributive
import Control.Applicative
import Data.Kind

type Cotree :: Type → Type → Type
newtype Cotree σ a =
  Cotree { fromCotree :: C.Cofree ((→) σ) a }
  deriving newtype (Functor, Representable)

instance Comonad (Cotree σ) where
  extract = extract . fromCotree
  duplicate = Cotree . fmap Cotree . duplicate . fromCotree

instance Distributive (Cotree σ) where
  distribute = distributeRep
  collect = collectRep

instance Applicative (Cotree σ) where
  pure = pureRep
  (<*>) = apRep

-- | Also known as a trie
type PrefixTree :: (Type → Type) → Type → Type → Type
newtype PrefixTree f σ a =
  PT { fromPT' :: Cotree σ (f a) }
  deriving stock (Functor)

pattern (:<) :: f a → (σ → C.Cofree ((→) σ) (f a)) → PrefixTree f σ a
pattern x :< xs = PT (Cotree (x C.:< xs))

{-# COMPLETE (:<) #-}

instance Applicative f ⇒ Applicative (PrefixTree f σ) where
  pure = PT . pure . pure
  PT t₁ <*> PT t₂ = PT (liftA2 (<*>) t₁ t₂)

instance Alternative f ⇒ Alternative (PrefixTree f σ) where
  empty = PT (pure empty)
  (PT t₁) <|> (PT t₂) = PT (liftA2 (<|>) t₁ t₂)

fromPT :: PrefixTree f σ a → C.Cofree ((→) σ) (f a)
fromPT (PT (Cotree t)) = t

mkPT :: f a → (σ → PrefixTree f σ a) → PrefixTree f σ a
mkPT fx f = fx :< (fromPT . f)

mkMatched :: Applicative f ⇒ a → (σ → PrefixTree f σ a) → PrefixTree f σ a
mkMatched x f = PT (Cotree (pure x C.:< (fromCotree . fromPT' . f)))

failThen :: Alternative f ⇒ (σ → PrefixTree f σ a) → PrefixTree f σ a
failThen f = PT (Cotree (empty C.:< (fromCotree . fromPT' . f)))
