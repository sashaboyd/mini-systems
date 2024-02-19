{-# LANGUAGE UndecidableInstances #-}

module Types where

import qualified Control.Comonad.Cofree as C
import Data.Functor.Rep
import Control.Comonad
import Data.Distributive
import Control.Applicative
import Data.Coerce

newtype Cotree σ a =
  Cotree { fromCotree :: C.Cofree ((→) σ) a }
  deriving newtype (Functor, Representable)

pattern (:<) :: a → (σ → C.Cofree ((→) σ) a) → Cotree σ a
pattern x :< xs = Cotree (x C.:< xs)

{-# COMPLETE (:<) #-}

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
newtype PrefixTree f σ a =
  PT { fromPT :: Cotree σ (f a) }
  deriving stock (Functor)

-- pattern (:<<) ::
-- pattern (:-<)

instance Applicative f ⇒ Applicative (PrefixTree f σ) where
  pure = PT . pure . pure
  PT t₁ <*> PT t₂ = PT (liftA2 (<*>) t₁ t₂)

instance Alternative f ⇒ Alternative (PrefixTree f σ) where
  empty = PT (pure empty)
  (PT t₁) <|> (PT t₂) = PT (liftA2 (<|>) t₁ t₂)

-- | An alternative version of 'pure'
single :: Alternative f ⇒ a → PrefixTree f σ a
single x = PT (pure x :< const (tabulate (const empty)))

-- | An alternative version of '<*>'
--
-- Implements ‘convolution’ of prefix trees.
conv :: Alternative f ⇒ (a → b → c) → PrefixTree f σ a → PrefixTree f σ b → PrefixTree f σ c
conv f (PT (m₁ :< h₁)) pt₂@(PT (m₂ :< h₂)) =
  PT (
  ( f <$> m₁ <*> m₂)
    :<
    \x →
      coerce
      ( coerce (fmap (liftA2 f m₁) (h₂ x))
        <|> conv f (coerce (h₁ x)) pt₂
      )
  )
