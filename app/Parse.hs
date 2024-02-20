module Parse where

import Data.Sequence (Seq)
import Control.Monad.Free
import Control.Applicative
import Data.Coerce
import Data.Functor.Rep
import Data.Foldable
import Text.Read

import Types

data TermSchema a
  = Number Integer -- ^ a string of digits
  | NumPlus Integer a -- ^ n+<t>
  | LeftPlus a a -- ^ (<t>)+<t>

type Term a = Free TermSchema a

-- | A prefix tree that matches on the empty sequence only
matchEmpty :: Alternative f ⇒ a → PrefixTree f σ a
matchEmpty x = mkMatched x (const empty)

-- | A prefix tree that matches a single symbol against a predicate function.
singlePred :: Alternative f ⇒ (σ → f a) → PrefixTree f σ a
singlePred p = failThen (go . p)
  where go x = mkPT x (const empty)

matchWith :: Alternative f ⇒ (Seq σ → f a) → PrefixTree f σ a
matchWith f = PT (Cotree (tabulate f))

matchListPred :: Alternative f ⇒ ([σ] → Maybe a) → PrefixTree f σ a
matchListPred f = PT (Cotree (tabulate go))
  where go = maybe empty pure . f . toList

-- | A prefix tree that matches on the given sequence
matchSeq :: Eq σ ⇒ Alternative f ⇒ Seq σ → a → PrefixTree f σ a
matchSeq s x = PT (tabulate go)
  where go w
          | w == s = pure x
          | otherwise = empty

-- | Implements ‘convolution’ of prefix trees.
conv :: Alternative f ⇒ (a → b → c) → PrefixTree f σ a → PrefixTree f σ b → PrefixTree f σ c
conv f (x₁ :< xs₁) pt₂@(x₂ :< xs₂) =
  ( f <$> x₁ <*> x₂)
    :<
    \x →
      coerce
      ( coerce (fmap (liftA2 f x₁) (xs₂ x))
        <|> conv f (coerce (xs₁ x)) pt₂
      )

matchInt :: PrefixTree Maybe Char Int
matchInt = PT (Cotree (tabulate (readMaybe . toList)))
