module Parse where

import Control.Monad.Free

import Types

data TermSchema a
  = Number Int
  | Plus a a

type Term a = Free TermSchema a
