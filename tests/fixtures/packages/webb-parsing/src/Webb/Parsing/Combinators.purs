module Webb.Parsing.Combinators
  ( alts , longest , mix , mix1 , reduce , reject , succeeds
  , within, strip, whenNext
  )
  where

import Parsing
import Parsing.Combinators.Array
import Prelude

import Control.Alt ((<|>))
import Control.Monad.Error.Class (catchError)
import Control.Monad.Error.Class as Err
import Data.Array as A
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Either (isRight)
import Data.Foldable (class Foldable, foldl)
import Data.Maybe (Maybe(..))
import Data.Traversable (sequence)
import Data.Tuple (snd)
import Data.Tuple.Nested ((/\), type (/\))
import Effect.Class (class MonadEffect, liftEffect)
import Parsing.Combinators (lookAhead, try)
import Webb.Monad.Prelude (forceMaybe')
import Webb.Parsing as P
import Webb.Stateful (localEffect)


{- Custom combinators for parsing. 
  Combine all the given parsers and match them _not_ as direct
  alternatives, but as sequential alternatives to take 'many' of
  them.
-}

-- Combine all the items in the foldable, using the specified combiner. Throws an error if 
-- no item could be found.
reduce :: forall m f a. MonadEffect m => Foldable f => (a -> a -> a) -> f a -> m a
reduce f coll = liftEffect do 
  let mresult = foldl combine Nothing coll
  forceMaybe' "Could not reduce. Collection was empty." mresult
  where 
  combine :: Maybe a -> a -> Maybe a
  combine macc a = case macc of
    Nothing -> Just a
    Just acc -> Just (f a acc)
  
type Pair s m a = (ParserT s m a) /\ Int
  
-- Tries all the parsers. The one that takes the longest chunk of the input
-- is the one that succeeds. If no input is consumed, we fail. Useful for generating
-- tokens while looking for the _longest_ possible match out of the options.
longest :: forall m s a. Array (ParserT s m a) -> ParserT s m a
longest arr = try do
  let parsers = getLength <$> arr
  parsed :: Array Int <- sequence parsers

  let pairs = A.zip arr parsed :: Array (Pair s m a)
      sorted = A.sortWith snd pairs :: Array (Pair s m a)
      mlongest = A.last sorted

  case mlongest of
    Nothing -> do
      fail "No token matched"
    Just (parser /\ len) -> do
      if (len <= 0) then do 
        fail "No input was consumed"
      else do
        parser
  
  where 
  -- Try the parser as a lookahead, or return an empty string. Does not modify the
  -- stream's position. This lets us find the best token to use.
  getLength parser = 
    catchError (do
      oldIndex <- P.index
      _ <- lookAhead parser
      newIndex <- P.index
      
      -- Succeeded in parsing.
      pure $ newIndex - oldIndex
    ) (\_ -> do 
      -- Failed to parse.
      pure 0
    )
    
-- Combine all parsers. Insert a 'try' for all of them so that recovery is automatic.
alts :: forall m s a. Array (ParserT s m a) -> ParserT s m a
alts arr =
  let parser = localEffect $ reduce combine (try <$> arr)
  in parser
  where
  combine p1 p2 = p1 <|> p2

-- Mix the given items as alternatives, and fetch many of them.
mix :: forall m s a. Array (ParserT s m a) -> ParserT s m (Array a)
mix arr = do many $ alts arr

-- Mix the given items as alternatives, and fetch at least one of them.
mix1 :: forall m s a. Array (ParserT s m a) -> ParserT s m (NonEmptyArray a)
mix1 arr = do many1 $ alts arr

-- Attempts the given parser, and returns whether it _would_ have suceeded.
succeeds :: forall m s a. ParserT s m a -> ParserT s m Boolean
succeeds prog = do
  e <- Err.try do lookAhead prog
  pure $ isRight e
  
-- Try the parse, but reject it if it equals the result.
reject :: forall m s a. Show a => Eq a => a -> ParserT s m a -> ParserT s m a
reject a prog = try do
  res <- prog
  if res == a then do
    fail $ "Rejected parse: " <> show a
  else do
    pure res
    
-- Require the prog to be between the two delimiters, but ignores the two delimiiters.
within :: forall m s a b c. ParserT s m a -> ParserT s m b -> ParserT s m c -> ParserT s m c
within a1 a2 prog = try do
  void a1 
  result <- prog
  void a2
  pure result 

-- Optionally strips the outer delims before matching the prog
strip :: forall m s a b c. ParserT s m a -> ParserT s m b -> ParserT s m c -> ParserT s m c
strip a1 a2 prog = try do
  alts
    [ do
        void a1
        result <- strip a1 a2 prog
        void a2
        pure result
    , do 
        prog
    ]
    
-- Uses the parser if the next character matches.
whenNext :: forall m s a b. ParserT s m a -> ParserT s m b -> ParserT s m b
whenNext a prog = try do
  void $ lookAhead a
  prog