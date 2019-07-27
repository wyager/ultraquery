module Lib.Parser where

import Lib(Query(..), ExampleFinite(..))

import Data.Attoparsec.Text as A
import Data.Text (Text)
import Control.Applicative ((<|>), many)
import Data.Char (isSpace)
import Data.Set (Set, fromList, member)
import Control.Monad (guard)
import Data.Foldable (asum)

keywords :: Set Text
keywords = fromList ["in", "∈", "∃", "exists", "and", "&", "∧"]

spacey :: Parser a -> Parser a
spacey p = A.skipSpace *> p <* A.skipSpace
parenthesized :: Parser a -> Parser a
parenthesized p = A.char '(' *> p <* A.char ')'

nonIdentifierCharacter :: Char -> Bool
nonIdentifierCharacter c = isSpace c || c `member` punctuation
    where
    punctuation = fromList "()[]"

query :: forall finite . Parser finite -> Parser (Query finite Text)
query finite = spacey go 
    where
    go = member_ <|> exists <|> and_ <|> parenthesized go
    var = do
        v <- takeTill nonIdentifierCharacter
        guard $ not $ (v `member` keywords)
        return v
    member_ = Member <$> var <* spacey lexeme <*> finite
        where
        lexeme = asum ["∈", "in"]
    exists = lexeme *> (Exists <$> spacey var <*> go)
        where
        lexeme = asum ["∃", "exists"]
    and_ = (And <$> parenthesized go <* spacey lexeme <*> parenthesized go)
        where
        lexeme = asum ["and", "&", "∧"]

exampleFinite :: Parser ExampleFinite
exampleFinite = EInt <$> ints_ 
    where
    ints_ = A.char '[' *> many int_ <* A.char ']'
    int_ = spacey decimal <* option ',' (A.char ',')

example :: Text -> Either String (Query ExampleFinite Text)
example = parseOnly (query exampleFinite <* A.endOfInput)
