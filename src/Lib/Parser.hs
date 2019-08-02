module Lib.Parser where

import Lib(Query(..), ExampleExtrinsic(..))

import Data.Attoparsec.Text as A
import Data.Text (Text)
import Control.Applicative ((<|>), many)
import Data.Char (isSpace)
import Data.Set (Set, fromList, member)
import Control.Monad (guard)
import Data.Foldable (asum)

keywords :: Set Text
keywords = fromList ["∃", "exists"]

spacey :: Parser a -> Parser a
spacey p = A.skipSpace *> p <* A.skipSpace
parenthesized :: Parser a -> Parser a
parenthesized p = A.char '(' *> p <* A.char ')'

nonIdentifierCharacter :: Char -> Bool
nonIdentifierCharacter c = isSpace c || c `member` punctuation
    where
    punctuation = fromList "()[]"

query :: forall extrinsic . Set Text -> Parser extrinsic -> Parser (Query extrinsic Text)
query extrinsics extrinsic = spacey go 
    where
    arg = spacey (extrinsic_ <|> var <|> exists <|> parenthesized go)
    go = apply <|> arg 
    var = Var <$> ident
    extrinsic_ = Extrinsic <$> extrinsic
    ident = do
        v <- A.takeWhile1 (not . nonIdentifierCharacter)
        guard $ not $ (v `member` keywords || v `member` extrinsics)
        return v
    exists = lexeme *> (Exists <$> spacey ident <*> go)
        where
        lexeme = asum ["∃", "exists"]
    apply =  do
        fun <- spacey extrinsic_ -- TODO: Allow non-extrinic functions
        arg1 <- arg
        args <- many1 arg
        return $ foldl Apply (Apply fun arg1) args
        --Apply <$> spacey extrinsic <*> many arg


exampleExtrinsics :: Set Text
exampleExtrinsics = fromList ["in", "∈", "and", "&", "∧"]


exampleExtrinsic :: Parser ExampleExtrinsic
exampleExtrinsic = eint <|> emember 
    where
    emember = EMember <$ (A.string "in" <|> A.string "∈")
    eint = EInt <$> ints_ 
    ints_ = A.char '[' *> many int_ <* A.char ']'
    int_ = spacey decimal <* option ',' (A.char ',')

example :: Text -> Either String (Query ExampleExtrinsic Text)
example = parseOnly (query exampleExtrinsics exampleExtrinsic <* A.endOfInput)

