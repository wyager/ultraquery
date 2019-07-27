module Main where

import qualified Lib 
import qualified Lib.Parser
import Data.Text.IO as TIO (getContents)

main :: IO ()
main = do
    program <- TIO.getContents
    case Lib.Parser.example program of 
        Left string -> print string
        Right query -> let (renamed, rs, typeError, context) = Lib.process query in do
            print query
            print renamed
            print rs 
            print typeError 
            print context
