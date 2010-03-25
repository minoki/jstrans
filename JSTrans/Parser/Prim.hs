module JSTrans.Parser.Prim (ParserState(psHadNewLine,ParserState)
                           ,Parser,initialParserState,option'
                           ,allowIn,disallowIn,isInAllowed) where
import Text.ParserCombinators.Parsec hiding (Parser,parse)

data ParserState = ParserState { psHadNewLine :: Bool
                               , psAllowIn :: Bool
                               }
type Parser a = GenParser Char ParserState a

initialParserState = ParserState { psHadNewLine = False
                                 , psAllowIn = True
                                 }


-- Whether or not to allow 'in' operator

allowIn :: Parser a -> Parser a
allowIn p = do{ state <- getState
              ; setState (state {psAllowIn = True})
              ; x <- p
              ; updateState (\s -> s {psAllowIn = psAllowIn state})
              ; return x
              }

disallowIn :: Parser a -> Parser a
disallowIn p = do{ state <- getState
                 ; setState (state {psAllowIn = False})
                 ; x <- p
                 ; updateState (\s -> s {psAllowIn = psAllowIn state})
                 ; return x
                 }

isInAllowed :: Parser Bool
isInAllowed = fmap psAllowIn getState


--- Utility

option' :: Parser a -> Parser (Maybe a)
option' p = option Nothing (fmap Just p)
