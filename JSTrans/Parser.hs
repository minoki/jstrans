module JSTrans.Parser (parse,program) where
import Text.ParserCombinators.Parsec (runParser,eof,ParseError)
import JSTrans.AST
import JSTrans.Parser.Prim
import JSTrans.Parser.Token (whiteSpace)
import JSTrans.Parser.ExprStat

parse :: Parser a -> FilePath -> String -> Either ParseError a
parse p = flip runParser initialParserState
          $ do{ whiteSpace
              ; x <- p
              ; eof
              ; return x
              }


