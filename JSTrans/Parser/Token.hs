module JSTrans.Parser.Token (whiteSpace,noLineTerminator
                            ,symbol,parens,squares,braces,comma,colon,dot
                            ,identifierOrReserved,identifier
                            ,identifierExcludingEvalOrArguments
                            ,reserved,reservedOp,semi,autoSemi
                            ,numericLiteral,stringLiteral
                            ,regExpLiteral
                            ,lineTerminatorChars
                            ,reservedNames) where
import Text.ParserCombinators.Parsec hiding (Parser)
import JSTrans.AST
import JSTrans.Parser.Prim
{-
import Data.Char (generalCategory
                 ,GeneralCategory(Space,NonSpacingMark
                                 ,SpacingCombiningMark
                                 ,DecimalNumber
                                 ,ConnectorPunctuation))
-}
import List

--unicodeCategory :: GeneralCategory -> Parser Char
lineTerminatorChars :: [Char]
whiteSpace :: Parser ()
noLineTerminator,lineTerminator :: Parser ()
lexeme :: Parser a -> Parser a
symbol :: String -> Parser String
parens,squares,braces :: Parser a -> Parser a
comma,semi,colon,dot :: Parser Char
identifierStart,identifierPart :: Parser Char
ident :: Parser String
identifierOrReserved :: Parser String
identifier :: Parser String
identifierExcludingEvalOrArguments :: Parser String
reserved :: String -> Parser String
reservedOp :: String -> Parser String
autoSemi :: Parser ()

numericLiteral :: Parser Literal
stringLiteral :: Parser Literal
regExpLiteral :: Parser Literal


reservedOpNames = ["{","}","(",")" --,"[","]",".",";",","
                  ,"<",">","<=",">=","==","!=","===","!=="
                  ,"+","-","*","%","++","--"
                  ,"<<",">>",">>>","&","|","^"
                  ,"!","~","&&","||","?",":"
                  ,"=","+=","-=","*=","%=","<<="
                  ,">>=",">>>=","&=","|=","^="
                  ,"/","/="
                  ]

reservedOpNames' = sortBy (\a b -> compare (length b) (length a)) reservedOpNames
reservedOpNames'' = map (try . symbol) reservedOpNames'

reservedNames = [-- Keywords
                 "break","case","catch","const","continue"
                ,"debugger","default","delete","do","else"
                ,"finally","for","function","if","in"
                ,"instanceof","let","new","return","switch"
                ,"this","throw","try","typeof","var","void"
                ,"while","with","yield"
                 -- Future Reserved Words
                ,"class","export","enum","extends","import"
                ,"super"
                 -- Future Reserved Words (within strict mode)
                ,"implements","interface","package","private"
                ,"protected","public","static"
                 -- Literals
                ,"null","true","false"
                ]

--unicodeCategory cat = satisfy ((cat ==) . generalCategory)

-- U+2028:LS,U+2029:PS
lineTerminatorChars = "\LF\CR\x2028\x2029"

whiteSpace = do{ updateState (\st -> st {psHadNewLine = False})
               ; skipMany (whiteSpaceChars
                       <|> lineTerminator
                       <|> comment)
               }
          <?> ""
  where
    comment = (try
              $ do{ char '/'
                  ; do{ char '/'
                      ; skipMany $ noneOf lineTerminatorChars
                      }
                <|> do{ char '*'
                      ; inComment
                      }
                  }) <?> ""
    inComment = do{ char '*'
                  ; (char '/' >> return ())
                <|> inComment
                  }
            <|> do{ lineTerminator
                  ; inComment
                  }
            <|> do{ anyChar
                  ; skipMany $ noneOf ("*"++lineTerminatorChars)
                  ; inComment
                  }
    -- U+00A0:NBSP,U+FEFF:BOM,Zs
    whiteSpaceChars = skipMany1 (oneOf "\HT\VT\FF\SP\x00A0\xFEFF"
                                {- <|> unicodeCategory Space -})
    lineTerminator = do{ oneOf lineTerminatorChars
                       ; updateState (\s -> s {psHadNewLine = True})
                       }

noLineTerminator = do{ s <- getState
                     ; if psHadNewLine s
                        then unexpected "LineTerminator"
                        else return ()
                     }
               <?> "no LineTerminator"

lineTerminator = do{ s <- getState
                   ; if psHadNewLine s
                      then return ()
                      else unexpected "no LineTerminator"
                   }
               <?> "LineTerminator"

lexeme p = do{ x <- p
             ; whiteSpace
             ; return x
             }

symbol = lexeme . string
parens = between (symbol "(") (symbol ")")
squares = between (symbol "[") (symbol "]")
braces = between (symbol "{") (symbol "}")
semi = lexeme $ char ';'
comma = lexeme $ char ','
colon = lexeme $ char ':'
dot = lexeme $ char '.'

identifierStart = letter <|> oneOf "$_" -- TODO: unicodeEscapeSequence
identifierPart = identifierStart
             {- <|> unicodeCategory NonSpacingMark -}
             {- <|> unicodeCategory SpacingCombiningMark -}
             <|> digit {- <|> unicodeCategory DecimalNumber -}
             {- <|> unicodeCategory ConnectorPunctuation -}
             -- U+200C:Zero width non-joiner <ZWNJ>,U+200D:Zero with joiner <ZWJ>
             <|> oneOf "\x200C\x200D"

ident = do{ c <- identifierStart
          ; cs <- many identifierPart
          ; return (c:cs)
          }

identifierOrReserved = lexeme ident <?> "Identifier"
identifier = lexeme $ try $
             (do{ name <- ident
               ; if name `elem` reservedNames
                  then unexpected ("reserved word " ++ show name)
                  else return name
               }
         <?> "Identifier")
identifierExcludingEvalOrArguments
    = do{ name <- identifier
        ; if name == "eval" || name == "arguments"
           then unexpected "SyntaxError: variable name \"eval\" or \"arguments\" is fobidden here"
           else return name
        }

reserved name = lexeme $ try $
                (do{ s <- string name
                  ; notFollowedBy identifierPart <?> ("end of " ++ show name)
                  ; return s
                  }
            <?> show name)

reservedOp name = lexeme $ try $
                  -- TODO: more efficient implementation
                  (do{ n <- choice reservedOpNames''
                    ; if n == name
                       then return name
                       else unexpected ("reserved word " ++ show n)
                    }
              <?> show name)

autoSemi = (semi >> return ())
       <|> lineTerminator
       <|> do{ input <- getInput
             ; char '}'
             ; setInput input
             }
       <?> "semicolon"



numericLiteral = lexeme
                 (do{ cs <- hexIntegerLiteral <|> decimalLiteral
                   ; notFollowedBy (identifierStart <|> decimalDigit)
                   ; return $ NumericLiteral cs
                   })
  where
    decimalLiteral = try (
                     do{ d0 <- option [] decimalIntegerLiteral
                       ; c1 <- char '.'
                       ; d2 <- many decimalDigit
                       ; d3 <- exponentPartOpt
                       ; return $ d0 ++ (c1:(d2++d3))
                       })
                 <|> do{ d0 <- decimalIntegerLiteral
                       ; d1 <- exponentPartOpt
                       ; return (d0 ++ d1)
                       }
    decimalIntegerLiteral = do{ c <- char '0'
                              ; do{ decimalDigit
                                  ; fail "octal literals are deprecated"
                                  }
                            <|> return [c]
                              }
                        <|> do{ c0 <- nonZeroDigit
                              ; cs <- many decimalDigit
                              ; return (c0:cs)
                              }
    exponentPartOpt = do{ c0 <- oneOf "eE"
                        ; do{ c1 <- oneOf "+-"
                            ; cs <- many1 decimalDigit
                            ; return (c0:c1:cs)
                            }
                      <|> do{ cs <- many1 decimalDigit
                            ; return (c0:cs)
                            }
                        }
                  <|> return []
    hexIntegerLiteral = lexeme $
                        do{ (c0,c1) <- try $ do{ c0 <- char '0'
                                               ; c1 <- oneOf "xX"
                                               ; return (c0,c1)
                                               }
                          ; cs <- many1 hexDigit
                          ; return (c0:c1:cs)
                          }
    decimalDigit = oneOf "0123456789"
    nonZeroDigit = oneOf "123456789"
    hexDigit = oneOf "0123456789abcdefABCDEF"

stringLiteral = lexeme
               (do{ c0 <- char '"'
                  ; d1 <- manyTill stringChar (char '"')
                  ; return $ StringLiteral (c0:(foldr ($) "\"" d1))
                  }
            <|> do{ c0 <- char '\''
                  ; d1 <- manyTill stringChar (char '\'')
                  ; return $ StringLiteral (c0:(foldr ($) "'" d1))
                  })
  where
    stringChar = do{ c0 <- char '\\'
                   ; c1 <- anyChar -- TODO: implement properly
                   ; return $ (c0:).(c1:)
                   }
             <|> do{ c0 <- noneOf "\\\CR\LF\x2028\x2029" -- U+2028:LS,U+2029:PS
                   ; return (c0:)
                   }
             <?> "StringCharacter"

regExpLiteral = lexeme
               (do{ c0 <- char '/'
                  ; d1 <- regExpBody
                  ; c2 <- char '/'
                  ; d3 <- many identifierPart
                  ; return $ RegExpLiteral (c0:(d1 (c2:d3)))
                  })
            <?> "RegExp Literal"
  where
    regExpBody = do{ c0 <- regExpFirstChar
                   ; cs <- many regExpChar
                   ; return $ c0 . (foldr (.) id cs)
                   }
    regExpFirstChar = do{ c0 <- noneOf ("*\\/["++lineTerminatorChars)
                        ; return (c0:)
                        }
                  <|> regExpBackslashSequence
                  <|> regExpClass
    regExpChar = do{ c0 <- noneOf ("\\/["++lineTerminatorChars)
                   ; return (c0:)
                   }
             <|> regExpBackslashSequence
             <|> regExpClass
    regExpBackslashSequence = do{ c0 <- char '\\'
                                ; c1 <- noneOf lineTerminatorChars
                                ; return $ (c0:).(c1:)
                                }
    regExpClass = do{ c0 <- char '['
                    ; d1 <- many regExpClassChar
                    ; c2 <- char ']'
                    ; return $ (c0:) . (foldr (.) (c2:) d1)
                    }
    regExpClassChar = do{ c0 <- noneOf ("]\\"++lineTerminatorChars)
                        ; return (c0:)
                        }
                  <|> regExpBackslashSequence
