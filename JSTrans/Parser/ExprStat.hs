module JSTrans.Parser.ExprStat (functionBody,program,expr) where
import JSTrans.AST as AST hiding (functionBody)
import JSTrans.Parser.Prim (Parser,option',allowIn,disallowIn,isInAllowed)
import JSTrans.Parser.Token
import Text.ParserCombinators.Parsec hiding (Parser,parse)
import Text.ParserCombinators.Parsec.Expr as ParsecExpr

-- Expressions
literal :: Parser Literal
primaryExpr,arrayLiteral,objectLiteral :: Parser Expr
memberExpr,functionExpr,callExpr :: Parser Expr
leftHandSideExpr,postfixExpr :: Parser Expr
unaryExpr :: Parser Expr
logicalORExprBase,conditionalExprBase,exprBase :: Parser Expr
assignmentExpr,assignmentExprNoIn :: Parser Expr
expr,exprNoIn :: Parser Expr

--- Statements
block :: Parser Block
varStatement,emptyStatement :: Parser Statement
expressionStatement,ifStatement,iterationStatement :: Parser Statement
continueStatement,breakStatement,returnStatement :: Parser Statement
switchStatement :: Parser Statement
labelledStatement :: Parser Statement
throwStatement,tryStatement :: Parser Statement
debuggerStatement :: Parser Statement
statement :: Parser Statement
sourceElement :: Parser SourceElement
functionDeclaration :: Parser SourceElement
functionBody :: Parser FunctionBody
program :: Parser [SourceElement]


---
--- Expressions
---

primaryExpr = parens expr
          <|> (reserved "this" >> return This)
          <|> fmap Variable identifier
          <|> fmap Literal literal
          <|> arrayLiteral
          <|> objectLiteral
          <?> "PrimaryExpression"

literal = do{ reserved "null" ; return NullLiteral }
      <|> do{ reserved "true" ; return $ BooleanLiteral True }
      <|> do{ reserved "false" ; return $ BooleanLiteral False }
      <|> numericLiteral
      <|> stringLiteral
      <|> regExpLiteral


arrayLiteral = fmap ArrayLiteral $ squares $ sepBy element comma
  where
    element = option' assignmentExpr

objectLiteral = fmap ObjectLiteral $ braces $ sepEndBy propertyAssignment comma
  where
    propertyAssignment :: Parser (PropertyName,Either Expr (AccessorKind,Function))
    propertyAssignment
        = do{ name <- try (reserved "get" >> propertyName)
            ; parens (return ())
            ; body <- braces functionBody
            ; let fn = makeFunction Nothing [] body
            ; return (name,Right (Getter,fn))
            }
      <|> do{ name <- try (reserved "set" >> propertyName)
            ; paramName <- parens identifierExcludingEvalOrArguments
            ; body <- braces functionBody
            ; let fn = makeFunction Nothing [paramName] body
            ; return (name,Right (Setter,fn))
            }
      <|> do{ name <- propertyName
            ; colon
            ; value <- assignmentExpr
            ; return (name,Left value)
            }
    propertyName :: Parser PropertyName
    propertyName = fmap PNIdentifier identifierOrReserved -- EXT
               <|> fmap PNLiteral (stringLiteral <|> numericLiteral)

memberExpr = suffix =<< (primaryExpr
                     <|> functionExpr
                     <|> letExpr
                     <|> do{ reserved "new"
                           ; e <- memberExpr
                           ; a <- option [] arguments
                           ; return $ New e a
                           })
  where
    suffix a = do{ x <- squares expr
                 ; suffix $ Index a x
                 }
           <|> do{ dot
                 ; n <- identifierOrReserved -- EXT
                 ; suffix $ Field a n
                 }
           <|> return a

letExpr = do{ reserved "let"
            ; variables <- parens $ sepBy1 varDeclaration comma
            ; body <- assignmentExprBase
            ; return $ Let variables body
            }

callExpr = do{ f <- memberExpr
             ; do{ args <- arguments
                 ; suffix $ FuncCall f args
                 }
           <|> return f
             }
  where
    suffix a = do{ args <- arguments
                 ; suffix $ FuncCall a args
                 }
           <|> do{ x <- squares expr
                 ; suffix $ Index a x
                 }
           <|> do{ dot
                 ; n <- identifierOrReserved -- EXT
                 ; suffix $ Field a n
                 }
           <|> return a

arguments :: Parser [Expr]
arguments = parens $ sepBy assignmentExpr comma

leftHandSideExpr = callExpr <?> "LeftHandSideExpr"

postfixExpr = leftHandSideExpr >>= suffix where
  suffix a = do{ noLineTerminator
               ; op <- reservedOp "++" <|> reservedOp "--"
               ; return $ AST.Postfix (operatorForName op) a
               }
         <|> return a
         <?> "PostfixExpr"

-- We can't use buildExpressionParser for UnaryExpression because it won't allow prefix operators of the same precedence to occur more than once
-- e.g. typeof -123
unaryExpr = do{ op <- reserved "delete"
                  <|> reserved "void"
                  <|> reserved "typeof"
                  <|> reservedOp "++"
                  <|> reservedOp "--"
                  <|> reservedOp "+"
                  <|> reservedOp "-"
                  <|> reservedOp "~"
                  <|> reservedOp "!"
              ; e <- unaryExpr
              ; return $ AST.Prefix (operatorForName op) e
              }
        <|> postfixExpr
        <?> "UnaryExpression"

logicalORExprBase = buildExpressionParser table unaryExpr
                <?> "LogicalORExpression"
  where
    table = [[op "*" AssocLeft,op "/" AssocLeft,op "%" AssocLeft]
            ,[op "+" AssocLeft,op "-" AssocLeft]
            ,[op "<<" AssocLeft,op ">>" AssocLeft,op ">>>" AssocLeft]
            ,[op "<" AssocLeft,op ">" AssocLeft
             ,op "<=" AssocLeft,op ">=" AssocLeft
             ,op' "instanceof" AssocLeft,inOp]
            ,[op "==" AssocLeft,op "!=" AssocLeft
             ,op "===" AssocLeft,op "!==" AssocLeft]
            ,[op "&" AssocLeft]
            ,[op "^" AssocLeft]
            ,[op "|" AssocLeft]
            ,[op "&&" AssocLeft]
            ,[op "||" AssocLeft]
            ]
    op name assoc = flip ParsecExpr.Infix assoc
                    $ do{ reservedOp name
                        ; return $ AST.Binary $ operatorForName name
                        }
    op' name assoc = flip ParsecExpr.Infix assoc
                     $ do{ reserved name
                         ; return $ AST.Binary $ operatorForName name
                         }
    inOp = flip ParsecExpr.Infix AssocLeft
           $ do{ inAllowed <- isInAllowed
               ; if inAllowed
                 then reserved "in" >> return ()
                 else pzero
               ; return $ AST.Binary $ operatorForName "in"
               }

conditionalExprBase
    = do{ a <- logicalORExprBase
        ; do{ reservedOp "?"
            ; b <- assignmentExpr
            ; colon
            ; c <- assignmentExprBase
            ; return $ Cond a b c
            }
      <|> return a
        }
  <?> "ConditionalExpression"

assignmentExprBase
    = do{ (lhs,op)
              <- try $ 
                 do{ lhs <- leftHandSideExpr
                   ; op <- assignmentOperator
                   ; return (lhs,op)
                   } 
        ; rhs <- assignmentExprBase
        ; return $ Assign (operatorForName op) lhs rhs
        }
  <|> conditionalExprBase
  <?> "AssignmentExpression"
  where
    assignmentOperator =
      choice $ map reservedOp
        ["=","*=","%=","+=","-=","<<=",">>=",">>>=","&=","^=","|=","/="]
assignmentExpr = allowIn assignmentExprBase
assignmentExprNoIn = disallowIn assignmentExprBase

exprBase = assignmentExprBase >>= suffix
       <?> "Expression"
  where
    suffix a = do{ comma
                 ; b <- assignmentExprBase
                 ; suffix $ Binary (operatorForName ",") a b
                 }
           <|> return a
expr = allowIn exprBase
exprNoIn = disallowIn exprBase


---
--- Statements
---

block = braces $ many statement
varStatement = do{ defKind <- definition
                 ; varDecls <- sepBy1 varDeclaration comma
                 ; autoSemi
                 ; return $ VarDef defKind varDecls
                 }

varDeclarationBase
    = do{ name <- identifierExcludingEvalOrArguments
        ; init <- option' (reservedOp "=" >> assignmentExprBase)
        ; return (name,init)
        }
varDeclaration = allowIn varDeclarationBase
varDeclarationNoIn = disallowIn varDeclarationBase

definition :: Parser DefinitionKind
definition = do{ reserved "var" ; return VariableDefinition }
         <|> do{ reserved "const" ; return ConstantDefinition }
         <|> do{ try (reserved "let" >> notFollowedBy (char '(')) ; return LetDefinition }

emptyStatement = semi >> return EmptyStat
letStatement = do{ reserved "let"
                 ; variables <- parens $ sepBy1 varDeclaration comma
                 ; do{ body <- block
                     ; return $ LetStatement variables body
                     }
               <|> do{ body <- assignmentExpr
                     ; return $ ExpressionStatement $ Let variables body
                     }
                 }
expressionStatement
    = do{ try (do{ c <- reservedOp "{" <|> reserved "function"
                 ; unexpected (show c)
                 }
           <|> return ())
        ; e <- expr
        ; autoSemi
        ; return $ ExpressionStatement e
        }
ifStatement = do{ reserved "if"
                ; cond <- parens expr
                ; thenstat <- statement
                ; elsestat <- option' (reserved "else" >> statement)
                ; return $ If cond thenstat elsestat
                }
iterationStatement = doWhileStatement
                 <|> whileStatement
                 <|> forStatement
  where
    doWhileStatement = do{ reserved "do"
                         ; stat <- statement
                         ; reserved "while"
                         ; cond <- parens expr
                         ; autoSemi
                         ; return $ DoWhile cond stat
                         }
    whileStatement = do{ reserved "while"
                       ; cond <- parens expr
                       ; stat <- statement
                       ; return $ While cond stat
                       }
    forStatement = do{ reserved "for"
                     ; ctor
                         <- do{ reserved "each"
                              ; parens $ forInHead ForEach
                              }
                        <|> parens (try forHead <|> forInHead ForIn)
                     ; body <- statement
                     ; return $ ctor body
                     }
    forHead = do{ e0 <- do{ kind <- definition
                          ; varDecls <- sepBy1 varDeclarationNoIn comma
                          ; return $ Just $ VarDef kind varDecls
                          }
                    <|> (option' $ fmap ExpressionStatement exprNoIn)
                ; semi
                ; e1 <- option' expr
                ; semi
                ; e2 <- option' expr
                ; return (For e0 e1 e2)
                }
    forInHead ctor
        = do{ e0 <- fmap ExpressionStatement leftHandSideExpr
                <|> do{ kind <- (reserved "var" >> return VariableDefinition)
                            <|> (reserved "let" >> return LetDefinition)
                      ; decl <- varDeclarationNoIn
                      ; return $ VarDef kind [decl]
                      }
            ; reserved "in"
            ; e1 <- expr
            ; return (ctor e0 e1)
            }

continueStatement = do{ reserved "continue"
                      ; label <- option' (noLineTerminator >> identifier)
                      ; autoSemi
                      ; return $ Continue label
                      }
breakStatement = do{ reserved "break"
                   ; label <- option' (noLineTerminator >> identifier)
                   ; autoSemi
                   ; return $ Break label
                   }
returnStatement = do{ reserved "return"
                    ; expr <- option' (noLineTerminator >> expr)
                    ; autoSemi
                    ; return $ Return expr
                    }
withStatement = do{ reserved "with"
                  ; expr <- parens expr
                  ; statement
                  ; fail "with statement is deprecated"
                  }
switchStatement = do{ reserved "switch"
                    ; expr <- parens expr
                    ; clauses <- braces caseClausesOrDefaultClause
                    ; return $ Switch expr clauses
                    }
  where
    caseClausesOrDefaultClause
        = do{ clauses <- many caseClause
            ; do{ d <- defaultClause
                ; clauses2 <- many caseClause
                ; return $ clauses ++ d:clauses2
                }
          <|> return clauses
            }
    caseClause = do{ reserved "case"
                   ; e <- expr
                   ; colon
                   ; stmts <- many statement
                   ; return $ CaseClause e stmts
                   }
    defaultClause = do{ reserved "default"
                      ; colon
                      ; stmts <- many statement
                      ; return $ DefaultClause stmts
                      }

labelledStatement = try $ do{ label <- identifier
                            ; colon
                            ; stat <- statement
                            ; return $ Labelled label stat
                            }
throwStatement = do{ reserved "throw"
                   ; noLineTerminator
                   ; value <- expr
                   ; autoSemi
                   ; return $ Throw value
                   }
tryStatement
    = do{ reserved "try"
        ; body <- block
        ; do{ (conditionalCatches,unconditionalCatch)
                  <- catchClauses
            ; finallyClause <- option' finally
            ; return $ Try body conditionalCatches unconditionalCatch finallyClause
            }
      <|> do{ finallyClause <- finally
            ; return $ Try body [] Nothing (Just finallyClause)
            }
        }
  where
    catchClauses :: Parser ([(String,Expr,Block)],Maybe (String,Block))
    catchClauses
        = do{ reserved "catch"
            ; reservedOp "("
            ; name <- identifierExcludingEvalOrArguments
            ; do{ reservedOp ")"
                ; body <- block
                ; return ([],Just (name,body))
                }
          <|> do{ reserved "if" -- EXT: conditional catch
                ; cond <- expr
                ; reservedOp ")"
                ; body <- block
                ; (rest,unconditional) <- catchClauses <|> return ([],Nothing)
                ; return ((name,cond,body):rest,unconditional)
                }
            }
    finally = do{ reserved "finally"
                ; block
                }

debuggerStatement = do{ reserved "debugger"
                      ; autoSemi
                      ; return Debugger
                      }
statement = fmap BlockStatement block
        <|> varStatement
        <|> emptyStatement
        <|> labelledStatement
        <|> letStatement -- must be before expressionStatement
        <|> expressionStatement
        <|> ifStatement
        <|> iterationStatement
        <|> continueStatement
        <|> breakStatement
        <|> returnStatement
        <|> withStatement
        <|> switchStatement
        <|> throwStatement
        <|> tryStatement
        <|> debuggerStatement
        <?> "Statement"

sourceElement = fmap Statement statement
            <|> functionDeclaration
            <?> "SourceElement"

functionDeclaration
    = do{ reserved "function"
        ; name <- identifierExcludingEvalOrArguments
        ; params <- parens $ sepBy identifierExcludingEvalOrArguments comma
        ; checkDuplicate params
        ; body <- braces functionBody
        ; let fn = makeFunction Nothing params body
        ; return $ FunctionDeclaration name fn
        }
functionExpr
    = do{ reserved "function"
        ; name <- option' identifierExcludingEvalOrArguments
        ; params <- parens $ sepBy identifierExcludingEvalOrArguments comma
        ; checkDuplicate params
        ; (isEC,body) <- (fmap (\x -> (False,x)) $ braces functionBody)
                     <|> (fmap (\e -> (True,[Statement (Return (Just e))]))
                                   $ assignmentExprBase) -- EXT: Expression Closure
        ; let fn = makeFunction Nothing params body
        ; return $ FunctionExpression isEC fn
        }
functionBody = many sourceElement
program = do{ whiteSpace
            ; x <- many sourceElement
            ; eof
            ; return x
            }

checkDuplicate [] = return ()
checkDuplicate (x:xs) | x `elem` xs = fail ("SyntaxError: parameter name " ++ show x ++ " occured more than once in FormalParameterList")
                      | otherwise = checkDuplicate xs

