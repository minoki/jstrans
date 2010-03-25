module JSTrans.Transform where
import JSTrans.AST
import JSTrans.Parser.Token (reservedNames)
import Control.Monad.State
import Char (isDigit)
import Numeric (readDec)
import Maybe (maybeToList,isJust,isNothing,fromJust)
import List (union)

data TransformOptions = TransformOptions
  { transformConditionalCatch :: Bool
  , transformForEach :: Bool
  , transformGenerator :: Bool -- not parsed
  , transformArrayComprehension :: Bool
  , transformLetExpression :: Bool
  , transformLetStatement :: Bool -- not implemented
  , transformLetDefinition :: Bool -- not implemented
  , transformDestructingAssignment :: Bool -- not parsed
  , transformReservedNameAsIdentifier :: Bool
  , transformExpressionClosure :: Bool
  , transformGeneratorExpression :: Bool -- not parsed
  }

identifierToStringLiteral = StringLiteral . show

data TransformerData
    = TransformerData
      { genSymCounter :: Int
      , aliasForThis :: Maybe String
      , aliasForArguments :: Maybe String
      , isInsideImplicitlyCreatedFunction :: Bool
      }
type TransformerState = State TransformerData

genSym :: TransformerState String
genSym = do{ n <- gets genSymCounter
           ; modify (\s -> s {genSymCounter = n+1})
           ; return ('$':show n)
           }

transformProgram :: TransformOptions -> [SourceElement] -> [SourceElement]
transformProgram options s = evalState (mapM (transformSourceElem transformer) s) initialState
  where
    transformer = getTransformer options
    initialN = 1+scanInternalIdentifierUse s
    initialState = TransformerData { genSymCounter = initialN
                                   , aliasForThis = Nothing
                                   , aliasForArguments = Nothing
                                   , isInsideImplicitlyCreatedFunction = False
                                   }


transformAll = TransformOptions
  { transformConditionalCatch = True
  , transformForEach = True
  , transformGenerator = True -- not parsed
  , transformArrayComprehension = True -- not parsed
  , transformLetExpression = True -- not parsed
  , transformLetStatement = True -- not parsed
  , transformLetDefinition = True
  , transformDestructingAssignment = True -- not parsed
  , transformReservedNameAsIdentifier = True
  , transformExpressionClosure = True
  , transformGeneratorExpression = True -- not parsed
  }

getTransformer :: TransformOptions -> Transformer TransformerState
getTransformer options = myTransformer
  where
    myTransformer
        = defaultTransformer { transformExpr = myExpr
                             , transformStat = myStat
                             , transformBlock = myBlock
                             , transformFuncDecl = myFuncDecl
                             , transformFunction = myFunction
                             }
    defaultTransformer = getDefaultTransformer myTransformer
    myExpr :: Expr -> TransformerState Expr
    myExpr v@(Variable "arguments")
        = do{ f <- gets isInsideImplicitlyCreatedFunction
            ; if f
               then do{ w <- gets aliasForArguments
                      ; case w of
                          Just name -> return $ Variable name
                          Nothing ->
                              do{ name <- genSym
                                ; modify (\s -> s {aliasForArguments = Just name})
                                ; return $ Variable name
                                }
                      }
               else return v
            }
    myExpr v@This
        = do{ f <- gets isInsideImplicitlyCreatedFunction
            ; if f
               then do{ w <- gets aliasForThis
                      ; case w of
                          Just name -> return $ Variable name
                          Nothing ->
                              do{ name <- genSym
                                ; modify (\s -> s {aliasForThis = Just name})
                                ; return $ Variable name
                                }
                      }
               else return v
            }
    myExpr (Field x name)
        | transformReservedNameAsIdentifier options
          && name `elem` reservedNames
        = do{ x' <- myExpr x
            ; return $ Index x' $ Literal $ identifierToStringLiteral name
            }
    myExpr (ArrayComprehension x f i)
        | transformArrayComprehension options
        = do{ arrayName <- genSym
            ; let arrayVar = Variable arrayName
            ; prevIsInsideImplicitlyCreatedFunction
                <- gets isInsideImplicitlyCreatedFunction
            ; modify (\s -> s {isInsideImplicitlyCreatedFunction = True})
            ; let compFor ((kind,varName,objExpr):rest)
                      = do{ objExpr' <- myExpr objExpr
                          ; rest' <- compFor rest
                          ; return
                            $ (if kind == CompForIn then ForIn else ForEach)
                                  (ExpressionStatement $ Variable varName) objExpr' rest'
                          }
                  compFor [] = do{ x' <- myExpr x
                                 ; let p = ExpressionStatement
                                           $ FuncCall (Field arrayVar "push") [x']
                                 ; case i of
                                     Just g -> do{ g' <- myExpr g
                                                 ; return $ If g' p Nothing }
                                     Nothing -> return p
                                 }
            ; f' <- compFor f
            ; modify (\s -> s {isInsideImplicitlyCreatedFunction
                                   = prevIsInsideImplicitlyCreatedFunction})
            ; let body = map Statement
                         [VarDef VariableDefinition
                                     $ (arrayName,Just $ New (Variable "Array") [])
                                           :(map (\(_,n,_) -> (n,Nothing)) f)
                         ,f'
                         ,Return (Just arrayVar)
                         ]
            ; return $ FuncCall (FunctionExpression False $ makeFunction Nothing [] body) []
            }
    myExpr (ObjectLiteral elems)
        | transformReservedNameAsIdentifier options
        = do{ elems' <- mapM myProp elems
            ; return $ ObjectLiteral elems'
            }
      where
        myProp (name,Left x) = do{ x' <- myExpr x
                                 ; return (myPropName name,Left x')
                                 }
        myProp (name,Right (kind,fn))
            = do{ fn' <- myFunction fn
                ; return (myPropName name,Right (kind,fn'))
                }
        myPropName (PNIdentifier name)
            | name `elem` reservedNames
            = PNLiteral $ identifierToStringLiteral name
        myPropName x = x
    myExpr (FunctionExpression True fn)
        | transformExpressionClosure options
        = myExpr (FunctionExpression False fn)
    myExpr (Let vars e)
        | transformLetExpression options
        = do{ let varsWithInitializer = filter (isJust . snd) vars
                  varsWithNoInitializer = filter (isNothing . snd) vars
            ; varsWithInitializer' <- mapM (\(n,Just e) -> do { e' <- myExpr e
                                                              ; return (n,Just e')
                                                              }) varsWithInitializer
            ; prevIsInsideImplicitlyCreatedFunction
                <- gets isInsideImplicitlyCreatedFunction
            ; modify (\s -> s {isInsideImplicitlyCreatedFunction = True})
            ; e' <- myExpr e
            ; modify (\s -> s {isInsideImplicitlyCreatedFunction
                                   = prevIsInsideImplicitlyCreatedFunction})
            ; let body = [Statement $ Return (Just e')]
            ; return $ FuncCall
                         (FunctionExpression False
                            $ makeFunction Nothing
                                  (map fst $ varsWithInitializer'++varsWithNoInitializer)
                                  body)
                         (map (fromJust . snd) varsWithInitializer')
            }
    myExpr x = transformExpr defaultTransformer x

    myStat :: Statement -> TransformerState Statement
    myStat (Try b [(varName,e,c)] Nothing f)
        | transformConditionalCatch options
        = myStat (Try b [] (Just (varName,cc)) f)
      where cc = [If e (BlockStatement c) (Just (Throw (Variable varName)))]
    myStat (Try b c@(_:_) uc f)
        | transformConditionalCatch options
        = do{ varName <- genSym
            ; let
                  cc [] = case uc of
                            Nothing -> (Throw (Variable varName))
                            Just (n,x) -> BlockStatement (substVarInBlock x n varName)
                  cc ((n,e,x):xs) = If (substVarInExpr e n varName)
                                       (BlockStatement (substVarInBlock x n varName))
                                       (Just (cc xs))
              in myStat (Try b [] (Just (varName,[cc c])) f)
            }
    myStat (ForEach (ExpressionStatement lhs) o body)
        | transformForEach options
        = do{ objName <- genSym
            ; keyName <- genSym
            ; o' <- myExpr o
            ; return (BlockStatement [VarDef VariableDefinition [(objName,Just o')]
                                     ,ForIn (VarDef VariableDefinition [(keyName,Nothing)]) (Variable objName) (BlockStatement [ExpressionStatement (Assign "=" lhs (Variable keyName)),body])])
            }
    myStat (ForEach def@(VarDef kind [(valName,_)]) o body)
        | transformForEach options
        = do{ objName <- genSym
            ; keyName <- genSym
            ; o' <- myExpr o
            ; return (BlockStatement [VarDef VariableDefinition [(objName,Just o')]
                                     ,def
                                     ,ForIn (VarDef VariableDefinition [(keyName,Nothing)]) (Variable objName) (BlockStatement [ExpressionStatement (Assign "=" (Variable valName) (Variable keyName)),body])])
            }
    myStat x = transformStat defaultTransformer x

    myBlock :: Block -> TransformerState Block
    myBlock x = transformBlock defaultTransformer x

    myFuncDecl :: String -> Function -> TransformerState Function
    myFuncDecl name x = transformFuncDecl defaultTransformer name x

    myFunction :: Function -> TransformerState Function
    myFunction fn = do{ prevAliasForThis <- gets aliasForThis
                      ; prevAliasForArguments <- gets aliasForArguments
                      ; prevIsInsideImplicitlyCreatedFunction
                          <- gets isInsideImplicitlyCreatedFunction
                      ; modify (\s -> s { aliasForThis = Nothing
                                        , aliasForArguments = Nothing
                                        , isInsideImplicitlyCreatedFunction = False
                                        })
                      ; fn' <- transformFunction defaultTransformer fn
                      ; aliasForThis' <- gets aliasForThis
                      ; aliasForArguments' <- gets aliasForArguments
                      ; let internalVars
                                = (maybe [] (\s -> [(s,Just This)]) aliasForThis')
                                  ++ (maybe [] (\s -> [(s,Just (Variable "arguments"))])
                                            aliasForArguments')
                      ; let fn'' = if null internalVars
                                    then fn'
                                    else makeFunction
                                             (functionName fn')
                                             (functionArguments fn')
                                             ((Statement $ VarDef VariableDefinition internalVars)
                                                : functionBody fn')
                      ; modify (\s -> s { aliasForThis = prevAliasForThis
                                        , aliasForArguments = prevAliasForArguments
                                        , isInsideImplicitlyCreatedFunction
                                            = prevIsInsideImplicitlyCreatedFunction
                                        })
                      ; return fn''
                      }


scanInternalIdentifierUse :: [SourceElement] -> Int
scanInternalIdentifierUse code = flip execState 0 $ mapM_ (visitSourceElem myVisitor) code
  where
    myVisitor,defaultVisitor :: Visitor (State Int)
    myVisitor = defaultVisitor { visitExpr = myExpr
                               , visitStat = myStat
                               , visitFuncDecl = myFuncDecl
                               , visitFunction = myFunction
                               }
    defaultVisitor = getDefaultVisitor myVisitor
    handleIdentifier ('$':s)
        | and $ map isDigit s
        = do{ let [(m,_)] = readDec s
            ; n <- get
            ; put $ max n m
            }
    handleIdentifier _ = return ()
    myExpr (Variable name) = handleIdentifier name
    myExpr v = visitExpr defaultVisitor v
    myStat (VarDef _ vars) = mapM_ handleIdentifier $ map fst vars
    myStat s = visitStat defaultVisitor s
    myFuncDecl name fn = handleIdentifier name >> visitFuncDecl defaultVisitor name fn
    myFunction fn
        = do{ mapM_ handleIdentifier $ functionArguments fn
            ; mapM_ handleIdentifier $ functionVariables fn
            ; mapM_ handleIdentifier $ maybeToList (functionName fn)
            ; --TODO: let variable
            ; visitFunction defaultVisitor fn
            }

substVarInExpr :: Expr -> String -> String -> Expr
substVarInExpr e from to = evalState (transformExpr (substVar from to) e) ()
substVarInBlock :: Block -> String -> String -> Block
substVarInBlock e from to = evalState (transformBlock (substVar from to) e) ()
substVar from to = myTransformer
  where
    myTransformer,defaultTransformer :: Transformer (State ())
    myTransformer = defaultTransformer { transformExpr = myExpr
                                       , transformStat = myStat
                                       , transformFunction = myFunction
                                       }
    defaultTransformer = getDefaultTransformer myTransformer
    ident name | name == from = to
               | otherwise = name
    myExpr (Variable name) = return (Variable $ ident name)
    myExpr v = transformExpr defaultTransformer v
    myStat (VarDef kind vars) = do{ vars' <- mapM varDecl vars
                                  ; return $ VarDef kind vars'
                                  }
      where varDecl (name,Just e) = do{ e' <- myExpr e
                                      ; return (ident name,Just e')
                                      }
            varDecl (name,Nothing) = return (ident name,Nothing)
    myStat s = transformStat defaultTransformer s
    myFunction fn
        = if from `elem` functionArguments fn
          || from `elem` functionVariables fn
          || from == "argument"
          || Just from == functionName fn
           then return fn
           else transformFunction defaultTransformer fn
