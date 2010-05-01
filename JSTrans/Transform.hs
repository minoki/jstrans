module JSTrans.Transform where
import JSTrans.AST as AST
import JSTrans.Parser.Token (reservedNames)
import Control.Monad.State
import Char (isDigit)
import Numeric (readDec)
import Maybe (maybeToList,isJust,isNothing,fromJust,catMaybes)
import List (union)

data TransformOptions = TransformOptions
  { transformConditionalCatch :: Bool
  , transformForEach :: Bool
  , transformGenerator :: Bool -- not parsed
  , transformArrayComprehension :: Bool
  , transformLetExpression :: Bool
  , transformLetStatement :: Bool -- not implemented
  , transformLetDefinition :: Bool -- not implemented
  , transformDestructuringAssignment :: Bool -- not implemented
  , transformReservedNameAsIdentifier :: Bool
  , transformExpressionClosure :: Bool
  , transformGeneratorExpression :: Bool -- not parsed
  }

identifierToStringLiteral = StringLiteral . show

data FunctionContext
    = FunctionContext
      { aliasForThis :: Maybe String
      , aliasForArguments :: Maybe String
      , isInsideImplicitlyCreatedFunction :: Bool
      , isGlobal :: Bool
      }

data TransformerData
    = TransformerData
      { genSymCounter :: Int
      , functionContext :: FunctionContext
      }
type TransformerState = State TransformerData

emptyFunctionContext = FunctionContext { aliasForThis = Nothing
                                       , aliasForArguments = Nothing
                                       , isInsideImplicitlyCreatedFunction = False
                                       , isGlobal = False
                                       }

getsF f = gets (f . functionContext)
modifyF f = modify (\s -> s { functionContext = f (functionContext s) })

genSym :: TransformerState String
genSym = do{ n <- gets genSymCounter
           ; modify (\s -> s {genSymCounter = n+1})
           ; return ('$':show n)
           }

transformProgram :: TransformOptions -> Program -> Program
transformProgram options p = evalState (AST.transformProgram transformer p) initialState
  where
    transformer = getTransformer options
    Program statements = p
    initialN = 1+scanInternalIdentifierUse statements
    initialState = TransformerData { genSymCounter = initialN
                                   , functionContext = emptyFunctionContext { isGlobal = True }
                                   }


transformAll = TransformOptions
  { transformConditionalCatch = True
  , transformForEach = True
  , transformGenerator = True -- not parsed
  , transformArrayComprehension = True
  , transformLetExpression = True
  , transformLetStatement = True -- not parsed
  , transformLetDefinition = True
  , transformDestructuringAssignment = True
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
        = do{ f <- getsF isInsideImplicitlyCreatedFunction
            ; if f
               then do{ w <- getsF aliasForArguments
                      ; case w of
                          Just name -> return $ Variable name
                          Nothing ->
                              do{ name <- genSym
                                ; modifyF (\s -> s {aliasForArguments = Just name})
                                ; return $ Variable name
                                }
                      }
               else return v
            }
    myExpr v@This
        = do{ f <- getsF isInsideImplicitlyCreatedFunction
            ; if f
               then do{ w <- getsF aliasForThis
                      ; case w of
                          Just name -> return $ Variable name
                          Nothing ->
                              do{ name <- genSym
                                ; modifyF (\s -> s {aliasForThis = Just name})
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
                <- getsF isInsideImplicitlyCreatedFunction
            ; modifyF (\s -> s {isInsideImplicitlyCreatedFunction = True})
            ; let compFor ((kind,varName,objExpr):rest)
                      = do{ objExpr' <- myExpr objExpr
                          ; rest' <- compFor rest
                          ; return
                            $ (if kind == CompForIn then ForIn else ForEach)
                                  (ForInLHSExpr $ patternNoExprToExpr varName) objExpr' rest'
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
            ; modifyF (\s -> s {isInsideImplicitlyCreatedFunction
                                   = prevIsInsideImplicitlyCreatedFunction})
            ; let body = FunctionBody $ map Statement
                         [VarDef VariableDefinition
                                     $ (LHSSimple arrayName,Just $ New (Variable "Array") [])
                                           :(map (\(_,n,_) -> (n,Nothing)) f) -- TODO: apply transformations to this
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
                <- getsF isInsideImplicitlyCreatedFunction
            ; modifyF (\s -> s {isInsideImplicitlyCreatedFunction = True})
            ; e' <- myExpr e
            ; modifyF (\s -> s {isInsideImplicitlyCreatedFunction
                                   = prevIsInsideImplicitlyCreatedFunction})
            ; let body = FunctionBody [Statement $ Return (Just e')]
            ; return $ FuncCall
                         (FunctionExpression False
                            $ makeFunction Nothing
                                  (map fst $ varsWithInitializer'++varsWithNoInitializer)
                                  body)
                         (map (fromJust . snd) varsWithInitializer')
            }
    myExpr x = transformExpr defaultTransformer x

    myStat :: Statement -> TransformerState Statement
    myStat (Try b [(var@(LHSSimple varName),e,c)] Nothing f)
        | transformConditionalCatch options
        = myStat (Try b [] (Just (var,cc)) f)
      where cc = Block [If e (BlockStatement c) (Just (Throw (Variable varName)))]
    myStat (Try b c@(_:_) uc f)
        | transformConditionalCatch options
        = do{ varName <- genSym
            ; let
                  cc [] = case uc of
                            Nothing -> (Throw (Variable varName))
                            Just (LHSSimple n,x) -> BlockStatement (substVarInBlock x n varName)
                            Just (pat,x) -> undefined {-BlockStatement (substVarInBlock x n varName)-}
                  cc ((LHSSimple n,e,x):xs) = If (substVarInExpr e n varName)
                                                 (BlockStatement (substVarInBlock x n varName))
                                                 (Just (cc xs))
                  cc ((n,e,x):xs) = undefined {-If (substVarInExpr e n varName)
                                                 (BlockStatement (substVarInBlock x n varName))
                                                 (Just (cc xs))-} -- FIXME
              in myStat (Try b [] (Just (LHSSimple varName,Block [cc c])) f)
            }
    myStat (ForEach (ForInLHSExpr lhs) o body)
        | transformForEach options
        = do{ objName <- genSym
            ; keyName <- genSym
            ; o' <- myExpr o
            ; return (BlockStatement
                      $ Block [VarDef VariableDefinition [(LHSSimple objName,Just o')]
                              ,ForIn (ForInVarDef VariableDefinition (LHSSimple keyName) Nothing)
                                     (Variable objName)
                                     (BlockStatement
                                      $ Block [ExpressionStatement (Assign "=" lhs (Variable keyName)),body])])
            }
    myStat (ForEach (ForInVarDef kind valName init) o body)
        | transformForEach options
        = do{ objName <- genSym
            ; keyName <- genSym
            ; o' <- myExpr o
            ; return (BlockStatement
                      $ Block
                            [VarDef VariableDefinition [(LHSSimple objName,Just o')]
                            ,VarDef kind [(valName,init)] -- FIXME: be recursive
                            ,ForIn (ForInVarDef VariableDefinition (LHSSimple keyName) Nothing)
                                   (Variable objName)
                                   (BlockStatement
                                    $ Block [ExpressionStatement (Assign "=" (patternNoExprToExpr valName) (Variable keyName)),body])])
            }
    myStat x = transformStat defaultTransformer x

    myBlock :: Block -> TransformerState Block
    myBlock x = transformBlock defaultTransformer x

    myFuncDecl :: String -> Function -> TransformerState Function
    myFuncDecl name x = transformFuncDecl defaultTransformer name x

    myFunction :: Function -> TransformerState Function
    myFunction fn = do{ outer <- getsF id
                      ; modifyF (const emptyFunctionContext)
                      ; fn' <- transformFunction defaultTransformer fn
                      ; aliasForThis' <- getsF aliasForThis
                      ; aliasForArguments' <- getsF aliasForArguments
                      ; let internalVars
                                = (maybe [] (\s -> [(LHSSimple s,Just This)]) aliasForThis')
                                  ++ (maybe [] (\s -> [(LHSSimple s,Just (Variable "arguments"))])
                                            aliasForArguments')
                      ; let fn''
                                = if null internalVars
                                   then fn'
                                   else makeFunction
                                            (functionName fn')
                                            (functionArguments fn')
                                            (case functionBody fn' of
                                               FunctionBody body
                                                   -> FunctionBody ((Statement $ VarDef VariableDefinition internalVars):body))
                      ; modifyF (const outer)
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
    handlePattern (LHSSimple name) = handleIdentifier name
    handlePattern (LHSArray elems) = mapM_ (maybe (return ()) handlePattern) elems
    handlePattern (LHSObject elems) = mapM_ (handlePattern . snd) elems
    myExpr (Variable name) = handleIdentifier name
    myExpr v = visitExpr defaultVisitor v
    myStat (VarDef _ vars) = mapM_ handlePattern $ map fst vars
    myStat s = visitStat defaultVisitor s
    myFuncDecl name fn = handleIdentifier name >> visitFuncDecl defaultVisitor name fn
    myFunction fn
        = do{ mapM_ handlePattern $ functionArguments fn
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
    pattern p@(LHSSimple name) | name == from = LHSSimple to
                               | otherwise = p
    pattern (LHSArray elems) = LHSArray $ map (fmap pattern) elems
    pattern (LHSObject elems) = LHSObject $ map (\(name,pat) -> (name,pattern pat)) elems
    myExpr (Variable name) = return (Variable $ ident name)
    myExpr v = transformExpr defaultTransformer v
    myStat (VarDef kind vars) = do{ vars' <- mapM varDecl vars
                                  ; return $ VarDef kind vars'
                                  }
      where varDecl (name,Just e) = do{ e' <- myExpr e
                                      ; return (pattern name,Just e')
                                      }
            varDecl (name,Nothing) = return (pattern name,Nothing)
    myStat s = transformStat defaultTransformer s
    myFunction fn
        = if from `elem` concatMap patternComponents (functionArguments fn)
          || from `elem` functionVariables fn
          || from == "argument"
          || Just from == functionName fn
           then return fn
           else transformFunction defaultTransformer fn


unpackPatternNoExpr :: LHSPatternNoExpr -> Expr -> TransformerState [(String,Expr)]
unpackPatternNoExpr (LHSSimple name) e = return [(name,e)]
unpackPatternNoExpr (LHSArray elems) e = liftM concat $ sequence $ zipWith elem elems [0..]
  where elem Nothing _ = return []
        elem (Just pat) i
            | isEmptyPattern pat = return []
            | isSingleElementPattern pat = unpackPatternNoExpr pat (referIndex e i)
            | otherwise = do{ tmpName <- genSym
                            ; inner <- unpackPatternNoExpr pat (Variable tmpName)
                            ; return $ (tmpName,referIndex e i):inner
                            }
        referIndex e i = Index e $ Literal $ NumericLiteral $ show i
unpackPatternNoExpr (LHSObject elems) e = liftM concat $ sequence $ map elem elems
  where elem (propName,pat)
            | isEmptyPattern pat = return []
            | isSingleElementPattern pat = unpackPatternNoExpr pat (referProp e propName)
            | otherwise = do{ tmpName <- genSym
                            ; inner <- unpackPatternNoExpr pat (Variable tmpName)
                            ; return $ (tmpName,referProp e propName):inner
                            }
        referProp e (PNIdentifier name) | name `notElem` reservedNames = Field e name
                                        | otherwise = Index e $ Literal $ StringLiteral $ show name
        referProp e (PNLiteral lit) = Index e $ Literal lit
