module JSTrans.Transform where
import JSTrans.AST as AST
import JSTrans.Parser.Token (reservedNames)
import Control.Monad.State
import Char (isDigit)
import Numeric (readDec)
import Maybe (maybeToList,isJust,isNothing,fromJust,catMaybes)
import List (union,find,intersect,partition)

data TransformOptions = TransformOptions
  { transformConditionalCatch :: Bool
  , transformForEach :: Bool
  , transformGenerator :: Bool -- not parsed
  , transformArrayComprehension :: Bool
  , transformLetExpression :: Bool
  , transformLetStatement :: Bool
  , transformLetDefinition :: Bool -- not implemented
  , transformDestructuringAssignment :: Bool -- partially implemented
  , transformReservedNameAsIdentifier :: Bool
  , transformExpressionClosure :: Bool
  , transformGeneratorExpression :: Bool -- not parsed
  }

identifierToStringLiteral = StringLiteral . show
integerToNumericLiteral = NumericLiteral . show

data FunctionContext
    = FunctionContext
      { aliasForThis :: Maybe String
      , aliasForArguments :: Maybe String
      , isInsideImplicitlyCreatedFunction :: Bool
      , isGlobal :: Bool
      , internalVariables :: [(LHSPattern String,Maybe Expr)]
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
                                       , internalVariables = []
                                       }

addInternalVariables :: [(LHSPattern String,Maybe Expr)] -> TransformerState ()
addInternalVariables variables = modifyF (\s -> s { internalVariables = internalVariables s ++ variables })

getsF f = gets (f . functionContext)
modifyF f = modify (\s -> s { functionContext = f (functionContext s) })

genSym :: TransformerState String
genSym = do{ n <- gets genSymCounter
           ; modify (\s -> s {genSymCounter = n+1})
           ; return ('$':show n)
           }

newInternalVariable :: TransformerState String
newInternalVariable = do{ name <- genSym
                        ; addInternalVariables [(LHSSimple name,Nothing)]
                        ; return name
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
  , transformGenerator = True
  , transformArrayComprehension = True
  , transformLetExpression = True
  , transformLetStatement = True
  , transformLetDefinition = True
  , transformDestructuringAssignment = True
  , transformReservedNameAsIdentifier = True
  , transformExpressionClosure = True
  , transformGeneratorExpression = True
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

    mmap :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
    mmap f (Just x) = f x >>= return . Just
    mmap f Nothing = return Nothing

    myPatternExpr (LHSSimple a) = liftM LHSSimple $ myExpr a
    myPatternExpr (LHSArray elems) = liftM LHSArray $ mapM (mmap myPatternExpr) elems
    myPatternExpr (LHSObject elems) = liftM LHSObject $ mapM (\(name,pat) -> do{ pat' <- myPatternExpr pat ; return (name,pat') }) elems

    tAssign :: Operator -> LHSPatternExpr -> Expr -> TransformerState Expr
    tAssign "=" pat rhs
        | transformDestructuringAssignment options && not (isTrivialPattern pat)
        = if isEmptyPattern pat
          then myExpr rhs
          else do{ vars <- unpackPattern2 newInternalVariable pat rhs
                 ; vars' <- mapM (\(lhs,rhs) -> tAssign "=" (LHSSimple lhs) rhs) vars
                 ; return $ foldl1 (Binary ",") vars'
                 }
    tAssign op pat rhs = do{ rhs <- myExpr rhs
                           ; return $ Assign op pat rhs
                           }
    tVarDef kind variables
        = do{ variables <- mapM varDef1 variables
            ; return $ VarDef kind variables
            }
      where varDef1 (pat,Just rhs) = do{ rhs <- myExpr rhs
                                       ; return (pat,Just rhs)
                                       }
            varDef1 (pat,Nothing) = return (pat,Nothing)
    tForInHead (ForInLHSExpr e) = liftM ForInLHSExpr $ myPatternExpr e
    tForInHead (ForInVarDef kind pat e) = liftM (ForInVarDef kind pat) (mmap myExpr e)
    tForIn head o body
        = do{ head <- tForInHead head
            ; body <- myStat body
            ; o <- myExpr o
            ; return $ ForIn head o body
            }
    tForEach (ForInLHSExpr lhs) o body
        | transformForEach options
        = do{ objName <- genSym
            ; keyName <- genSym
            ; def <- tVarDef VariableDefinition [(LHSSimple objName,Just o)]
            ; a <- tAssign "=" lhs $ Index (Variable objName) (Variable keyName)
            ; return (BlockStatement
                      $ Block [def
                              ,ForIn (ForInVarDef VariableDefinition (LHSSimple keyName) Nothing)
                                     (Variable objName)
                                     (BlockStatement
                                      $ Block [ExpressionStatement a,body])])
            }
    tForEach (ForInVarDef kind valName init) o body
        | transformForEach options
        = do{ objName <- genSym
            ; keyName <- genSym
            ; def <- tVarDef VariableDefinition [(LHSSimple objName,Just o)]
            ; def2 <- tVarDef kind [(valName,init)]
            ; a <- tAssign "=" (patternNoExprToExpr valName) $ Index (Variable objName) (Variable keyName)
            ; return (BlockStatement
                      $ Block [def
                              ,def2
                              ,ForIn (ForInVarDef VariableDefinition (LHSSimple keyName) Nothing)
                                     (Variable objName)
                                     (BlockStatement
                                      $ Block [ExpressionStatement a,body])])
            }
    tForEach head o body
        = do{ head <- tForInHead head
            ; body <- myStat body
            ; o <- myExpr o
            ; return $ ForEach head o body
            }

    myExpr :: Expr -> TransformerState Expr
    myExpr v@(Variable "arguments")
        = do{ f <- getsF isInsideImplicitlyCreatedFunction
            ; if f
               then do{ w <- getsF aliasForArguments
                      ; name <- maybe (do{ name <- genSym
                                         ; modifyF (\s -> s {aliasForArguments = Just name})
                                         ; return name
                                         }) return w
                      ; return $ Variable name
                      }
               else return v
            }
    myExpr v@This
        = do{ f <- getsF isInsideImplicitlyCreatedFunction
            ; if f
               then do{ w <- getsF aliasForThis
                      ; name <- maybe (do{ name <- genSym
                                         ; modifyF (\s -> s {aliasForThis = Just name})
                                         ; return name
                                         }) return w
                      ; return $ Variable name
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
            ; splitIntoFunction [] []
            $ do{ let compFor ((kind,varName,objExpr):rest)
                          = do{ objExpr' <- myExpr objExpr
                              ; rest' <- compFor rest
                              ; (if kind == CompForIn then tForIn else tForEach)
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
                ; def <- tVarDef VariableDefinition
                         $ (LHSSimple arrayName,Just $ New (Variable "Array") [])
                               :(map (\(_,n,_) -> (n,Nothing)) f)
                ; return [def,f',Return (Just arrayVar)]
                }
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
        = letVariables (tAssign "=") vars e
            (\initializer e -> do{ e' <- myExpr e
                                 ; return $ Binary "," initializer e'
                                 })
            (\params args -> splitIntoFunction params args
                             $ do{ e' <- myExpr e
                                 ; return [Return $ Just e']
                                 })
    myExpr (Assign op pat rhs) = tAssign op pat rhs
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
                            Just (LHSSimple n,x) -> BlockStatement (substVariable n varName x)
                            Just (pat,x) -> undefined {-BlockStatement (substVariable n varName x)-}
                  cc ((LHSSimple n,e,x):xs) = If (substVariable n varName e)
                                                 (BlockStatement (substVariable n varName x))
                                                 (Just (cc xs))
                  cc ((n,e,x):xs) = undefined {-If (substVariable n varName e)
                                                 (BlockStatement (substVariable n varName x))
                                                 (Just (cc xs))-} -- FIXME
              in myStat (Try b [] (Just (LHSSimple varName,Block [cc c])) f)
            }
    myStat (ForEach head o body) = tForEach head o body
    myStat (LetStatement vars body)
        | transformLetStatement options
        = letVariables (tAssign "=") vars body
            (\initializer body -> do{ Block statements <- myBlock body
                                    ; let statements' = (ExpressionStatement initializer):statements
                                    ; return $ BlockStatement $ Block statements'
                                    })
            (\params args -> splitStatementsIntoFunction params args
                             $ do{ Block body' <- myBlock body
                                 ; return body'
                                 })
    myStat x = transformStat defaultTransformer x

    myBlock :: Block -> TransformerState Block
    myBlock x = transformBlock defaultTransformer x

    myFuncDecl :: String -> Function -> TransformerState Function
    myFuncDecl name x = transformFuncDecl defaultTransformer name x

    myFunction :: Function -> TransformerState Function
    myFunction fn = do{ outer <- getsF id
                      ; modifyF (const emptyFunctionContext)
                      ; fn' <- transformFunctionArguments fn >>= transformFunction defaultTransformer
                      ; aliasForThis' <- getsF aliasForThis
                      ; aliasForArguments' <- getsF aliasForArguments
                      ; internalVars' <- getsF internalVariables
                      ; modifyF (const outer)
                      ; let internalVars
                                = (maybe [] (\s -> [(LHSSimple s,Just This)]) aliasForThis')
                                  ++ (maybe [] (\s -> [(LHSSimple s,Just (Variable "arguments"))])
                                            aliasForArguments')
                                  ++ internalVars'
                      ; return
                          $ if null internalVars
                            then fn'
                            else makeFunction
                                     (functionName fn')
                                     (functionArguments fn')
                                     (let FunctionBody body = functionBody fn'
                                      in FunctionBody ((Statement $ VarDef VariableDefinition internalVars):body))
                      }

    transformFunctionArguments fn
        | transformDestructuringAssignment options
        = do{ let FunctionBody body = functionBody fn
                  args = functionArguments fn
            ; (args',vars') <- liftM unzip $ mapM transformFunctionArgument args
            ; let vars = concat vars'
                  body' = if null vars
                          then body
                          else (Statement $ VarDef VariableDefinition vars):body
            ; return $ makeFunction (functionName fn) args' $ FunctionBody body'
            }
      where
        transformFunctionArgument pat@(LHSSimple _)
            = return (pat,[])
        transformFunctionArgument pat
            = do{ name <- genSym
                ; vars <- unpackPattern genSym pat (Variable name)
                ; return (LHSSimple name,map (\(n,x) -> (LHSSimple n,Just x)) vars)
                }
    transformFunctionArguments fn
        | not $ transformDestructuringAssignment options
        = return fn

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

substVariable :: CodeFragment a => String -> String -> a -> a
substVariable from to code = evalState (applyTransformer myTransformer code) ()
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

substVariables :: CodeFragment a => [(String,String)] -> a -> a
substVariables subst code = evalState (applyTransformer myTransformer code) ()
  where
    substFrom = map fst subst
    myTransformer,defaultTransformer :: Transformer (State ())
    myTransformer = defaultTransformer { transformExpr = myExpr
                                       , transformStat = myStat
                                       }
    defaultTransformer = getDefaultTransformer myTransformer
    ident name = case find (\(from,_) -> name == from) subst of
                   Just (_,to) -> to
                   Nothing -> name
    pattern f (LHSSimple name) = LHSSimple name
    pattern f (LHSArray elems) = LHSArray $ map (fmap (pattern f)) elems
    pattern f (LHSObject elems) = LHSObject $ map (\(k,v) -> (k,pattern f v)) elems
    patternNoExpr = pattern ident
    patternExpr = pattern myExpr
    myExpr (Variable name) = return (Variable $ ident name)
    myExpr v = transformExpr defaultTransformer v
    myStat (VarDef kind vars) = do{ vars' <- mapM varDecl vars
                                  ; return $ VarDef kind vars'
                                  }
      where varDecl (name,Just e) = do{ e' <- myExpr e
                                      ; return (patternNoExpr name,Just e')
                                      }
            varDecl (name,Nothing) = return (patternNoExpr name,Nothing)
    myStat s = transformStat defaultTransformer s

substVariablesInPattern :: [(String,String)] -> LHSPatternNoExpr -> LHSPatternNoExpr
substVariablesInPattern subst pat = pattern pat
  where
    ident name = case find (\(from,_) -> name == from) subst of
                   Just (_,to) -> to
                   Nothing -> name
    pattern (LHSSimple name) = LHSSimple name
    pattern (LHSArray elems) = LHSArray $ map (fmap pattern) elems
    pattern (LHSObject elems) = LHSObject $ map (\(k,v) -> (k,pattern v)) elems

unpackPattern :: (Monad m,PatternFromIdentifier a) => m String -> LHSPattern a -> Expr -> m [(a,Expr)]
unpackPattern _ (LHSSimple lhs) e = return [(lhs,e)]
unpackPattern newVar (LHSArray elems) e = liftM concat $ sequence $ zipWith elem elems [0..]
  where elem Nothing _ = return []
        elem (Just pat) i
            | isEmptyPattern pat = return []
            | isSingleElementPattern pat = unpackPattern newVar pat (referIndex e i)
            | otherwise = do{ tmpName <- newVar
                            ; inner <- unpackPattern newVar pat (Variable tmpName)
                            ; return $ (patternFromIdentifier tmpName,referIndex e i):inner
                            }
        referIndex e i = Index e $ Literal $ NumericLiteral $ show i
unpackPattern newVar (LHSObject elems) e = liftM concat $ sequence $ map elem elems
  where elem (propName,pat)
            | isEmptyPattern pat = return []
            | isSingleElementPattern pat = unpackPattern newVar pat (referProp e propName)
            | otherwise = do{ tmpName <- newVar
                            ; inner <- unpackPattern newVar pat (Variable tmpName)
                            ; return $ (patternFromIdentifier tmpName,referProp e propName):inner
                            }
        referProp e (PNIdentifier name) | name `notElem` reservedNames = Field e name
                                        | otherwise = Index e $ Literal $ StringLiteral $ show name
        referProp e (PNLiteral lit) = Index e $ Literal lit

unpackPattern2 newVar pat e
    | isSingleElementPattern pat = unpackPattern newVar pat e
    | otherwise = do{ name <- newVar
                    ; vars <- unpackPattern newVar pat (Variable name)
                    ; return $ (Variable name,e):vars
                    }

splitIntoFunction :: [LHSPatternNoExpr] -> [Expr] -> TransformerState [Statement] -> TransformerState Expr
splitIntoFunction params args getStatements
    = do{ prevIsInsideImplicitlyCreatedFunction <- getsF isInsideImplicitlyCreatedFunction
        ; modifyF (\s -> s {isInsideImplicitlyCreatedFunction = True})
        ; statements <- getStatements
        ; modifyF (\s -> s {isInsideImplicitlyCreatedFunction
                                = prevIsInsideImplicitlyCreatedFunction})
        ; let body = FunctionBody $ map Statement statements
              fn = makeFunction Nothing params body
        ; fn' <- transformFunctionArguments fn
        ; return $ FuncCall (FunctionExpression False fn') args
        }

data JumpKind = JKReturn
              | JSValuedReturn
              | JKBreak
              | JKContinue
              | JSLabelledBreak String
              | JSLabelledContinue String
                deriving (Eq,Show)
data SplitStatementsData = SplitStatementsData{ ssSeenLabels :: [String]
                                              , ssIsInsideLoop :: Bool
                                              , ssIsInsideSwitch :: Bool
                                              , ssIds :: [(Statement,Int)]
                                              , ssNextId :: Int
                                              , ssModeVar :: String
                                              , ssValueVar :: String
                                              }
                         deriving (Eq,Show)
ssIsInsideLoopOrSwitch ssdata = ssIsInsideLoop ssdata || ssIsInsideSwitch ssdata
splitStatementsIntoFunction :: [LHSPatternNoExpr] -> [Expr] -> TransformerState [Statement] -> TransformerState Statement
splitStatementsIntoFunction params args getStatements
    = do{ prevIsInsideImplicitlyCreatedFunction <- getsF isInsideImplicitlyCreatedFunction
        ; modifyF (\s -> s {isInsideImplicitlyCreatedFunction = True})
        ; statements <- getStatements
        ; modifyF (\s -> s {isInsideImplicitlyCreatedFunction
                                = prevIsInsideImplicitlyCreatedFunction})
        ; let scanJumpResult = scanJumps statements
              hasAnyJump = scanJumpResult /= (ScanJumpResult False False False False [])
              hasValuedReturn = sjHasValuedReturn scanJumpResult
              hasMultiplePath = let boolToInt True = 1
                                    boolToInt False = 0
                                in True
        ; let makeFuncCall statements
                  = do{ let fn = makeFunction Nothing params
                                                         $ FunctionBody $ map Statement statements
                      ; fn' <- transformFunctionArguments fn
                      ; return $ FuncCall (FunctionExpression False fn') args
                      }
        ; if not hasAnyJump
          then liftM ExpressionStatement $ makeFuncCall statements
          else
            do{ modeVar <- if hasMultiplePath then genSym else genSym
              ; valueVar <- if hasValuedReturn then genSym else genSym --return (error "valueVar referred")
              ; addInternalVariables [(LHSSimple modeVar,Nothing),(LHSSimple valueVar,Nothing)]
              ; let (statements',state) = transformStatements statements modeVar valueVar
              ; let --jumpOuter [] = Throw $ Literal $ StringLiteral "\"YOU SHOULDN'T REACH HERE\""--EmptyStat
                    jumpOuter [(jump,_)] = jump
                    jumpOuter ((jump,id):xs) = If (Binary "===" (Variable modeVar) (Literal $ integerToNumericLiteral id))
                                               jump (Just $ jumpOuter xs)
              ; call <- makeFuncCall $ statements'++[Return $ Just $ Literal $ BooleanLiteral False]
              ; return $ If call (jumpOuter $ ssIds state) Nothing
              }
        }
  where
    transformStatements code modeVar valueVar = runState (applyTransformer myTransformer code) (SplitStatementsData [] False False [] 0 modeVar valueVar)
    myTransformer,defaultTransformer :: Transformer (State SplitStatementsData)
    myTransformer = defaultTransformer { transformExpr = return
                                       , transformStat = myStat
                                       , transformFunction = return
                                       }
    defaultTransformer = getDefaultTransformer myTransformer
    loop body = do{ isInsideLoop <- gets ssIsInsideLoop
                  ; modify (\s -> s { ssIsInsideLoop = True })
                  ; body' <- myStat body
                  ; modify (\s -> s { ssIsInsideLoop = isInsideLoop })
                  ; return body'
                  }
    getJumpId jump = do{ ids <- gets ssIds
                       ; case find ((== jump) . fst) ids of
                           Just (_,id) -> return id
                           Nothing -> do{ id <- gets ssNextId
                                        ; modify (\s -> s { ssNextId = id+1
                                                          , ssIds = (jump,id):ids
                                                          })
                                        ; return id
                                        }
                       }
    transformJump jump = do{ modeVar <- gets ssModeVar
                           ; id <- getJumpId jump
                           ; return $ BlockStatement $ Block [ExpressionStatement $ Assign "=" (LHSSimple $ Variable modeVar) $ Literal $ integerToNumericLiteral id
                                                             ,Return $ Just $ Literal $ BooleanLiteral True
                                                             ]
                           }
    myStat (While a body) = liftM (While a) $ loop body
    myStat (DoWhile a body) = liftM (DoWhile a) $ loop body
    myStat (For a b c body) = liftM (For a b c) $ loop body
    myStat (ForIn a b body) = liftM (ForIn a b) $ loop body
    myStat (ForEach a b body) = liftM (ForEach a b) $ loop body
    myStat stat@(Switch _ _) = do{ isInsideSwitch <- gets ssIsInsideSwitch
                                 ; modify (\s -> s { ssIsInsideSwitch = True })
                                 ; stat' <- transformStat defaultTransformer stat
                                 ; modify (\s -> s { ssIsInsideSwitch = isInsideSwitch })
                                 ; return stat'
                                 }
    myStat stat@(Break Nothing) = do{ isInsideLoopOrSwitch <- gets ssIsInsideLoopOrSwitch
                                    ; if isInsideLoopOrSwitch
                                      then return stat
                                      else transformJump stat
                                    }
    myStat stat@(Break (Just label)) = do{ seenLabels <- gets ssSeenLabels
                                         ; if label `elem` seenLabels
                                           then return stat
                                           else transformJump stat
                                         }
    myStat stat@(Continue Nothing) = do{ isInsideLoop <- gets ssIsInsideLoop
                                       ; if isInsideLoop
                                         then return stat
                                         else transformJump stat
                                       }
    myStat stat@(Continue (Just label)) = do{ seenLabels <- gets ssSeenLabels
                                            ; if label `elem` seenLabels
                                              then return stat
                                              else transformJump stat
                                            }
    myStat stat@(Return Nothing) = transformJump stat
    myStat (Return (Just value)) = do{ modeVar <- gets ssModeVar
                                     ; valueVar <- gets ssValueVar
                                     ; id <- getJumpId (Return $ Just $ Variable valueVar)
                                     ; return $ BlockStatement $ Block [ExpressionStatement $ Assign "=" (LHSSimple $ Variable valueVar) $ value
                                                      ,ExpressionStatement $ Assign "=" (LHSSimple $ Variable modeVar) $ Literal $ integerToNumericLiteral id
                                                      ,Return $ Just $ Literal $ BooleanLiteral True
                                                      ]
                                     }
    myStat (Labelled label stat) = do{ labels <- gets ssSeenLabels
                                     ; modify (\s -> s { ssSeenLabels = label:labels })
                                     ; stat' <- transformStat defaultTransformer stat
                                     ; modify (\s -> s { ssSeenLabels = labels })
                                     ; return (Labelled label stat')
                                     }
    myStat s = transformStat defaultTransformer s

letVariables :: CodeFragment a => (LHSPatternExpr -> Expr -> TransformerState Expr) -> [(LHSPatternNoExpr,Maybe Expr)] -> a -> (Expr -> a -> TransformerState b) -> ([LHSPatternNoExpr] -> [Expr] -> TransformerState b) -> TransformerState b
letVariables tAssign vars x transComma transFunction
    = do{ let usedVariables = variablesUsedInInternalFunctions x
        ; let definedVariables = concatMap (patternComponents . fst) vars
        ; if null $ intersect usedVariables definedVariables
          then
            do{ let tVar (LHSSimple name,Nothing)
                        = do{ name2 <- newInternalVariable
                            ; return ([(name,name2)],Nothing,Just name2)
                            }
                    tVar (LHSSimple name,Just init)
                        = do{ name2 <- newInternalVariable
                            ; return ([(name,name2)],Just (LHSSimple $ Variable name2,init),Nothing)
                            }
                    tVar (pat,Just init)
                        = do{ let names = patternComponents pat
                            ; names2 <- mapM (const newInternalVariable) names
                            ; let namesSubst = zip names names2
                            ; let pat' = substVariablesInPattern namesSubst pat
                            ; return (namesSubst,Just (patternNoExprToExpr pat',init),Nothing)
                            }
              ; (subst',init',uninitialized') <- liftM unzip3 $ mapM tVar vars
              ; let subst = concat subst'
                    init = catMaybes init'
                    uninitialized = catMaybes uninitialized'
              ; initializers <- mapM (uncurry tAssign) init
              ; initializers
                  <- if null uninitialized
                     then return initializers
                     else liftM (:initializers) (foldr (\v -> (tAssign (LHSSimple $ Variable v) =<<)) (return undefinedExpr) uninitialized)
              ; transComma (foldl1 (Binary ",") initializers) $ substVariables subst x
              }
          else
            let (init,uninit) = partition (isJust . snd) vars
            in transFunction (map fst $ init++uninit) (map (fromJust . snd) init)
        }
  where undefinedExpr = Prefix "void" $ Literal $ NumericLiteral "0"
