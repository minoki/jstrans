{-# OPTIONS_GHC -XRelaxedPolyRec -XPolymorphicComponents #-}
module JSTrans.AST where
import Prelude
import Text.ParserCombinators.Parsec.Expr (Assoc)
import Monad
import Control.Monad.State
import Control.Monad.Identity
import List
import Maybe (maybeToList,catMaybes,isNothing)

type Operator = String
operatorForName :: String -> Operator
operatorForName = id

data Literal = NullLiteral
             | NumericLiteral String
             | RegExpLiteral String
             | BooleanLiteral Bool
             | StringLiteral String
               deriving (Eq,Show)
data LHSPattern a = LHSSimple a
                  | LHSArray [Maybe (LHSPattern a)]
                  | LHSObject [(PropertyName,LHSPattern a)]
                    deriving (Eq,Show)
type LHSPatternExpr = LHSPattern Expr
type LHSPatternNoExpr = LHSPattern String
data PropertyName = PNIdentifier String
                  | PNLiteral Literal
                    deriving (Eq,Show)
data AccessorKind = Getter | Setter deriving (Eq,Show)
data ComprehensionKind = CompForIn | CompForEach deriving (Eq,Show)
data Expr = Binary Operator Expr Expr
          | Prefix Operator Expr
          | Postfix Operator Expr
          | Cond Expr Expr Expr
          | Field Expr String
          | Index Expr Expr
          | FuncCall Expr [Expr]
          | ArrayLiteral [Maybe Expr]
          | ArrayComprehension Expr
              [(ComprehensionKind,LHSPatternNoExpr,Expr) {- for / for each -}]
              (Maybe Expr {- if -})
          | ObjectLiteral [(PropertyName,Either Expr (AccessorKind,Function))]
          | Let [(LHSPatternNoExpr,Maybe Expr)] Expr
          | FunctionExpression Bool{-isExpressionClosure-} Function
          | Variable String
          | Literal Literal
          | This
          | New Expr [Expr]
          | Assign Operator LHSPatternExpr Expr
            deriving (Eq,Show)
data DefinitionKind = VariableDefinition
                    | ConstantDefinition
                    | LetDefinition
                      deriving (Eq,Show)
newtype Block = Block [Statement] deriving (Eq,Show)
data ForInHead = ForInLHSExpr LHSPatternExpr
               | ForInVarDef DefinitionKind LHSPatternNoExpr (Maybe Expr)
                 deriving (Eq,Show)
data Statement = EmptyStat
               | VarDef DefinitionKind [(LHSPatternNoExpr,Maybe Expr)]
               | LetStatement [(LHSPatternNoExpr,Maybe Expr)] Block
               | ExpressionStatement Expr
               | Return (Maybe Expr)
               | Throw Expr
               | MultiStatements [Statement]
               | BlockStatement Block
               | If Expr Statement (Maybe Statement)
               | While Expr Statement
               | DoWhile Expr Statement
               | For (Maybe Statement) (Maybe Expr) (Maybe Expr) Statement
               | ForIn ForInHead Expr Statement
               | ForEach ForInHead Expr Statement
               | Try Block [(LHSPatternNoExpr,Expr,Block)] (Maybe (LHSPatternNoExpr,Block)) (Maybe Block)
               | Switch Expr [SwitchClause]
               | Break (Maybe String)
               | Continue (Maybe String)
               | Labelled String Statement
               | Debugger
                 deriving (Eq,Show)
data SwitchClause = CaseClause Expr [Statement]
                  | DefaultClause [Statement]
                    deriving (Eq,Show)
data SourceElement = Statement Statement
                   | FunctionDeclaration String Function
                     deriving (Eq,Show)
newtype FunctionBody = FunctionBody [SourceElement] deriving (Eq,Show)
newtype Program = Program [SourceElement] deriving (Eq,Show)

data Function
    = Function { functionName :: Maybe String
               , functionArguments :: [LHSPatternNoExpr]
               , functionBody :: FunctionBody
               , functionVariables :: [String] -- variables and functions explicitly declared inside the function
               , outerVariables :: [String] -- variables used in this function and not declared inside
--               , innerFunctions :: [Function]
               } deriving (Eq,Show)
makeFunction :: Maybe String -> [LHSPatternNoExpr] -> FunctionBody -> Function

data Monad m => Transformer m
    = Transformer { transformExpr :: Expr -> m Expr
                  , transformStat :: Statement -> m Statement
                  , transformBlock :: Block -> m Block
                  , transformFuncDecl :: String -> Function -> m Function
                  , transformFunction :: Function -> m Function
                  , transformProgram :: Program -> m Program
                  , transformerVarDeclHook :: forall a. [LHSPatternNoExpr] -> m a -> m a
                  }
transformSourceElem :: Monad m => Transformer m -> SourceElement -> m SourceElement
transformFunctionBody :: Monad m => Transformer m -> FunctionBody -> m FunctionBody

data Monad m => Visitor m
    = Visitor { visitExpr :: Expr -> m ()
              , visitStat :: Statement -> m ()
              , visitBlock :: Block -> m ()
              , visitFuncDecl :: String -> Function -> m ()
              , visitFunction :: Function -> m ()
              , visitProgram :: Program -> m ()
              , visitorVarDeclHook :: [LHSPatternNoExpr] -> m () -> m ()
              }
visitSourceElem :: Monad m => Visitor m -> SourceElement -> m ()
visitFunctionBody :: Monad m => Visitor m -> FunctionBody -> m ()

class CodeFragment a where
  applyTransformer :: Monad m => Transformer m -> a -> m a
  applyVisitor :: Monad m => Visitor m -> a -> m ()

instance CodeFragment Expr where
  applyTransformer = transformExpr
  applyVisitor = visitExpr

instance CodeFragment Statement where
  applyTransformer = transformStat
  applyVisitor = visitStat

instance CodeFragment Block where
  applyTransformer = transformBlock
  applyVisitor = visitBlock

instance CodeFragment FunctionBody where
  applyTransformer = transformFunctionBody
  applyVisitor = visitFunctionBody

instance CodeFragment SourceElement where
  applyTransformer = transformSourceElem
  applyVisitor = visitSourceElem

instance CodeFragment Function where
  applyTransformer = transformFunction
  applyVisitor = visitFunction

instance CodeFragment Program where
  applyTransformer = transformProgram
  applyVisitor = visitProgram

instance CodeFragment a => CodeFragment [a] where
  applyTransformer transformer = mapM (applyTransformer transformer)
  applyVisitor visitor = mapM_ (applyVisitor visitor)

-- workaround (should use -XFlexibleInstances?)
class StringToList a where
  stringToList :: String -> [a]

instance StringToList Char where
  stringToList = id

class PatternFromIdentifier a where
  patternFromIdentifier :: String -> a

instance StringToList a => PatternFromIdentifier [a] where -- String
  patternFromIdentifier = stringToList

instance PatternFromIdentifier Expr where
  patternFromIdentifier = Variable

class FromLiteral a where
  fromLiteral :: Literal -> a

instance FromLiteral Literal where
  fromLiteral = id

instance FromLiteral PropertyName where
  fromLiteral = PNLiteral

instance FromLiteral Expr where
  fromLiteral = Literal

class StatementLike a where
  toStatement :: a -> Statement
  toStatements :: a -> [Statement]
  toStatements x = [toStatement x]

instance StatementLike Statement where
  toStatement = id
  toStatements EmptyStat = []
  toStatements (MultiStatements ss) = ss
  toStatements x = [x]

instance StatementLike Expr where
  toStatement = ExpressionStatement

catStats :: (StatementLike a,StatementLike b) => a -> b -> Statement
catStats x y = case toStatements x ++ toStatements y of
                 [] -> EmptyStat
                 [s] -> s
                 ss -> MultiStatements ss

blockStatement = BlockStatement . Block

makeFunction name args body = fn
  where
    fn :: Function
    fn = Function { functionName = name
                  , functionArguments = args
                  , functionBody = body
                  , functionVariables = scanVarDecl fn
                  , outerVariables = scanUsedVar fn
                  }

transformSourceElem v (Statement st) = liftM Statement $ transformStat v st
transformSourceElem v (FunctionDeclaration name fn)
    = liftM (FunctionDeclaration name) $ transformFuncDecl v name fn
transformFunctionBody v (FunctionBody b)
    = liftM FunctionBody $ mapM (transformSourceElem v) b

getDefaultTransformer :: Monad m => Transformer m -> Transformer m
getDefaultTransformer v
    = Transformer { transformExpr = myExpr
                  , transformStat = myStat
                  , transformBlock = myBlock
                  , transformFuncDecl = myFuncDecl
                  , transformFunction = myFunction
                  , transformProgram = myProgram
                  , transformerVarDeclHook = const id
                  }
  where
    expr = transformExpr v
    stat = transformStat v
    block = transformBlock v
    sourceElem = transformSourceElem v
    function = transformFunction v
    withVariableDeclared = transformerVarDeclHook v

    varDecl (name,e) = do{ v <- mmap expr e
                         ; return (name,v)
                         }
    mmap :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
    mmap f (Just x) = f x >>= return . Just
    mmap f Nothing = return Nothing

    patternExpr (LHSSimple a) = liftM LHSSimple $ expr a
    patternExpr (LHSArray elems) = liftM LHSArray $ mapM (mmap patternExpr) elems
    patternExpr (LHSObject elems) = liftM LHSObject $ mapM (\(name,pat) -> do{ pat' <- patternExpr pat ; return (name,pat') }) elems

    forInHead (ForInLHSExpr e) = liftM ForInLHSExpr $ patternExpr e
    forInHead (ForInVarDef kind pat e) = liftM (ForInVarDef kind pat) (mmap expr e)

    myExpr (Binary op x y) = liftM2 (Binary op) (expr x) (expr y)
    myExpr (Prefix op x) = liftM (Prefix op) (expr x)
    myExpr (Postfix op x) = liftM (Postfix op) (expr x)
    myExpr (Cond x y z) = liftM3 Cond (expr x) (expr y) (expr z)
    myExpr (Field x name) = liftM (flip Field name) (expr x)
    myExpr (Index x y) = liftM2 Index (expr x) (expr y)
    myExpr (FuncCall fn args) = liftM2 FuncCall (expr fn) (mapM expr args)
    myExpr (ArrayLiteral elems) = liftM ArrayLiteral (mapM (mmap expr) elems)
    myExpr (ArrayComprehension x f i)
        = withVariableDeclared (map (\(_,n,_) -> n) f)
          $ do{ x' <- expr x
              ; f' <- mapM (\(k,n,o) -> do{ o' <- expr o ; return (k,n,o') }) f
              ; i' <- mmap expr i
              ; return $ ArrayComprehension x' f' i'
              }
    myExpr (ObjectLiteral elems) = liftM ObjectLiteral (mapM elem elems)
      where 
        elem (pname,Left value) = do{ value' <- expr value
                                    ; return (pname,Left value')
                                    }
        elem (pname,Right (kind,fn)) = do{ fn' <- function fn
                                         ; return (pname,Right (kind,fn'))
                                         }
    myExpr (Let l e) = liftM2 Let (mapM varDecl l) $ withVariableDeclared (map fst l) (expr e)
    myExpr (FunctionExpression isEC fn)
        = liftM (FunctionExpression isEC) (function fn)
    myExpr t@(Variable _) = return t
    myExpr t@(Literal _) = return t
    myExpr t@This = return t
    myExpr (New ctor args) = liftM2 New (expr ctor) (mapM expr args)
    myExpr (Assign op x y) = liftM2 (Assign op) (patternExpr x) (expr y)

    myStat t@EmptyStat = return t
    myStat (VarDef kind l) = liftM (VarDef kind) (mapM varDecl l)
    myStat (LetStatement l b) = liftM2 LetStatement (mapM varDecl l) $ withVariableDeclared (map fst l) (block b)
    myStat (ExpressionStatement e) = liftM ExpressionStatement (expr e)
    myStat (Return x) = liftM Return (mmap expr x)
    myStat (Throw x) = liftM Throw (expr x)
    myStat (MultiStatements ss) = liftM MultiStatements (mapM stat ss)
    myStat (BlockStatement b) = liftM BlockStatement (block b)
    myStat (If c t e) = liftM3 If (expr c) (stat t) (mmap stat e)
    myStat (While c b) = liftM2 While (expr c) (stat b)
    myStat (DoWhile c b) = liftM2 DoWhile (expr c) (stat b)
    myStat (For a@(Just (VarDef LetDefinition vars)) b c d) = withVariableDeclared (map fst vars) $ liftM4 For (mmap stat a) (mmap expr b) (mmap expr c) (stat d)
    myStat (For a b c d) = liftM4 For (mmap stat a) (mmap expr b) (mmap expr c) (stat d)
    myStat (ForIn a@(ForInVarDef LetDefinition var _) b c) = withVariableDeclared [var] $ liftM3 ForIn (forInHead a) (expr b) (stat c)
    myStat (ForIn a b c) = liftM3 ForIn (forInHead a) (expr b) (stat c)
    myStat (ForEach a@(ForInVarDef LetDefinition var _) b c) = withVariableDeclared [var] $ liftM3 ForEach (forInHead a) (expr b) (stat c)
    myStat (ForEach a b c) = liftM3 ForEach (forInHead a) (expr b) (stat c)
    myStat (Try b cc uc f) = liftM4 Try (block b) (mapM tcc cc) (mmap tuc uc) (mmap block f)
      where tcc (a,b,c) = withVariableDeclared [a] $ liftM2 ((,,) a) (expr b) (block c)
            tuc (a,b) = withVariableDeclared [a] $ liftM ((,) a) (block b)
    myStat (Switch e c) = liftM2 Switch (expr e) (mapM cc c)
      where cc (CaseClause e s) = liftM2 CaseClause (expr e) (mapM stat s)
            cc (DefaultClause s) = liftM DefaultClause (mapM stat s)
    myStat t@(Break _) = return t
    myStat t@(Continue _) = return t
    myStat (Labelled label s) = liftM (Labelled label) (stat s)
    myStat t@Debugger = return t

    myBlock (Block s) = liftM Block $ withVariableDeclared vars $ mapM stat s
      where vars = scanLetDecl s
    myFuncDecl name f = function f
    myFunction f = liftM (makeFunction (functionName f) (functionArguments f))
                            (withVariableDeclared vars
                                                      $ transformFunctionBody v (functionBody f))
      where vars = functionArguments f
                   `union` (map LHSSimple $ functionVariables f)
                   `union` [LHSSimple "arguments"]
                   `union` maybe [] (\n -> [LHSSimple n]) (functionName f)
    myProgram (Program p) = liftM Program $ withVariableDeclared vars $ mapM sourceElem p
      where vars = map (\n -> LHSSimple n) $ scanVarDecl p


visitSourceElem v (Statement st) = visitStat v st
visitSourceElem v (FunctionDeclaration name fn)
    = visitFuncDecl v name fn
visitFunctionBody v (FunctionBody b)
    = mapM_ (visitSourceElem v) b

getDefaultVisitor :: Monad m => Visitor m -> Visitor m
getDefaultVisitor v
    = Visitor { visitExpr = myExpr
              , visitStat = myStat
              , visitBlock = myBlock
              , visitFuncDecl = myFuncDecl
              , visitFunction = myFunction
              , visitProgram = myProgram
              , visitorVarDeclHook = const id
              }
  where
    expr = visitExpr v
    stat = visitStat v
    block = visitBlock v
    sourceElem = visitSourceElem v
    function = visitFunction v
    withVariableDeclared = visitorVarDeclHook v

    mmap :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
    mmap f (Just x) = f x >>= return . Just
    mmap f Nothing = return Nothing
    mmap_ :: Monad m => (a -> m ()) -> Maybe a -> m ()
    mmap_ f (Just x) = f x
    mmap_ f Nothing = return ()
    varDecl (name,e) = do{ v <- mmap expr e
                         ; return (name,v)
                         }

    patternExpr (LHSSimple a) = expr a
    patternExpr (LHSArray elems) = mapM_ (mmap_ patternExpr) elems
    patternExpr (LHSObject elems) = mapM_ (patternExpr . snd) elems

    forInHead (ForInLHSExpr e) = patternExpr e
    forInHead (ForInVarDef kind pat e) = mmap_ expr e

    myExpr (Binary _ x y) = expr x >> expr y
    myExpr (Prefix _ x) = expr x
    myExpr (Postfix _ x) = expr x
    myExpr (Cond x y z) = expr x >> expr y >> expr z
    myExpr (Field x _) = expr x
    myExpr (Index x y) = expr x >> expr y
    myExpr (FuncCall fn args) = expr fn >> mapM_ expr args
    myExpr (ArrayLiteral elems) = mapM_ (mmap expr) elems
    myExpr (ArrayComprehension x f i)
        = withVariableDeclared (map (\(_,n,_) -> n) f)
          $ expr x >> mapM_ (\(_,_,o) -> expr o) f >> mmap_ expr i
    myExpr (ObjectLiteral elems) = mapM_ elem elems
      where 
        elem (_,Left value) = expr value
        elem (_,Right (_,fn)) = function fn
    myExpr (Let l e) = mapM_ varDecl l >> withVariableDeclared (map fst l) (expr e)
    myExpr (FunctionExpression isEC fn) = function fn
    myExpr t@(Variable _) = return ()
    myExpr t@(Literal _) = return ()
    myExpr t@This = return ()
    myExpr (New ctor args) = expr ctor >> mapM_ expr args
    myExpr (Assign _ x y) = patternExpr x >> expr y

    myStat t@EmptyStat = return ()
    myStat (VarDef _ l) = mapM_ varDecl l
    myStat (LetStatement l b) = mapM_ varDecl l >> withVariableDeclared (map fst l) (block b)
    myStat (ExpressionStatement e) = expr e
    myStat (Return x) = mmap_ expr x
    myStat (Throw x) = expr x
    myStat (MultiStatements ss) = mapM_ stat ss
    myStat (BlockStatement b) = block b
    myStat (If c t e) = expr c >> stat t >> mmap_ stat e
    myStat (While c b) = expr c >> stat b
    myStat (DoWhile c b) = expr c >> stat b
    myStat (For a@(Just (VarDef LetDefinition vars)) b c d) = withVariableDeclared (map fst vars) $ mmap_ stat a >> mmap_ expr b >> mmap_ expr c >> stat d
    myStat (For a b c d) = mmap_ stat a >> mmap_ expr b >> mmap_ expr c >> stat d
    myStat (ForIn a@(ForInVarDef LetDefinition var _) b c) = withVariableDeclared [var] $ forInHead a >> expr b >> stat c
    myStat (ForIn a b c) = forInHead a >> expr b >> stat c
    myStat (ForEach a@(ForInVarDef LetDefinition var _) b c) = withVariableDeclared [var] $ forInHead a >> expr b >> stat c
    myStat (ForEach a b c) = forInHead a >> expr b >> stat c
    myStat (Try b cc uc f) = block b >> mapM_ tcc cc >> mmap_ tuc uc >> mmap_ block f
      where tcc (a,b,c) = withVariableDeclared [a] $ expr b >> block c
            tuc (a,b) = withVariableDeclared [a] $ block b
    myStat (Switch e c) = expr e >> mapM_ cc c
      where cc (CaseClause e s) = expr e >> mapM_ stat s
            cc (DefaultClause s) = mapM_ stat s
    myStat t@(Break _) = return ()
    myStat t@(Continue _) = return ()
    myStat (Labelled label s) = stat s
    myStat t@Debugger = return ()

    myBlock (Block s) = withVariableDeclared vars $ mapM_ stat s
      where vars = scanLetDecl s
    myFuncDecl name f = function f
    myFunction f = withVariableDeclared vars $ visitFunctionBody v (functionBody f)
      where vars = functionArguments f
                   `union` (map LHSSimple $ functionVariables f)
                   `union` [LHSSimple "arguments"]
                   `union` maybe [] (\n -> [LHSSimple n]) (functionName f)
    myProgram (Program p) = withVariableDeclared vars $ mapM_ sourceElem p
      where vars = map (\n -> LHSSimple n) $ scanVarDecl p


-- Scans declared variables in a code fragment, a function or a program
scanVarDecl :: CodeFragment a => a -> [String]
scanVarDecl x = flip execState ([]::[String]) $ applyVisitor myVisitor x
  where
    myVisitor,defaultVisitor :: Visitor (State [String])
    myVisitor = defaultVisitor { visitExpr = const $ return ()
                               , visitStat = myStat
                               , visitFuncDecl = myFunc
                               }
    defaultVisitor = getDefaultVisitor myVisitor
    myStat (VarDef _ vars) = modify (`union` concatMap (patternComponents . fst) vars)
    myStat s@(ForIn (ForInVarDef kind var _) b c) = modify (`union` patternComponents var) >> visitStat defaultVisitor s
    myStat s@(ForEach (ForInVarDef kind var _) b c) = modify (`union` patternComponents var) >> visitStat defaultVisitor s
    myStat s = visitStat defaultVisitor s
    myFunc name fn = modify (`union` [name])

scanLetDecl :: CodeFragment a => a -> [LHSPatternNoExpr]
scanLetDecl x = flip execState ([]::[LHSPatternNoExpr]) $ applyVisitor myVisitor x
  where
    myVisitor,defaultVisitor :: Visitor (State [LHSPatternNoExpr])
    myVisitor = defaultVisitor { visitExpr = const $ return ()
                               , visitStat = myStat
                               , visitBlock = const $ return ()
                               , visitFuncDecl = const $ const $ return ()
                               , visitFunction = const $ return ()
                               }
    defaultVisitor = getDefaultVisitor myVisitor
    myStat (VarDef LetDefinition vars) = modify (`union` map fst vars)
    myStat s = visitStat defaultVisitor s

-- Scans declared functions in a function or a program
scanFuncDecl :: CodeFragment a => a -> [(String,Function)]
scanFuncDecl x = flip execState [] $ applyVisitor myVisitor x
  where
    myVisitor,defaultVisitor :: Visitor (State [(String,Function)])
    myVisitor = defaultVisitor { visitExpr = const $ return ()
                               , visitStat = const $ return ()
                               , visitBlock = const $ return ()
                               , visitFuncDecl = myFuncDecl
                               }
    defaultVisitor = getDefaultVisitor myVisitor
    myFuncDecl name fn = modify ((name,fn):)

-- Scans variables that are referenced but not declared inside
scanUsedVar :: CodeFragment a => a -> [String]
scanUsedVar x = fst $ flip execState ([],[]) $ applyVisitor myVisitor x
  where
    myVisitor,defaultVisitor :: Visitor (State ([String]{-usedVariables-},[String]{-declaredVariables-}))
    myVisitor = defaultVisitor { visitExpr = myExpr
                               , visitorVarDeclHook = withVariableDeclared
                               }
    defaultVisitor = getDefaultVisitor myVisitor
    withVariableDeclared vars f
        = do{ let vars' = concatMap patternComponents vars
            ; (usedVariables,declaredVariables) <- get
            ; let declaredVariables' = declaredVariables `union` vars'
            ; put (usedVariables,declaredVariables')
            ; f
            ; (usedVariables',_) <- get
            ; put (usedVariables',declaredVariables)
            }
    myExpr (Variable name)
        = do{ (usedVariables,declaredVariables) <- get
            ; when (name `notElem` declaredVariables)
                (put (usedVariables `union` [name],declaredVariables))
            }
    myExpr v = visitExpr defaultVisitor v

-- Scans variables used in internal functions
variablesUsedInInternalFunctions :: CodeFragment a => a -> [String]
variablesUsedInInternalFunctions x = flip execState [] $ applyVisitor myVisitor x
  where
    myVisitor,defaultVisitor :: Visitor (State [String]{-usedVariables-})
    myVisitor = defaultVisitor { visitFunction = myFunction
                               }
    defaultVisitor = getDefaultVisitor myVisitor
    myFunction fn = modify (\s -> s ++ outerVariables fn)


data ScanJumpResult = ScanJumpResult{ sjHasReturn :: Bool
                                    , sjHasValuedReturn :: Bool
                                    , sjHasUnlabelledBreak :: Bool
                                    , sjHasUnlabelledContinue :: Bool
                                    , sjExternalLabels :: [String]
                                    }
                      deriving (Eq,Show)
data ScanJumpData = ScanJumpData{ sjResult :: ScanJumpResult
                                , sjSeenLabels :: [String]
                                , sjIsInsideLoop :: Bool
                                , sjIsInsideSwitch :: Bool
                                }
                    deriving (Eq,Show)
sjIsInsideLoopOrSwitch sjdata = sjIsInsideLoop sjdata || sjIsInsideSwitch sjdata
scanJumps :: CodeFragment a => a -> ScanJumpResult
scanJumps code = sjResult $ flip execState (ScanJumpData (ScanJumpResult False False False False []) [] False False) $ applyVisitor myVisitor code
  where
    myVisitor,defaultVisitor :: Visitor (State ScanJumpData)
    myVisitor = defaultVisitor { visitExpr = const $ return ()
                               , visitStat = myStat
                               , visitFunction = const $ return ()
                               }
    defaultVisitor = getDefaultVisitor myVisitor
    loop body = do{ isInsideLoop <- gets sjIsInsideLoop
                  ; modify (\s -> s { sjIsInsideLoop = True })
                  ; myStat body
                  ; modify (\s -> s { sjIsInsideLoop = isInsideLoop })
                  }
    modifyR f = modify (\s@ScanJumpData { sjResult = r } -> s { sjResult = f r })
    myStat (While _ body) = loop body
    myStat (DoWhile _ body) = loop body
    myStat (For _ _ _ body) = loop body
    myStat (ForIn _ _ body) = loop body
    myStat (ForEach _ _ body) = loop body
    myStat stat@(Switch _ _) = do{ isInsideSwitch <- gets sjIsInsideSwitch
                                 ; modify (\s -> s { sjIsInsideSwitch = True })
                                 ; visitStat defaultVisitor stat
                                 ; modify (\s -> s { sjIsInsideSwitch = isInsideSwitch })
                                 }
    myStat (Break Nothing) = do{ isInsideLoopOrSwitch <- gets sjIsInsideLoopOrSwitch
                               ; unless isInsideLoopOrSwitch
                                   $ modifyR (\r -> r { sjHasUnlabelledBreak = True })
                               }
    myStat (Break (Just label)) = do{ seenLabels <- gets sjSeenLabels
                                    ; when (label `notElem` seenLabels)
                                        $ modifyR (\r -> r { sjExternalLabels = label : sjExternalLabels r })
                                    }
    myStat (Continue Nothing) = do{ isInsideLoop <- gets sjIsInsideLoop
                                  ; unless isInsideLoop
                                      $ modifyR (\r -> r { sjHasUnlabelledContinue = True })
                                  }
    myStat (Continue (Just label)) = do{ seenLabels <- gets sjSeenLabels
                                       ; when (label `notElem` seenLabels)
                                           $ modifyR (\r -> r { sjExternalLabels = label : sjExternalLabels r })
                                       }
    myStat (Return Nothing) = modifyR (\r -> r { sjHasReturn = True })
    myStat (Return (Just _)) = modifyR (\r -> r { sjHasValuedReturn = True })
    myStat (Labelled label stat) = do{ labels <- gets sjSeenLabels
                                     ; modify (\s -> s { sjSeenLabels = label:labels })
                                     ; visitStat defaultVisitor stat
                                     ; modify (\s -> s { sjSeenLabels = labels })
                                     }
    myStat stat = visitStat defaultVisitor stat

hasUnconditionalJump :: CodeFragment a => a -> Bool
hasUnconditionalJump code = isNothing $ flip execStateT (ScanJumpData (ScanJumpResult False False False False []) [] False False) $ applyVisitor myVisitor code
  where
    myVisitor,defaultVisitor :: Visitor (StateT ScanJumpData Maybe)
    myVisitor = defaultVisitor { visitExpr = const $ lift $ Just ()
                               , visitStat = myStat
                               , visitFunction = const $ lift $ Just ()
                               }
    defaultVisitor = getDefaultVisitor myVisitor
    loop body = do{ isInsideLoop <- gets sjIsInsideLoop
                  ; modify (\s -> s { sjIsInsideLoop = True })
                  ; myStat body
                  ; modify (\s -> s { sjIsInsideLoop = isInsideLoop })
                  }
    modifyR f = modify (\s@ScanJumpData { sjResult = r } -> s { sjResult = f r })
    myStat (If _ t (Just e)) | hasUnconditionalJump t && hasUnconditionalJump e = lift Nothing
    myStat (If _ _ _) = lift $ Just ()
    myStat (While _ body) = lift $ Just ()
    myStat (DoWhile _ body) = loop body
    myStat (For _ Nothing _ body) = loop body
    myStat (For _ _ _ body) = lift $ Just ()
    myStat (ForIn _ _ body) = lift $ Just ()
    myStat (ForEach _ _ body) = lift $ Just ()
    myStat (Try b conditionalCatches unconditionalCatch _)
        | hasUnconditionalJump b
          && and (map (\(_,_,b) -> hasUnconditionalJump b) conditionalCatches)
          && maybe True (hasUnconditionalJump . snd) unconditionalCatch
              = lift Nothing
    myStat (Try _ _ _ _) = lift $ Just ()
    myStat stat@(Switch _ _) = do{ isInsideSwitch <- gets sjIsInsideSwitch
                                 ; modify (\s -> s { sjIsInsideSwitch = True })
                                 ; visitStat defaultVisitor stat
                                 ; modify (\s -> s { sjIsInsideSwitch = isInsideSwitch })
                                 }
    myStat (Break Nothing) = do{ isInsideLoopOrSwitch <- gets sjIsInsideLoopOrSwitch
                               ; if isInsideLoopOrSwitch
                                 then lift $ Just ()
                                 else lift Nothing
                               }
    myStat (Break (Just label)) = do{ seenLabels <- gets sjSeenLabels
                                    ; if label `elem` seenLabels
                                      then lift $ Just ()
                                      else lift Nothing
                                    }
    myStat (Continue Nothing) = do{ isInsideLoop <- gets sjIsInsideLoop
                                  ; if isInsideLoop
                                    then lift $ Just ()
                                    else lift Nothing
                                  }
    myStat (Continue (Just label)) = do{ seenLabels <- gets sjSeenLabels
                                       ; if label `elem` seenLabels
                                         then lift $ Just ()
                                         else lift Nothing
                                       }
    myStat (Return Nothing) = lift Nothing
    myStat (Return (Just _)) = lift Nothing
    myStat (Labelled label stat) = do{ labels <- gets sjSeenLabels
                                     ; modify (\s -> s { sjSeenLabels = label:labels })
                                     ; visitStat defaultVisitor stat
                                     ; modify (\s -> s { sjSeenLabels = labels })
                                     }
    myStat stat = visitStat defaultVisitor stat

patternComponents :: LHSPattern a -> [a]
patternComponents (LHSSimple x) = [x]
patternComponents (LHSArray elems) = concatMap patternComponents $ catMaybes elems
patternComponents (LHSObject elems) = concatMap (patternComponents . snd) elems

patternNoExprToExpr :: LHSPatternNoExpr -> LHSPatternExpr
patternNoExprToExpr (LHSSimple x) = LHSSimple $ Variable x
patternNoExprToExpr (LHSArray elems) = LHSArray $ map (fmap patternNoExprToExpr) elems
patternNoExprToExpr (LHSObject elems) = LHSObject $ map (\(n,x) -> (n,patternNoExprToExpr x)) elems

isEmptyPattern (LHSSimple _) = False
isEmptyPattern (LHSArray elems) = all isEmptyPattern $ catMaybes elems
isEmptyPattern (LHSObject elems) = all (isEmptyPattern . snd) elems

isSingleElementPattern (LHSSimple _) = True
isSingleElementPattern (LHSArray elems) = (length $ filter (not . isEmptyPattern) $ catMaybes elems) == 1
isSingleElementPattern (LHSObject elems) = (length $ filter (not . isEmptyPattern . snd) elems) == 1

isTrivialPattern (LHSSimple _) = True
isTrivialPattern _ = False


expandMultiStatements :: CodeFragment a => a -> a
expandMultiStatements code = runIdentity (applyTransformer myTransformer code)
  where
    myTransformer,defaultTransformer :: Transformer Identity
    myTransformer = defaultTransformer { transformStat = myStat
                                       , transformBlock = myBlock
                                       , transformFunction = myFunction
                                       , transformProgram = myProgram
                                       }
    defaultTransformer = getDefaultTransformer myTransformer
    myStat (MultiStatements ss) = defaultStat =<< (liftM BlockStatement $ myBlock $ Block ss)
    myStat s = defaultStat s
    defaultStat = transformStat defaultTransformer
    myBlock (Block ss) = transformBlock defaultTransformer $ Block $ flatten ss
    myFunction f = transformFunction defaultTransformer $ makeFunction (functionName f) (functionArguments f) $ let FunctionBody body = functionBody f in FunctionBody $ flattenSE body
    myProgram (Program ss) = transformProgram defaultTransformer $ Program $ flattenSE ss
    flatten ss = concatMap expand ss
    expand (MultiStatements ss) = flatten ss
    expand s = [s]
    flattenSE ss = concatMap expandSE ss
    expandSE (Statement (MultiStatements ss)) = map Statement $ flatten ss
    expandSE s = [s]
