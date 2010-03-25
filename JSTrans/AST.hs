{-# OPTIONS_GHC -XRelaxedPolyRec #-}
module JSTrans.AST where
import Prelude
import Text.ParserCombinators.Parsec.Expr (Assoc)
import Monad
import Control.Monad.State
import List
import Maybe (maybeToList)

type Operator = String
operatorForName :: String -> Operator
operatorForName = id

data Literal = NullLiteral
             | NumericLiteral String
             | RegExpLiteral String
             | BooleanLiteral Bool
             | StringLiteral String
               deriving (Eq,Show)
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
              [(ComprehensionKind,String,Expr) {- for / for each -}]
              (Maybe Expr {- if -})
          | ObjectLiteral [(PropertyName,Either Expr (AccessorKind,Function))]
          | Let [(String,Maybe Expr)] Expr
          | FunctionExpression Bool{-isExpressionClosure-} Function
          | Variable String
          | Literal Literal
          | This
          | New Expr [Expr]
          | Assign Operator Expr Expr
            deriving (Eq,Show)
data DefinitionKind = VariableDefinition
                    | ConstantDefinition
                    | LetDefinition
                      deriving (Eq,Show)
type Block = [Statement]
data Statement = EmptyStat
               | VarDef DefinitionKind [(String,Maybe Expr)]
               | LetStatement [(String,Maybe Expr)] Block
               | ExpressionStatement Expr
               | Return (Maybe Expr)
               | Throw Expr
               | BlockStatement Block
               | If Expr Statement (Maybe Statement)
               | While Expr Statement
               | DoWhile Expr Statement
-- | ForE (Maybe Expr) (Maybe Expr) (Maybe Expr) Statement
-- | ForE DefinitionKind String (Maybe Expr) (Maybe Expr) (Maybe Expr) Statement
               | For (Maybe Statement) (Maybe Expr) (Maybe Expr) Statement
               | ForIn Statement Expr Statement
               | ForEach Statement Expr Statement
               | Try Block [(String,Expr,Block)] (Maybe (String,Block)) (Maybe Block)
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
--                   | FunctionDeclaration String [String] FunctionBody
                     deriving (Eq,Show)
type FunctionBody = [SourceElement]


data Function
    = Function { functionName :: Maybe String
               , functionArguments :: [String]
               , functionBody :: FunctionBody
               , functionVariables :: [String] -- variables and functions explicitly declared inside the function
               , outerVariables :: [String] -- variables used in this function and not declared inside
--               , innerFunctions :: [Function]
               } deriving (Eq,Show)
makeFunction name args body
    = Function { functionName = name
               , functionArguments = args
               , functionBody = body
               , functionVariables = variables
               , outerVariables
                   = (scanUsedVar body)
                     \\ (args `union` variables `union` ["arguments"]
                         `union` maybeToList name)
               }
  where
    variables = scanVarDecl body

data Monad m => Transformer m
    = Transformer { transformExpr :: Expr -> m Expr
                  , transformStat :: Statement -> m Statement
                  , transformBlock :: Block -> m Block
                  , transformFuncDecl :: String -> Function -> m Function
                  , transformFunction :: Function -> m Function
                  }

transformSourceElem v (Statement st) = liftM Statement $ transformStat v st
transformSourceElem v (FunctionDeclaration name fn)
    = liftM (FunctionDeclaration name) $ transformFuncDecl v name fn

getDefaultTransformer :: Monad m => Transformer m -> Transformer m
getDefaultTransformer v
    = Transformer { transformExpr = myExpr
                  , transformStat = myStat
                  , transformBlock = myBlock
                  , transformFuncDecl = myFuncDecl
                  , transformFunction = myFunction
                  }
  where
    expr = transformExpr v
    stat = transformStat v
    block = transformBlock v
    sourceElem = transformSourceElem v
    function = transformFunction v

    varDecl (name,e) = do{ v <- mmap expr e
                         ; return (name,v)
                         }
    mmap :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
    mmap f (Just x) = f x >>= return . Just
    mmap f Nothing = return Nothing

    myExpr (Binary op x y) = liftM2 (Binary op) (expr x) (expr y)
    myExpr (Prefix op x) = liftM (Prefix op) (expr x)
    myExpr (Postfix op x) = liftM (Postfix op) (expr x)
    myExpr (Cond x y z) = liftM3 Cond (expr x) (expr y) (expr z)
    myExpr (Field x name) = liftM (flip Field name) (expr x)
    myExpr (Index x y) = liftM2 Index (expr x) (expr y)
    myExpr (FuncCall fn args) = liftM2 FuncCall (expr fn) (mapM expr args)
    myExpr (ArrayLiteral elems) = liftM ArrayLiteral (mapM (mmap expr) elems)
    myExpr (ArrayComprehension x f i)
        = do{ x' <- expr x
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
    myExpr (Let l e) = liftM2 Let (mapM varDecl l) (expr e)
    myExpr (FunctionExpression isEC fn)
        = liftM (FunctionExpression isEC) (function fn)
    myExpr t@(Variable _) = return t
    myExpr t@(Literal _) = return t
    myExpr t@This = return t
    myExpr (New ctor args) = liftM2 New (expr ctor) (mapM expr args)
    myExpr (Assign op x y) = liftM2 (Assign op) (expr x) (expr y)

    myStat t@EmptyStat = return t
    myStat (VarDef kind l) = liftM (VarDef kind) (mapM varDecl l)
    myStat (LetStatement l b) = liftM2 LetStatement (mapM varDecl l) (block b)
    myStat (ExpressionStatement e) = liftM ExpressionStatement (expr e)
    myStat (Return x) = liftM Return (mmap expr x)
    myStat (Throw x) = liftM Throw (expr x)
    myStat (BlockStatement b) = liftM BlockStatement (block b)
    myStat (If c t e) = liftM3 If (expr c) (stat t) (mmap stat e)
    myStat (While c b) = liftM2 While (expr c) (stat b)
    myStat (DoWhile c b) = liftM2 DoWhile (expr c) (stat b)
    myStat (For a b c d) = liftM4 For (mmap stat a) (mmap expr b) (mmap expr c) (stat d)
    myStat (ForIn a b c) = liftM3 ForIn (stat a) (expr b) (stat c)
    myStat (ForEach a b c) = liftM3 ForEach (stat a) (expr b) (stat c)
    myStat (Try b cc uc f) = liftM4 Try (block b) (mapM tcc cc) (mmap tuc uc) (mmap block f)
      where tcc (a,b,c) = liftM2 ((,,) a) (expr b) (block c)
            tuc (a,b) = liftM ((,) a) (block b)
    myStat (Switch e c) = liftM2 Switch (expr e) (mapM cc c)
      where cc (CaseClause e s) = liftM2 CaseClause (expr e) (mapM stat s)
            cc (DefaultClause s) = liftM DefaultClause (mapM stat s)
    myStat t@(Break _) = return t
    myStat t@(Continue _) = return t
    myStat (Labelled label s) = liftM (Labelled label) (stat s)
    myStat t@Debugger = return t

    myBlock s = mapM stat s
    myFuncDecl name f = function f
    myFunction f = liftM (makeFunction (functionName f) (functionArguments f)) (mapM sourceElem (functionBody f))

data Monad m => Visitor m
    = Visitor { visitExpr :: Expr -> m ()
              , visitStat :: Statement -> m ()
              , visitBlock :: Block -> m ()
              , visitFuncDecl :: String -> Function -> m ()
              , visitFunction :: Function -> m ()
              }

visitSourceElem v (Statement st) = visitStat v st
visitSourceElem v (FunctionDeclaration name fn)
    = visitFuncDecl v name fn

getDefaultVisitor :: Monad m => Visitor m -> Visitor m
getDefaultVisitor v
    = Visitor { visitExpr = myExpr
              , visitStat = myStat
              , visitBlock = myBlock
              , visitFuncDecl = myFuncDecl
              , visitFunction = myFunction
              }
  where
    expr = visitExpr v
    stat = visitStat v
    block = visitBlock v
    sourceElem = visitSourceElem v
    function = visitFunction v

    mmap :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
    mmap f (Just x) = f x >>= return . Just
    mmap f Nothing = return Nothing
    mmap_ :: Monad m => (a -> m ()) -> Maybe a -> m ()
    mmap_ f (Just x) = f x
    mmap_ f Nothing = return ()
    varDecl (name,e) = do{ v <- mmap expr e
                         ; return (name,v)
                         }

    myExpr (Binary _ x y) = expr x >> expr y
    myExpr (Prefix _ x) = expr x
    myExpr (Postfix _ x) = expr x
    myExpr (Cond x y z) = expr x >> expr y >> expr z
    myExpr (Field x _) = expr x
    myExpr (Index x y) = expr x >> expr y
    myExpr (FuncCall fn args) = expr fn >> mapM_ expr args
    myExpr (ArrayLiteral elems) = mapM_ (mmap expr) elems
    myExpr (ArrayComprehension x f i)
        = expr x >> mapM_ (\(_,_,o) -> expr o) f >> mmap_ expr i
    myExpr (ObjectLiteral elems) = mapM_ elem elems
      where 
        elem (_,Left value) = expr value
        elem (_,Right (_,fn)) = function fn
    myExpr (Let l e) = mapM_ varDecl l >> expr e
    myExpr (FunctionExpression isEC fn) = function fn
    myExpr t@(Variable _) = return ()
    myExpr t@(Literal _) = return ()
    myExpr t@This = return ()
    myExpr (New ctor args) = expr ctor >> mapM_ expr args
    myExpr (Assign _ x y) = expr x >> expr y

    myStat t@EmptyStat = return ()
    myStat (VarDef _ l) = mapM_ varDecl l
    myStat (LetStatement l b) = mapM_ varDecl l >> block b
    myStat (ExpressionStatement e) = expr e
    myStat (Return x) = mmap_ expr x
    myStat (Throw x) = expr x
    myStat (BlockStatement b) = block b
    myStat (If c t e) = expr c >> stat t >> mmap_ stat e
    myStat (While c b) = expr c >> stat b
    myStat (DoWhile c b) = expr c >> stat b
    myStat (For a b c d) = mmap_ stat a >> mmap_ expr b >> mmap_ expr c >> stat d
    myStat (ForIn a b c) = stat a >> expr b >> stat c
    myStat (ForEach a b c) = stat a >> expr b >> stat c
    myStat (Try b cc uc f) = block b >> mapM_ tcc cc >> mmap_ tuc uc >> mmap_ block f
      where tcc (a,b,c) = expr b >> block c
            tuc (a,b) = block b
    myStat (Switch e c) = expr e >> mapM_ cc c
      where cc (CaseClause e s) = expr e >> mapM_ stat s
            cc (DefaultClause s) = mapM_ stat s
    myStat t@(Break _) = return ()
    myStat t@(Continue _) = return ()
    myStat (Labelled label s) = stat s
    myStat t@Debugger = return ()

    myBlock s = mapM_ stat s
    myFuncDecl name f = function f
    myFunction f = mapM_ sourceElem (functionBody f)


scanVarDecl :: FunctionBody -> [String]
scanVarDecl funcBody = flip execState ([]::[String]) $ mapM_ (visitSourceElem myVisitor) funcBody
  where
    myVisitor,defaultVisitor :: Visitor (State [String])
    myVisitor = defaultVisitor { visitExpr = const $ return ()
                               , visitStat = myStat
                               , visitFuncDecl = myFunc
                               , visitFunction = const $ return ()
                               }
    defaultVisitor = getDefaultVisitor myVisitor
    myStat (VarDef _ vars) = modify (`union` map fst vars)
    myStat s = visitStat defaultVisitor s
    myFunc name fn = modify (`union` [name])

scanFuncDecl :: FunctionBody -> [(String,Function)]
scanFuncDecl funcBody = flip execState [] $ mapM_ (visitSourceElem myVisitor) funcBody
  where
    myVisitor,defaultVisitor :: Visitor (State [(String,Function)])
    myVisitor = defaultVisitor { visitExpr = const $ return ()
                               , visitStat = const $ return ()
                               , visitBlock = const $ return ()
                               , visitFuncDecl = myFuncDecl
                               , visitFunction = const $ return ()
                               }
    defaultVisitor = getDefaultVisitor myVisitor
    myFuncDecl name fn = modify ((name,fn):)

scanUsedVar :: FunctionBody -> [String]
scanUsedVar funcBody = fst $ flip execState ([],[]) $ mapM_ (visitSourceElem myVisitor) funcBody
  where
    myVisitor,defaultVisitor :: Visitor (State ([String]{-usedVariables-},[String]{-declaredVariables-}))
    myVisitor = defaultVisitor { visitExpr = myExpr
                               , visitFunction = myFunction
                               }
    defaultVisitor = getDefaultVisitor myVisitor
    myExpr (Variable name)
        = do{ (usedVariables,declaredVariables) <- get
            ; when (name `notElem` declaredVariables)
                (put (usedVariables `union` [name],declaredVariables))
            }
    myExpr (ArrayComprehension x f i)
        = do{ let compVars = map (\(_,n,_) -> n) f
            ; (usedVariables,declaredVariables) <- get
            ; let declaredVariables'
                      = declaredVariables
                        `union` compVars
            ; put (usedVariables,declaredVariables')
            ; myExpr x
            ; mapM_ myExpr $ map (\(_,_,x) -> x) f
            ; maybe (return ()) myExpr i
            ; (usedVariables',_) <- get
            ; put (usedVariables',declaredVariables)
            }
    myExpr v = visitExpr defaultVisitor v
    myFunction fn
        = do{ (usedVariables,declaredVariables) <- get
            ; let declaredVariables'
                      = declaredVariables
                        `union` functionArguments fn
                        `union` functionVariables fn
                        `union` ["arguments"]
                        `union` maybeToList (functionName fn)
            ; put (usedVariables,declaredVariables')
            ; visitFunction defaultVisitor fn
            ; (usedVariables',_) <- get
            ; put (usedVariables',declaredVariables)
            }


