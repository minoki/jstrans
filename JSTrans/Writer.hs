module JSTrans.Writer where
import JSTrans.AST
import List (intersperse)
import Char (isAlphaNum,isDigit)
import Maybe (isJust,fromJust)

expr :: Expr -> ShowS
stat :: Statement -> ShowS
block :: Block -> ShowS

primaryExpr :: Expr -> ShowS
memberExpr :: Expr -> ShowS

many = foldr (.) id
sepBy a x = foldr (.) id (intersperse x a)
option' = maybe id

isIdentifierPart c = isAlphaNum c || c == '_' || c == '$' || isDigit c -- TODO: Unicode
isOperatorPart c = c `elem` "=<>&|+-"

char = showChar
string = showString
parens = showParen True
squares x = char '[' . x . char ']'
braces x = char '{' . x . char '}'
comma = char ','
colon = char ':'
semi = char ';'
dot = char '.'

ident x [] = x
ident x rest@(y:_) | isIdentifierPart y = x ++ ' ':rest
                   | otherwise = x ++ rest

operator x [] = x
operator x rest@(y:_) | (isIdentifierPart (head x) && isIdentifierPart y)
                        || (isOperatorPart (head x) && isOperatorPart y)
                          = x ++ ' ':rest
                      | otherwise = x ++ rest

propertyName (PNIdentifier name) = ident name
propertyName (PNLiteral lit) = literal lit

functionParameterAndBody fn
    = (parens $ sepBy (map ident $ functionArguments fn) comma)
      . (braces $ many $ map sourceElement $ functionBody fn)

literal :: Literal -> ShowS
literal NullLiteral = ident "null"
literal (NumericLiteral t) = ident t
literal (RegExpLiteral t) = ident t
literal (StringLiteral t) = showString t
literal (BooleanLiteral True) = ident "true"
literal (BooleanLiteral False) = ident "false"

primaryExpr This = ident "this"
primaryExpr (Variable name) = ident name
primaryExpr (Literal lit) = literal lit

primaryExpr (ArrayLiteral elems) = squares $ sepBy (map element elems) comma
  where
    element Nothing = id
    element (Just x) = assignmentExpression x

primaryExpr (ObjectLiteral elems) = braces $ sepBy (map element elems) comma
  where
    element (name,Left e) = propertyName name
                            . colon
                            . assignmentExpression e
    element (name,Right (kind,fn))
        = ident (if kind==Getter then "get" else "set")
          . propertyName name
          . functionParameterAndBody fn
primaryExpr e = parens $ expr e

memberExpr (FunctionExpression True fn)
    | isJust body'
    = ident "function"
      . option' ident (functionName fn)
      . parens (sepBy (map ident $ functionArguments fn) comma)
      . let c = assignmentExpression body -- TODO: allowIn
        in case c "" of
             '{':_ -> parens c
             _ -> c
  where
    body' = case functionBody fn of
              [Statement (Return b@(Just _))] -> b
              _ -> Nothing
    body = fromJust body'
memberExpr (FunctionExpression _ fn)
    = ident "function"
      . option' ident (functionName fn)
      . functionParameterAndBody fn
memberExpr (Let vars body)
    = ident "let"
      . (parens $ sepBy (map varDecl vars) comma)
      . assignmentExpression body -- TODO: allowIn
memberExpr (Index x y) = memberExpr x . squares (expr y)
memberExpr (Field x name) = memberExpr x . char '.' . ident name
memberExpr (New ctor args) = ident "new" . memberExpr ctor . arguments args
memberExpr (FuncCall fn args) = memberExpr fn . arguments args
memberExpr e = primaryExpr e
arguments args = parens $ sepBy (map assignmentExpression args) comma

leftHandSideExpression = memberExpr

postfixExpression (Postfix op e) = leftHandSideExpression e . operator op
postfixExpression e = leftHandSideExpression e

unaryExpression (Prefix op e) = operator op . unaryExpression e
unaryExpression e = postfixExpression e

make :: [String] -> (Expr -> ShowS) -> Expr -> ShowS
make' :: [String] -> (Bool -> Expr -> ShowS) -> Bool -> Expr -> ShowS
make1 :: String -> (Bool -> Expr -> ShowS) -> Bool -> Expr -> ShowS
make set super (Binary op' x y)
    | op' `elem` set = make set super x . operator op' . super y
make _ super e = super e
make' set super allowIn (Binary op' x y)
    | op' `elem` set = make' set super allowIn x . operator op' . super allowIn y
make' _ super allowIn e = super allowIn e
make1 op super allowIn (Binary op' x y)
    | op == op' = make1 op super allowIn x . operator op' . super allowIn y
make1 _ super allowIn e = super allowIn e

multiplicativeExpression = make ["*","/","%"] unaryExpression
additiveExpression = make ["+","-"] multiplicativeExpression
shiftExpression = make ["<<",">>",">>>"] additiveExpression
relationalExpressionBase True = make ["<",">","<=",">=","instanceof","in"] shiftExpression
relationalExpressionBase False = make ["<",">","<=",">=","instanceof"] shiftExpression
equalityExpressionBase = make' ["==","!=","===","!=="] relationalExpressionBase
bitwiseANDExpressionBase = make1 "&" equalityExpressionBase
bitwiseXORExpressionBase = make1 "^" bitwiseANDExpressionBase
bitwiseORExpressionBase = make1 "|" bitwiseXORExpressionBase
logicalANDExpressionBase = make1 "&&" bitwiseORExpressionBase
logicalORExpressionBase = make1 "||" logicalANDExpressionBase
conditionalExpressionBase allowIn (Cond x y z)
    = logicalORExpressionBase allowIn x
      . operator "?" . assignmentExpression y
      . operator ":" . assignmentExpressionBase allowIn z
conditionalExpressionBase allowIn e = logicalORExpressionBase allowIn e
assignmentExpressionBase allowIn (Assign op x y)
    = leftHandSideExpression x
      . operator op . assignmentExpressionBase allowIn y
assignmentExpressionBase allowIn e = conditionalExpressionBase allowIn e
exprBase allowIn (Binary "," x y)
    = exprBase allowIn x . operator "," . assignmentExpressionBase allowIn y
exprBase allowIn e = assignmentExpressionBase allowIn e

assignmentExpression = assignmentExpressionBase True
expr = exprBase True
exprNoIn = exprBase False

---
--- Statements
---

block stats = braces $ many $ map stat stats
varDecl (name,value) = ident name . option' (\e -> operator "=" . assignmentExpression e) value
stat EmptyStat = semi
stat (VarDef kind v) = definitionKind kind . sepBy (map varDecl v) comma . semi
stat (LetStatement _ _) = undefined
stat (ExpressionStatement e)
    = let c = expr e
      in case c "" of
           ('{':_) -> parens c . semi
           ('f':'u':'n':'c':'t':'i':'o':'n':d:_)
               | not $ isIdentifierPart d -> parens c . semi
           _ -> c . semi
stat (Return value) = ident "return" . maybe id expr value . semi
stat (Throw value) = ident "throw" . expr value . semi
stat (BlockStatement b) = block b
stat (If cond body else') = ident "if" . parens (expr cond)
                            . stat body
                            . option' (\x -> ident "else" . stat x) else'
stat (While cond body) = ident "while" . parens (expr cond) . stat body
stat (DoWhile cond body) = ident "do" . stat body
                           . ident "while" . parens (expr cond) . semi
stat (For Nothing b c d) = ident "for"
                           . parens (semi . option' expr b . semi . option' expr c)
                           . stat d
stat (For (Just (VarDef kind vars)) b c d)
    = ident "for" . parens (definitionKind kind . sepBy (map varDecl vars) comma
                            . semi . option' expr b . semi . option' expr c)
      . stat d
stat (For (Just (ExpressionStatement a)) b c d)
    = ident "for" . parens (exprNoIn a . semi . option' expr b
                            . semi . option' expr c)
      . stat d
stat (ForIn (VarDef kind [var]) b body)
    = ident "for" . parens (definitionKind kind . varDecl var . ident "in" . expr b)
      . stat body
stat (ForIn (ExpressionStatement a) b body)
    = ident "for" . parens (leftHandSideExpression a . ident "in" . expr b)
      . stat body
stat (ForEach (VarDef kind [var]) b body)
    = ident "for each" . parens (definitionKind kind . varDecl var
                                 . ident "in" . expr b)
      . stat body
stat (ForEach (ExpressionStatement a) b body)
    = ident "for each" . parens (leftHandSideExpression a . ident "in" . expr b)
      . stat body
stat (Try body conditionalCatchClauses unconditionalCatchClause finallyClause)
    = ident "try" . block body
      . many (map c conditionalCatchClauses)
      . maybe id u unconditionalCatchClause
      . maybe id f finallyClause
  where
    c (vname,cond,body) = ident "catch"
                          . parens (ident vname . ident "if" . expr cond)
                          . block body
    u (vname,body) = ident "catch" . parens (ident vname) . block body
    f body = ident "finally" . block body
stat (Switch e clauses) = ident "switch" . (parens $ expr e)
                          . (braces $ many $ map c clauses)
  where
    c (CaseClause e s) = ident "case" . expr e . colon . many (map stat s)
    c (DefaultClause s) = ident "default" . colon . many (map stat s)
stat (Break label) = ident "break" . maybe id ident label . semi
stat (Continue label) = ident "continue" . maybe id ident label . semi
stat (Labelled label s) = ident label . colon . stat s
stat Debugger = ident "debugger" . semi
definitionKind VariableDefinition = ident "var"
definitionKind ConstantDefinition = ident "const"
definitionKind LetDefinition = ident "let"

sourceElement (Statement s) = stat s
sourceElement (FunctionDeclaration name fn)
    = ident "function" . ident name
      . functionParameterAndBody fn

program = many . map sourceElement
