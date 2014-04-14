{- PiForall language, OPLSS, Summer 2013 -}

{-# LANGUAGE FlexibleInstances, FlexibleContexts, TupleSections,
  ExplicitForAll #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-orphans #-}

-- | A parsec-based parser for the concrete syntax.
module Parser
  (
   parseModuleFile,
   parseModuleImports,
   parseExpr
  )
  where


import Syntax hiding (moduleImports)

import Unbound.LocallyNameless hiding (Data,Refl,Infix,join,name)
import Unbound.LocallyNameless.Ops (unsafeUnbind)

import Text.Parsec hiding (State,Empty)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified LayoutToken as Token

import Control.Monad.State.Lazy hiding (join)
import Control.Applicative ((<$>), (<*>), (<*), (*>), (<$))
import Control.Monad.Error hiding (join)

import Data.List
import qualified Data.Set as S

{-

Concrete syntax for the language:
Optional components in this BNF are marked with < >

  levels:
     l ::= natural numbers

  terms:
    a,b,A,B ::=
      Type <l>                 Universes
    | x                        Variables   (start with lowercase)
    | \ x . a                  Function definition
    | a b                      Application
    | (x : A) -> B             Pi type

    | A / R                    Quotient type
    | <x:Q>                    Quotient introduction
    | expose x P p rsp         Quotient elimination

        expose : (P : A / R -> Type i) (s : (a : A) -> P <a>) (rsp : (x : A) (y : A) -> R x y -> (s x = s y)) (x : A / R) -> P x

    | (a : A)                  Annotations
    | (a)                      Parens
    | TRUSTME                  An axiom 'TRUSTME', inhabits all types
    | {?x}                     A hole named x

    | let x = a in b           Let expression

    | Zero                     Empty type
    | One                      Unit type
    | tt                       Unit value

    | { x : A | B }            Dependent pair type
    | (a, b)                   Prod introduction
    | pcase a of (x,y) -> b    Prod elimination

    | a = b                    Equality type
    | subst a by b <at x.c>    Type conversion
    | contra a                 Contra
    | refl p                   Equality proof with evidence

    | trivial                  Trivial tactic
    | induction [x,...y]       Induction tactic

    | C a ...                  Type / Term constructors
    | case a [y] of            Pattern matching
        C1 [x] y z -> b1
        C2 x [y]   -> b2
    | ind f x = a              Induction
    | ( x : A | C) -> B        Constrained type
    | a < b                    Ordering constrant

    | \ [x <:A> ] . a          Erased lambda
    | a [b]                    Erased application
    | [x : A] -> B             Erased pi
    | let [x] = a in b         Erased let
    | ind f [x] = a            Erased ind



  declarations:

      foo : A
      foo = a

      axiom foo : A

      data T D : Type <l> where
         C1 of D1
         ...
         Cn of Dn

  telescopes:
    D ::=
                               Empty
     | (x : A) D               runtime cons
     | (A) D
     | [x : A] D               erased cons
     | [A] D

  Syntax sugar:

   - You can collapse lambdas, like:

         \ x [y] z . a

     This gets parsed as \ x . \ [y] . \ z . a

   - You can make a top level declaration an ind:

     foo : (n : Nat) -> A
     ind foo x = ...

-}

liftError :: (MonadError e m) => Either e a -> m a
liftError (Left e) = throwError e
liftError (Right a) = return a

-- | Parse a module declaration from the given filepath.
parseModuleFile :: (MonadError ParseError m, MonadIO m) => ConstructorNames -> String -> m Module
parseModuleFile cnames name = do
  liftIO $ putStrLn $ "Parsing File " ++ show name
  contents <- liftIO $ readFile name
  liftError $ runFreshM $
    flip evalStateT cnames $
     runParserT (whiteSpace *> moduleDef <* eof) [] name contents

-- | Parse only the imports part of a module from the given filepath.
parseModuleImports :: (MonadError ParseError m, MonadIO m) => String -> m Module
parseModuleImports name = do
  contents <- liftIO $ readFile name
  liftError $ runFreshM $
    flip evalStateT emptyConstructorNames $
     runParserT (whiteSpace *> moduleImports) [] name contents

-- | Test an 'LParser' on a String.
--
-- E.g., do
--
-- > testParser decl "axiom fix : (aTy : Type 0) -> (f : ((a:aTy) -> aTy)) -> aTy"
--
-- to parse an axiom declaration of a logical fixpoint combinator.
testParser :: LParser t -> String -> Either ParseError t
testParser parser str = runFreshM $
   flip evalStateT emptyConstructorNames $
     runParserT (do { whiteSpace; v <- parser; eof; return v}) [] "<interactive>" str

-- | Parse an expression.
parseExpr :: String -> Either ParseError Term
parseExpr = testParser expr

-- * Lexer definitions
type LParser a = ParsecT
                    String                      -- The input is a sequence of Char
                    [Column]                    -- The internal state for Layout tabs
                    (StateT ConstructorNames
                       FreshM)                   -- The internal state for generating fresh names,
                                                -- and for remembering which names are constructors.
                    a                           -- the type of the object being parsed

instance Fresh (ParsecT s u (StateT ConstructorNames FreshM))  where
  fresh = lift . lift . fresh

-- Based on Parsec's haskellStyle (which we can not use directly since
-- Parsec gives it a too specific type).
trellysStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
trellysStyle = Token.LanguageDef
                { Token.commentStart   = "{-"
                , Token.commentEnd     = "-}"
                , Token.commentLine    = "--"
                , Token.nestedComments = True
                , Token.identStart     = letter <|> oneOf "~"
                , Token.identLetter    = alphaNum <|> oneOf "_'⁺~"
                , Token.opStart	       = oneOf ":!#$%&*+.,/<=>?@\\^|-"
                , Token.opLetter       = oneOf ":!#$%&*+.,/<=>?@\\^|-"
                , Token.caseSensitive  = True
                , Token.reservedNames =
                  ["refl"
                  ,"ind"
                  ,"Type"
                  ,"data"
                  ,"where"
                  ,"case"
                  ,"of"
                  ,"with"
                  ,"under"
                  ,"by"
                  ,"contra"
                  ,"subst", "by", "at"
                  ,"let", "in"
                  ,"axiom"
                  ,"erased"
                  ,"TRUSTME"
                  ,"ord"
                  ,"pcase"
                  ,"expose"
                  ,"trivial"
                  ,"induction"
                  ,"Zero","One", "tt"
                  ]
               , Token.reservedOpNames =
                 ["!","?","\\",":",".",",","<", "=", "+", "-", "^", "()", "_", "[|", "|]", "|", "{", "}"]
                }

tokenizer :: Token.GenTokenParser String [Column] (StateT ConstructorNames FreshM)
layout :: forall a t. LParser a -> LParser t -> LParser [a]
(tokenizer, layout) =
  let (t, Token.LayFun l) = Token.makeTokenParser trellysStyle "{" ";" "}"
      in (t, l)

identifier :: LParser String
identifier = Token.identifier tokenizer

whiteSpace :: LParser ()
whiteSpace = Token.whiteSpace tokenizer

variable :: LParser TName
variable =
  do i <- identifier
     cnames <- get
     if string2Name i `S.member` tconNames cnames || i `S.member` dconNames cnames
       then fail "Expected a variable, but a constructor was found"
       else return $ string2Name i

wildcard :: LParser TName
wildcard = reservedOp "_" >> return wildcardName

varOrWildcard :: LParser TName
varOrWildcard = try wildcard <|> variable

dconstructor :: LParser DCName
dconstructor =
  do i <- identifier
     cnames <- get
     if i `S.member` dconNames cnames
       then return i
       else fail $ if string2Name i `S.member` tconNames cnames
             then "Expected a data constructor, but a type constructor was found."
             else "Expected a constructor, but a variable was found"

tconstructor :: LParser TCName
tconstructor =
  do i <- identifier
     cnames <- get
     if string2Name i `S.member` tconNames cnames
       then return $ string2Name i
       else fail $ if i `S.member` dconNames cnames
             then "Expected a type constructor, but a data constructor was found."
             else "Expected a constructor, but a variable was found"

-- variables or zero-argument constructors
varOrCon :: LParser Term
varOrCon = do i <- identifier
              cnames <- get
              return $ if i `S.member` dconNames cnames
                then DCon i [] $ Annot Nothing
                else if string2Name i `S.member` tconNames cnames
                       then TCon (string2Name i) []
                       else Var $ string2Name i

colon, dot, comma :: LParser ()
colon = () <$ Token.colon tokenizer
dot = () <$ Token.dot tokenizer
comma = () <$ Token.comma tokenizer

reserved,reservedOp :: String -> LParser ()
reserved = Token.reserved tokenizer
reservedOp = Token.reservedOp tokenizer

parens,brackets,braces :: LParser a -> LParser a
parens = Token.parens tokenizer
brackets = Token.brackets tokenizer
braces = Token.braces tokenizer

natural :: LParser Int
natural = fromInteger <$> Token.natural tokenizer

natenc :: LParser Term
natenc =
  do n <- natural
     return $ encode n
   where encode 0 = DCon "zero" [] natty
         encode n = DCon "succ" [Arg Runtime (encode (n-1))] natty
         natty    = Annot $ Just (TCon (string2Name "ℕ") [])

moduleImports :: LParser Module
moduleImports = do
  reserved "module"
  modName <- identifier
  reserved "where"
  imports <- layout importDef (return ())
  return $ Module (string2Name modName) imports [] emptyConstructorNames

moduleDef :: LParser Module
moduleDef = do
  reserved "module"
  modName <- identifier
  reserved "where"
  imports <- layout importDef (return ())
  decls <- layout decl (return ())
  cnames <- get
  return $ Module (string2Name modName) imports decls cnames

importDef :: LParser ModuleImport
importDef = reserved "import" >> ModuleImport <$> importName
  where importName = liftM string2Name identifier

telescope :: LParser Telescope
telescope = do
  bindings <- telebindings
  return $ foldr g Empty bindings where
    g (n, t, ep) rst = Cons ep (rebind (n, embed t) rst)

telebindings :: LParser [(TName, Term, Epsilon)]
telebindings = many teleBinding
  where
    annot :: Epsilon -> LParser (TName, Term, Epsilon)
    annot ep = do
      (x,ty) <-    try ((,) <$> varOrWildcard      <*> (colon >> expr))
                <|>    ((,) <$> fresh wildcardName <*> expr)
      return (x,ty,ep)
    teleBinding :: LParser (TName, Term,Epsilon)
    teleBinding =
      (    parens (annot Runtime)
       <|> brackets (annot Erased)) <?> "binding"

---
--- Top level declarations
---

decl,dataDef,sigDef,valDef,indDef :: LParser Decl
decl = try dataDef <|> sigDef <|> valDef <|> indDef

-- datatype declarations.
dataDef = do
  reserved "data"
  name <- identifier
  params <- telescope
  colon
  Type level <- typen
  modify (\cnames ->
           cnames{ tconNames = S.insert (string2Name name)
                               (tconNames cnames) })
  reserved "where"
  cs <- layout constructorDef (return ())
  forM_ cs
    (\(ConstructorDef _ cname _) ->
       modify (\cnames -> cnames{ dconNames = S.insert cname (dconNames cnames)}))
  return $ Data (string2Name name) params level cs

constructorDef :: LParser ConstructorDef
constructorDef = (ConstructorDef <$> getPosition <*> identifier <*> option Empty (reserved "of" *> telescope))
             <?> "Constructor"

sigDef = do
  axOrSig <- option Sig $ reserved "axiom" >> return Axiom
  axOrSig <$> try (variable <* colon) <*> expr

valDef = Def <$> try (variable <* reservedOp "=") <*> expr

indDef = do
  r@(Ind _ b _) <- ind
  let ((n,_),_) = unsafeUnbind b
  return $ Def n r


------------------------
------------------------
-- Terms
------------------------
------------------------

trustme :: LParser Term
trustme = TrustMe (Annot Nothing) <$ reserved "TRUSTME"

hole :: LParser Term
hole = Hole <$> name <*> return (Annot Nothing)
  where
    name = braces $ string2Name <$> (reservedOp "?" *> many (noneOf "{}"))

trivialTactic :: LParser Term
trivialTactic = Trivial (Annot Nothing) <$ (reserved "trivial" <|> reservedOp "_")

inductionTactic :: LParser Term
inductionTactic = reserved "induction" *> (Induction (Annot Nothing) <$> brackets scrutinees)
  where
    scrutinees = expr `sepBy1` comma

refl :: LParser Term
refl = do
  reserved "refl"
  evidence <- option LitUnit expr
  annot <- optionMaybe (colon >> expr)
  return $ Refl (Annot annot) evidence

-- Expressions

expr,term,factor :: LParser Term

-- expr is the toplevel expression grammar
expr = Pos <$> getPosition <*> buildExpressionParser table term
  where table = [[ifix  AssocLeft "<" Smaller],
                 [ifix  AssocLeft "=" mkEq],
                 [ifix  AssocLeft "//" Quotient],
                 [ifixM AssocRight "->" mkArrow]
                ]
        ifix  assoc op f = Infix (reservedOp op >> return f) assoc
        ifixM assoc op f = Infix (reservedOp op >> f) assoc
        mkEq a b = TyEq a b (Annot Nothing) (Annot Nothing)
        mkArrow  =
          do n <- fresh wildcardName
             return $ \tyA tyB ->
               Pi Runtime (bind (n,embed tyA) tyB)

-- A "term" is either a function application or a constructor
-- application.  Breaking it out as a seperate category both
-- eliminates left-recursion in (<expr> := <expr> <expr>) and
-- allows us to keep constructors fully applied in the abstract syntax.
term = try dconapp <|> try tconapp <|> funapp

arg :: LParser Arg
arg = Arg Erased <$> brackets expr <|> Arg Runtime <$> factor

dconapp :: LParser Term
dconapp = DCon <$> dconstructor <*> many arg <*> return (Annot Nothing)

tconapp :: LParser Term
tconapp = TCon <$> tconstructor <*> many factor

funapp :: LParser Term
funapp = do
  f <- factor
  foldl' app f <$> many bfactor
  where bfactor = ((,Erased)  <$> brackets expr) <|>
                  ((,Runtime) <$> factor)
        app e1 (e2,ep)  =  App e1 (Arg ep e2)

factor = choice [ varOrCon   <?> "a variable or nullary data constructor"
                , typen      <?> "Type n"
                , natenc     <?> "a literal"
                , lambda     <?> "a lambda"
                , ind        <?> "ind"
                , letExpr    <?> "a let"
                , contra     <?> "a contra"
                , caseExpr   <?> "a case"
                , pcaseExpr  <?> "a pcase"
                , exposeExpr <?> "an expose"
                , sigmaTy    <?> "a sigma type"
                , squashTy   <?> "a squash type"
                , qboxExpr   <?> "a quotient box"
                , substExpr  <?> "a subst"
                , ordax      <?> "ord"
                , refl       <?> "refl"
                , trivialTactic <?> "the trivial tactic"
                , inductionTactic <?> "the induction tactic"
                , trustme    <?> "TRUSTME"
                , hole       <?> "hole"
                , impProd    <?> "an implicit function type"
                , bconst     <?> "a constant"
                , expProdOrAnnotOrParens
                    <?> "an explicit function type or annotated expression"
                ]

{-
impBind,expBind :: LParser (TName,Epsilon,Term)
impBind = brackets $ do
  x <- variable
  colon
  ty <- expr
  return (x,Erased,ty)

expBind = try (parens $ do
  x <- variable
  colon
  ty <- expr
  return (x,Runtime,ty))

impOrExpBind :: LParser (TName,Epsilon,Term)
impOrExpBind = impBind <|> expBind
-}


impOrExpVar :: LParser (TName, Epsilon)
impOrExpVar = try ((,Erased) <$> brackets variable)
              <|> (,Runtime) <$> variable


typen :: LParser Term
typen = Type <$> (reserved "Type" *> (try natural <|> return 0))

-- Lambda abstractions have the syntax '\x . e'
lambda :: LParser Term
lambda = do reservedOp "\\"
            binds <- many1 impOrExpVar
            dot
            body <- expr
            return $ foldr lam body binds where
    lam (x, ep) m = Lam ep (bind (x, embed $ Annot Nothing) m)


ordax :: LParser Term
ordax = OrdAx (Annot Nothing) <$ reserved "ord"

-- recursive abstractions, with the syntax 'ind f x = e', no type annotation.
ind :: LParser Term
ind = do
  reserved "ind"
  f <- variable
  (x, ep) <- impOrExpVar
  reservedOp "="
  body <- expr
  return $ Ind ep (bind (f,x) body) $ Annot Nothing


bconst  :: LParser Term
bconst = choice [TyEmpty <$ reserved "Zero",
                 TyUnit <$ reserved "One",
                 LitUnit <$ reserved "tt"]
--
letExpr :: LParser Term
letExpr =
  do reserved "let"
     (x,ep) <- impOrExpVar
     reservedOp "="
     boundExp <- expr
     reserved "in"
     body <- expr
     return $ Let ep $ bind (x,embed boundExp) body

-- impProd - implicit dependent products
-- These have the syntax [x:a] -> b or [a] -> b .
impProd :: LParser Term
impProd =
  do (x,tyA, mc) <- brackets
       (try ((,,) <$> variable <*> (colon >> expr) <*> return Nothing)
        <|> ((,,) <$> fresh wildcardName <*> expr) <*> return Nothing)
     optional (reservedOp "->")
     tyB <- expr
     return $ case mc of
       Just c  -> PiC Erased (bind (x,embed tyA) (c,tyB))
       Nothing -> Pi Erased (bind (x,embed tyA) tyB)

qboxExpr :: LParser Term
qboxExpr = do
  reservedOp "<"
  x <- expr
  mty <- optionMaybe (reservedOp ":" *> expr)
  reservedOp ">"
  return $ QBox x (Annot $ mty)

exposeExpr :: LParser Term
exposeExpr = do
  reserved "expose"
  q <- expr
  reserved "under"
  p <- expr
  reserved "with"
  s <- expr
  reserved "by"
  rsp <- expr
  return $ QElim p s rsp q

-- Function types have the syntax '(x:A) -> B'.  This production deals
-- with the ambiguity caused because these types, annotations and
-- regular old parens all start with parens.

data InParens = Colon Term Term | Comma Term Term | Nope Term

expProdOrAnnotOrParens :: LParser Term
expProdOrAnnotOrParens =
  let
    -- afterBinder picks up the return type of a pi
    afterBinder :: LParser Term
    afterBinder = optional (reservedOp "->") *> expr

    -- before binder parses an expression in parens
    -- If it doesn't involve a colon, you get (Right tm)
    -- If it does, you get (Left tm1 tm2).  tm1 might be a variable,
    --    in which case you might be looking at an explicit pi type.
    beforeBinder :: LParser InParens
    beforeBinder = parens $
      choice [ Colon <$> try (term <* colon) <*> expr
             , Comma <$> try (term <* comma) <*> expr
             , Nope <$> expr]
  in
    do bd <- beforeBinder
       case bd of
         Colon (Var x) a ->
           option (Ann (Var x) a)
                  (Pi Runtime <$> (bind (x, embed a) <$> afterBinder))
         Colon a b -> return $ Ann a b
         Comma a b -> return $ Prod a b (Annot Nothing)
         Nope a    -> return $ a

pattern :: LParser Pattern
-- Note that 'dconstructor' and 'variable' overlaps, annoyingly.
pattern =  try (PatCon <$> dconstructor <*> many arg_pattern)
       <|> atomic_pattern
  where
    arg_pattern    =  ((,Erased) <$> brackets pattern)
                  <|> ((,Runtime) <$> atomic_pattern)
    atomic_pattern =  parens pattern
                  <|> (PatVar <$> wildcard)
                  <|> do t <- varOrCon
                         case t of
                           (Var x) -> return $ PatVar x
                           (DCon c [] _) -> return $ PatCon c []
                           (TCon c []) -> fail "expected a data constructor but a type constructor was found"
                           _ -> error "internal error in atomic_pattern"

match :: LParser Match
match = Match <$> (bind <$> pattern <* reservedOp "->" <*> term)

caseExpr :: LParser Term
caseExpr = Case
       <$> (reserved "case" *> factor)
       <*> (reserved "of" *> layout match (return ()))
       <*> return (Annot Nothing)

pcaseExpr :: LParser Term
pcaseExpr = do
    reserved "pcase"
    scrut <- expr
    reserved "of"
    reservedOp "("
    x <- variable
    reservedOp ","
    y <- variable
    reservedOp ")"
    reservedOp "->"
    a <- expr
    return $ Pcase scrut (bind (x,y) a) (Annot Nothing)

-- subst e0 by e1 { at [x.t] }
substExpr :: LParser Term
substExpr = do
  reserved "subst"
  a <- expr
  reserved "by"
  b <- expr
  ctx <- option Nothing (try (do
     reserved "at"
     x <- variable
     dot
     c <- expr
     return (Just (bind x c))))
  return $ Subst a b ctx

contra :: LParser Term
contra = Contra <$> (reserved "contra" *> expr) <*> return (Annot Nothing)

squashTy :: LParser Term
squashTy = do
  x <- between (reservedOp "[|") (reservedOp "|]") expr
  return (TySquash x) <?> "Squash"

sigmaTy :: LParser Term
sigmaTy = do
  reservedOp "{"
  x <- variable
  colon
  a <- expr
  reservedOp "&"
  b <- expr
  reservedOp "}"
  return (Sigma (bind (x, embed a) b))


