{- PiForall language, OPLSS, Summer 2013 -}

{-# LANGUAGE ViewPatterns, TypeSynonymInstances,
  ExistentialQuantification, NamedFieldPuns, FlexibleContexts,
  ScopedTypeVariables, TupleSections, FlexibleInstances #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | The main routines for type-checking
module TypeCheck(tcModules, inferType, checkType) where

import Syntax
import Environment
import PrettyPrint
import Equal

import Unbound.LocallyNameless hiding (Data, Refl)
import Control.Applicative ((<$>), (<*>), (<$), pure)
import Control.Monad.Error hiding (ap)
import Text.PrettyPrint.HughesPJ
import Data.Maybe
import Control.Monad.RWS.Lazy (MonadReader)
import Data.List(nub)
import qualified Data.Set as S
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import Debug.Trace

-- Type abbreviation for documentation
type Type = Term

-- | Infer the type of a term, producing an annotated version of the
-- term (whose type can *always* be inferred).
inferType :: Term -> TcMonad (Term,Type)
inferType t = tcTerm t Nothing

-- | Check that the given term has the expected type. This type
-- may not necessarily be in whnf, it will be reduced first thing.
checkType :: Term -> Type -> TcMonad (Term, Type)
checkType tm expectedTy = do
  nf <- whnf expectedTy
  tcTerm tm (Just nf)

-- | check a term, producing an elaborated term
-- where all of the type annotations have been filled in
-- The second argument is 'Nothing' in inference mode and
-- an expected type (must be in whnf) in checking mode
tcTerm :: Term -> Maybe Type -> TcMonad (Term,Type)

tcTerm t@(Var x) Nothing = (t,) <$> lookupTy x
tcTerm t@(Type i) Nothing = return (t, Type (i+1))

tcTerm q@(Quotient t r) Nothing = do
  (at, _) <- tcType t
  (ar, rt) <- checkType r (Pi Runtime (bind (string2Name "x", embed t)
                            (Pi Runtime (bind (string2Name "y", embed t)
                              (Type 0)))))
  return $ (q, Type 0)

tcTerm sq@(TySquash a) Nothing = do
  nsq <- whnf sq
  tcTerm nsq Nothing


tcTerm q@(QBox x (Annot mty)) Nothing = do
  case mty of
    Nothing -> err [DS "Could not infer type of quotient", DD q]
    Just ty -> return (q, ty)

tcTerm (QBox x ann1) ann2 = do
  Just ty <- matchAnnots ann1 ann2
  (carrier, rel) <- ensureQuotient ty
  (ax, _) <- checkType x carrier
  return $ (QBox ax (Annot $ Just ty), ty)

tcTerm (QElim p s rsp q) Nothing = do
  (aq, tyQ) <- inferType q
  (carrier, rel) <- ensureQuotient tyQ

  let varX = string2Name "x"
  let varY = string2Name "Y"

  tyPx <- whnf $ App p (Arg Runtime (QBox (Var varX) (Annot $ Just tyQ)))
  tyPy <- whnf $ App p (Arg Runtime (QBox (Var varY) (Annot $ Just tyQ)))

  (ap, tyP) <- checkType p (Pi Runtime (bind (varX, embed tyQ) (Type 0)))
  (as, tyS) <- checkType s (Pi Runtime (bind (varX, embed carrier) tyPx))

  (arsp, tyRsp) <- checkType rsp $ Pi Runtime $ bind (varX, embed carrier) $
                                  (Pi Runtime (bind (varY, embed carrier)
                                    (Pi Runtime (bind (string2Name "rpf", embed (App (App rel (Arg Runtime (Var varX))) (Arg Runtime (Var varY))))
                                      (TyEq (App s (Arg Runtime (Var varX))) (App s (Arg Runtime (Var varY))) (Annot $ Just tyPx) (Annot $ Just tyPy))))))

  nf <- whnf (App p (Arg Runtime q))
  return (QElim ap as arsp aq, nf)

tcTerm (Pi ep bnd) Nothing = do
  ((x, unembed -> tyA), tyB) <- unbind bnd
  (atyA,i) <- tcType tyA
  (atyB,j) <- extendCtx (Sig x atyA) $ tcType tyB
  return (Pi ep (bind (x, embed atyA) atyB), Type $ max i j)

-- Check the type of a function
tcTerm (Lam ep1 bnd) (Just (Pi ep2 bnd2)) | ep1 == ep2 = do
  -- unbind the variables in the lambda expression and pi type
  ((x,unembed -> Annot ma), body,
   (_, unembed -> tyA), tyB) <- unbind2Plus bnd bnd2
  -- check tyA matches type annotation on binder, if present
  maybe (return ()) (equate tyA) ma
  -- check the type of the body of the lambda expression
  (ebody, etyB) <- extendCtx (Sig x tyA) (checkType body tyB)
    -- make sure that an 'erased' variable isn't used
  when ((ep1 == Erased) && (x `elem` fv (erase ebody))) $
    err [DS "Erased variable", DD x,
         DS "used in body"]

  return (Lam ep1 $ bind (x, embed $ Annot $ Just tyA) ebody, Pi ep1 bnd2)

tcTerm (Lam ep1 _) (Just (Pi ep2 _))  =
  err [DS "Epsilon", DD ep1,
       DS "on lambda does not match expected", DD ep2]
tcTerm e@(Lam _ bnd) (Just nf) = err [DS "Lambda expression has a function type, not", DD nf]

-- infer the type of a lambda expression, when an annotation
-- on the binder is present
tcTerm (Lam ep bnd) Nothing = do
  ((x, unembed -> Annot annot), body) <- unbind bnd
  tyA <- maybe (err [DS "Must annotate lambda"]) return annot
  -- check that the type annotation is well-formed
  (atyA, i)     <- tcType tyA
  -- infer the type of the body of the lambda expression
  (ebody, atyB) <- extendCtx (Sig x atyA) (inferType body)
    -- make sure that an 'erased' variable isn't used
  when ((ep == Erased) && (x `elem` fv (erase ebody))) $
    err [DS "Erased variable", DD x, DS "used in body"]

  return (Lam ep (bind (x, embed (Annot (Just atyA))) ebody),
          Pi ep  (bind (x, embed atyA) atyB))

tcTerm (App t1 (Arg ep2 t2)) Nothing = do
  (at1, ty1)             <- inferType t1
  (ep1, x, tyA, tyB, mc) <- ensurePi ty1
  (at2, ty2)             <- checkType t2 tyA
  let result = (App at1 $ Arg ep2 at2, subst x at2 tyB)
    -- make sure the epsilons match up
  unless (ep1 == ep2) $
    err [DD ep1, DS "argument supplied for", DD ep2, DS "function"]

  -- if the function has a constrained type
  -- make sure that it is satisfied
  () <- case mc of
    Just constr@(Smaller b c) -> do
      let subterm y [] = False
          subterm y (Arg _ y' : ys) | y `aeq` y' = True
          subterm y (_ : ys) = subterm y ys
      b' <- whnf (subst x at2 b)
      c' <- whnf (subst x at2 c)
      case c' of
        (DCon _ args _) | b' `subterm` args ->
          return ()
        _ -> do
          gamma <- getLocalCtx
          err [DS "The constraint", DD (Smaller b' c'),
                  DS "was not satisfied in the application.",
                  DS "The local context was:",
                  DD gamma]
    Just c -> err [DS "I don't know how to satisfy the constraint", DD c]
    _ -> return ()

  return result

tcTerm (PiC ep bnd) Nothing = do
  ((x, unembed -> tyA), (tyC,tyB)) <- unbind bnd
  (atyA,i) <- tcType tyA
  (atyB,j) <- extendCtx (Sig x atyA) $ tcType tyB
  (atyC,k) <- extendCtx (Sig x atyA) $ tcType tyC
  when (k /= 0) $
    err [DS "constraint must be a Type 0. Instead found Type", DD k]
  return (PiC ep (bind (x, embed atyA) (atyC, atyB)), Type (max i j))


tcTerm (Ann tm ty) Nothing = do
  (ty', i)    <- tcType ty
  (tm', ty'') <- checkType tm ty'
  return (tm', ty'')

tcTerm (Pos p tm) mTy = extendSourceLocation p tm $ tcTerm tm mTy

tcTerm (Hole name ann1) ann2 = do
  Just expectedTy <- matchAnnots ann1 ann2
  return (Hole name (Annot (Just expectedTy)), expectedTy)
tcTerm (TrustMe ann1) ann2 = do
  Just expectedTy <- matchAnnots ann1 ann2
  return (TrustMe (Annot (Just expectedTy)), expectedTy)

tcTerm (TyEmpty) Nothing = return (TyEmpty, Type 0)
tcTerm (TyUnit) Nothing = return (TyUnit, Type 0)
tcTerm (LitUnit) Nothing = return (LitUnit, TyUnit)

tcTerm (Let ep bnd) ann = do
  ((x,unembed->rhs),body) <- unbind bnd
  (arhs,aty) <- inferType rhs
  (abody,ty) <- extendCtxs [Sig x aty, Def x arhs] $
                tcTerm body ann

  when ((ep == Erased) && (x `elem` fv (erase abody))) $
    err [DS "Erased variable", DD x,
         DS "used in body"]

  when (x `elem` fv ty) $
    err [DS "Let bound variable", DD x, DS "escapes in type", DD ty]
  return (Let ep (bind (x,embed arhs) abody), ty)


-- Type constructor application
tcTerm (TCon c params) Nothing = do
  (delta, lev, _) <- lookupTCon c
  unless (length params == teleLength delta) $
    err [DS "Datatype constructor", DD c,
         DS $ "should have " ++ show (teleLength delta) ++
         "parameters, but was given", DD (length params)]
  eparams <- tsTele params delta
  return (TCon c eparams, Type lev)

-- Data constructor application
tcTerm t@(DCon c args ann1) ann2 = do
  ann <- matchAnnots ann1 ann2
  case ann of
    -- we know the expected type of the data constructor
    -- so look up its type in the context
    (Just (TCon tname params)) -> do
      (delta, deltai) <- lookupDCon c tname
      let numArgs   = teleLength deltai
      unless (length args == numArgs) $
        err [DS "Constructor", DS c,
             DS "should have", DD numArgs,
             DS "data arguments, but was given",
             DD (length args), DS "arguments."]
      eargs  <- tcArgTele args (substTele delta params deltai)
      let ty = TCon tname params
      return (DCon c eargs (Annot (Just ty)), ty)
    Just ty ->
      err [DS "Unexpected type", DD ty, DS "for data constructor", DD t]
    Nothing -> do
      -- we don't know the expected type, so see if there
      -- is only one datacon of that name that takes no
      -- parameters
      matches <- lookupDConAll c
      case matches of
        [(tname,(Empty,ConstructorDef _ _ deltai))] -> do
          let numArgs   = teleLength deltai
          unless (length args == numArgs) $
            err [DS "Constructor", DS c,
                 DS "should have", DD numArgs,
                 DS "data arguments, but was given",
                 DD (length args), DS "arguments."]
          eargs  <- tcArgTele args deltai
          let ty =  TCon tname []
          return (DCon c eargs (Annot (Just ty)),ty)
        [_] -> err [DS "Cannot infer the parameters to data constructors.",
                    DS "Add an annotation."]
        _ -> err [DS "Ambiguous data constructor", DS c]

-- If we are in inference mode, then
--      we do not use refinement
-- otherwise, we must have a typing annotation
tcTerm (Case scrut alts ann1) ann2 = do
  (ascrut, sty) <- inferType scrut
  (n, params) <- ensureTCon sty
  ann <- matchAnnots ann1 ann2
  let checkAlt (Match bnd) = do
         (pat, body) <- unbind bnd
         -- add variables from pattern to context
         (decls, evars) <- declarePat pat Runtime (TCon n params)
         (ebody, atyp) <- case ann of
           (Just expectedTy) -> do
             -- add scrut = pat equation to the context.
             decls' <- equateWithPat scrut pat (TCon n params)
             (ebody, _) <- extendCtxs (decls ++ decls') $ checkType body expectedTy
             return (ebody, expectedTy)
           Nothing -> -- extendCtxs decls $ inferType body
             err [DS "must be in checking mode for case"]
         -- make sure 'erased' components aren't used
         when (any (`elem` fv (erase ebody)) evars) $
           err [DS "Erased variable bound in match used"]
         return (Match (bind pat ebody), atyp)
  exhaustivityCheck sty (map (\(Match bnd) ->
                          fst (unsafeUnbind bnd)) alts)
  aalts_atyps <- mapM checkAlt alts
  let (aalts, atyps) = unzip aalts_atyps
  ty <- merge ann atyps
  return (Case ascrut aalts (Annot (Just ty)), ty)

tcTerm (Smaller a b) Nothing = do
  (aa,aTy) <- inferType a
  (ab,bTy) <- checkType b aTy
  return (Smaller aa ab, Type 0)

tcTerm (OrdAx ann1) ann2 = do
  let subterm y [] = False
      subterm y (Arg _ y' : ys) | y `aeq` y' = True
      subterm y (_ : ys) = subterm y ys

  ann <- matchAnnots ann1 ann2
  case ann of
    Just sm@(Smaller x y) -> do
      x' <- whnf x
      y' <- whnf y
      case y' of
        (DCon _ args _) | x' `subterm` args ->
          return (OrdAx (Annot ann), sm)
        _ -> err [DS "ord must be used at type 'a < C ... a ...'",
                    DS "Instead, the type", DD sm, DS "was expected."]
    Just sm -> err [DS "ord must be used at type 'a < C ... a ...'",
                    DS "Instead, the type", DD sm, DS "was expected."]
    Nothing -> err [DS "Cannot figure out type of ord."]

tcTerm (Ind ep1 bnd ann1) ann2 = do
  ann <- matchAnnots ann1 ann2
  case ann of
    Just ty@(Pi ep2 bnd2) | ep1 == ep2 -> do
      ((f,x), body) <- unbind bnd
      ((y,unembed -> tyA), tyB) <- unbind bnd2

      -- make type of f inside the body
      -- constraining it to apply only to smaller arguments
      let tyF = PiC ep1 (bind (y, embed tyA)
                    (Smaller (Var y) (Var x), tyB))

      -- compute expected type of the body
      let x_tyB = swaps (single (AnyName x)(AnyName y)) tyB

      -- check the body of the ind
      (ebody, tyB') <-
        extendCtx (Sig x tyA) $
           extendCtx (Sig f tyF) $
             checkType body x_tyB

      -- check for erasure
      when ((ep1 == Erased) && (x `elem` fv (erase ebody))) $
        err [DS "Erased variable", DD x,
             DS "used in body"]

      return (Ind ep1 (bind (f,x) ebody) (Annot (Just ty)), ty)

    Just ty ->
      err [DS "Ind expression expected to have type", DD ty,
           DS "Sadly, it doesn't."]
    Nothing ->
      err [DS "Ind expression should be annotated with its type"]

tcTerm t@(Induction ann1@(Annot ty1) ss) ann2 = do
  ann@(Just ty) <- matchAnnots ann1 ann2

  let performInduction [] = return $ Trivial (Annot ann)
      performInduction (x:xs) = do
        (x', xty) <- inferType x
        (tcn, _) <- ensureTCon xty
        (tele, _, Just dcons) <- lookupTCon tcn

        let patVars :: Telescope -> [(Pattern, Epsilon)]
            patVars Empty = []
            patVars (Cons e (unrebind->((n,_), tele'))) = (PatVar n, e) : patVars tele'

        let buildMatch :: ConstructorDef -> TcMonad Match
            buildMatch (ConstructorDef _ dcn args) =
              Match <$> bind (PatCon dcn (patVars args)) <$> (performInduction xs)

        matches <- sequence $ buildMatch <$> dcons
        return $ Case x matches (Annot ann)

  switch <- performInduction ss
  checkType switch ty

tcTerm t@(Trivial ann1) ann2 = do
  ann@(Just ty) <- matchAnnots ann1 ann2
  nty <- whnf ty

  let proofSearch = do
        gam <- getCtx
        let checkDecls ((Sig nm ty') : gs) =
              do { mtm <- lookupDef nm
                 ; (ntm, nty') <- (checkType (Contra (Var nm) (Annot ann)) nty) <|> (checkType (Var nm) nty)
                 ; return $ (ntm, nty)
                 } <|> checkDecls gs
            checkDecls (_ : gs) = checkDecls gs
            checkDecls [] = err [DS "Could not find suitable value of type", DD nty, DS "in context", DD gam]
        checkDecls gam

  let conventional =
        case nty of
          TyUnit ->
            return (LitUnit, nty)
          Pi ep bnd -> do
            ((x, unembed -> tyA), tyB) <- unbind bnd
            checkType (Lam ep (bind (x, embed (Annot Nothing)) (Trivial $ Annot Nothing))) nty
          Sigma bnd -> do
            ((x, unembed -> tyA), tyB) <- unbind bnd
            checkType (Prod (Trivial $ Annot Nothing) (Trivial $ Annot Nothing) (Annot ann)) nty
          TyEq x y (Annot (Just tyX)) (Annot (Just tyY)) -> do
            Just ev <- resolveEq x y tyX tyY
            checkType (Refl (Annot Nothing) (Trivial $ Annot $ Just ev)) nty
          _ -> do
            gam <- getLocalCtx
            err [DS "Trivial tactic not effective for type", DD nty, DS "in context", DD gam]

  conventional <|> proofSearch

tcTerm (Refl ann1 evidence) ann2 = do
  ann <- matchAnnots ann1 ann2
  case ann of
    Just ty@(TyEq a b (Annot (Just tyA)) (Annot (Just tyB))) -> do
      mp <- resolveEq a b tyA tyB
      case mp of
        Just p -> do
          (evidence', _) <- checkType evidence p
          return (Refl (Annot ann) evidence', ty)
        Nothing -> do
          equate a b
          return (Refl (Annot ann) evidence, ty)
    _ -> err [DS "refl requires annotation", DD ann]

tcTerm (TyEq a b (Annot mtyA) (Annot mtyB)) ann2 = do
  (na, tyA) <- tcTerm a mtyA
  (nb, tyB) <- tcTerm b mtyB
  (_, i) <- tcType tyA
  (_, j) <- tcType tyB
  return (TyEq na nb (Annot $ Just tyA) (Annot $ Just tyB), Type (max i j))

tcTerm (Subst tm p mbnd) Nothing = do
  -- infer the type of the proof p
  (apf, tp) <- inferType p
  -- make sure that it is an equality between m and n
  (m,n)     <- ensureTyEq tp
  (m', n')  <- case mbnd of
    Just bnd -> do
      (x, a) <- unbind bnd
      -- ensure that m' and n' are good
      (m',_) <- tcType (subst x m a)
      (n',_) <- tcType (subst x n a)
      return (m', n')
    Nothing -> return (m,n)
  (atm, ty') <- checkType tm m'
  return (Subst atm apf mbnd, n')


tcTerm t@(Contra p ann1) ann2 =  do
  ann <- matchAnnots ann1 ann2
  case ann of
    Nothing -> err [DS "Cannot check term", DD t, DS "without annotation"]
    Just ty -> do
      (apf, ty') <- inferType p
      (a,b) <- ensureTyEq ty'
      a' <- whnf a
      b' <- whnf b
      case (a',b') of
        (DCon da _ _, DCon db _ _) | da /= db ->
          return (Contra apf (Annot (Just ty)), ty)
        (_,_) -> err [DS "I can't tell that", DD a, DS "and", DD b,
                      DS "are contradictory"]


tcTerm t@(Sigma bnd) Nothing = do
  ((x,unembed->tyA),tyB) <- unbind bnd
  (aa, i) <- tcType tyA
  (ba, j) <- extendCtx (Sig x aa) $ tcType tyB
  return (Sigma (bind (x,embed aa) ba), Type (max i j))


tcTerm t@(Prod a b ann1) ann2 = do
  ann <- matchAnnots ann1 ann2
  case ann of
    Nothing -> err [DS "Cannot check term", DD t, DS "without annotation"]
    Just ty@(Sigma bnd) -> do
      ((x, unembed-> tyA), tyB) <- unbind bnd
      (aa,_) <- checkType a tyA
      (ba,_) <- extendCtxs [Sig x tyA, Def x aa] $ checkType b tyB
      return (Prod aa ba (Annot ann), ty)
    Just ty -> err [DS "Products must have Sigma Type", DD ty,
                   DS "found instead"]


tcTerm t@(Pcase p bnd ann1) ann2 = do
  ann <- matchAnnots ann1 ann2
  case ann of
    Nothing -> err [DS "Cannot check term", DD t, DS "without annotation"]
    Just ty -> do
      (apr, pty) <- inferType p
      pty' <- whnf pty
      case pty' of
        Sigma bnd' -> do
          ((x,unembed->tyA),tyB) <- unbind bnd'
          ((x',y'),body) <- unbind bnd
          let tyB' = subst x (Var x') tyB
          nfp  <- whnf apr
          let ctx = case nfp of
                Var x0 -> [Def x0 (Prod (Var x') (Var y')
                                  (Annot (Just pty')))]
                _     -> []
          (abody, bTy) <- extendCtxs ([Sig x' tyA, Sig y' tyB'] ++ ctx) $
            checkType body ty
          return (Pcase apr (bind (x',y') abody) (Annot ann), bTy)
        _ -> err [DS "Pcase must be on sigma type.", DD pty',
                  DS "found instead."]


tcTerm tm (Just ty) = do
  (atm, ty') <- inferType tm
  equate ty' ty
  return (atm, ty)




---------------------------------------------------------------------
-- helper functions for type checking

-- | Merge together two sources of type information
-- The first annotation is assumed to come from an annotation on
-- the syntax of the term itself, the second as an argument to
-- 'checkType'.
matchAnnots :: Annot -> Maybe Type -> TcMonad (Maybe Type)
matchAnnots (Annot Nothing) Nothing     = return Nothing
matchAnnots (Annot Nothing) (Just t)    = return (Just t)
matchAnnots (Annot (Just t)) Nothing    = Just . fst <$> tcType t
matchAnnots (Annot (Just t1)) (Just t2) = do
  (at1, _) <- tcType t1
  equate at1 t2
  return (Just at1)

-- | Make sure that the term is a type (i.e. has type 'Type i'
-- for some particular level i).
tcType :: Term -> TcMonad (Term,Int)
tcType tm = do
  (atm, aty) <- inferType tm
  i <- ensureType aty
  return (atm, i)


---------------------------------------------------------------------
-- helper functions for type constructor / data constructor creation

-- | calculate the length of a telescope
teleLength :: Telescope -> Int
teleLength Empty = 0
teleLength (Cons _ (unrebind->(_,tele'))) = 1 + teleLength tele'

-- | type check a list of type constructor arguments against a telescope
tsTele :: [Term] -> Telescope -> TcMonad [Term]
tsTele tms tele = fmap unArg <$> tcArgTele (Arg Runtime <$> tms) tele

-- | type check a list of data constructor arguments against a telescope
tcArgTele ::  [Arg] -> Telescope -> TcMonad [Arg]
tcArgTele [] Empty = return []
tcArgTele (Arg ep1 tm:terms) (Cons ep2 (unrebind->((x,unembed->ty),tele'))) | ep1 == ep2 = do
  (etm, ety) <- checkType tm ty
  eterms <- tcArgTele terms (subst x etm tele')
  return $ Arg ep1 etm:eterms
tcArgTele (Arg ep1 _ : _) (Cons ep2 _) =
  err [DD ep1, DS "argument provided when",
       DD ep2, DS "argument was expected"]
tcArgTele [] _ =
  err [DD "Too few arguments provided."]
tcArgTele _ Empty =
  err [DD "Too many arguments provided."]


-----------------------------------------------------------
-- helper functions for checking pattern matching

-- given the annotation and the types for each branch, merge them together
merge :: Maybe Type -> [Type] -> TcMonad Type
merge Nothing   []   =
  err [DS "Need an annotation on empty case expression"]
merge (Just ty) []   = return ty
merge _ [hd] = return hd
merge ann (x : xs) = x <$ (equate <$> merge ann xs <*> pure x)


-- | Create the binding in the context for each of the variables in
-- the pattern.
declarePat :: Pattern -> Epsilon -> Type -> TcMonad ([Decl], [TName])
-- declarePat (PatVar x) ep ty@(TyEq (Var y) z) | y `notElem` fv z = do
--   mt <- lookupDef y
--   let ydef = case mt of
--         Nothing -> [Def y z]
--         Just _  -> []
--   return (Sig x ty : ydef, [x | ep == Erased])
declarePat (PatVar x) Runtime y = return ([Sig x y],[])
declarePat (PatVar x) Erased  y = return ([Sig x y],[x])
declarePat (PatCon d pats) Runtime (TCon c params) = do
  (delta, deltai) <- lookupDCon d c
  declarePats pats (substTele delta params deltai)
declarePat (PatCon d pats) Erased (TCon c params) =
  err [DS "Cannot pattern match erased arguments"]
declarePat pat ep ty =
  err [DS "Cannot match pattern", DD pat, DS "with type", DD ty]

declarePats :: [(Pattern,Epsilon)] -> Telescope -> TcMonad ([Decl],[TName])
declarePats [] Empty = return ([],[])
declarePats ((pat,_):pats) (Cons ep rbnd) = do
  let ((x,unembed -> ty),tele) = unrebind rbnd
  (ds1,v1) <- declarePat pat ep ty
  tm <- pat2Term pat ty
  (ds2,v2) <- declarePats pats (subst x tm tele)
  return (ds1 ++ ds2, v1 ++ v2)
declarePats [] _     = err [DS "Not enough patterns in match"]
declarePats _  Empty = err [DS "Too many patterns in match"]


-- | Convert a pattern to an (annotated) term so that we can add an
-- equation for it in the context. Because data constructors must
-- be annotated with their types, we need to have the expected type of
-- the pattern available.
pat2Term :: Pattern -> Type -> TcMonad Term
pat2Term (PatCon dc pats) ty@(TCon n params) = do
  (delta, deltai) <- lookupDCon dc n
  let tele = substTele delta params deltai
  let pats2Terms :: [(Pattern,Epsilon)] -> Telescope -> TcMonad [Arg]
      pats2Terms [] Empty = return []
      pats2Terms ((p,_) : ps) (Cons ep (unrebind-> ((x,unembed->ty1), d))) = do
        ty' <- whnf ty1
        t <- pat2Term p ty'
        ts <- pats2Terms ps (subst x t d)
        return (Arg ep t : ts)
      pats2Terms _ _ = err [DS "Invalid number of args to pattern", DD dc]
  args <- pats2Terms pats tele
  return $ DCon dc args $ Annot $ Just ty
pat2Term (PatCon _ _) ty = error "Internal error: should be a tcon"
pat2Term (PatVar x) ty = return (Var x)

-- | Create a list of variable definitions from the scrutinee
-- of a case expression and the pattern in a branch. Scrutinees
-- that are not variables or constructors applied to vars may not
-- produce any equations.
equateWithPat :: Term -> Pattern -> Type -> TcMonad [Decl]
equateWithPat (Pos  _ x) pat ty = equateWithPat x pat ty
equateWithPat (Var x) pat ty = (:[]) . Def x <$> pat2Term pat ty
equateWithPat (DCon dc args _) (PatCon dc' pats) (TCon n params)
  | dc == dc' = do
    (delta, deltai) <- lookupDCon dc n
    let tele = substTele delta params deltai
    let eqWithPats :: [Term] -> [(Pattern,Epsilon)] -> Telescope -> TcMonad [Decl]
        eqWithPats [] [] Empty = return []
        eqWithPats (t : ts) ((p,_) : ps) (Cons _ (unrebind-> ((x,unembed->ty), tl))) =
          (++) <$> equateWithPat t p ty <*> eqWithPats ts ps (subst x t tl)
        eqWithPats _ _ _ =
          err [DS "Invalid number of args to pattern", DD dc]
    eqWithPats (map unArg args) pats tele
equateWithPat _ _ _ = return []

-- | Check all of the types contained within a telescope returning
-- a telescope where all of the types have been annotated, and the
-- maximum level of any type in the telescope.
tcTypeTele :: Telescope -> TcMonad (Telescope, Int)
tcTypeTele Empty = return (Empty, 0)
tcTypeTele (Cons ep rbnd) = do
  let ((x, unembed -> ty),tl) = unrebind rbnd
  (ty', i) <- tcType ty
  (tele', j) <- extendCtx (Sig x ty') $ tcTypeTele tl
  return (Cons ep (rebind (x, embed ty') tele'), max i j)


--------------------------------------------------------
-- Using the typechecker for decls and modules and stuff
--------------------------------------------------------

-- | Typecheck a collection of modules. Assumes that each module
-- appears after its dependencies. Returns the same list of modules
-- with each definition typechecked
tcModules :: [Module] -> TcMonad [Module]
tcModules = foldM tcM []
  -- Check module m against modules in defs, then add m to the list.
  where defs `tcM` m = do -- "M" is for "Module" not "monad"
          let name = moduleName m
          liftIO $ putStrLn $ "Checking module " ++ show name
          m' <- defs `tcModule` m
          return $ defs ++ [m']

-- | Typecheck an entire module.
tcModule :: [Module]        -- ^ List of already checked modules (including their Decls).
         -> Module          -- ^ Module to check.
         -> TcMonad Module  -- ^ The same module with all Decls checked and elaborated.
tcModule defs m' = do checkedEntries <- extendCtxMods importedModules $
                                          foldr tcE (return [])
                                                  (moduleEntries m')
                      return $ m' { moduleEntries = checkedEntries }
  where d `tcE` m = do
          -- Extend the Env per the current Decl before checking
          -- subsequent Decls.
          x <- tcEntry d
          case x of
            AddHint  hint  -> extendHints hint m
                           -- Add decls to the Decls to be returned
            AddCtx decls -> (decls ++) <$> extendCtxsGlobal decls m
        -- Get all of the defs from imported modules (this is the env to check current module in)
        importedModules = filter (\x -> ModuleImport (moduleName x) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Decl.
data HintOrCtx = AddHint Hint
               | AddCtx [Decl]

-- | Check each sort of declaration in a module
tcEntry :: Decl -> TcMonad HintOrCtx
tcEntry (Def n term) = do
  oldDef <- lookupDef n
  case oldDef of
    Nothing -> tc
    Just term' -> die term'
  where
    tc = do
      lkup <- lookupHint n
      case lkup of
        Nothing -> do (aterm, ty) <- inferType term
                      return $ AddCtx [Sig n ty, Def n aterm]
        Just ty ->
          let handler (Err ps msg) = throwError $ Err ps (msg $$ msg')
              msg' = disp [DS "When checking the term ", DD term,
                           DS "against the signature", DD ty]
          in do
            (eterm, ety) <- checkType term ty `catchError` handler
            -- Put the elaborated version of term into the context.
            return $ AddCtx [Sig n ety, Def n eterm]
    die term' =
      extendSourceLocation (unPosFlaky term) term $
         err [DS "Multiple definitions of", DD n,
              DS "Previous definition was", DD term']

tcEntry (Sig n ty) = do
  duplicateTypeBindingCheck n ty
  (ety,_) <- tcType ty
  return $ AddHint (Hint n ety)

tcEntry (Axiom n ty) = do
  duplicateTypeBindingCheck n ty
  (ety,_) <- tcType ty
  return $ AddCtx [Sig n ety, Def n (TrustMe (Annot (Just ety)))]

-- rule Decl_data
tcEntry decl@(Data t delta lev cs) =
  do -- Check that the telescope for the datatype definition is well-formed
     (edelta, i) <- tcTypeTele delta
     ---- check that the telescope provided
     ---  for each data constructor is wellfomed, and elaborate them
     ---  TODO: worry about universe levels also?
     let elabConstructorDef defn@(ConstructorDef pos d tele) =
            extendSourceLocation pos defn $
              extendCtx decl $
                extendCtxTele edelta $ ConstructorDef pos d . fst <$> tcTypeTele tele
     ecs <- mapM elabConstructorDef cs
     -- check that types are strictly positive.
     mapM_ (positivityCheck t) cs
     -- Implicitly, we expect the constructors to actually be different...
     let cnames = map (\(ConstructorDef _ c _) -> c) cs
     unless (length cnames == length (nub cnames)) $
       err [DS "Datatype definition", DD t, DS"contains duplicated constructors" ]
     -- finally, add the datatype to the env and perform action m
     return $ AddCtx [Data t edelta lev ecs]


-- | Make sure that we don't have the same name twice in the
-- environment. (We don't rename top-level module definitions.)
duplicateTypeBindingCheck :: TName -> Term -> TcMonad ()
duplicateTypeBindingCheck n ty = do
  -- Look for existing type bindings ...
  l  <- lookupTyMaybe n
  l' <- lookupHint    n
  -- ... we don't care which, if either are Just.
  case catMaybes [l,l'] of
    [] ->  return ()
    -- We already have a type in the environment so fail.
    ty':_ ->
      let (Pos p  _) = ty
          msg = [DS "Duplicate type signature ", DD ty,
                 DS "for name ", DD n,
                 DS "Previous typing was", DD ty']
       in
         extendSourceLocation p ty $ err msg

----------------------------------------------
-- Positivity Check
----------------------------------------------

-- | Determine if a data type only occurs in strictly positive positions in a
-- constructor's arguments.

positivityCheck
  :: (Fresh m, MonadError Err m, MonadReader Env m) =>
     TCName -> ConstructorDef -> m ()
positivityCheck tName (ConstructorDef _ cName tele)  = go tele
  where go Empty = return ()
        go (Cons _ rbnd) = do
          let ((_, unembed -> teleTy), rest) = unrebind rbnd
          occursPositive tName teleTy
            `extendErr`
            (text "When checking the constructor" <+> text cName)
          go rest


occursPositive  :: (Fresh m, MonadError Err m, MonadReader Env m) =>
                   TCName -> Term -> m ()
occursPositive tName (Pos p ty) =
  extendSourceLocation p ty $
    occursPositive tName ty
occursPositive tName (Pi _ bnd) = do
  ((_,unembed->tyA), tyB) <- unbind bnd
  when (tName `S.member` fv tyA) $
    err [DD tName, DS "occurs in non-positive position"]
  occursPositive tName tyB
occursPositive tName ty = do
  let children = subtrees ty
  mapM_ (occursPositive tName) children


-----------------------------------------------------------
-- Checking that pattern matching is exhaustive
-----------------------------------------------------------

-- | Given a particular type and a list of patterns, make
-- sure that the patterns cover all potential cases for that
-- type.
-- If the list of patterns starts with a variable, then it doesn't
-- matter what the type is, the variable is exhaustive. (This code
-- does not report unreachable patterns.)
-- Otherwise, the scrutinee type must be a type constructor, so the
-- code looks up the data constructors for that type and makes sure that
-- there are patterns for each one.
exhaustivityCheck :: Type -> [Pattern] -> TcMonad ()
exhaustivityCheck ty (PatVar x:_) = return ()
exhaustivityCheck ty pats = do
  (tcon, tys)     <- ensureTCon ty
  (delta,_,mdefs) <- lookupTCon tcon
  case mdefs of
    Just datacons -> loop pats datacons
      where
        loop [] [] = return ()
        loop [] dcons = err $ DS "Missing cases for" : ((\(ConstructorDef _ dc _) -> DD dc) <$> dcons)
        loop (PatVar x : _) dcons = return ()
        loop (PatCon dc args : pats') dcons = do
          (cd@(ConstructorDef _ _ tele, dcons')) <-
            removeDcon dc dcons
          let tele' = substTele delta tys tele
          let (aargs, pats'') = relatedPats dc pats'
          checkSubPats tele' (args:aargs)
          loop pats'' dcons'
    Nothing ->
      err [DS "Cannot determine constructors of", DD ty]

-- | Given a particular data constructor name and a list of data
-- constructor definitions, pull the definition out of the list and
-- return it paired with the remainder of the list.
removeDcon :: DCName -> [ConstructorDef] ->
              TcMonad (ConstructorDef, [ConstructorDef])
removeDcon dc (cd@(ConstructorDef _ dc' _):rest) | dc == dc' =
  return (cd, rest)
removeDcon dc (cd1:rest) = do
  (cd2, rr) <- removeDcon dc rest
  return (cd2, cd1:rr)
removeDcon dc [] = err [DS $ "Internal error: Can't find" ++ show dc]

-- | Given a particular data constructor name and a list of patterns,
-- pull out the subpatterns that occur as arguments to that data
-- constructor and return them paired with the remaining patterns.
relatedPats :: DCName -> [Pattern] -> ([[(Pattern,Epsilon)]], [Pattern])
relatedPats dc [] = ([],[])
relatedPats dc (PatCon dc' args : pats) | dc == dc' =
  let (aargs, rest) = relatedPats dc pats in
  (args:aargs, rest)
relatedPats dc (pc@(PatCon _ _):pats) =
  let (aargs, rest) = relatedPats dc pats in
  (aargs, pc:rest)
relatedPats dc (pc@(PatVar _):pats) = ([], pc:pats)

-- | Occurs check for the subpatterns of a data constructor. Given
-- the telescope specifying the types of the arguments, plus the
-- subpatterns identified by relatedPats, check that they are each
-- exhaustive.

-- for simplicity, this function requires that all subpatterns
-- are pattern variables.
checkSubPats :: Telescope -> [[(Pattern,Epsilon)]] -> TcMonad ()
checkSubPats Empty _ = return ()
checkSubPats (Cons _ (unrebind->((name,unembed->tyP),tele))) patss
  | not (null (concat patss)) = do
  let hds = map (fst . head) patss
  let tls = map tail patss
  case hds of
    (PatVar _ : []) -> checkSubPats tele tls
    _ -> err [DS "All subpatterns must be variables in this version."]
checkSubPats t ps =
  err [DS "Internal error in checkSubPats", DD t, DS (show ps)]


