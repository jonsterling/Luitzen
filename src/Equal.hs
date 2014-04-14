{- PiForall language, OPLSS, Summer 2013 -}

{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | Compare two terms for equality
module Equal (whnf,equate,ensureType,ensurePi, ensureTyEq,  ensureTCon, ensureQuotient, resolveEq) where

import Syntax
import Environment

import Unbound.LocallyNameless hiding (Data, Refl)
import Control.Monad.Error (catchError, zipWithM, zipWithM_)
import Control.Applicative ((<$>), (<*>), (<$), pure)
import Debug.Trace

-- | compare two expressions for equality
-- ignores type annotations during comparison
-- throws an error if the two types cannot be matched up
equate :: Term -> Term -> TcMonad ()
equate t1 t2 = do
  n1 <- whnf t1
  n2 <- whnf t2
  case n1 `aeq` n2 of
    True -> pure ()
    False ->
      case (n1, n2) of
        (Var x,  Var y)  | x == y -> pure ()
        (Lam ep1 bnd1, Lam ep2 bnd2) | ep1 == ep2 -> do
          Just (x, b1, _, b2) <- unbind2 bnd1 bnd2
          equate b1 b2
        (App a1 a2, App b1 b2) -> do
          equate a1 b1
          equateArgs a2 b2
        (Type i, Type j) | i == j -> pure ()
        (Pi ep1 bnd1, Pi ep2 bnd2) | ep1 == ep2 -> do
          Just ((x, unembed -> tyA1), tyB1,
                (_, unembed -> tyA2), tyB2) <- unbind2 bnd1 bnd2
          equate tyA1 tyA2
          equate tyB1 tyB2
        (Quotient a1 r1, Quotient a2 r2) -> do
          equate a1 a2
          equate r1 r2

        (Ann at1 _, at2) -> equate at1 at2
        (at1, Ann at2 _) -> equate at1 at2
        (Pos _ at1, at2) -> equate at1 at2
        (at1, Pos _ at2) -> equate at1 at2

        (TrustMe _, TrustMe _) -> pure ()

        (Let ep1 bnd1, Let ep2 bnd2) | ep1 == ep2 -> do
          Just ((x,unembed -> rhs1), body1,
                (_,unembed -> rhs2), body2) <- unbind2 bnd1 bnd2
          equate rhs1 rhs2
          equate body1 body2

        (TyEq a1 b1 annS1 annT1, TyEq a2 b2 annS2 annT2) -> do
          equate a1 a2
          equate b1 b2

        (Sigma bnd1, Sigma bnd2) -> do
          Just ((x, unembed -> tyA1), tyB1,
                (_, unembed -> tyA2), tyB2) <- unbind2 bnd1 bnd2
          equate tyA1 tyA2
          equate tyB1 tyB2

        (Prod a1 b1 _, Prod a2 b2 _) -> do
          equate a1 a2
          equate b1 b2

        (Pcase s1 bnd1 _, Pcase s2 bnd2 _) -> do
          equate s1 s2
          Just ((x,y), body1, _, body2) <- unbind2 bnd1 bnd2
          equate body1 body2

        (Subst at1 _ _, at2) -> equate at1 at2

        (at1, Subst at2 _ _) -> equate at1 at2

        (Contra a1 _, Contra a2 _) -> return ()


        (TCon c1 ts1, TCon c2 ts2) | c1 == c2 ->
          zipWithM_ equate ts1 ts2
        (DCon d1 a1 _, DCon d2 a2 _) | d1 == d2 ->
          zipWithM_ equateArgs a1 a2
        (Case s1 brs1 ann1, Case s2 brs2 ann2)
          | length brs1 == length brs2 -> do
          equate s1 s2
          -- require branches to be in the same order
          -- on both expressions
          let matchBr (Match bnd1) (Match bnd2) = do
                mpb <- unbind2 bnd1 bnd2
                case mpb of
                  Just (p1, a1, p2, a2) | p1 == p2 -> equate a1 a2
                  _ -> err [DS "Cannot match branches in", DD n1, DS "and", DD n2]
          zipWithM_ matchBr brs1 brs2

        (Smaller a b, Smaller c d) ->
          equate a c >> equate b d

        (Ind ep1 bnd1 ann1, Ind ep2 bnd2 ann2) | ep1 == ep2 -> do
          Just ((f,x), b1, _, b2) <- unbind2 bnd1 bnd2
          equate b1 b1

        (PiC ep1 bnd1, PiC ep2 bnd2) | ep1 == ep2 -> do
          Just ((x, unembed -> tyA1), (c1, tyB1),
                (_, unembed -> tyA2), (c2, tyB2)) <- unbind2 bnd1 bnd2
          equate tyA1 tyA2
          equate c1 c2
          equate tyB1 tyB2


        (_,_) -> do
          gamma <- getLocalCtx
          err [DS "Expected", DD t2, DS "which normalizes to", DD n2,
               DS "but found", DD t1,  DS "which normalizes to", DD n1,
               DS "in context:", DD gamma]

-- | Note: ignores erased args during comparison
equateArgs :: Arg -> Arg -> TcMonad ()
equateArgs (Arg Runtime t1) (Arg Runtime t2) = equate t1 t2
equateArgs a@(Arg Erased t1) (Arg Erased t2) = return ()
equateArgs a1 a2 = err [DS "Arguments do not match",
                       DD a1, DS "and", DD a2]

-------------------------------------------------------

-- | Ensure that the given type 'ty' is some 'Type i' for
-- some i
ensureType :: Term -> TcMonad Int
ensureType ty = do
  nf <- whnf ty
  case nf of
    Type i -> return i
    _  -> err [DS "Expected a Type i, instead found", DD nf]

-- | Ensure that the given type 'ty' is some sort of 'Pi' type
-- (or could be normalized to be such) and return the components of
-- the type.
-- Throws an error if this is not the case.
ensurePi :: Term -> TcMonad (Epsilon, TName, Term, Term, Maybe Term)
ensurePi ty = do
  nf <- whnf ty
  case nf of
    Pi ep bnd -> do
      ((x, unembed -> tyA), tyB) <- unbind bnd
      return (ep, x, tyA, tyB, Nothing)
    PiC ep bnd -> do
      ((x, unembed -> tyA), (constr, tyB)) <- unbind bnd
      return (ep, x, tyA, tyB, Just constr)
    _ -> err [DS "Expected a function type, instead found", DD nf]


-- | Ensure that the given 'ty' is an equality type
-- (or could be normalized to be such) and return
-- the LHS and RHS of that equality
-- Throws an error if this is not the case.
ensureTyEq :: Term -> TcMonad (Term,Term)
ensureTyEq ty = do
  nf <- whnf ty
  case nf of
    TyEq m n s t -> return (m, n)
    _ -> err [DS "Expected an equality type, instead found", DD nf]


-- | Ensure that the given type 'ty' is some tycon applied to
--  params (or could be normalized to be such).
-- Throws an error if this is not the case.
ensureTCon :: Term -> TcMonad (TCName, [Term])
ensureTCon aty = do
  nf <- whnf aty
  case nf of
    TCon n params -> return (n, params)
    _ -> err [DS "Expected a data type",
              DS ", but found", DD nf]

ensureQuotient :: Term -> TcMonad (Term, Term)
ensureQuotient qty = do
  nf <- whnf qty
  case nf of
    Quotient ty rel -> return (ty, rel)
    _ -> err [DS "Expected a quotient type",
              DS ", but found", DD nf]


-------------------------------------------------------
-- | Convert a term to its weak-head normal form.
-- If there is a variable in the active position with
-- a definition in the context, expand it.
whnf :: Term -> TcMonad Term

whnf (Var x) = do
  maybeDef <- lookupDef x
  case maybeDef of
    (Just d) -> whnf d
    _ -> return (Var x)

whnf (App t1 arg@(Arg _ t2)) = do
  nf <- whnf t1
  case nf of
    (Lam _ bnd) -> do
      ((x,_),body) <- unbind bnd
      whnf (subst x t2 body)
        -- only unfold applications of inductive definitions
    -- if the argument is a data constructor.
    (Ind _ bnd _) -> do
      nf2 <- whnf t2
      case nf2 of
        DCon{} -> do
          ((f,x),body) <- unbind bnd
          whnf $ subst x nf2 $ subst f nf body
        _ -> return $ App nf arg

    _ -> return $ App nf arg

whnf (Pcase a bnd ann) = do
  nf <- whnf a
  case nf of
    Prod b c _ -> do
      ((x,y), body) <- unbind bnd
      whnf (subst x b (subst y c body))
    _ -> return (Pcase nf bnd ann)


whnf (QElim p s rsp q) = do
  QBox x ann <- whnf q
  nx <- whnf x
  whnf (App s (Arg Runtime nx))

whnf (Ann tm ty) = do
  tm' <- whnf tm
  ty' <- whnf ty
  return $ Ann tm' ty'
whnf t@(Pos _ x) = whnf x
  -- err [DS "Unexpected position arg to whnf:", DD t]

whnf (Let ep bnd)  = do
  ((x,unembed->rhs),body) <- unbind bnd
  whnf (subst x rhs body)

whnf (Subst tm pf annot) = do
  tm' <- whnf tm
  pf' <- whnf pf
  case pf' of
    Refl _ _ -> return tm'
    _ -> return $ Subst tm' pf' annot


whnf (Case scrut mtchs annot) = do
  nf <- whnf scrut
  case nf of
    (DCon d args _) -> f mtchs where
      f (Match bnd : alts) = (do
          (pat, br) <- unbind bnd
          ss <- patternMatches (Arg Runtime nf) pat
          whnf (substs ss br))
            `catchError` \ _ -> f alts
      f [] = err $ [DS "Internal error: couldn't find a matching",
                    DS "branch for", DD nf, DS "in"] ++ map DD mtchs
    _ -> return (Case nf mtchs annot)


whnf (TyEq a b (Annot mtyA) (Annot mtyB)) = do
  na <- whnf a
  nb <- whnf b
  nmtyA <- case mtyA of
    Just tyA -> Just <$> whnf tyA
    Nothing -> return Nothing
  nmtyB <- case mtyB of
    Just tyB -> Just <$> whnf tyB
    Nothing -> return Nothing
  return $ TyEq na nb (Annot nmtyA) (Annot nmtyB)

whnf (TySquash a) = do
  na <- whnf a
  return $
    Quotient na $
      Lam Runtime $
        bind (string2Name "x", embed (Annot (Just na))) $
          Lam Runtime $
            bind (string2Name "y", embed (Annot (Just na))) $
              TyUnit

-- all other terms are already in WHNF
whnf tm = return tm

resolveEq :: Term -> Term -> Term -> Term -> TcMonad (Maybe Term)
resolveEq x y tyX tyY = do
  nx <- whnf x
  ny <- whnf y
  ntyX <- whnf tyX
  ntyY <- whnf tyY

  let fallback = (equate nx ny >> return (Just TyUnit)) `catchError` (\e -> return Nothing)

  case (ntyX, ntyY) of
    (TyUnit, TyUnit) -> return $ Just TyUnit
    (Quotient a1 r1, Quotient a2 r2) -> do
      equate a1 a2
      equate r1 r2
      case (nx, ny) of
        (QBox xa _, QBox xb _) ->
          return $ Just $ App (App r1 (Arg Runtime xa)) (Arg Runtime xb)
        _ -> fallback
    (Pi ep bnd1, Pi _ bnd2) -> do
      ((xn, etyA1), tyB1) <- unbind bnd1
      ((yn, etyA2), tyB2) <- unbind bnd2
      case (nx, ny) of
        (Lam _ b1, Lam _ b2) ->
          let body = TyEq (App nx (Arg ep (Var xn))) (App ny (Arg ep (Var yn))) (Annot (Just tyB1)) (Annot (Just tyB2)) in
          return $ Just $ Pi ep $ bind (xn, etyA1) $
                            Pi ep $ bind (yn, etyA2) $
                              Pi ep $ bind (string2Name "pxy", embed $ TyEq (Var xn) (Var yn) (Annot $ Just $ unembed etyA1) (Annot $ Just $ unembed etyA2))
                                body
        _ -> fallback
    (Sigma bnd1, Sigma bnd2) -> do
      ((_, eTyA1), tyB1) <- unbind bnd1
      ((_, eTyA2), tyB2) <- unbind bnd2
      case (nx, ny) of
        (Prod nx1 ny1 _, Prod nx2 ny2 _) ->
          return $ Just $ Sigma $ bind (string2Name "px", embed $ TyEq nx1 nx2 (Annot $ Just $ unembed eTyA1) (Annot $ Just $ unembed eTyA2))
                            (TyEq ny1 ny2 (Annot $ Just tyB1) (Annot $ Just tyB2))
        _ -> fallback
    _ -> fallback

-- | Determine whether the pattern matches the argument
-- If so return the appropriate substitution
patternMatches :: Arg -> Pattern -> TcMonad [(TName, Term)]
patternMatches (Arg _ t) (PatVar x) = return [(x, t)]
patternMatches (Arg Runtime t) pat@(PatCon d' pats) = do
  nf <- whnf t
  case nf of
    DCon d args _ | d == d' ->
       concat <$> zipWithM patternMatches args (map fst pats)
    _ -> err [DS "arg", DD nf, DS "doesn't match pattern", DD pat]
patternMatches (Arg Erased _) pat@(PatCon _ _) =
  err [DS "Cannot match against irrelevant args"]


