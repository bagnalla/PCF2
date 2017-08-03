-- This module contains the typechecker. It is a function from untyped ASTs
-- that are annotated with line/column number information to ASTs with
-- type annotations. By type annotations, we mean annotations on the the
-- internal AST structures, not the type annotations provided by the
-- programmer on abstraction variable binders.

module Tycheck (
  TyInfo,
  tycheckProg,
  runTycheck
  ) where


import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

import Data.Maybe (fromJust)

import Ast
import Core (info_of_term, info_of_command, freeTypeVars, Constr, TypeSubst,
             unify, tyVarOf, TySubstClass(..), tySubstAll)
import Gensym (nextSym)
import Parser
import Symtab (Symtab, Id(..), empty, add, get, exists)

-------------------------------------------
-- The type of info for typechecked terms.

data TyInfo =
  TyInfo { ty_of :: Type }
  deriving (Show)

mkInfo ty = TyInfo { ty_of = ty }

-- TyInfo can receive type substitution
instance TySubstClass TyInfo where
  tySubst s t fi = fi { ty_of = tySubst s t (ty_of fi) }

---------------
-- Typechecker

-- Following the example from "Monad Transformers Step by Step"
-- https://page.mi.fu-berlin.de/scravy/realworldhaskell/materialien/monad-transformers-step-by-step.pdf

type Context = Symtab TypeScheme

type TycheckM a = ReaderT Context
  (ExceptT String (StateT Int Identity)) a

runTycheck :: TycheckM a -> Either String a
runTycheck t = fst $ runIdentity (runStateT (runExceptT (runReaderT t empty))
                                  0)

-- Typecheck a variable
tycheckTerm :: Show info => Term info -> TycheckM (Term TyInfo, Constr)
tycheckTerm (TmVar fi id) = do
  -- 'asks' takes a function mapping the context to a value
  ts <- asks (Symtab.get id)
  case ts of
    Just ts' -> do
      ty <- instantiate_tyscheme ts'
      return $ (TmVar (mkInfo ty) id, [])
    Nothing  -> throwError $ "Type error: unbound identifier at " ++ show fi

-- Typecheck an abstraction
tycheckTerm (TmAbs fi id ty tm) = do
  (tm', c) <- local (add id (mkTypeScheme [] ty)) (tycheckTerm tm)
  case unify c of
    Left  (s, t) -> throwError $ "Type error: unable to unify " ++ show s ++
      " and " ++ show t ++ " at " ++ show fi
    Right tsubst -> do
      let ty' = ty_of_term tm'
      let fi' = mkInfo (tySubstAll tsubst (TyArrow ty ty'))
      let tm'' = TmAbs fi' id (tySubstAll tsubst ty) tm'
      return (tySubstAll tsubst tm'', c)

-- Typecheck an application
tycheckTerm (TmApp fi t1 t2) = do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  let ty1 = ty_of_term t1'
  let ty2 = ty_of_term t2'
  x <- nextSym "?Y_"
  let tyx = TyVar (Id x)
  let c = c1 ++ c2 ++ [(ty1, TyArrow ty2 tyx)]
  case unify c of
    Left  (s, t) -> throwError $ "Type error: unable to unify " ++ show s ++
      " and " ++ show t ++ " at " ++ show fi
    Right tsubst -> do
      let fi' = mkInfo (tySubstAll tsubst tyx)
      let tm' = TmApp fi' t1' t2'
      return (tySubstAll tsubst tm', c)

tycheckTerm (TmTrue fi) =
  return (TmTrue (mkInfo TyBool), [])

tycheckTerm (TmFalse fi) =
  return (TmFalse (mkInfo TyBool), [])

tycheckTerm (TmIf fi t1 t2 t3) = do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  (t3', c3) <- tycheckTerm t3
  let ty1 = ty_of_term t1'
  let ty2 = ty_of_term t2'
  let ty3 = ty_of_term t3'
  let c = c1 ++ c2 ++ c3 ++ [(ty1, TyBool), (ty2, ty3)]
  case unify c of
    Left  (s, t) -> throwError $ "Type error: unable to unify " ++ show s ++
      " and " ++ show t ++ " at " ++ show fi
    Right tsubst -> do
      let fi' = mkInfo (tySubstAll tsubst ty2)
      let tm' = TmIf fi' t1' t2' t3'
      return (tySubstAll tsubst tm', c)

tycheckTerm (TmZero fi) =
  return (TmZero (mkInfo TyNat), [])

tycheckTerm (TmSucc fi t) = do
  (t', c) <- tycheckTerm t
  let ty1 = ty_of_term t'
  let c' = c ++ [(ty1, TyNat)]
  case unify c' of
    Left  (s, t) -> throwError $ "Type error: unable to unify " ++ show s ++
      " and " ++ show t ++ " at " ++ show fi
    Right tsubst -> do
      let tm' = TmSucc (mkInfo TyNat) t'
      return (tySubstAll tsubst tm', c')
  
tycheckTerm (TmPred fi t) = do
  (t', c) <- tycheckTerm t
  let ty1 = ty_of_term t'
  let c' = c ++ [(ty1, TyNat)]
  case unify c' of
    Left  (s, t) -> throwError $ "Type error: unable to unify " ++ show s ++
      " and " ++ show t ++ " at " ++ show fi
    Right tsubst -> do
      let tm' = TmPred (mkInfo TyNat) t'
      return (tySubstAll tsubst tm', c')
  
tycheckTerm (TmIszero fi t) = do
  (t', c) <- tycheckTerm t
  let ty1 = ty_of_term t'
  let c' = c ++ [(ty1, TyNat)]
  case unify c' of
    Left  (s, t) -> throwError $ "Type error: unable to unify " ++ show s ++
      " and " ++ show t ++ " at " ++ show fi
    Right tsubst -> do
      let tm' = TmIszero (mkInfo TyBool) t'
      return (tySubstAll tsubst tm', c')

tycheckTerm (TmFix fi t) = do
  (t', c) <- tycheckTerm t
  let ty1 = ty_of_term t'
  y <- nextSym "?Y_"
  let tyy = TyVar (Id y)
  let c' = c ++ [(ty1, TyArrow tyy tyy)]
  case unify c' of
    Left  (s, t) -> throwError $ "Type error: unable to unify " ++ show s ++
      " and " ++ show t ++ " at " ++ show fi
    Right tsubst -> do
      let fi' = mkInfo (tySubstAll tsubst tyy)
      let tm' = TmFix fi' t'
      return (tySubstAll tsubst tm', c')

tycheckCommand :: Show info => Command info -> TycheckM (Command TyInfo)
tycheckCommand (CBind fi id t) = do
  (t', _) <- tycheckTerm t
  return $ CBind (mkInfo (ty_of_term t')) id t'

tycheckCommand (CEval fi t) = do
  (t', _) <- tycheckTerm t
  return $ CEval (mkInfo (ty_of_term t')) t'

tycheckCommands :: Show info => [Command info] -> TycheckM [Command TyInfo]
tycheckCommands [] = return []
tycheckCommands (com:coms) = do
  com' <- tycheckCommand com
  let ty = ty_of_command com'
  case com' of
    CBind _ id _ -> do
      ts <- generalize_ty ty
      coms' <- local (add id ts) (tycheckCommands coms)
      return $ com' : coms'
    _ -> do
      coms' <- tycheckCommands coms
      return $ com' : coms'

tycheckProg :: Show info => Prog info -> TycheckM (Prog TyInfo)
tycheckProg p = do
  coms <- tycheckCommands (prog_of p)
  return $ Prog { pinfo_of = mkInfo TyBool, prog_of = coms }

--------
-- Misc

ty_of_term :: Term TyInfo -> Type
ty_of_term = ty_of . info_of_term

ty_of_command :: Command TyInfo -> Type
ty_of_command = ty_of . info_of_command

generalize_ty :: Type -> TycheckM TypeScheme
generalize_ty ty = do
  ctx <- ask
  let fvs= freeTypeVars ty
  let generalizable = map (fromJust . tyVarOf)
        (filter (\(TyVar x) -> not $ x `exists` ctx) fvs)
  return $ mkTypeScheme generalizable ty

instantiate_tyscheme :: TypeScheme -> TycheckM Type
instantiate_tyscheme ts = do
  ts' <- foldM (\acc id -> do
                   x <- nextSym "?Y_"
                   return $ tySubst (TyVar id) (TyVar (Id x)) acc)
         ts (ts_tyvars_of ts)
  return (ts_ty_of ts')
