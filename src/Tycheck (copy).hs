-- This module contains the typechecker. It is a function from untyped ASTs
-- that are annotated with line/column number information to ASTs with
-- type annotations. By type annotations, we mean annotations on the the
-- internal AST structures, not the type annotations provided by the
-- programmer on abstraction variable binders.

module Tycheck (
  TyInfo,
  tycheckProg
  ) where

import Control.Monad.State

import Ast
import Core (info_of_term, info_of_command)
import Gensym (GensymState, gensymInitState, nextSym)
import Parser
import Symtab (Symtab, empty, add, get)

-------------------------------------------
-- The type of info for typechecked terms.

data TyInfo =
  TyInfo { tyscheme_of :: TypeScheme }
  deriving (Show)

mkInfo ty = TyInfo { tyscheme_of = ty }

---------------------------
-- Typecheck a single term

tycheckTerm :: Show info => Symtab TypeScheme -> Term info ->
                 State GensymState (Either String (Term TyInfo))
-- TmVar
tycheckTerm ctx (TmVar fi id) = do
  let ts = Symtab.get id ctx
  case ts of
    Just ts' -> return $ Right $ TmVar (mkInfo ts') id
    Nothing  -> return $ Left $ "Type error: " ++ show fi

-- TmAbs
tycheckTerm ctx (TmAbs fi id ty t) = do
  t' <- tycheckTerm (add id (mkTypeScheme [] ty) ctx) t
  ts <- tyscheme_of_term t'
  return $ do
    ty' <- instantiate_tyscheme ctx ts
    let ts' = generalize_ty ctx (TyArrow ty ty')
    return $ TmAbs (mkInfo ts') id ty t'

-- TmApp
tycheckTerm ctx (TmApp fi t1 t2) = do
  t1' <- tycheckTerm ctx t1
  t2' <- tycheckTerm ctx t2
  let ty1 = ty_of_term t1'
  let ty2 = ty_of_term t2'
  case ty1 of
    TyArrow ty1' ty2' ->
      if ty1' /= ty2 then
        Left $ "Type error : " ++ show fi
      else
        return $ TmApp (mkInfo ty2') t1' t2'

-- TmTrue
tycheckTerm ctx (TmTrue fi) =
  return $ TmTrue (mkInfo TyBool)

-- TmFalse
tycheckTerm ctx (TmFalse fi) =
  return $ TmFalse (mkInfo TyBool)

-- TmIf
tycheckTerm ctx (TmIf fi t1 t2 t3) = do
  t1' <- assertTy ctx t1 TyBool
  t2' <- tycheckTerm ctx t2
  let ty2 = ty_of_term t2'
  t3' <- assertTy ctx t3 ty2
  return $ TmIf (mkInfo ty2) t1' t2' t3'

-- TmZero
tycheckTerm ctx (TmZero fi) =
  return $ TmZero (mkInfo TyNat)

-- TmSucc
tycheckTerm ctx (TmSucc fi t) = do
  t' <- assertTy ctx t TyNat
  return $ TmSucc (mkInfo TyNat) t'

-- TmPred
tycheckTerm ctx (TmPred fi t) = do
  t' <- assertTy ctx t TyNat
  return $ TmPred (mkInfo TyNat) t'
  
-- TmIszero
tycheckTerm ctx (TmIszero fi t) = do
  t' <- assertTy ctx t TyNat
  return $ TmIszero (mkInfo TyBool) t'

-- TmFix
tycheckTerm ctx (TmFix fi t) = do
  t' <- tycheckTerm ctx t
  let ty = ty_of_term t'
  case ty of
    TyArrow ty1' ty2' ->
      if ty1' == ty2' then
        return $ TmFix (mkInfo ty1') t'
      else
        Left $ "Type error: " ++ show (info_of_term t)
    _ ->
      Left $ "Type error: " ++ show (info_of_term t)

-------------------------------
-- Typecheck a single command.

tycheckCommand :: Show info => Symtab Type -> Command info ->
                    Either String (Command TyInfo)
-- CBind
tycheckCommand ctx (CBind fi id t) = do
  t' <- tycheckTerm ctx t
  return $ CBind (mkInfo (ty_of_term t')) id t'

-- CEval
tycheckCommand ctx (CEval fi t) = do
  t' <- tycheckTerm ctx t
  return $ CEval (mkInfo (ty_of_term t')) t'

-------------------------------
--Typecheck a list of commands.

tycheckCommands :: Show info => Symtab Type -> [Command info] ->
                     Either String [Command TyInfo]
tycheckCommands ctx [] = return []
tycheckCommands ctx (c:cs) = do
  c' <- tycheckCommand ctx c
  let ty = ty_of_command c'
  case c' of
    CBind _ id _ -> do
      cs' <- tycheckCommands (add id ty ctx) cs
      return $ c' : cs'
    _ -> do
      cs' <- tycheckCommands ctx cs
      return $ c' : cs'

--------------------------------
-- Typecheck an entire program.

tycheckProg :: Show info => Prog info -> Either String (Prog TyInfo)
tycheckProg p = do
  cs <- tycheckCommands empty (prog_of p)
  return $ Prog { pinfo_of = mkInfo TyBool, prog_of = cs }

---------
-- Misc.

assertTy :: Show info => Symtab Type -> Term info -> Type ->
              Either String (Term TyInfo)
assertTy ctx t ty = do
  t' <- tycheckTerm ctx t
  if ty_of_term t' /= ty then
    Left $ "Type error: " ++ show (info_of_term t)
  else
    Right $ t'

tyscheme_of_term :: Term TyInfo -> Type
tyscheme_of_term = tyscheme_of . info_of_term

ty_of_command :: Command TyInfo -> Type
ty_of_command = ty_of . info_of_command

generalize_ty :: Symtab TypeScheme -> Type -> TypeScheme
generalize_ty ctx ty =
  let fvs           = freeTypeVars ty
      generalizable = filter (\x -> not $ x `exists` ctx) fvs in
    mkTypeScheme generalizable ty

instantiate_tyscheme :: Symtab TypeScheme -> TypeScheme ->
  State GensymState Type
instantiate_tyscheme ctx ts =
  -- foldM (\acc id ->
  --           if id `exists` ctx then
  --             return acc
  --           else do
  --             x <- nextSym
  --             return $ typeSubstTypeScheme (TyVar id) (TyVar x) acc)
  -- ts (ts_tyvars_of ts)
  foldM (\acc id -> do
            x <- nextSym
            return $ typeSubstTypeScheme (TyVar id) (TyVar x) acc)
  ts (ts_tyvars_of ts)
