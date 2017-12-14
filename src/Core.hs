-- This module provides utility functions for working with the inner
-- language (mostly related to evaluation of terms).

module Core (
  isValue,
  isNumericValue,
  termSubst,
  freeVars,
  genTypeVarsProg,
  boolOf,
  info_of_term,
  info_of_command,
  int_of_nat,
  freeTypeVars,
  Constr,
  TypeSubst,
  unify,
  tySubstAll,
  tyVarOf,
  TySubstClass(..)
  ) where

import Control.Monad.State
import qualified Data.Traversable as T

import Ast
import Gensym (nextSym)
import Symtab (Id(..), Symtab(..), map)

isValue :: Term info -> Bool
isValue (TmTrue _)      = True
isValue (TmFalse _)     = True
isValue (TmAbs _ _ _ _) = True
isValue tm              = isNumericValue tm

isNumericValue :: Term info -> Bool
isNumericValue (TmZero _)   = True
isNumericValue (TmSucc _ t) = isNumericValue t
isNumericValue _            = False

--------------
-- Unification

-- The type of constraint sets
type Constr = [(Type, Type)]

-- The type of type substitutions
type TypeSubst = [(Type, Type)]

unify :: Constr -> Either (Type, Type) TypeSubst
unify [] = Right []

-- Keep it simple, even if a little inefficient
unify ((s, t) : xs) =
  if s == t  then
    unify xs
  else if isTyVar s && (not $ s `elem` freeTypeVars t) then
    do
      rest <- unify $ typeSubstConstr t s xs
      return $ (s, t) : rest
  else if isTyVar t && (not $ t `elem` freeTypeVars s) then
    do
      rest <- unify $ typeSubstConstr s t xs
      return $ (t, s) : rest
  else if isTyArrow s && isTyArrow t then
      let (s1, s2) = tyArrowOf s
          (t1, t2) = tyArrowOf t in
        unify $ (s1, t1) : (s2, t2) : xs
  else
    Left (s, t)

-------------------------
-- Variable substitution

termSubst :: Id -> Term info -> Term info -> Term info
termSubst x e (TmVar fi y)       = if x == y then e else TmVar fi y
termSubst x e (TmAbs fi y ty t)  = if x == y then TmAbs fi y ty t else
                                     TmAbs fi y ty (termSubst x e t)
termSubst x e (TmApp fi t1 t2)   = TmApp fi (termSubst x e t1)
                                     (termSubst x e t2)
termSubst x e (TmIf fi t1 t2 t3) = TmIf fi (termSubst x e t1)
                                     (termSubst x e t2) (termSubst x e t3)
termSubst x e (TmSucc fi t)      = TmSucc fi (termSubst x e t)
termSubst x e (TmPred fi t)      = TmPred fi (termSubst x e t)
termSubst x e (TmIszero fi t)    = TmIszero fi (termSubst x e t)
termSubst x e (TmFix fi t)       = TmFix fi (termSubst x e t)
termSubst _ _ t                  = t

------------------------------
-- Type variable substitution

-- Substitute one type for another in a constraint set
typeSubstConstr :: Type -> Type -> Constr -> Constr
typeSubstConstr x y c = c

-- Substitute one type for another in a type
typeSubstType :: Type -> Type -> Type -> Type
typeSubstType s t (TyArrow ty1 ty2) =
  TyArrow (typeSubstType s t ty1) (typeSubstType s t ty2)
typeSubstType s t ty =
  if s == ty then t else ty
  
-- Substitute one type for another in a type scheme
typeSubstTypeScheme :: Type -> Type -> TypeScheme -> TypeScheme
typeSubstTypeScheme s t ts =
  case s of
    TyVar id -> 
      if id `elem` ts_tyvars_of ts then
        TypeScheme { ts_tyvars_of = ts_tyvars_of ts,
                     ts_ty_of     = ts_ty_of ts }
      else
        ts { ts_ty_of = typeSubstType s t (ts_ty_of ts) }
    _ -> ts { ts_ty_of = typeSubstType s t (ts_ty_of ts) }

-- Substitute one type for another in a lambda term
typeSubstTerm :: (TySubstClass info) => Type -> Type -> Term info -> Term info
typeSubstTerm s t (TmAbs fi i ty tm) =
  TmAbs (tySubst s t fi) i (if ty == s then t else ty) (typeSubstTerm s t tm)
typeSubstTerm s t (TmApp fi tm1 tm2) =
  TmApp (tySubst s t fi) (typeSubstTerm s t tm1) (typeSubstTerm s t tm2)
typeSubstTerm s t (TmIf fi tm1 tm2 tm3) =
  TmIf (tySubst s t fi) (typeSubstTerm s t tm1) (typeSubstTerm s t tm2)
    (typeSubstTerm s t tm3)
typeSubstTerm s t (TmSucc fi tm)   = TmSucc (tySubst s t fi)
                                     (typeSubstTerm s t tm)
typeSubstTerm s t (TmPred fi tm)   = TmPred (tySubst s t fi)
                                     (typeSubstTerm s t tm)
typeSubstTerm s t (TmIszero fi tm) = TmIszero (tySubst s t fi)
                                     (typeSubstTerm s t tm)
typeSubstTerm s t (TmFix fi tm)    = TmFix (tySubst s t fi)
                                     (typeSubstTerm s t tm)
typeSubstTerm s t (TmVar fi id)    = TmVar (tySubst s t fi) id
typeSubstTerm s t (TmTrue fi)      = TmTrue (tySubst s t fi)
typeSubstTerm s t (TmFalse fi)     = TmFalse (tySubst s t fi)
typeSubstTerm s t (TmZero fi)      = TmZero (tySubst s t fi)

-- Substitute one type for another in a typing context
typeSubstContext :: Type -> Type -> Symtab TypeScheme -> Symtab TypeScheme
typeSubstContext s t =
  Symtab.map (typeSubstTypeScheme s t)

-- A class for types that can receive type substitution
class TySubstClass a where
  tySubst :: Type -> Type -> a -> a

instance TySubstClass Type where
  tySubst = typeSubstType

instance TySubstClass TypeScheme where
  tySubst = typeSubstTypeScheme

instance TySubstClass info => TySubstClass (Term info) where
  tySubst = typeSubstTerm
  
-- instance TySubstClass a => TySubstClass (Symtab a) where
--   tySubst s t = Symtab.map (tySubst s t)

-- Fold over a list of individual substitutions on an instance of
-- TySubstClass
tySubstAll :: TySubstClass a => TypeSubst -> a -> a
tySubstAll tsubst x =
  foldl (\acc (s, t) -> tySubst s t acc) x tsubst

----------------------------
-- Free variables of a term

freeVars :: Term info -> [Id]
freeVars = aux []
  where
    aux bv (TmVar _ id)      = if id `elem` bv then [] else [id]
    aux bv (TmAbs _ id _ t)  = aux (id:bv) t
    aux bv (TmApp _ t1 t2)   = aux bv t1 ++ aux bv t2
    aux bv (TmIf _ t1 t2 t3) = aux bv t1 ++ aux bv t2 ++ aux bv t3
    aux bv (TmSucc _ t)      = aux bv t
    aux bv (TmPred _ t)      = aux bv t
    aux bv (TmIszero _ t)    = aux bv t
    aux bv (TmFix _ t)       = aux bv t
    aux _ _                  = []

---------------------------------
-- Free type variables of a type

-- Type variables with Ids not in the given list of Ids are considered
-- free
freeTypeVarsAux :: [Id] -> Type -> [Type]
freeTypeVarsAux ids (TyVar id)        = if id `elem` ids then [TyVar id] else []
freeTypeVarsAux ids (TyArrow ty1 ty2) = freeTypeVarsAux ids ty1 ++
                                        freeTypeVarsAux ids ty2
freeTypeVarsAux _ _                   = []

-- No bound Ids so all type variables are free
freeTypeVars :: Type -> [Type]
freeTypeVars = freeTypeVarsAux []

-- Forall quantified type variables of the type scheme are not free
freeTypeVarsOfTypeScheme :: TypeScheme -> [Type]
freeTypeVarsOfTypeScheme ts = freeTypeVarsAux (ts_tyvars_of ts) (ts_ty_of ts)

-- ---------------------------------
-- -- Free type variables of a term

-- freeTypeVars :: Term info -> [Id]
-- freeTypeVars (TmAbs _ _ ty t)          = freeTypeVarsOfType ty ++
--                                          freeTypeVars t
-- freeTypeVars (TmApp _ t1 t2)           = freeTypeVars t1 ++ freeTypeVars t2
-- freeTypeVars (TmIf _ t1 t2 t3)         = freeTypeVars t1 ++ freeTypeVars t2
--                                          ++ freeTypeVars t3
-- freeTypeVars (TmSucc _ t)              = freeTypeVars t
-- freeTypeVars (TmPred _ t)              = freeTypeVars t
-- freeTypeVars (TmIszero _ t)            = freeTypeVars t
-- freeTypeVars (TmFix _ t)               = freeTypeVars t
-- freeTypeVars _                         = []

------------------------------------------------------------------------
-- Fill in omitted typed annotations with auto-generated type
-- variables.  Uses prefix "?X_".

-- Generate fresh type variables for a type
genTypeVarsType :: Type -> State Int Type

-- Blank type variables (this is where fresh ids are used)
genTypeVarsType (TyVar (Id "")) = do
  id' <- nextSym "?X_"
  return (TyVar (Id id'))

-- Arrow types
genTypeVarsType (TyArrow ty1 ty2) = do
  ty1' <- genTypeVarsType ty1
  ty2' <- genTypeVarsType ty2
  return $ TyArrow ty1 ty2

-- All other types
genTypeVarsType ty = return ty

-- Generate fresh type variables for a single term (including its
-- subterms).
genTypeVarsTerm :: Term info -> State Int (Term info)

-- TmAbs
genTypeVarsTerm (TmAbs fi id ty t) = do
  ty' <- genTypeVarsType ty
  t' <- genTypeVarsTerm t
  return $ TmAbs fi id ty' t'

-- TmApp
genTypeVarsTerm (TmApp fi t1 t2) = do
  t1' <- genTypeVarsTerm t1
  t2' <- genTypeVarsTerm t2
  return (TmApp fi t1' t2')

-- TmIf
genTypeVarsTerm (TmIf fi t1 t2 t3) = do
  t1' <- genTypeVarsTerm t1
  t2' <- genTypeVarsTerm t2
  t3' <- genTypeVarsTerm t3
  return (TmIf fi t1' t2' t3')

-- TmSucc
genTypeVarsTerm (TmSucc fi t) = do
  t' <- genTypeVarsTerm t
  return (TmSucc fi t')

-- TmPred
genTypeVarsTerm (TmPred fi t) = do
  t' <- genTypeVarsTerm t
  return (TmPred fi t')

-- TmIszero
genTypeVarsTerm (TmIszero fi t) = do
  t' <- genTypeVarsTerm t
  return (TmIszero fi t')

-- TmFix
genTypeVarsTerm (TmFix fi t) = do
  t' <- genTypeVarsTerm t
  return (TmFix fi t')

-- TmVar, TmTrue, TmFalse, TmZero
genTypeVarsTerm t = return t

-- Generate fresh type variables for a single command
genTypeVarsCommand :: Command info -> State Int (Command info)
genTypeVarsCommand (CBind fi id t) = do
  t' <- genTypeVarsTerm t
  return $ CBind fi id t'
genTypeVarsCommand (CEval fi t) = do
  t' <- genTypeVarsTerm t
  return $ CEval fi t'

-- Generate fresh type variables for an entire program.
genTypeVarsProg :: Prog info -> Prog info
genTypeVarsProg p =
  p { prog_of = fst (runState (T.mapM genTypeVarsCommand (prog_of p))
                      0)}

--------
-- Misc

boolOf :: Term info -> Bool
boolOf (TmTrue _)  = True
boolOf (TmFalse _) = False
boolOf _           = error "boolOf: expected boolean term"

tyVarOf :: Type -> Maybe Id
tyVarOf (TyVar id) = Just id
tyVarOf _          = Nothing

isTyVar :: Type -> Bool
isTyVar (TyVar _) = True
isTyVar _         = False

isTyArrow :: Type -> Bool
isTyArrow (TyArrow _ _) = True
isTyArrow _             = False

tyArrowOf :: Type -> (Type, Type)
tyArrowOf (TyArrow s t) = (s, t)
tyArrowOf _             = error "tyArrowOf: expected arrow type"

info_of_term t =
  case t of
    TmVar fi _     -> fi
    TmAbs fi _ _ _ -> fi
    TmApp fi _ _   -> fi
    TmTrue fi      -> fi
    TmFalse fi     -> fi
    TmIf fi _ _ _  -> fi
    TmZero fi      -> fi
    TmSucc fi _    -> fi
    TmPred fi _    -> fi
    TmIszero fi _  -> fi
    TmFix fi _     -> fi

info_of_command c =
  case c of
    CBind fi _ _ -> fi
    CEval fi _   -> fi

int_of_nat t =
  case t of
    TmZero _   -> 0
    TmSucc _ t -> int_of_nat t + 1
    TmPred _ t -> int_of_nat t - 1
    _          -> error "int_of_nat: expected a nat term"

term_of_command c =
  case c of
    CBind _ _ t -> t
    CEval _ t   -> t

