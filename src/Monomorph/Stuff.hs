{-# LANGUAGE CPP, ViewPatterns, LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Monomorph.Stuff
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Working up to a monomorphization GHC plugin.
----------------------------------------------------------------------

module Monomorph.Stuff (plugin) where

-- TODO: explicit exports

import Prelude hiding (id,(.))
import qualified Prelude

import Control.Category (id,(.))
import Data.Functor ((<$>),void)
import Control.Applicative ((<*>))
import Data.Traversable (mapAccumL)
import Control.Arrow (arr)
-- import Control.Monad (unless)
import Data.List (isPrefixOf,partition)
import Data.Maybe (catMaybes)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.String (fromString)

import qualified Type  -- from GHC

import HERMIT.Core (CoreDef(..),exprTypeM,bindsToProg,progToBinds)
import HERMIT.Dictionary hiding (externals,simplifyR)
import qualified HERMIT.Dictionary as HD
import HERMIT.External (External,external)
import HERMIT.GHC
import HERMIT.Kure hiding ((<$>),(<*>))
import HERMIT.Plugin (hermitPlugin,pass,interactive)
import HERMIT.Name (HermitName,newGlobalIdH)
import HERMIT.Monad (getModGuts,getHscEnv)

import HERMIT.Extras hiding (simplifyE)

-- import Circat.Rep

-- TODO: Trim imports

{--------------------------------------------------------------------
    GHC and HERMIT utilities to be moved to HERMIT.Extras
--------------------------------------------------------------------}

onScrutineeR :: Unop ReExpr
onScrutineeR r = caseAllR r id id (const id)

-- | let v = rhs |> co in body
-- --> let v = (let v' = rhs in v') |> co in body
-- --> let v = (let v' = rhs in v' |> co) in body
-- --> let v' = rhs in (let v = v' |> co) in body
-- --> let v' = rhs in body[(v' |> co)/v]
castFloatLetRhsR :: ReExpr
castFloatLetRhsR =
  withPatFailMsg ("castFloatLetRhsR failed: " ++
                 wrongExprForm "Let (NonRec v (Cast rhs co)) body") $
  do Let (NonRec v (Cast _ _)) _ <- id
     id
      -- . error "castFloatLetRhsR bail"
      . letAllR id letSubstR  -- or leave for later elimination
      . letFloatLetR
      . letAllR (nonRecAllR id (letFloatCastR . castAllR (letIntroR (uqVarName v)) id)) id

castFloatLetBodyR :: ReExpr
castFloatLetBodyR =
  withPatFailMsg ("castFloatLetBodyR failed: " ++
                 wrongExprForm "Let bind (Cast body co)") $
  do Let bind (Cast body co) <- id
     return $
       Cast (Let bind body) co

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

observing :: Observing
observing = True

-- #define LintDie

#ifdef LintDie
watchR, nowatchR :: String -> Unop ReExpr
watchR lab r = lintingExprR lab (labeled observing (lab,r)) -- hard error
#else
-- watchR :: String -> Unop ReExpr
-- watchR lab r = labeled observing (lab,r) >>> lintExprR  -- Fail softly on core lint error.

watchR :: InCoreTC a => String -> RewriteH a -> RewriteH a
watchR lab r = labeled' observing (lab,r)  -- don't lint

-- Experiment. To replace watchR when labeled' replaces labeled. Rename both.
watchR' :: (InCoreTC a, Injection b LCoreTC)
       => String -> TransformH a b -> TransformH a b
watchR' lab r = labeled' observing (lab,r)  -- don't lint

nowatchR :: InCoreTC a => String -> RewriteH a -> RewriteH a
nowatchR _ = id

-- nowatchR = watchR

#endif

{--------------------------------------------------------------------
    Monomorphization
--------------------------------------------------------------------}

repName :: String -> HermitName
repName = moduledName "Circat.Rep"

closedType :: Type -> Bool
closedType = isEmptyVarSet . tyVarsOfType

hasRepMethodF :: TransformH Type (String -> TransformH a CoreExpr)
hasRepMethodF =
  prefixFailMsg "hasRepMethodF failed: " $
  do ty <- id
     -- The following check avoids a problem in buildDictionary.
     guardMsg (not (isEqPred ty)) "Predicate type"  -- still needed?
     guardMsg (closedType ty) "Type has free variables"
     hasRepTc <- findTyConT (repName "HasRep")
     dict  <- prefixFailMsg "Couldn't build dictionary." $
              buildDictionaryT $* TyConApp hasRepTc [ty]
     repTc <- findTyConT (repName "Rep")
     (mkEqBox -> eq,ty') <- prefixFailMsg "normaliseTypeT failed: "$
                            normaliseTypeT Nominal $* TyConApp repTc [ty]
     return $ \ meth -> prefixFailMsg "apps' failed: " $
                        apps' (repName meth) [ty] [dict,Type ty',eq]

-- Would it be faster to also simplify/bash the dictionary so that we share that
-- much for multi-use? See notes for 2015-01-14.

-- Given that I'm pulling two methods out of a dictionary, maybe I can avoid
-- building the dictionary twice. Perhaps a function that returns (abst,repr')
-- and another that returns (abst',repr), with only one dictionary required to
-- construct both pairs.

hasRepMethodT :: TransformH Type (String -> ReExpr)
hasRepMethodT = (\ f -> \ s -> App <$> f s <*> id) <$> hasRepMethodF

-- In Core, abst is
-- abst ty $hasRepTy ty' (Eq# * ty' (Rep ty) (sym (co :: Rep ty ~ ty'))),
-- where e :: ty, and co normalizes Rep ty to ty'.

-- | e ==> abst (repr e).
abstRepr :: ReExpr
abstRepr = -- watchR "abstRepr" $
           do meth <- hasRepMethodT . exprTypeT
              meth "abst" . meth "repr"

-- | e ==> abst' (repr e).
abst'Repr :: ReExpr
abst'Repr = -- watchR "abst'Repr" $
            do meth <- hasRepMethodT . exprTypeT
               meth "abst'" . meth "repr"

-- | e ==> abst (repr' e).
abstRepr' :: ReExpr
abstRepr' = -- watchR "abstRepr'" $
            do meth <- hasRepMethodT . exprTypeT
               meth "abst" . meth "repr'"

-- TODO: Refactor
-- TODO: Rethink these three names

-- Do one unfolding, and then a second one only if the inlining result is a
-- worker, as in the case of a method lifted to the top level.
unfoldMethod :: ReExpr
unfoldMethod = -- watchR "unfoldMethod" $
    tryR unfoldDollar  -- revisit
  . tryR (watchR "unfoldMethod simplify" simplifyE)
  . unfoldR

-- TODO: Do I still need unfoldMethod, or can I use unfoldPoly instead?

unfoldDollar :: ReExpr
unfoldDollar = watchR "unfoldDollar" $
               unfoldPredR (\ v _ -> isPrefixOf "$" (uqVarName v))

-- -- Prepare to eliminate non-standard constructor applications (fully saturated).
-- standardizeCon :: ReExpr
-- standardizeCon = watchR "standardizeCon" $
--                  go . rejectR isType
--  where
--    go   = (lamAllR id go . etaExpandR "eta") <+ doit
--    doit = appAllR id elimCon . (callDataConT >> abst'Repr)
--    elimCon = 


   -- elimCon = appAllR unfoldMethod id

-- Prepare to eliminate non-standard constructor applications (fully saturated).
standardizeCon :: ReExpr
standardizeCon = watchR "standardizeCon" $
                 go . rejectR isType
 where
   go   = (lamAllR id go . etaExpandR "eta") <+ doit
   doit = appAllR id (appAllR unfoldMethod id)
        . (callDataConT >> abst'Repr)

-- Simplified version, leaving more work for another pass.
standardizeCase :: ReExpr
standardizeCase = watchR "standardizeCase" $
  caseReducePlusR . onScrutineeR abstRepr'

-- TODO: For efficiency, try to narrow the scope of this simplifyE, and/or
-- replace with a more specific strategy.

-- More ambitious caseReduceR.
caseReducePlusR :: ReExpr
caseReducePlusR = go . acceptWithFailMsgR isCase "Not a case"
 where
   go =  caseReduceR False
      <+ (letAllR id go . letFloatCaseR)
      <+ (onAltRhss go . caseFloatCaseR)
      <+ (go . onScrutineeR (unfoldSafeR <+ simplifyE))

onAltRhss :: Unop ReExpr
onAltRhss r = caseAllR id id id (const (altAllR id (const id) r))

isCase :: CoreExpr -> Bool
isCase (Case {}) = True
isCase _         = False

-- | Like 'unfoldR', but without work duplication
unfoldSafeR :: ReExpr
unfoldSafeR = prefixFailMsg "unfoldSafeR failed: " $
  tryR betaReducePlusSafer . inlineHeadR

inlineHeadR :: ReExpr
inlineHeadR = {- watchR "inlineHeadR" -} go
 where
   go = appAllR go idR <+ inlineR

unfoldPredSafeR :: (Id -> [CoreExpr] -> Bool) -> ReExpr
unfoldPredSafeR p = callPredT p >> unfoldSafeR

betaReducePlusSafer :: ReExpr
betaReducePlusSafer = betaReduceSafePlusR (arr okayToSubst)

-- Since we're traversing top-down, the eta-expand will only happen if necessary.
-- etaExpandR dies on Type t. Avoided via rejectR isType
-- To do: check that standardizeCon accomplished its goal.

unfoldNonPrim :: ReExpr
unfoldNonPrim =
  unfoldNonPrim' <+ (castAllR unfoldNonPrim' id . castFloatApps)

unfoldNonPrim' :: ReExpr
unfoldNonPrim' = watchR "unfoldNonPrim" $
                 tryR (watchR "unfoldNonPrim' simplify" simplifyE) .
                 do ty <- exprTypeT
                    guardMsg (simple ty) "Non-simple arguments"
                    prefixFailMsg "Given primitive."
                      (unfoldPredR (\ v _ -> not (isPrim v)))
 where
   simple :: Type -> Bool
   simple (coreView -> Just ty) = simple ty
   simple (FunTy dom ran)       = simple dom && simple ran
   simple (ForAllTy _ ty)       = simple ty
   simple ty                    = not (isDictLikeTy ty)

isPrim :: Id -> Bool
isPrim v =
     isDictLikeTy (rangeType (varType v))
  || isPrimVar v
  -- || ...

-- isPrim = isPrefixOf "$" . uqVarName

primNames :: S.Set String
primNames = S.fromList
             [ "GHC."++modu++"."++name | (modu,names) <- prims , name <- names ]
 where
   prims = [("Num",["+","-","*","negate","abs","signum","fromInteger"])]
   -- TODO: more classes & methods

isPrimVar :: Var -> Bool
isPrimVar v = fqVarName v `S.member` primNames

rangeType :: Type -> Type
rangeType (coreView -> Just ty) = rangeType ty
rangeType (FunTy _          ty) = rangeType ty
rangeType (ForAllTy _       ty) = rangeType ty
rangeType                   ty  = ty

-- | Various single-step cast-floating rewrite
castFloat :: ReExpr
castFloat =
     {- watchR "castFloatAppR"     -} castFloatAppR
  <+ {- watchR "castFloatLamR"     -} castFloatLamR
  <+ {- watchR "castFloatCaseR"    -} castFloatCaseR
  <+ {- watchR "castCastR"         -} castCastR
  <+ {- watchR "castElimReflR"     -} castElimReflR
  <+ {- watchR "castElimSymR "     -} castElimSymR
  <+ {- watchR "optimizeCastR"     -} optimizeCastR
  <+ {- watchR "castFloatLetRhsR"  -} castFloatLetRhsR
  <+ {- watchR "castFloatLetBodyR" -} castFloatLetBodyR

isPolyTy :: Type -> Bool
isPolyTy (coreView -> Just ty) = isPolyTy ty
isPolyTy (ForAllTy {})         = True
isPolyTy _                     = False

polyOrPredTy :: Type -> Bool
polyOrPredTy (coreView -> Just ty) = polyOrPredTy ty
polyOrPredTy (ForAllTy {})         = True
polyOrPredTy (FunTy dom ran)       = polyOrPredTy dom || polyOrPredTy ran
polyOrPredTy ty                    = isPredTy ty

unfoldPoly :: ReExpr
unfoldPoly = watchR "unfoldPoly" $
  do ty <- exprTypeT -- rejects Type t
     guardMsg (not (polyOrPredTy ty)) "Must not involve polymorphism or predicates"
     id -- watchR "unfold & simplify for unfoldPoly"
       (tryR simplifyE . unfoldPredSafeR (okay ty)) -- TODO: replace simplifyE
 where
   okay ty v args =  not (isPrimVar v && primTy)
                  && (isGlobalId v || if null args then isPolyTy (varType v) else all okayArg args)
    where
      okayArg (Type _) = True
      okayArg arg      = isDictLikeTy (exprType arg)
      primTy = const True ty                     -- TODO: Fix

-- We exclude regular arguments (not.okayArg) so that the post-unfold simplifyE
-- doesn't have much to do.

letNonRecSubstSaferR :: ReExpr
letNonRecSubstSaferR = -- letNonRecSubstSafeR  -- while experimenting
                       letNonRecSubstSafeR' (arr okayToSubst)

okayToSubst :: CoreExpr -> Bool
okayToSubst (Var _)   = True
okayToSubst (Type _)  = True
okayToSubst (Lam _ e) = okayToSubst e
okayToSubst ty        = polyOrPredTy (exprType ty)

simplifyE :: ReExpr
simplifyE = {- watchR "simplifyE" $ -} extractR simplifyR

-- | Replacement for HERMIT's 'simplifyR'. Uses a more conservative
-- 'letNonRecSubstSafeR', and adds 'castFloat'.
simplifyR :: ReLCore
simplifyR = 
  setFailMsg "Simplify failed: nothing to simplify." $
  innermostR (promoteBindR recToNonrecR <+ promoteExprR simplifyOneStepE)

simplifyOneStepE :: ReExpr
simplifyOneStepE = -- watchR "simplifyOneStepE" $
     nowatchR "unfoldBasicCombinatorR" unfoldBasicCombinatorR
  <+ nowatchR "betaReduceR" betaReduceR
  <+ nowatchR "letNonRecSubstSaferR" letNonRecSubstSaferR -- tweaked
  <+ nowatchR "caseReduceR" (caseReduceR False)
  <+ nowatchR "letElimR" letElimR
  -- added
  <+ nowatchR "castFloat" castFloat
  <+ nowatchR "caseReduceUnfoldR" (caseReduceUnfoldR False) -- added
  <+ nowatchR "caseFloatCaseR" caseFloatCaseR
  <+ nowatchR "caseDefaultR" caseDefaultR


simplifyWithLetFloatingR :: ReLCore
simplifyWithLetFloatingR =
  setFailMsg "Nothing to simplify." $
  innermostR (promoteBindR recToNonrecR <+ promoteExprR rew)
 where
   rew =    simplifyOneStepE
         <+ watchR "letFloatExprNoCastR" letFloatExprNoCastR

-- | Like 'letFloatExprNoCastR but without 'letFloatCastR'
letFloatExprNoCastR :: ReExpr
letFloatExprNoCastR = setFailMsg "Unsuitable expression for Let floating." $
     letFloatArgR <+ letFloatAppR <+ letFloatLetR <+ letFloatLamR
  <+ letFloatCaseR <+ letFloatCaseAltR Nothing
  -- <+ letFloatCastR

-- | @case scrut wild of p -> body ==> let wild = scrut in body@, when p has no free
-- variables where the wildcard variable isn't used. If wild is a dead Id, don't
-- bother substituting.
caseDefaultR :: ReExpr
caseDefaultR = prefixFailMsg "caseDefaultR failed: " $
  do Case scrut wild _ [(_,[],body)] <- id
     case idOccInfo wild of
       IAmDead -> return body
       _       -> return (Let (NonRec wild scrut) body)

-- Examples go a little faster (< 3%) with the IAmDead test.

lintCheckE :: ReExpr
lintCheckE = watchR "lintCheckE" id

{--------------------------------------------------------------------
    Simplify case alternatives
--------------------------------------------------------------------}

monoAlt :: CoreAlt -> Maybe CoreAlt
monoAlt (con,vs,rhs) = tweak <$> mbSub
 where
   tweak :: TvSubst -> CoreAlt
   tweak tvSub = (con,vs',substExpr (text "monoAlt") idSub' rhs)
    where
      (idSub',vs') = mapAccumL accum (tvSubstToSubst tvSub) vs
      accum :: Subst -> Var -> (Subst,Var)
      accum idSub v = (extendSubst idSub v (Var v'), v')
       where
         v' = setVarType v (Type.substTy tvSub (varType v))
   (coVars,filter isId -> ids) = partition isCoVar vs
   mbSub = uncurry (tcUnifyTys (const BindMe))
             (unzip (coVarKind <$> filter isCoVar vs))

tvSubstToSubst :: TvSubst -> Subst
tvSubstToSubst (TvSubst in_scope tenv) =
  Subst in_scope emptyIdSubst tenv emptyVarEnv
 where
   Subst _ emptyIdSubst _ _ = emptySubst  -- emptyIdSubst not exported from CoreSubst

-- Prune case expressions by dropping impossible alternatives and
-- type-specializing with information type equalities in coVars.
pruneCaseR :: ReExpr
pruneCaseR = caseT id id id (const (arr monoAlt))
               (\ e w ty mbAlts -> Case e w ty (catMaybes mbAlts))

-- TODO: Move monoAlt and pruneCaseR to HERMIT.Extras, and remove ghc dep here.

{-

The core looks good to my eye, but Core Lint says otherwise:

    ...
    case ds2 of wild Int
      L (~# :: N1 ~N Z) a0 -> a0
      B n0 (~# :: N1 ~N S n0) ds3 ->
        case ds3 of wild0 Int
          (:#) u v ->
            (+) Int $fNumInt (sumT n0 Int $fNumInt u) (sumT n0 Int $fNumInt v)
    hermit<6> prune-case
    case ds2 of wild Int
      B n0 (~# :: N1 ~N S N0) ds3 ->
        case ds3 of wild0 Int
          (:#) u v ->
            (+) Int $fNumInt (sumT N0 Int $fNumInt u) (sumT N0 Int $fNumInt v)
    hermit<7> *** Core Lint errors : in result of Core plugin:  HERMIT0 ***
    <no location info>: Warning:
        In the pattern of a case alternative: (B n0_s8q2 :: *,
                                                 dt_d7Un :: N1 ~# S N0,
                                                 ds3_s8q3 :: Pair (Tree N0 Int))
        Argument value doesn't match argument type:
        Fun type:
            N1 ~# S n0_s8q2 -> Pair (Tree n0_s8q2 Int) -> RTree N1 Int
        Arg type: N1 ~# S N0
        Arg: dt_d7Un
    
Hrmph. I changed the type of `dt_d7Un` in the pattern. I guess it would
type-check if I also replaced `n0_s8q2` by `N0`, but Core `Alt` pattern
arguments must be variables. Hm.

Well, I can still remove impossible alternatives.

Maybe I can do something useful with the unifying substitutions if I enhance
them with *equality proofs* built on the coercion variables. For instance,
starting with `dt :: S Z ~N S m`, we could form something like `Nth 0 dt :: Z ~N
m` and then `Sym (Nth 0 dt) :: m ~N Z`.


-}

#if 0

getTvSubst :: Subst -> TvSubst
getTvSubst (Subst in_scope _ tenv _) = TvSubst in_scope tenv

type Alt b = (AltCon, [b], Expr b)

data TvSubst
  = TvSubst InScopeSet  -- The in-scope type and kind variables
            TvSubstEnv  -- Substitutes both type and kind variables

data Subst
  = Subst InScopeSet  -- Variables in in scope (both Ids and TyVars) /after/
                      -- applying the substitution
          IdSubstEnv  -- Substitution for Ids
          TvSubstEnv  -- Substitution from TyVars to Types
          CvSubstEnv  -- Substitution from CoVars to Coercions

substIdType :: Subst -> Id -> Id


setVarType :: Id -> Type -> Id
setVarType id ty = id { varType = ty }

mapAccumL :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)

#endif

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (pass 0 . interactive externals)

externals :: [External]
externals =
    [ externC' "abst-repr" abstRepr
    , externC' "abst'-repr" abst'Repr
    , externC' "abst-repr'" abstRepr'
    , externC' "standardize-case" standardizeCase
    , externC' "standardize-con" standardizeCon
    , externC' "unfold-method" unfoldMethod
    , externC' "unfold-dollar" unfoldDollar
    , externC' "unfold-nonprim'" unfoldNonPrim' -- to eliminate
    , externC' "unfold-nonprim" unfoldNonPrim
    , externC' "cast-float-apps" castFloatApps
    , externC' "cast-float-case" castFloatCaseR
    , externC' "cast-float" castFloat
    , externC' "unfold-poly" unfoldPoly
    , externC' "simplify" simplifyE  -- override HERMIT's simplify
    , externC' "simplify-was" HD.simplifyR
    , externC' "cast-float-let-rhs" castFloatLetRhsR
    , externC' "cast-float-let-body" castFloatLetBodyR
    , externC' "cast-cast" castCastR
    , externC' "optimize-cast" optimizeCastR
    , externC' "case-default" caseDefaultR
    , externC' "unfold-safe" unfoldSafeR
    , externC' "prune-case" pruneCaseR
    , externC' "cse-prog" cseProg
    , externC' "cse-guts" cseGuts
    , externC' "cse-expr" cseExpr
    , externC' "let-float-expr" letFloatExprR
    , externC' "let-nonrec-subst-safer" letNonRecSubstSaferR
    , externC' "simplify-one-step" simplifyOneStepE
    , externC' "simplify-with-let-floating" simplifyWithLetFloatingR
    , externC' "lint-check" lintCheckE
    , externC' "let-float-expr-no-cast" letFloatExprNoCastR
    , externC' "case-reduce-plus" caseReducePlusR
    , externC' "beta-reduce-plus-safer" betaReducePlusSafer
    , externC' "inline-head" inlineHeadR
    ]

--     , externC' "standardize-con'" standardizeCon'
--     , externC' "beta-reduce-safe" betaReduceSafeR

--     , externC' "inline-worker" inlineWorkerR
--     , externC' "unfold-worker" unfoldWorkerR

--     , externC' "bash-it" bashIt
--     , externC' "bash-all" bashAll

--     , externC' "cse-guts" cseGuts
--     , externC' "cse-prog" cseProg
--     , externC' "cse-bind" cseBind
--     , externC' "cse-expr" cseExpr

--     , externC' "is-dictish" isDictish
--     , externC' "is-dict-like" isDictLike
--     , externC' "inline-global" inlineGlobal
