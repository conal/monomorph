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
import Control.Arrow (arr)
-- import Control.Monad (unless)
import Data.List (isPrefixOf)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.String (fromString)

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
observing = False

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
     guardMsg (not (isEqPred ty)) "Predicate type"  -- *
     guardMsg (closedType ty) "Type has free variables"
     hasRepTc <- findTyConT (repName "HasRep")
     dict  <- prefixFailMsg "Couldn't build dictionary." $
              ( -- tryR (watchR "simplify-dict" simplifyE)
                -- tryR (watchR "bash-dict" bashE)
                id
              . {- watchR' "buildDictionaryT" -} buildDictionaryT)
                $* TyConApp hasRepTc [ty]
     repTc <- findTyConT (repName "Rep")
     (mkEqBox -> eq,ty') <- prefixFailMsg "normaliseTypeT failed: "$
                            normaliseTypeT Nominal $* TyConApp repTc [ty]
     return $ \ meth ->
       prefixFailMsg "apps' failed: " $
       -- tryR (watchR "bash-method-selection" bashE) .
       do m <- tryR inlineR . (Var <$> findIdT (repName meth))
          -- TODO: composition ev' <- (if ...) . (Var <$> ...)
          return $ 
                 mkApps m [Type ty,dict,Type ty',eq]

-- Would it be faster to also simplify/bash the dictionary so that we share that
-- much for multi-use? See notes for 2015-01-14.

-- Given that I'm pulling two methods out of a dictionary, maybe I can avoid
-- building the dictionary twice. Perhaps a function that returns (abst,repr')
-- and another that returns (abst',repr), with only one dictionary required to
-- construct both pairs.

hasRepMethodT :: TransformH Type (String -> ReExpr)
hasRepMethodT = (\ f -> \ s -> App <$> f s <*> id) <$> hasRepMethodF

-- TODO: Rethink these three names

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
            -- simplifyE .  -- must succeed
            do meth <- hasRepMethodT . exprTypeT
               meth "abst" . meth "repr'"

-- TODO: Refactor

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

-- Simplified version, leaving more work for another pass.
standardizeCase :: ReExpr
standardizeCase = watchR "standardizeCase" $
  caseReducePlusR .
  onScrutineeR (simplifyE . abstRepr')

-- TODO: For efficiency, try to narrow the scope of this simplifyE, and/or
-- replace with a more specific strategy.

-- More ambitious caseReduceR.
caseReducePlusR :: ReExpr
caseReducePlusR = go . acceptWithFailMsgR isCase "Not a case"
 where
   go =  caseReduceR False
      <+ (go . onScrutineeR unfoldSafeR)
      <+ (letAllR id go . letFloatCaseR)
      <+ (onAltRhss go . caseFloatCaseR)

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

-- Prepare to eliminate non-standard constructor applications (fully saturated).
standardizeCon :: ReExpr
standardizeCon = watchR "standardizeCon" $
                 tryR (watchR "standardizeCon simplify" simplifyE)
                  . go . rejectR isType
 where
   go = doit <+ (lamAllR id go . etaExpandR "eta")
   doit = appAllR id (appAllR unfoldMethod id)
        . (callDataConT >> abst'Repr)

-- TODO: Ensure that standardizeCon accomplishes its goal or fails.

-- Prepare to eliminate non-standard constructor applications (fully saturated).
standardizeCon' :: ReExpr
standardizeCon' = watchR "standardizeCon'" $
                  {- tryR simplifyE . -} go . rejectR isType
 where
   go = doit <+ (lamAllR id go . etaExpandR "eta")
   doit = id -- appAllR id (appAllR unfoldMethod id)
        . (callDataConT >> abst'Repr)

-- etaExpandR dies on Type t. Avoided via rejectR isType

-- TODO: somehow prevent standardizeCase and standardizeCon from looping.
-- Must I explicitly add other transformations?

-- For now, I'm simplifying after standardizeCon and standardizeCase, for easier
-- inspection.

-- To do: check that the transformations accomplished their goal (which will
-- require simplification).

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
caseDefaultR =
  do Case scrut wild _ [(_,[],body)] <- id
     case idOccInfo wild of
       IAmDead -> return body
       _       -> return (Let (NonRec wild scrut) body)

-- Examples go a little faster (< 3%) with the IAmDead test.

lintCheckE :: ReExpr
lintCheckE = watchR "lintCheckE" id

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
    , externC' "cse-prog" cseProg
    , externC' "cse-guts" cseGuts
    , externC' "cse-expr" cseExpr
    , externC' "let-float-expr" letFloatExprR
    , externC' "let-nonrec-subst-safer" letNonRecSubstSaferR
    , externC' "simplify-one-step" simplifyOneStepE
    , externC' "simplify-with-let-floating" simplifyWithLetFloatingR
    , externC' "lint-check" lintCheckE
    , externC' "standardize-con'" standardizeCon'
    , externC' "let-float-expr-no-cast" letFloatExprNoCastR
    , externC' "case-reduce-plus" caseReducePlusR
    , externC' "beta-reduce-plus-safer" betaReducePlusSafer
    , externC' "inline-head" inlineHeadR
    ]

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
