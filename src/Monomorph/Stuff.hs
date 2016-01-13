{-# LANGUAGE CPP, ViewPatterns, LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

module Monomorph.Stuff where

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

castFloatLetRhsR :: ReExpr
castFloatLetRhsR = watchR "castFloatLetRhsR" $
  withPatFailMsg ("castFloatLetRhsR failed: " ++
                 wrongExprForm "Let (NonRec v (Cast rhs co)) body") $
  do Let (NonRec v (Cast _ _)) _ <- id
     id
      . letAllR id letSubstR  -- or leave for later elimination
      . letFloatLetR
      . letAllR (nonRecAllR id (letFloatCastR . castAllR (letIntroR (uqVarName v)) id)) id

castFloatLetBodyR :: ReExpr
castFloatLetBodyR = watchR "castFloatLetBodyR" $
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

#define LintDie

#ifdef LintDie
watchR, nowatchR :: String -> Unop ReExpr
watchR lab r = lintingExprR lab (labeled observing (lab,r)) -- hard error

#else
-- watchR :: String -> Unop ReExpr
-- watchR lab r = labeled observing (lab,r) >>> lintExprR  -- Fail softly on core lint error.
watchR, nowatchR :: InCoreTC a => String -> RewriteH a -> RewriteH a
watchR lab r = labeled observing (lab,r)  -- don't lint

#endif

nowatchR = watchR

-- nowatchR _ = id

skipT :: Monad m => Transform c m a b
skipT = fail "untried"

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
              buildDictionaryT $* TyConApp hasRepTc [ty]
     repTc <- findTyConT (repName "Rep")
     (mkEqBox -> eq,ty') <- prefixFailMsg "normaliseTypeT failed: "$
                            normaliseTypeT Nominal $* TyConApp repTc [ty]
     return $ \ meth -> prefixFailMsg "apps' failed: " $
                        apps' (repName meth) [ty] [dict,Type ty',eq]

-- * I don't know why I need this test. Equality (a ~ b) types were somehow
-- squeaking through. Perhaps a bug in buildDictionaryT.

hasRepMethodT :: TransformH Type (String -> ReExpr)
hasRepMethodT = (\ f -> \ s -> App <$> f s <*> id) <$> hasRepMethodF

hasRepMethod :: String -> TransformH Type CoreExpr
hasRepMethod meth = hasRepMethodF >>= ($ meth)

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
            do meth <- hasRepMethodT . exprTypeT
               meth "abst" . meth "repr'"

-- Do one unfolding, and then a second one only if the inlining result is a
-- worker, as in the case of a method lifted to the top level.
unfoldMethod :: ReExpr
unfoldMethod = -- watchR "unfoldMethod" $
    tryR unfoldDollar
  . (tryR simplifyE . unfoldR)

-- Move to hermit-extras
unfoldDollar :: ReExpr
unfoldDollar = unfoldPredR (\ v _ -> isPrefixOf "$" (uqVarName v))

-- Simplified version, leaving more work for another pass.
standardizeCase :: ReExpr
standardizeCase = watchR "standardizeCase" $
 tryR simplifyE .
 onScrutineeR (appAllR unfoldMethod id . abstRepr')
 -- onScrutineeR (unfoldMethod . abstRepr')  -- also fine

-- Prepare to eliminate non-standard constructor applications (fully saturated).
standardizeCon :: ReExpr
standardizeCon = watchR "standardizeCon" $
                 tryR simplifyE . go . rejectR isType
 where
   go = doit <+ (lamAllR id go . etaExpandR "eta")
   doit = appAllR id (appAllR unfoldMethod id)
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
                 tryR simplifyE .
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

castFloat = -- watchR "castFloat" $
     {- watchR "castFloatAppR"  -} castFloatAppR
  <+ {- watchR "castFloatLamR"  -} castFloatLamR
  <+ {- watchR "castFloatCaseR" -} castFloatCaseR
  <+ {- watchR "castCastR"      -} castCastR
  <+ {- watchR "castElimReflR"  -} castElimReflR
  <+ {- watchR "optimizeCastR"  -} optimizeCastR
  <+ {- watchR "castElimSymR "  -} castElimSymR
  <+ castFloatLetRhsR
  <+ castFloatLetBodyR

--   <+ letFloatCastR

-- castFloat = watchR "castFloat" $
--      castFloatAppR <+ castFloatLamR <+ castFloatCaseR <+ castCastR
--   <+ castElimReflR <+ castElimSymR  <+ letFloatCastR
--   <+ castFloatLetRhsR <+ castFloatLetBodyR

#if 0
inlinePolyOrGlobal :: ReExpr
inlinePolyOrGlobal =
  watchR "inlinePolyOrGlobal" $
  configurableInlineR AllBinders (arr okay)
 where
   okay v = fqVarName v `S.notMember` primNames
         && not (isDictLikeTy ty)
         && (isGlobalId v || isPolyTy ty)
    where
      ty = varType v

#endif

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
     guardMsg (not (polyOrPredTy ty)) "Polymorphic or predicate"
     tidy . unfoldPredR okay
 where
   -- TODO: Revisit okay. What about when null args and v is polymorphic?
   okay v args =  not (isPrimVar v)
               && (if null args then isPolyTy (varType v) else all okayArg args)
   okayArg (Type _) = True
   okayArg arg      = isDictLikeTy (exprType arg)
   tidy = tryR simplifyE -- . tryR (bashUsingE [castFloat])

-- TODO: Try innermostR instead of bash

dictish :: Type -> Bool
dictish (coreView -> Just ty) = dictish ty
dictish (ForAllTy _ ty)       = dictish ty
dictish (FunTy dom ran)       = dictish dom || dictish ran
dictish ty                    = isDictLikeTy ty

-- isDictish :: ReExpr
-- isDictish = (acceptR dictish . exprTypeT) >> id

-- isDictLike :: ReExpr
-- isDictLike = (acceptR isDictLikeTy . exprTypeT) >> id

inlineGlobal :: ReExpr
inlineGlobal = watchR "inlineGlobal" $
  configurableInlineR AllBinders (arr okay)
 where
   okay v = isGlobalId v
         && not (isPrimVar v)
         && not (dictish (varType v))

okayToSubst :: CoreExpr -> Bool
okayToSubst (Var _)  = True
okayToSubst (Type _) = True
okayToSubst ty       = polyOrPredTy (exprType ty)

letNonRecSubstSaferR :: ReExpr
letNonRecSubstSaferR = letNonRecSubstSafeR' (arr okayToSubst)

simplifyE :: ReExpr
simplifyE = watchR "simplifyE" $ extractR simplifyR

-- simplifyE = extractR (simplifyR' (arr okayToSubst))

-- | Replacement for HERMIT's 'simplifyR'. Uses a more conservative
-- 'letNonRecSubstSafeR'', and adds 'castFloat'.
simplifyR :: ReLCore
simplifyR = 
  setFailMsg "Simplify failed: nothing to simplify." $
  innermostR (  promoteBindR recToNonrecR
             <+ promoteExprR ( unfoldBasicCombinatorR
                            <+ betaReducePlusR
                            <+ letNonRecSubstSafeR' (arr okayToSubst) -- tweaked
                            <+ caseReduceR False
                            <+ caseReduceUnfoldR False -- added
                            <+ letElimR
                            -- added
                            <+ castFloat
                            <+ caseFloatCaseR
                            )
             )

#if 0

bashWith :: [ReExpr] -> ReExpr
bashWith rs = bashExtendedWithE' (promoteR <$> rs)

bashIt :: ReExpr
bashIt = watchR "bashWith" bashE'

-- Expensive!
bashAll :: ReExpr
bashAll = watchR "bashAll" $
  bashWith [ standardizeCase
           , standardizeCon
           , unfoldNonPrim
           ]

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
    , externC' "inline-global" inlineGlobal
    , externC' "simplify" simplifyE  -- override HERMIT's simplify
    , externC' "simplify-was" HD.simplifyR
    , externC' "cast-float-let-rhs" castFloatLetRhsR
    , externC' "cast-float-let-body" castFloatLetBodyR
    , externC' "optimize-cast" optimizeCastR
    ]

--     , externC' "bash-it" bashIt
--     , externC' "bash-all" bashAll

--     , externC' "cse-guts" cseGuts
--     , externC' "cse-prog" cseProg
--     , externC' "cse-bind" cseBind
--     , externC' "cse-expr" cseExpr

--     , externC' "is-dictish" isDictish
--     , externC' "is-dict-like" isDictLike
