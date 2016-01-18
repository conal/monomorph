{-# LANGUAGE CPP, ViewPatterns, LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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
-- Monomorphizing GHC Core
----------------------------------------------------------------------

module Monomorph.Stuff
  (externals,monomorphizeR,monoGutsR,detickE,observeProgR,simplifyR
  ) where

import Prelude hiding (id,(.))

import Control.Category (id,(.))
import Data.Functor (void)
import Control.Arrow (arr)
import Data.List (isPrefixOf)
import qualified Data.Set as S

-- #define CaseMono
#ifdef MonoCase
import Data.List (partition)
import Data.Traversable (mapAccumL)
import Data.Maybe (catMaybes,isJust)
import qualified Type  -- from GHC
#endif

import HERMIT.Core (CoreProg(..))
import HERMIT.Dictionary hiding (externals,simplifyR)
import qualified HERMIT.Dictionary as HD
import HERMIT.External (External)
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Name (HermitName)

import HERMIT.Extras hiding (simplifyE)

-- import Circat.Rep

-- TODO: Trim imports

{--------------------------------------------------------------------
    GHC and HERMIT utilities to be moved to HERMIT.Extras
--------------------------------------------------------------------}

lintCheckE :: ReExpr
lintCheckE = watchR "lintCheckE" id

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

-- TODO: What if variables from 'bind' occur freely in co?

-- Declutter diagnostic output in GHCi

detickE :: ReExpr
detickE = tickT id id (const id)

progBindsR :: ReBind -> ReProg
progBindsR b = go
 where
   go = progNilR <+ progConsAllR b go
   progNilR = progNilT ProgNil

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

nowatchR :: InCoreTC a => String -> RewriteH a -> RewriteH a
nowatchR _ = id

-- nowatchR = watchR

#endif

{--------------------------------------------------------------------
    HasRep dictionary construction and abst/repr
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
{--------------------------------------------------------------------
    Transformations
--------------------------------------------------------------------}

-- TODO: Refactor
-- TODO: Rethink these three names

-- Do one unfolding, and then a second one only if the inlining result is a
-- worker, as in the case of a method lifted to the top level.
unfoldMethod :: ReExpr
unfoldMethod = watchR "unfoldMethod" $
    tryR unfoldDollar  -- revisit
  . {- watchR "unfoldMethod simplify" -} simplifyE
  -- . observeR "unfoldMethod - post unfold"
  . unfoldR

-- TODO: Do I still need unfoldMethod, or can I use unfoldPolyR instead?

unfoldDollar :: ReExpr
unfoldDollar = watchR "unfoldDollar" $
               unfoldPredR (\ v _ -> isPrefixOf "$" (uqVarName v))

-- Prepare to eliminate non-standard constructor applications (fully saturated).
standardizeCon :: ReExpr
standardizeCon = watchR "standardizeCon" $
                 go . rejectR isType
 where
   go   = (lamAllR id go . etaExpandR "eta") <+ doit
   doit = appAllR id (appAllR unfoldMethod id)
        . (reallyCallDataCon >> abst'Repr)

-- *Really* a datacon call. Some casts satisfy callDataConT, perhaps due to the
-- representation of single-method dictionaries via a cast.
reallyCallDataCon :: FilterE
reallyCallDataCon =
  do void (acceptWithFailMsgR (not . isCast) "Cast") -- casts can appear as datacons
     void callDataConT
 where
   isCast (Cast {}) = True
   isCast _         = False

-- Simplified version, leaving more work for another pass.
standardizeCase :: ReExpr
standardizeCase = watchR "standardizeCase" $
  caseReducePlusR . onScrutineeR abstRepr'

-- TODO: For efficiency, try to narrow the scope of this simplifyE, and/or
-- replace with a more specific strategy.

-- More ambitious caseReduceR.
caseReducePlusR :: ReExpr
caseReducePlusR = setFailMsg "caseReducePlusR failed."
                  go . acceptWithFailMsgR isCase "Not a case"
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

#if 0
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
#endif

primNames :: S.Set String
primNames = S.fromList
             [ "GHC."++modu++"."++name | (modu,names) <- prims , name <- names ]
 where
   prims = [("Num",["+","-","*","negate","abs","signum","fromInteger"])]
   -- TODO: more classes & methods

isPrimVar :: Var -> Bool
isPrimVar v = fqVarName v `S.member` primNames

-- | Various single-step cast-floating rewrite
castFloatR :: ReExpr
castFloatR =
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

unfoldPolyR :: ReExpr
unfoldPolyR = watchR "unfoldPolyR" $
  do ty <- exprTypeT -- rejects Type t
     guardMsg (not (polyOrPredTy ty)) "Must not involve polymorphism or predicates"
     id -- watchR "unfold & simplify for unfoldPolyR"
       (tryR simplifyE . (unfoldDictCastR <+ unfoldPredSafeR (okay ty))) -- TODO: replace simplifyE
 where
   okay ty v args =  not (isPrimVar v && primTy)
                  && (isGlobalId v || if null args then isPolyTy vty else all okayArg args)
    where
      vty = varType v
      okayArg (Type _) = True
      okayArg arg      = isDictLikeTy (exprType arg)
      primTy = const True ty                     -- TODO: Fix

-- | Unfold under a cast of a dictionary. Corresponds to a single-method type class.
unfoldDictCastR :: ReExpr
unfoldDictCastR = watchR "unfoldDictCastR" $
                  castAllR (unfoldSafeR . acceptR (isDictLikeTy . exprType)) id

--    dictish :: Type -> Bool
--    dictish (coreView -> Just ty) = dictish ty
--    dictish (ForAllTy _ ty)       = dictish ty
--    dictish (FunTy dom ran)       = dictish dom || dictish ran
--    dictish ty                    = isDictLikeTy ty


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
  <+ nowatchR "letElimR" letElimR
  <+ nowatchR "letNonRecSubstSaferR" letNonRecSubstSaferR -- tweaked
  <+ nowatchR "caseReduceR" (caseReduceR False)
  <+ nowatchR "castFloatR" castFloatR
  <+ nowatchR "caseReducePlusR" caseReducePlusR
  <+ nowatchR "caseFloatCaseR" caseFloatCaseR
  <+ nowatchR "caseDefaultR" caseDefaultR

simplifyWithLetFloatingR :: ReLCore
simplifyWithLetFloatingR =
  setFailMsg "Nothing to simplify." $
  innermostR (promoteBindR recToNonrecR <+ promoteExprR rew)
 where
   rew =  simplifyOneStepE
       <+ nowatchR "letFloatExprNoCastR" letFloatExprNoCastR

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

-- | Monomorphize.
monomorphizeR :: ReCore
monomorphizeR = anytdR (promoteR monomorphizeE)

monomorphizeE :: ReExpr
monomorphizeE = repeatR (simplifyOneStepE <+ standardizeCase <+ standardizeCon <+ unfoldPolyR)

-- any-td (repeat (simplify-one-step <+ standardize-case <+ standardize-con <+ unfold-poly))

monoProgR :: ReProg
monoProgR = -- bracketR "monoProgR" $
            progBindsR (observeFailureR "Monomorphization failure" $
                        observeR "monoBindR" .
                        nonRecAllR id (tryR simplifyE . anytdE monomorphizeE))

-- TODO: Consider recursive as well. Maybe unnecessary, since I don't expect to
-- handle monomorphic recursive definitions (where monomorphizing won't cut recursion).

monoGutsR :: ReGuts
monoGutsR = modGutsR monoProgR

-- monoCoreR :: Injection ModGuts a => RewriteH a
-- monoCoreR = promoteR monoGutsR

observeProgR :: ReGuts
observeProgR = traceR "finish!"
               . modGutsR (observeR "program")
               . traceR "start!"

#ifdef MonoCase
{--------------------------------------------------------------------
    Attempts at case monomorphization/pruning.
--------------------------------------------------------------------}

-- Not working, and I don't know how to solve. See my journal for 2015-01-16.

-- -- Prune case expressions by dropping impossible alternatives and
-- -- type-specializing with information type equalities in coVars.
-- pruneCaseR :: ReExpr
-- pruneCaseR = watchR "pruneCaseR" $
--   do Case e w ty (map check -> mbAlts) <- id
--      guardMsg (not (all isJust mbAlts)) "No impossible alternatives"
--      return (Case e w ty (catMaybes mbAlts))
--  where
--    check :: CoreAlt -> Maybe CoreAlt
--    check lt@(_,vs,_) = lt <$ uncurry (tcUnifyTys (const BindMe))
--                                (unzip (coVarKind <$> filter isCoVar vs))

-- Oops. Since I don't substitute into RHSs in this version, I lose monomorphism.

pruneCaseR :: ReExpr
pruneCaseR = watchR "pruneCaseR" $
  do Case e w ty (map monoAlt -> mbAlts) <- id
     guardMsg (not (all isJust mbAlts)) "No impossible alternatives"
     return (Case e w ty (catMaybes mbAlts))

monoAlt :: CoreAlt -> Maybe CoreAlt
monoAlt (con,vs,rhs) = tweak <$> mbSub
 where
   tweak :: TvSubst -> CoreAlt
   tweak tvSub = (con,vs',substExpr (text "monoAlt") idSub' rhs)
    where
      -- TODO: Change from mapAccumL to foldMap, now that I'm not changing the pattern.
      (idSub',vs') = mapAccumL accum (tvSubstToSubst tvSub) vs
      accum :: Subst -> Var -> (Subst,Var)
      accum idSub v = (extendSubst idSub v (Var v'), v)
       where
         v' = setVarName
                (setVarType v (Type.substTy tvSub (varType v)))
                (varName v)  -- change
   (coVars,filter isId -> ids) = partition isCoVar vs
   mbSub = uncurry (tcUnifyTys (const BindMe))
             (unzip (coVarKind <$> filter isCoVar vs))

tvSubstToSubst :: TvSubst -> Subst
tvSubstToSubst (TvSubst in_scope tenv) =
  Subst in_scope emptyIdSubst tenv emptyVarEnv
 where
   Subst _ emptyIdSubst _ _ = emptySubst  -- emptyIdSubst not exported from CoreSubst

-- TODO: If I get it working, move pruneCaseR to HERMIT.Extras, and remove ghc dep here.
#endif

{--------------------------------------------------------------------
    Externals for interactive use
--------------------------------------------------------------------}

externals :: [External]
externals =
    [ externC' "abst-repr" abstRepr
    , externC' "abst'-repr" abst'Repr
    , externC' "abst-repr'" abstRepr'
    , externC' "standardize-case" standardizeCase
    , externC' "standardize-con" standardizeCon
    , externC' "unfold-method" unfoldMethod
    , externC' "unfold-dollar" unfoldDollar
    , externC' "cast-float-apps" castFloatApps
    , externC' "cast-float-case" castFloatCaseR
    , externC' "cast-float" castFloatR
    , externC' "unfold-poly" unfoldPolyR
    , externC' "unfold-dict-cast" unfoldDictCastR
    , externC' "simplify-was" HD.simplifyR
    , externC' "simplify" simplifyR  -- override HERMIT's simplify
    , externC' "simplify-with-let-floating" simplifyWithLetFloatingR
    , externC' "cast-float-let-rhs" castFloatLetRhsR
    , externC' "cast-float-let-body" castFloatLetBodyR
    , externC' "cast-cast" castCastR
    , externC' "optimize-cast" optimizeCastR
    , externC' "case-default" caseDefaultR
    , externC' "unfold-safe" unfoldSafeR
    , externC' "cse-guts" cseGutsR
    , externC' "cse-prog" cseProgR
    , externC' "cse-bind" cseBindR
    , externC' "cse-expr" cseExprR
    , externC' "let-float-expr" letFloatExprR
    , externC' "let-nonrec-subst-safer" letNonRecSubstSaferR
    , externC' "simplify-one-step" simplifyOneStepE
    , externC' "lint-check" lintCheckE
    , externC' "let-float-expr-no-cast" letFloatExprNoCastR
    , externC' "case-reduce-plus" caseReducePlusR
    , externC' "beta-reduce-plus-safer" betaReducePlusSafer
    , externC' "inline-head" inlineHeadR
    , externC' "really-call-data-con" (reallyCallDataCon >> id)

    , externC' "monomorphize" monomorphizeR
    , externC' "mono-guts" monoGutsR
    , externC' "detick" detickE
    , externC' "observe-prog" observeProgR
    ]

#if 0
    , externC' "prune-case" pruneCaseR
    , externC' "standardize-con'" standardizeCon'
    , externC' "beta-reduce-safe" betaReduceSafeR
    , externC' "inline-worker" inlineWorkerR
    , externC' "unfold-worker" unfoldWorkerR
    , externC' "bash-it" bashIt
    , externC' "bash-all" bashAll
    , externC' "is-dictish" isDictish
    , externC' "is-dict-like" isDictLike
    , externC' "inline-global" inlineGlobal
    , externC' "unfold-nonprim'" unfoldNonPrim' -- to eliminate
    , externC' "unfold-nonprim" unfoldNonPrim
#endif
