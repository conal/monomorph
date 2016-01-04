{-# LANGUAGE CPP, ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Monomorph.Stuff
-- Copyright   :  (c) 2015 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Experiments. Working up to a monomorphization GHC plugin.
----------------------------------------------------------------------

module Monomorph.Stuff where

-- TODO: explicit exports

import Prelude hiding (id,(.),(>>))
import qualified Prelude

import Control.Category (id,(.))
import Data.Functor ((<$>),void)
import Control.Applicative ((<*>))
import Control.Arrow (arr)
-- import Control.Monad (unless)
import Data.List (isPrefixOf)
import qualified Data.Map as M
import Data.String (fromString)

import HERMIT.Core (CoreDef(..),exprTypeM)
import HERMIT.Dictionary hiding (externals)
import HERMIT.External (External,external)
import HERMIT.GHC
import HERMIT.Kure hiding ((<$>),(<*>))
import HERMIT.Plugin (hermitPlugin,pass,interactive)
import HERMIT.Name (HermitName)
import HERMIT.Monad (getModGuts,getHscEnv)

import HERMIT.Extras

-- TODO: Trim imports

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
  do ty <- id
     -- The following check avoids a problem in buildDictionary.
     guardMsg (closedType ty) "Type has free variables"
     hasRepTc <- findTyConT (repName "HasRep")
     dict  <- buildDictionaryT $* TyConApp hasRepTc [ty]
     repTc <- findTyConT (repName "Rep")
     (mkEqBox -> eq,ty') <- normaliseTypeT Nominal $* TyConApp repTc [ty]
     return $ \ meth -> apps' (repName meth) [ty] [dict,Type ty',eq]

hasRepMethodT :: TransformH Type (String -> ReExpr)
hasRepMethodT = (\ f -> \ s -> App <$> f s <*> id) <$> hasRepMethodF

hasRepMethod :: String -> TransformH Type CoreExpr
hasRepMethod meth = hasRepMethodF >>= ($ meth)

-- TODO: Rethink these three names

-- | e ==> abst (repr e).  In Core, abst is
-- abst ty $hasRepTy ty' (Eq# * ty' (Rep ty) (sym (co :: Rep ty ~ ty'))),
-- where e :: ty, and co normalizes Rep ty to ty'.
abstReprR :: ReExpr
abstReprR = do meth <- hasRepMethodT . exprTypeT
               meth "abst" . meth "repr"

-- -- Do one unfolding, and then a second one only if the function name starts with
-- -- "$", as in the case of a method lifted to the top level.
-- unfoldMethodR :: ReExpr
-- unfoldMethodR = watchR "unfoldMethodR" $
--     tryR (tryR simplifyAll . unfoldPredR (\ v _ -> isPrefixOf "$" (uqVarName v)))
--   . (tryR simplifyAll . unfoldR)

-- unfoldMethodR = repeatR (tryR simplifyAll . unfoldR)

#if 0

standardizeCase :: ReExpr
#if 0
standardizeCase =
     caseReduceR True
  <+ caseReduceUnfoldR True
  <+ caseFloatCaseR
  <+ onScrutineeR (unfoldMethodR . watchR "abstReprR" abstReprR)
#else
standardizeCase =
    ( caseReduceR True <+
      ( anytdE ((onCaseAlts . onAltRhs) (caseReduceR True <+ caseReduceUnfoldR True))
      . anytdE caseFloatCaseR ) )
  . onScrutineeR (unfoldMethodR . watchR "abstReprR" abstReprR)
-- TODO: Will I need caseReduceUnfoldR twice?
#endif

-- For experimentation
standardizeCase' :: ReExpr
standardizeCase' =
    id
  . anytdE ((onCaseAlts . onAltRhs) (caseReduceR True <+ caseReduceUnfoldR True))
  . anytdE caseFloatCaseR
  . onScrutineeR (unfoldMethodR . watchR "abstReprR" abstReprR)


onScrutineeR :: Unop ReExpr
onScrutineeR r = caseAllR r id id (const id)

standardizeCon :: ReExpr
standardizeCon = go . rejectR isType
 where
   -- Handle both saturated and unsaturated constructors
   go =  (appAllR id unfoldMethodR . (void callDataConT >> abstReprR))
      <+ (lamAllR id standardizeCon . etaExpandR "eta")

-- etaExpandR dies on Type t. Avoided via rejectR isType

#endif

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (pass 0 . interactive externals)

externals :: [External]
externals =
    [ externC "abstRepr" abstReprR "..."
    ]
