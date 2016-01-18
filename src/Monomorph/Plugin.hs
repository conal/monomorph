-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Monomorph.Interactive
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Interactive HERMIT-based plugin
----------------------------------------------------------------------

module Monomorph.Plugin where

-- TODO: explicit exports

import Prelude hiding ((.))

import Control.Category ((.))
import Data.Default.Class

import GhcPlugins (Plugin)
import Language.KURE (tryR,anybuR,promoteR)
import HERMIT.Kernel (CommitMsg(..))
import HERMIT.Kure (RewriteH,Core)
import HERMIT.GHC (ModGuts)
import HERMIT.Plugin
import HERMIT.Plugin.Renderer (changeRenderer)
import HERMIT.PrettyPrinter.Common
import HERMIT.Extras (ReGuts)
import Monomorph.Stuff

plugin :: Plugin
plugin = hermitPlugin (pass 0 . const plug)
 where
   plug = do changeRenderer "ascii"
             setPrettyOptions (tweakPretty def)
             apply (Always "monomorphize") rew
   rew :: RewriteH Core
   rew = tryR (promoteR monoGutsR)
         -- {- promoteR observeProgR . -} tryR monomorphizeR {- . promoteR observeProgR -}
    -- . tryR (anybuR (promoteR detickE)) -- for ghci break points

-- The modGutsR just lets tracing show the program defs instead of the module header.

tweakPretty :: PrettyOptions -> PrettyOptions
tweakPretty = updateCoShowOption   Omit -- Kind
            . updateTypeShowOption Omit -- Show
            -- . updateWidthOption 80 -- default
              
-- What's the CommitMsg about?

-- Oh! I just noticed setPrettyOptions in HERMIT.Plugin. Never mind.


-- foo opt st = setPrettyOpts st (updateTypeShowOption opt (cl_pretty_opts st))

-- tweakPrettyOpts = modify (flip setPrettyOpts 
