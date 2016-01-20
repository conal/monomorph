-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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
import Language.KURE (tryR)
import HERMIT.Kernel (CommitMsg(..))
import HERMIT.Plugin
import HERMIT.Plugin.Renderer (changeRenderer)
import HERMIT.Plugin.Types (PluginM)
import HERMIT.PrettyPrinter.Common
import Monomorph.Stuff (monomorphizeR)

plugin :: Plugin
plugin = hermitPlugin (pass 0 . const plug)
 where
   plug = tweakPretty >> apply (Always "monomorphize") (tryR monomorphizeR)

-- What's the CommitMsg about?

tweakPretty :: PluginM ()
tweakPretty = do changeRenderer "ascii"
                 setPrettyOptions (tweak def)
  where
   tweak = updateCoShowOption   Omit -- Kind
         . updateTypeShowOption Omit -- Show
      -- . updateWidthOption 80 -- default
