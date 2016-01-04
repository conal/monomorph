-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Examples
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Examples / tinkering. To run:
-- 
--   hermit TreeTest.hs -v0 -opt=Monomorph.Stuff Go.hss && ./Examples
--   
-- Alternatively, use a target in the Makefile, e.g., go (default).
-- 
-- Add 'resume' after Go.hss if you don't want to see the intermediate Core.
----------------------------------------------------------------------

module Examples where

-- TODO: explicit exports

trip1 :: (Int,Double,Bool)
trip1 = (3,pi,False)

