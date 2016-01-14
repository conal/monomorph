{-# LANGUAGE CPP, TupleSections, GADTs, TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

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

import Data.Monoid (Sum(..))

import TypeUnary.Vec

import Circat.Rep
import Circat.Pair
import Circat.RTree

#if 1
sumP :: Pair Int -> Int
sumP = sum

sumV0 = sum :: Vec N0 Int -> Int
sumV1 = sum :: Vec N1 Int -> Int
sumV2 = sum :: Vec N2 Int -> Int
sumV3 = sum :: Vec N3 Int -> Int
sumV4 = sum :: Vec N4 Int -> Int
sumV8 = sum :: Vec N8 Int -> Int
#endif

#if 1
sumT0  = sum :: Tree N0 Int -> Int
sumT1  = sum :: Tree N1 Int -> Int
sumT2  = sum :: Tree N2 Int -> Int
sumT3  = sum :: Tree N3 Int -> Int
sumT4  = sum :: Tree N4 Int -> Int
sumT5  = sum :: Tree N5 Int -> Int
sumT6  = sum :: Tree N6 Int -> Int
sumT7  = sum :: Tree N7 Int -> Int
sumT8  = sum :: Tree N8 Int -> Int
sumT16 = sum :: Tree N16 Int -> Int
#endif

#if 0
type N32 = N16 :+: N16
type N64 = N32 :+: N32

sumT32 = sum :: Tree N32 Int -> Int
sumT64 = sum :: Tree N64 Int -> Int
#endif

#if 0
type N128 =  N64 :+:  N64
type N256 = N128 :+: N128

sumT128 = sum :: Tree N128 Int -> Int
sumT256 = sum :: Tree N256 Int -> 'Int'
#endif

#if 1
type MV n = (Int -> Int) -> (Vec n Int -> Vec n Int)

fmapV0  = fmap :: MV N0
fmapV1  = fmap :: MV N1
fmapV2  = fmap :: MV N2
fmapV3  = fmap :: MV N3
fmapV4  = fmap :: MV N4
fmapV8  = fmap :: MV N8
fmapV16 = fmap :: MV N16
#endif

#if 0
type MT n = (Int -> Int) -> (RTree n Int -> RTree n Int)

fmapT0  = fmap :: MT N0
fmapT1  = fmap :: MT N1
fmapT2  = fmap :: MT N2
fmapT3  = fmap :: MT N3
fmapT4  = fmap :: MT N4
fmapT8  = fmap :: MT N8
fmapT16 = fmap :: MT N16
#endif
