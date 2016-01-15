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
import Control.Applicative (liftA2)

import TypeUnary.Vec

import Circat.Rep
import Circat.Pair
import Circat.RTree

type Unop a = a -> a
type Binop a = a -> Unop a

#if 0
sump :: Pair Int -> Int
sump = sum

sumv0  = sum :: Vec N0 Int -> Int
sumv1  = sum :: Vec N1 Int -> Int
sumv2  = sum :: Vec N2 Int -> Int
sumv3  = sum :: Vec N3 Int -> Int
sumv4  = sum :: Vec N4 Int -> Int
sumv8  = sum :: Vec N8 Int -> Int
sumv16 = sum :: Vec N16 Int -> Int
#endif

#if 0
sumt0  = sum :: Tree N0 Int -> Int
sumt1  = sum :: Tree N1 Int -> Int
sumt2  = sum :: Tree N2 Int -> Int
sumt3  = sum :: Tree N3 Int -> Int
sumt4  = sum :: Tree N4 Int -> Int
sumt5  = sum :: Tree N5 Int -> Int
sumt6  = sum :: Tree N6 Int -> Int
sumt7  = sum :: Tree N7 Int -> Int
sumt8  = sum :: Tree N8 Int -> Int
sumt16 = sum :: Tree N16 Int -> Int
#endif

#if 01
type N32 = N16 :+: N16
type N64 = N32 :+: N32

sumt32 = sum :: Tree N32 Int -> Int
sumt64 = sum :: Tree N64 Int -> Int
#endif

#if 0
type N128 =  N64 :+:  N64
type N256 = N128 :+: N128

sumt128 = sum :: Tree N128 Int -> Int
sumt256 = sum :: Tree N256 Int -> Int
#endif

#if 0
type MV n = Unop Int -> Unop (Vec n Int)

mapv0  = fmap :: MV N0
mapv1  = fmap :: MV N1
mapv2  = fmap :: MV N2
mapv3  = fmap :: MV N3
mapv4  = fmap :: MV N4
mapv8  = fmap :: MV N8
mapv16 = fmap :: MV N16
#endif

#if 0
type MT n = Unop Int -> Unop (RTree n Int)

mapt0  = fmap :: MT N0
mapt1  = fmap :: MT N1
mapt2  = fmap :: MT N2
mapt3  = fmap :: MT N3
mapt4  = fmap :: MT N4
mapt8  = fmap :: MT N8
mapt16 = fmap :: MT N16
#endif

#if 0
type LT n = Binop Int -> Binop (RTree n Int)

liftA2T0 = liftA2 :: LT N0
liftA2T1 = liftA2 :: LT N1
liftA2T2 = liftA2 :: LT N2
liftA2T3 = liftA2 :: LT N3
liftA2T4 = liftA2 :: LT N4
liftA2T8 = liftA2 :: LT N8

#endif

#if 1
pureT1 = pure :: Int -> RTree N1 Int

nat0 = nat :: Nat N0
nat1 = nat :: Nat N1
nat2 = nat :: Nat N2
nat8 = nat :: Nat N8
#endif
