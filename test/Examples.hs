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

trip1 :: (Int,Double,Bool)
trip1 = (3,pi,False)

trip1' :: Bool -> (Int,Double,Bool)
trip1' = (,,) 3 pi

trip2 :: (Int,Double,Bool)
trip2 = abst (repr' trip1)

ar1 :: (Int,Double,Bool) -> (Int,Double,Bool)
ar1 = abst . repr'

abst1 :: ((Int,Double),Bool) -> (Int,Double,Bool)
abst1 = abst

repr1 :: (Int,Double,Bool) -> ((Int,Double),Bool)
repr1 = repr

negateI :: Int -> Int
negateI = negate

addI :: Int -> Int
addI x = x + 3

sumP :: Pair Int -> Int
sumP = sum

-- sumV :: Num a => Vec n a -> a
-- sumV ZVec      = 0
-- sumV (a :< as) = a + sumV as

sumV0 :: Vec N0 Int -> Int
sumV0 = sum

sumV1 :: Vec N1 Int -> Int
sumV1 = sum

sumV2 :: Vec N2 Int -> Int
sumV2 = sum

sumV4 :: Vec N4 Int -> Int
sumV4 = sum

sumV8 :: Vec N8 Int -> Int
sumV8 = sum

sumT :: Num a => Tree n a -> a
sumT (L a)      = a
sumT (B (u :# v)) = sumT u + sumT v

sumT0 :: Tree N0 Int -> Int
sumT0 = sum

sumT1 :: Tree N1 Int -> Int
sumT1 = sum

#if 1

-- Eta-expanded variant
sumT1' :: Tree N1 Int -> Int
sumT1' t = sum t

sumT2 :: Tree N2 Int -> Int
sumT2 = sum

sumT3 :: Tree N3 Int -> Int
sumT3 = sum

sumT4 :: Tree N4 Int -> Int
sumT4 = sum

sumT4' :: Tree N4 Int -> Int
sumT4' = sumT

sumT5 :: Tree N5 Int -> Int
sumT5 = sum

sumT6 :: Tree N6 Int -> Int
sumT6 = sum

sumT7 :: Tree N7 Int -> Int
sumT7 = sum

sumT8 :: Tree N8 Int -> Int
sumT8 = sum

sumT16 :: Tree N16 Int -> Int
sumT16 = sum

#endif

#if 0

type N32 = N16 :+: N16
type N64 = N32 :+: N32

sumT32 :: Tree N32 Int -> Int
sumT32 = sum

sumT64 :: Tree N64 Int -> Int
sumT64 = sum

#endif

#if 0

type N128 =  N64 :+:  N64
type N256 = N128 :+: N128

sumT128 :: Tree N128 Int -> Int
sumT128 = sum

sumT256 :: Tree N256 Int -> Int
sumT256 = sum

#endif

#endif

#if 0

fiddle, faddle :: Int
fiddle = 2 + 3
faddle = 2 + 3

voop, boop :: Int
voop = let x = 2+3 in x*x
boop = let x = 2+3 in x*x

#endif

#if 0
p1 :: Pair Int -> Pair Int
p1 = fmap negate

sqr :: Int -> Int
sqr x = x * x

q :: Int
q = sqr (2 + 3)

pickle :: (Int -> Int) -> Int
pickle f = f 2 + f 3

qbert :: Int
qbert = pickle negate

-- voot :: RTree Z Int -> Sum Int
-- voot (L a) = Sum a

-- boop :: Sum Int
-- boop = voot (L 3)

boop :: Sum Int
boop = voot (L 3)
 where
   voot :: RTree Z Int -> Sum Int
   voot (L a) = Sum a
#endif

type Mty n = (Int -> Int) -> (RTree n Int -> RTree n Int)

fmapT0  = fmap :: Mty N0
fmapT1  = fmap :: Mty N1
fmapT2  = fmap :: Mty N2
fmapT4  = fmap :: Mty N4
fmapT8  = fmap :: Mty N8
fmapT16 = fmap :: Mty N16

-- foo :: Pair (RTree Z Int) -> RTree N1 Int
-- foo = B
