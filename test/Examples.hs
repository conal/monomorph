{-# LANGUAGE TupleSections, GADTs #-}
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

import Circat.Rep

import TypeUnary.Vec

import Circat.Pair
import Circat.RTree

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

sumV :: Num a => Vec n a -> a
sumV ZVec      = 0
sumV (a :< as) = a + sumV as

sumV0 :: Vec N0 Int -> Int
sumV0 = sumV

sumV1 :: Vec N1 Int -> Int
sumV1 = sumV

-- Running into trouble with Sum a / a coercion
sumV1' :: Vec N1 Int -> Int
sumV1' = sum

sumV2 :: Vec N2 Int -> Int
sumV2 = sumV

sumV4 :: Vec N4 Int -> Int
sumV4 = sumV

sumV8 :: Vec N8 Int -> Int
sumV8 = sumV

sumT :: Num a => Tree n a -> a
sumT (L a)      = a
sumT (B (u :# v)) = sumT u + sumT v

sumT0 :: Tree N0 Int -> Int
sumT0 = sumT

sumT1 :: Tree N1 Int -> Int
sumT1 = sumT

-- Running into trouble with Sum a / a coercion
sumT1' :: Tree N1 Int -> Int
sumT1' = sum

sumT2 :: Tree N2 Int -> Int
sumT2 = sumT

sumT3 :: Tree N3 Int -> Int
sumT3 = sumT

sumT4 :: Tree N4 Int -> Int
sumT4 = sumT

sumT8 :: Tree N8 Int -> Int
sumT8 = sumT
