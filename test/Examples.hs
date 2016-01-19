{-# OPTIONS_GHC -fplugin=Monomorph.Plugin -O -fobject-code -dcore-lint #-}

-- {-# OPTIONS_GHC -fplugin=Monomorph.Interactive -O -fobject-code -dcore-lint #-}

-- The "-O" and "-fobject-code" flags are essential for unfolding, while
-- -dcore-lint is for debugging and may be removed later.

-- It was tricky to find these settings, because first version used in a ghci
-- session sticks. Strange, since [the GHC
-- guide](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/flag-reference.html)
-- say that "-O" and "-fobject-code" are both dynamic.

{-# LANGUAGE CPP, TupleSections, GADTs, TypeOperators, Rank2Types #-}
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
-- Examples / tinkering.
----------------------------------------------------------------------

module Examples where

-- TODO: explicit exports

import Data.Monoid (Sum(..))
import Control.Applicative (liftA2)

import TypeUnary.Vec

import Circat.Misc (Unop,Binop)
import Circat.Rep
import Circat.Pair
import Circat.RTree

-- fish :: Num a => a
-- fish = 3

-- sumt4 = sum  :: Tree  N4 Int -> Int
-- mapt4 = fmap :: Unop Int -> Unop (Tree N4 Int)

#if 1

-- t0 :: RTree N0 Int
-- t0 = L 5

t1 :: RTree N1 Int
t1 = B (L 3 :# L 4)

sumT :: Num a => Tree n a -> a
sumT (L a)      = a
sumT (B (u :# v)) = sumT u + sumT v

s1 :: Tree N1 Int -> Int
s1 = sumT
#endif

#if 0
reprp :: Pair Int -> Rep (Pair Int)
reprp = repr

sump :: Pair Int -> Int
sump = sum

sumv0  = sum :: Vec  N0 Int -> Int
sumv1  = sum :: Vec  N1 Int -> Int
sumv2  = sum :: Vec  N2 Int -> Int
sumv3  = sum :: Vec  N3 Int -> Int
sumv4  = sum :: Vec  N4 Int -> Int
sumv8  = sum :: Vec  N8 Int -> Int
sumv16 = sum :: Vec N16 Int -> Int

sumt0  = sum :: Tree  N0 Int -> Int
sumt1  = sum :: Tree  N1 Int -> Int
sumt2  = sum :: Tree  N2 Int -> Int
sumt3  = sum :: Tree  N3 Int -> Int
sumt4  = sum :: Tree  N4 Int -> Int
sumt5  = sum :: Tree  N5 Int -> Int
sumt6  = sum :: Tree  N6 Int -> Int
sumt7  = sum :: Tree  N7 Int -> Int
sumt8  = sum :: Tree  N8 Int -> Int
sumt16 = sum :: Tree N16 Int -> Int
#endif

#if 0
type N32  =  N16 :+: N16
type N64  =  N32 :+: N32
type N128 =  N64 :+:  N64
type N256 = N128 :+: N128

sumt32  = sum :: Tree N32 Int -> Int
sumt64  = sum :: Tree N64 Int -> Int
sumt128 = sum :: Tree N128 Int -> Int
sumt256 = sum :: Tree N256 Int -> Int
#endif

#if 0
type MV n = Unop Int -> Unop (Vec n Int)

mapv0  = fmap :: MV  N0
mapv1  = fmap :: MV  N1
mapv2  = fmap :: MV  N2
mapv3  = fmap :: MV  N3
mapv4  = fmap :: MV  N4
mapv8  = fmap :: MV  N8
mapv16 = fmap :: MV N16

type MT n = Unop Int -> Unop (RTree n Int)

mapt0  = fmap :: MT  N0
mapt1  = fmap :: MT  N1
mapt2  = fmap :: MT  N2
mapt3  = fmap :: MT  N3
mapt4  = fmap :: MT  N4
mapt8  = fmap :: MT  N8
mapt16 = fmap :: MT N16
#endif

#if 0
nat0 = nat :: Nat N0
nat1 = nat :: Nat N1
nat2 = nat :: Nat N2
nat4 = nat :: Nat N4
nat8 = nat :: Nat N8
#endif

#if 0

purep  = pure :: Int -> Pair Int

purev0 = pure :: Int -> Vec N0 Int
purev1 = pure :: Int -> Vec N1 Int
purev2 = pure :: Int -> Vec N2 Int

puret0 = pure :: Int -> RTree N0 Int
puret1 = pure :: Int -> RTree N1 Int
puret2 = pure :: Int -> RTree N2 Int
#endif

#if 0
type AP = Pair (Int -> Int) -> Pair Int -> Pair Int

applyp = (<*>) :: AP

type AV n = Vec n (Int -> Int) -> Vec n Int -> Vec n Int

applyv0 = (<*>) :: AV N0
applyv1 = (<*>) :: AV N1
applyv2 = (<*>) :: AV N2
applyv4 = (<*>) :: AV N4

type AT n = Tree n (Int -> Int) -> Tree n Int -> Tree n Int

applyt0 = (<*>) :: AT N0
applyt1 = (<*>) :: AT N1
applyt2 = (<*>) :: AT N2
applyt4 = (<*>) :: AT N4

#endif

#if 0
type LP = Binop Int -> Binop (Pair Int)

lifta2p = liftA2 :: LP

type LV n = Binop Int -> Binop (Vec n Int)

lifta2v0 = liftA2 :: LV N0
lifta2v1 = liftA2 :: LV N1
lifta2v2 = liftA2 :: LV N2
lifta2v3 = liftA2 :: LV N3
lifta2v4 = liftA2 :: LV N4
lifta2v8 = liftA2 :: LV N8

type LT n = Binop Int -> Binop (RTree n Int)

lifta2t0 = liftA2 :: LT N0
lifta2t1 = liftA2 :: LT N1
lifta2t2 = liftA2 :: LT N2
lifta2t3 = liftA2 :: LT N3
lifta2t4 = liftA2 :: LT N4
lifta2t8 = liftA2 :: LT N8
#endif

#if 0
add :: (Applicative f, Num a) => Binop (f a)
add = liftA2 (+)

addp = add :: Binop (Pair Int)

addv0 = add :: Binop (Vec N0 Int)
addv1 = add :: Binop (Vec N1 Int)
addv2 = add :: Binop (Vec N2 Int)
addv3 = add :: Binop (Vec N3 Int)
addv4 = add :: Binop (Vec N4 Int)
addv8 = add :: Binop (Vec N8 Int)

addt0 = add :: Binop (RTree N0 Int)
addt1 = add :: Binop (RTree N1 Int)
addt2 = add :: Binop (RTree N2 Int)
addt3 = add :: Binop (RTree N3 Int)
addt4 = add :: Binop (RTree N4 Int)
addt8 = add :: Binop (RTree N8 Int)
#endif

#if 0
type Tr g f = g (f Int) -> f (g Int)

transpose_pt1  = sequenceA :: Tr Pair (RTree N1)
transpose_pt2  = sequenceA :: Tr Pair (RTree N2)
transpose_v3t2 = sequenceA :: Tr (Vec N3) (RTree N2)
transpose_v5t4 = sequenceA :: Tr (Vec N5) (RTree N4)
#endif
