{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-} 
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Mod.Internal where

import GHC.TypeLits
import Data.Proxy
import GHC.Exts
import Data.Type.Bool
import Data.Type.Equality
import Data.Kind
import Unsafe.Coerce

newtype SInt (n :: Nat) = SInt Int

class KnownMod n where
    intSing :: SInt n

data SomeMod where 
    SomeMod :: KnownMod n => Proxy n -> SomeMod

data WrapN a b = WrapN (KnownMod a => Proxy a -> b)

withSInt :: (KnownMod n => Proxy n -> b) -> SInt n -> Proxy n -> b
withSInt f n proxy = magicDict (WrapN f) n proxy

someModVal :: Int -> Maybe SomeMod
someModVal n 
    | n <= 1 = Nothing 
    | otherwise = 
        Just $ withSInt SomeMod (SInt n) Proxy

{-# INLINE CONLIKE modVal #-}
modVal :: forall n proxy. KnownMod n => proxy n -> Int
modVal _ = case intSing @n of SInt i -> i

instance ((2 <=?  n 
          || TypeError ('Text "Modulo " 
                        ':<>: 'ShowType n 
                        ':<>: 'Text " must be greater than one: ")) ~ 'True
         , KnownNat n) => KnownMod n where
    {-# INLINE CONLIKE intSing #-}
    intSing = SInt $ fromInteger $ natVal' @n proxy#

{-# INLINE unsafeRem #-}
unsafeRem :: Int -> Int -> Int
unsafeRem (I# x) (I# y) = I# (remInt# x y)

isPrime :: Int -> Bool
isPrime 1 = False
isPrime 2 = True
isPrime n 
    | even n = False
    | otherwise = all primeTest $ takeWhile (<n) [2,7,61]
    where
    (s, d) = split2Power (n-1)
    primeTest a 
        | x == 1 = True
        | otherwise = elem (n-1) $ take s $ iterate (\x -> x*x) x
        where x = modPow a d n

checkPrime :: forall n. KnownMod n => Proxy n -> Maybe (PrimeCert n)
checkPrime proxy = 
    case isPrime (modVal proxy) of
        False -> Nothing
        True -> Just foolCert 
            where
            foolCert :: PrimeCert n
            foolCert = unsafeCoerce (PrimeCert (Proxy @ '[]) (Proxy @ 1) :: PrimeCert 2)

modPow a 0 n = 1
modPow a d n = 
    let x = modPow a (div d 2) n ^(2::Int) `mod` n 
    in if even d then x else x * a `mod` n

split2Power :: Int -> (Int, Int)
split2Power = go 0
    where
    go !acc n | odd n = (acc, n)
              | otherwise = go (acc + 1) (div n 2)

type family CheckPrimeCert (n :: Nat) (l :: [Nat]) (a :: Nat) :: Constraint
    where
    CheckPrimeCert n l a = 
        ((IsFactorization (n-1) l 
            || TypeError (ShowType l :<>: Text " is not the prime factors of " :<>: ShowType n)) 
          &&
          (IsPrimeCert n l a 
            || TypeError (ShowType a :<>: Text " is not a generator of the multiplicative group modulo " 
                          :<>: ShowType n))) ~ True

type family IsFactorization (n :: Nat) (l :: [Nat]) :: Bool where
    IsFactorization 0 l = False
    IsFactorization 1 '[] = True
    IsFactorization 1 l = False
    IsFactorization n (p ': l) = Mod n p == 0 && IsFactorizationSub n p l (Mod n p)

type family  IsFactorizationSub n p l m where
    IsFactorizationSub n p l 0 = IsFactorizationSub (Div n p) p l (Mod (Div n p) p)
    IsFactorizationSub n p l _ = IsFactorization n l

type family IsPrimeCert (n :: Nat) (l :: [Nat]) (a :: Nat) :: Bool
    where
    IsPrimeCert n l a = PowMod a (n - 1) n == 1 && IsPrimeCertSub n l a

type family IsPrimeCertSub n l a :: Bool
    where
    IsPrimeCertSub n '[] a = True
    IsPrimeCertSub n (p ': l) a = 
        Not (PowMod a (Div (n - 1) p) n == 1) && IsPrimeCertSub n l a

data PrimeCert (n :: Nat) where
    PrimeCert :: CheckPrimeCert n l a => Proxy l -> Proxy a -> PrimeCert n

class KnownPrime n where
    primeCert :: PrimeCert n

type family PowMod (a :: Nat) (d :: Nat) (n :: Nat) :: Nat where
    PowMod a 0 n = 1
    PowMod a d n = PowModSub a d n (Mod d 2 == 0)

type family PowModSub (a :: Nat) (d :: Nat) (n :: Nat) (b :: Bool) where
    PowModSub a d n True = (Square (PowMod a (Div d 2) n) n) 
    PowModSub a d n False = 
            (Mod (Square (PowMod a (Div d 2) n) n GHC.TypeLits.* a) n)

type family Square (a :: Nat) (n :: Nat):: Nat where
    Square 1 n = 1 
    Square 0 n = 0 
    Square a n = Mod (a GHC.TypeLits.* a) n
