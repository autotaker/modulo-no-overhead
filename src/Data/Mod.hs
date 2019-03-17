{-# LANGUAGE GADTs #-} 
{-# LANGUAGE KindSignatures #-} 
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-} 
{-# LANGUAGE ScopedTypeVariables #-} 
{-# LANGUAGE Strict #-} 
{-# LANGUAGE UndecidableInstances #-} 
{-# LANGUAGE FlexibleInstances #-} 
{-# LANGUAGE RoleAnnotations #-} 



module Data.Mod (Mod, unMod, modulo, KnownMod, SomeMod(..), someModVal, KnownPrime, PrimeCert) where

import GHC.TypeLits hiding (Mod)
import Data.Ratio
import Data.Proxy
import Data.Mod.Internal

type role Mod representational
newtype Mod (n :: Nat) = Mod { unMod :: Int }
    deriving(Eq, Ord)

instance KnownMod n => Show (Mod n) where
    {-# INLINE show #-}
    show n = showM (unMod n) (modulo n)
    {-# INLINE showsPrec #-}
    showsPrec prec n = 
        showParen (prec >= 7) $ 
            shows (unMod n) 
            . showString " % " 
            . shows (modulo n)

{-# INLINE showM #-}
showM :: Int -> Int -> String
showM n m = show n ++ " % " ++ show m

{-# INLINE modulo #-}
modulo :: forall n. KnownMod n => Mod n -> Int
modulo = modVal

instance KnownPrime 3 where
    primeCert = PrimeCert (Proxy @ '[2]) (Proxy @2)
instance KnownPrime 5 where
    primeCert = PrimeCert (Proxy @ '[2]) (Proxy @2)
instance KnownPrime 7 where
    primeCert = PrimeCert (Proxy @ '[2,3]) (Proxy @3)
instance KnownPrime 1000000007 where
    primeCert = PrimeCert (Proxy @ '[2,500000003]) (Proxy @5)
instance KnownPrime 1000000009 where
    primeCert = PrimeCert (Proxy @ '[2,3,7,109,167]) (Proxy @13)

instance KnownMod n => Num (Mod n) where
    {-# INLINE (+) #-}
    x + y = Mod ((unMod x + unMod y) `unsafeRem` modulo x)
    {-# INLINE (*) #-}
    x * y = Mod ((unMod x * unMod y) `unsafeRem` modulo x)
    {-# INLINE negate #-}
    negate x = Mod (modulo x - unMod x)
    {-# INLINE (-) #-}
    x - y = Mod ((unMod x + (modulo x - unMod y)) `unsafeRem` modulo x)
    {-# INLINE fromInteger #-}
    fromInteger ~x = 
        case fromInteger x `unsafeRem` m of
            v | v < 0 -> Mod (m + v)
              | otherwise -> Mod v
        where m = modVal @n Proxy
    {-# INLINE abs #-}
    abs = id
    {-# INLINE signum #-}
    signum = const (Mod 1)

instance (KnownMod n, KnownPrime n) => Fractional (Mod n) where
    {-# INLINE fromRational #-}
    fromRational r = fromInteger (numerator r) / fromInteger (denominator r)
    {-# INLINE recip #-}
    recip a = Mod $ recipM (unMod a) (modulo a)

data EGCD = EGCD !Int !Int !Int

{-# NOINLINE recipM #-}
recipM :: Int -> Int -> Int
recipM x m | g /= 1 = error $ "No inverse for " ++ show x ++ " % " ++ show m 
           | s <  0 = s + m
           | otherwise = s
    where 
    EGCD s _ g = extgcd x m

extgcd :: Int -> Int -> EGCD
extgcd = go
    where 
    go a 0 = EGCD 1 0 a
    go a b = EGCD t (s - q * t) g
        where
        (q, r) = quotRem a b
        EGCD s t g = go b r
