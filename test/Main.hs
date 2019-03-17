{-# LANGUAGE DataKinds, ScopedTypeVariables #-}

import Mod
import Text.Printf
import Data.Proxy
import GHC.TypeLits hiding(Mod)

type M = 1000000007

{-# NOINLINE testAdd #-}
testAdd :: Mod 107 -> Mod 107 -> Mod 107
testAdd x y = x + y

{-# NOINLINE testSub #-}
testSub :: Mod 0 -> Mod 0 -> Mod 0
testSub x y = x + y

{-# NOINLINE testMul #-}
testMul :: Mod M -> Mod M -> Mod M
testMul x y = x * y

{-# NOINLINE testDiv #-}
testDiv :: Mod M -> Mod M -> Mod M
testDiv x y = x / y

{-# NOINLINE testShow #-}
testShow :: Mod M -> String
testShow m = show m

{-# NOINLINE testComb #-}
testComb :: Int -> Int -> Int -> Int
testComb n r m =
    case someModVal m of 
        Nothing -> error $ "Invalid modulo: " ++ show m
        Just (SomeMod (_ :: Proxy nat)) -> 
            unMod (product (map fromIntegral [n-r+1..n]) 
                    / product (map fromIntegral [1..r]) :: Mod nat)

main :: IO ()
main = do
    let test f name x y = 
            putStrLn $ showString name . showChar ' ' 
                     . showsPrec 10 x . showChar ' ' 
                     . showsPrec 10 y . showString " = " . showsPrec 5 (f x y) $ ""
    test testAdd "add" (-1) 2
    test testSub "sub"  2 6
    test testMul "mul"  1000000 100000000
    test testDiv "div"  48209 58420802
    printf "testShow %s\n" $ show (testShow 54321)
    printf "testConv %s\n" $ show (testComb 100 50 1000000007)

