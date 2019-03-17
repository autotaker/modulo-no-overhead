{-# LANGUAGE GADTs, TypeFamilies, DataKinds, TypeOperators, UndecidableInstances, ExplicitForAll, TemplateHaskell, QuasiQuotes, TypeApplications #-}
module Data.Prime where
import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Equality
import Data.Proxy
import Language.Haskell.TH
import Data.Mod.Internal(isPrime)
import Data.Kind

type family CheckPrimeCert (n :: Nat) (l :: [Nat]) (a :: Nat) :: Constraint
    where
    CheckPrimeCert n l a = 
        ((IsFactorization (n-1) l 
            || TypeError (ShowType l :<>: Text " is not the prime factors of " :<>: ShowType n)) 
            ~ True
        , (IsPrimeCert n l a 
            || TypeError (ShowType a :<>: Text " is not a generator of the multiplicative group modulo " 
                          :<>: ShowType n)) 
            ~ True)

type family IsFactorization (n :: Nat) (l :: [Nat]) :: Bool where
    IsFactorization 1 '[] = True
    IsFactorization 1 l = False
    IsFactorization n (p ': l) = Mod n p == 0 && IsFactorizationSub n p l (Mod n p)

type family  IsFactorizationSub n p l m where
    IsFactorizationSub n p l 0 = IsFactorizationSub (Div n p) p l (Mod (Div n p) p)
    IsFactorizationSub n p l _ = IsFactorization n l

type family IsPrimeCert (n :: Nat) (l :: [Nat]) (a :: Nat) :: Bool
    where
    IsPrimeCert n '[] a = True
    IsPrimeCert n (p ': l) a = 
        Not (PowMod a (Div (n - 1) p) n == 1) && IsPrimeCert n l a

data PrimeCert (n :: Nat) where
    PrimeCert :: CheckPrimeCert n l a => Proxy l -> Proxy a -> Proxy n -> PrimeCert n

class KnownPrime n where
    primeCert :: PrimeCert n

type family IsPrime (n :: Nat) :: Bool where
    IsPrime 1 = False
    IsPrime 2 = True
    IsPrime 7 = True
    IsPrime 61 = True
    IsPrime n = 
        Mod n 2 == 1 
         && n <=? 4759123141 
         && IsPrimeSub 2 n (Split2Powers (n-1) 0) (n <=? 1)

type family IsPrimeSub a n p b where
    IsPrimeSub 2 n p b = Suspect 7 n p && IsPrimeSub 7 n p (n <=? 6) 
    IsPrimeSub 7 n p False = Suspect 61 n p 

type family Split2Powers (n :: Nat) (s :: Nat) :: (Nat, Nat) where
    Split2Powers n s = Split2PowersSub n s (Mod n 2 == 1)

type family Split2PowersSub (n :: Nat) (s :: Nat) (b :: Bool) :: (Nat, Nat) where
    Split2Powers n s True = '(s, n) 
    Split2Powers n s False = Split2Powers (Div n 2) (s + 1)

type family Suspect (a :: Nat) (n :: Nat) (p :: (Nat,Nat)) :: Bool where
    Suspect a n '(s, d) = SuspectSub n (PowMod a d n) s

type family SuspectSub (n :: Nat) (x :: Nat) (s :: Nat) :: Bool where
    SuspectSub n x s = x == 1 || SuspectLoop n x s
    
type family PowMod (a :: Nat) (d :: Nat) (n :: Nat) :: Nat where
    PowMod a 0 n = 1
    PowMod a d n = PowModSub a d n (Mod d 2 == 0)

type family PowModSub (a :: Nat) (d :: Nat) (n :: Nat) (b :: Bool) where
    PowModSub a d n True = (Square (PowMod a (Div d 2) n) n) 
    PowModSub a d n False = 
            (Mod (Square (PowMod a (Div d 2) n) n GHC.TypeLits.* a) n)

type family Square (a :: Nat) (n :: Nat):: Nat where
    Square a n = Mod (a GHC.TypeLits.* a) n

type family SuspectLoop (n :: Nat) (x :: Nat) (r :: Nat) :: Bool where
    SuspectLoop n x 0 = False
    SuspectLoop n x r = 
        (x == n - 1)  || SuspectLoop n (Square x n) (r - 1)
