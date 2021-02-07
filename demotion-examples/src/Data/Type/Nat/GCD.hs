{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Nat.GCD where

import Data.Type.Equality (testEquality, (:~:) (Refl), type (==))
import Data.Type.Natural (Equality (Equal, NonEqual), SBool (SFalse, STrue), SNat, SOrdering (..), sCmpNat, sMod, sNat, (%~))
import GHC.TypeNats (CmpNat, Mod, Nat)

type family GCD (n :: Nat) (m :: Nat) :: Nat where
  GCD 0 m = m
  GCD n 0 = n
  GCD n m = GCD (m `Mod` n) n

-- >>> :kind! GCD 12 9
-- GCD 12 9 :: Nat
-- = 3

sGCD :: SNat n -> SNat m -> SNat (GCD n m)
sGCD sn sm = case (testEquality sn sZero, testEquality sm sZero) of
  (Just Refl, _) -> sm
  (_, Just Refl) -> sn
  (Nothing, Nothing) -> sGCD (sMod sm sn) sn

sZero :: SNat 0
sZero = sNat
