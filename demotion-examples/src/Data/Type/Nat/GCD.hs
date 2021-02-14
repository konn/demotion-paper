{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Nat.GCD where

import Data.Type.Bool (type (&&))
import Data.Type.Equality (TestEquality, testEquality, (:~:) (Refl), type (==))
import Data.Type.Natural (SBool (SFalse, STrue), SNat, sMod, sNat)
import Data.Void
import GHC.TypeNats (Mod, Nat)
import Unsafe.Coerce (unsafeCoerce)

-- from base

type GCD n m = GCD_ (n === 0) (m === 0) n m

type family GCD_ nEq0 mEq0 n m :: Nat where
  GCD_ 'True _ _ m = m -- n is zero; return m
  GCD_ _ 'True n _ = n -- m is zero; return n
  GCD_ 'False 'False n m = GCD_ (Mod m n === 0) 'False (Mod m n) n

-- >>> :kind GCD

sGCD :: SNat n -> SNat m -> SNat (GCD n m)
sGCD sn sm = case (sn %=== sZero, sm %=== sZero) of
  (STrue, _) -> sm
  (SFalse, STrue) -> sn
  (SFalse, SFalse) -> sGCD (sMod sm sn) sn

(%===) :: TestEquality f => f a -> f b -> SBool (a === b)
sa %=== sb = case testEquality sa sb of
  Just Refl -> STrue
  Nothing -> unsafeCoerce SFalse

sZero :: SNat 0
sZero = sNat

data Eql a b where
  Equal :: ((a == b) ~ 'True, (a === b) ~ 'True, a ~ b) => Eql a b

fromFalse :: (a === b) ~ 'False => a :~: b -> Void
fromFalse = \case

-- >>> :t NonEqual
-- NonEqual
--   :: forall k (n :: k) (m :: k).
--      (Empty (n :~: m), (n === m) ~ 'False, (n == m) ~ 'False) =>
--      Equality n m

type family a === b where
  a === a = 'True
  _ === _ = 'False

data TypeFlavour = IsCompound | IsSimple
  deriving (Read, Show, Eq, Ord)

type family FlavourOf (a :: k) :: TypeFlavour where
  FlavourOf (_ _) = 'IsCompound
  FlavourOf _ = 'IsSimple

type (====) :: k -> k -> Bool

type a ==== b = EqAux (FlavourOf a) (FlavourOf b) a b

-- >>> :kind! FlavourOf 12

type family
  EqAux
    (flavA :: TypeFlavour)
    (flavB :: TypeFlavour)
    (a :: k)
    (b :: k) ::
    Bool
  where
  EqAux 'IsCompound 'IsCompound (f x) (g y) =
    (f ==== g) && (x ==== y)
  EqAux 'IsSimple 'IsSimple a a = 'True
  EqAux _ _ _ _ = 'False

-- >>> sGCD (sNat @12) (sNat @30)
-- 6
