{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Type.Singletons where

import Data.Kind
import Data.Type.Natural
  ( Equality (..),
    KnownNat,
    Nat,
    SBool (..),
    SNat,
    SOrdering (..),
    sNat,
  )
import qualified Data.Type.Natural as TN
import Unsafe.Coerce (unsafeCoerce)

type family Sing :: k -> Type

type instance Sing = SMaybe

class Known a where
  sing :: Sing a

instance KnownNat n => Known n where
  sing = sNat

instance Known '[] where
  sing = SNil

instance (Known x, Known xs) => Known (x ': xs) where
  sing = sing `SCons` sing

class SEqual k where
  (%~) :: Sing (a :: k) -> Sing b -> Equality a b

type instance Sing = SNat

type instance Sing = SList

data SList (xs :: [k]) where
  SNil :: SList '[]
  SCons :: Sing x -> SList xs -> SList (x ': xs)

data SMaybe (m :: Maybe k) where
  SNothing :: SMaybe 'Nothing
  SJust :: Sing a -> SMaybe ( 'Just a)

instance SEqual Nat where
  (%~) = (TN.%~)

instance SEqual Bool where
  STrue %~ STrue = Equal
  SFalse %~ SFalse = Equal
  STrue %~ SFalse = NonEqual
  SFalse %~ STrue = NonEqual

instance SEqual Ordering where
  SLT %~ SLT = Equal
  SGT %~ SGT = Equal
  SEQ %~ SEQ = Equal
  _ %~ _ = unsafeCoerce $ NonEqual @0 @1

type instance Sing = SBool

type instance Sing = SOrdering

instance Known 'True where
  sing = STrue

instance Known 'False where
  sing = SFalse

instance Known 'LT where
  sing = SLT

instance Known 'GT where
  sing = SGT

instance Known 'EQ where
  sing = SEQ

instance Known 'Nothing where
  sing = SNothing

instance Known k => Known ( 'Just k) where
  sing = SJust sing

instance SEqual k => SEqual (Maybe k) where
  SNothing %~ SNothing = Equal
  SJust l %~ SJust r = case l %~ r of
    Equal -> Equal
    NonEqual -> unsafeCoerce $ NonEqual @0 @1
  SNothing %~ SJust {} = unsafeCoerce $ NonEqual @0 @1
  SJust {} %~ SNothing = unsafeCoerce $ NonEqual @0 @1
