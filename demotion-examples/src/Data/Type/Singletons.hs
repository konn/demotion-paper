{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Type.Singletons
  ( SEqual (..),
    Sing,
    SomeSing (..),
    SomeSingSuchThat (..),
    Known (..),
    withKnown,
    SList (..),
    SMaybe (..),
    SOrdering (..),
    SBool (..),
    Promotable (..),
    All,
    ShowF (),
    trustMeNonEqual,
    unsafeTrustMeNonEqual,
  )
where

import Data.Kind
import Data.Type.Equality ((:~:) (Refl), type (==))
import Data.Type.Natural
  ( Equality (..),
    KnownNat,
    Nat,
    SBool (..),
    SNat,
    SOrdering (..),
    sNat,
    type (===),
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
  SLT %~ _ = unsafeTrustMeNonEqual
  SGT %~ SGT = Equal
  SGT %~ _ = unsafeTrustMeNonEqual
  SEQ %~ SEQ = Equal
  SEQ %~ _ = unsafeTrustMeNonEqual

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
    NonEqual -> trustMeNonEqual
  SNothing %~ SJust {} = trustMeNonEqual
  SJust {} %~ SNothing = trustMeNonEqual

newtype WithKnown a r = WithKnown (Known a => r)

withKnown :: forall a r. Sing a -> (Known a => r) -> r
withKnown sn act = unsafeCoerce (WithKnown @a @r act) sn

class Promotable k where
  promote :: k -> SomeSing k

data SomeSing k where
  MkSomeSing :: Sing (a :: k) -> SomeSing k

data SomeSingSuchThat c where
  MkSomeSingSuchThat :: c a => Sing a -> SomeSingSuchThat c

type family All c keys :: Constraint where
  All c '[] = ()
  All c (k ': ks) = (c k, All c ks)

class Show (f a) => ShowF f a

instance Show (f a) => ShowF f a

trustMeNonEqual :: (a == b) ~ 'False => Equality a b
trustMeNonEqual = unsafeCoerce $ NonEqual @0 @1

unsafeTrustMeNonEqual :: Equality a b
unsafeTrustMeNonEqual = unsafeCoerce $ NonEqual @0 @1
