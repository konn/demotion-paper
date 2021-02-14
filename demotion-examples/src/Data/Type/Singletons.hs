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
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Data.Type.Singletons
  ( SEqual (..),
    Sing,
    SomeSing (..),
    FromJust,
    withPromoted,
    SomeSingSuchThat (..),
    Known (..),
    withKnown,
    SList (..),
    SMaybe (..),
    SOrdering (..),
    SBool (..),
    HasSing (..),
    All,
    ShowF (),
    trustMeNonEqual,
    unsafeTrustMeNonEqual,
    SEither (..),
    FMap,
    sFMap,
    type (<|>),
    LiftMaybe2,
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
    withSNat,
    type (===),
  )
import qualified Data.Type.Natural as TN
import GHC.Natural (Natural)
import GHC.TypeLits (TypeError)
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

class HasSing k where
  type Demoted k
  type Demoted k = k
  promote :: Demoted k -> SomeSing k
  demote :: Sing (a :: k) -> Demoted k

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

data SEither (eith :: Either l r) where
  SLeft :: Sing a -> SEither ( 'Left a)
  SRight :: Sing b -> SEither ( 'Right b)

type instance Sing = SEither

instance Known a => Known ( 'Left a) where
  sing = SLeft sing

instance Known a => Known ( 'Right a) where
  sing = SRight sing

sFMap :: (forall x. Sing x -> Sing (f x)) -> SMaybe may -> SMaybe (FMap f may)
sFMap _ SNothing = SNothing
sFMap f (SJust x) = SJust (f x)

type family FMap (f :: k -> k') (n :: Maybe k) :: Maybe k' where
  FMap _ 'Nothing = 'Nothing
  FMap f ( 'Just a) = 'Just (f a)

type family ma <|> mb where
  'Nothing <|> a = a
  'Just a <|> _ = 'Just a

infixl 3 <|>

type family LiftMaybe2 f ma mb where
  LiftMaybe2 _ 'Nothing _ = 'Nothing
  LiftMaybe2 _ _ 'Nothing = 'Nothing
  LiftMaybe2 f ( 'Just a) ( 'Just b) = 'Just (f a b)

withPromoted ::
  forall k r.
  HasSing k =>
  Demoted k ->
  (forall x. Sing (x :: k) -> r) ->
  r
withPromoted a f = case promote @k a of
  MkSomeSing sx -> f sx

instance HasSing a => HasSing [a] where
  type Demoted [a] = [Demoted a]
  promote [] = MkSomeSing SNil
  promote (x : xs) = withPromoted x $ \sx -> withPromoted xs $ \sxs ->
    MkSomeSing $ sx `SCons` sxs
  demote SNil = []
  demote (sx `SCons` sxs) = demote sx : demote sxs

instance HasSing k => HasSing (Maybe k) where
  type Demoted (Maybe k) = Maybe (Demoted k)
  promote Nothing = MkSomeSing SNothing
  promote (Just a) = case promote a of
    MkSomeSing sa -> MkSomeSing (SJust sa)
  demote SNothing = Nothing
  demote (SJust a) = Just $ demote a

instance (HasSing l, HasSing r) => HasSing (Either l r) where
  type Demoted (Either l r) = Either (Demoted l) (Demoted r)
  promote (Left l) = withPromoted l $ MkSomeSing . SLeft
  promote (Right r) = withPromoted r $ MkSomeSing . SRight
  demote (SLeft l) = Left $ demote l
  demote (SRight r) = Right $ demote r

instance HasSing Nat where
  type Demoted Nat = Natural
  promote n = withSNat n MkSomeSing
  demote = TN.toNatural

type family FromJust msg mb where
  FromJust err 'Nothing = TypeError err
  FromJust _ ( 'Just x) = x