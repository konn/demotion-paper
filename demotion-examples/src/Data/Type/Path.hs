{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Path where

import Data.Kind
import Data.Type.Singletons
import GHC.Generics
import GHC.TypeLits

data Path a f where
  InV1 :: Path a V1
  InK1 :: Path a (K1 i a)
  InM1 :: Path a f -> Path a (M1 i c f)
  InL :: Path a f -> Path a (f :*: g)
  InR :: Path a g -> Path a (f :*: g)
  Both :: Path a f -> Path a g -> Path a (f :+: g)

traversePath :: Path a f -> f x -> a
traversePath InK1 (K1 a) = a
traversePath InV1 v1 = case v1 of
traversePath (InM1 p) (M1 f) = traversePath p f
traversePath (InL pth) (l :*: _) = traversePath pth l
traversePath (InR pth) (_ :*: r) = traversePath pth r
traversePath (Both pathL _) (L1 f) = traversePath pathL f
traversePath (Both _ pathR) (R1 g) = traversePath pathR g

type CalcPath a b = CalcPathF a (Rep b)

type CalcPathF :: forall a f -> Maybe (Path a f)
type family CalcPathF a f where
  CalcPathF a (K1 i a) = 'Just 'InK1
  CalcPathF a (M1 i c f) = FMap 'InM1 (CalcPathF a f)
  CalcPathF a (l :*: r) =
    FMap 'InL (CalcPathF a l) <|> FMap 'InR (CalcPathF a r)
  CalcPathF a (l :+: r) = LiftMaybe2 'Both (CalcPathF a l) (CalcPathF a r)
  CalcPathF a V1 = 'Just 'InV1
  CalcPathF _ _ = 'Nothing

type SPath :: Path a f -> Type
data SPath (path :: Path a f) where
  SInV1 :: SPath 'InV1
  SInK1 :: SPath 'InK1
  SInM1 :: SPath pth -> SPath ( 'InM1 pth)
  SInL :: SPath pthL -> SPath ( 'InL pthL)
  SInR :: SPath pthR -> SPath ( 'InR pthR)
  SBoth :: SPath pthL -> SPath pthR -> SPath ( 'Both pthL pthR)

type instance Sing = SPath

instance Known 'InV1 where
  sing = SInV1

instance Known 'InK1 where
  sing = SInK1

instance Known p => Known ( 'InL p) where
  sing = SInL sing

instance Known p => Known ( 'InR p) where
  sing = SInR sing

instance (Known l, Known r) => Known ( 'Both l r) where
  sing = SBoth sing sing

instance Known p => Known ( 'InM1 p) where
  sing = SInM1 sing

instance HasSing (Path a f) where
  promote InV1 = MkSomeSing SInV1
  promote InK1 = MkSomeSing SInK1
  promote (InM1 p) = withPromoted p $ MkSomeSing . SInM1
  promote (InL p) = withPromoted p $ MkSomeSing . SInL
  promote (InR p) = withPromoted p $ MkSomeSing . SInR
  promote (Both p q) = withPromoted p $ \l ->
    withPromoted q $ \r -> MkSomeSing $ SBoth l r
  demote SInV1 = InV1
  demote SInK1 = InK1
  demote (SInM1 p) = InM1 $ demote p
  demote (SInL p) = InL $ demote p
  demote (SInR p) = InR $ demote p
  demote (SBoth p q) = Both (demote p) (demote q)

type CalcPath' a b =
  FromJust
    ( 'Text "A type " ':<>: 'ShowType b
        ':<>: 'Text " doesn't have a field with type "
        ':$$: 'ShowType b
    )
    (CalcPath a b)

class HasFactor a b where
  getFactor :: b -> a
  default getFactor :: (GHasFactor a b) => b -> a
  getFactor = traversePath (demote $ sing @(CalcPath' a b)) . from

data DataA = DataA Int Bool String
  deriving (Read, Show, Eq, Ord, Generic)

type GHasFactor a b = (Generic b, Known (CalcPath' a b))

deriving anyclass instance
  GHasFactor a DataA => HasFactor a DataA

deriving anyclass instance
  GHasFactor a DataB => HasFactor a DataB

data DataB = DataB (Maybe Double) [Integer]
  deriving (Read, Show, Eq, Ord, Generic)

data Unioned a b = Unioned {inLeft :: a, inRight :: b}
  deriving (Read, Show, Eq, Ord, Generic)

type UnionedPath a l r =
  FromJust
    ( 'Text "Neither `" ':<>: 'ShowType l
        ':<>: 'Text "' nor `"
        ':<>: 'ShowType r
        ':<>: 'Text "' has a field of type `"
        ':<>: 'ShowType a
        ':<>: 'Text "'"
    )
    (FMap 'Left (CalcPath a l) <|> FMap 'Right (CalcPath a r))

instance
  (Known (UnionedPath a l r), Generic l, Generic r) =>
  HasFactor a (Unioned l r)
  where
  getFactor (Unioned l r) =
    case sing @(UnionedPath a l r) of
      SRight pth -> traversePath (demote pth) $ from r
      SLeft pth -> traversePath (demote pth) $ from l

{-
>>> let unionedAB = Unioned (DataA 42 False "Hey!") (DataB Nothing [4,2])
>>> getFactor @Int unionedAB
42

>>> getFactor @Bool unionedAB
False

>>> getFactor @String unionedAB
"Hey!"

>>> getFactor @(Maybe Double) unionedAB
Nothing

>>> getFactor @(Maybe Bool) unionedAB
Neither `DataA' nor `DataB' has a field of type `Maybe Bool'
-}

{-
noInst :: Unioned DataA DataB -> Maybe Bool
noInst = getFactor
-}
