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

type CalcPathF a f = CalcPathFWith @Maybe a f

type CalcPathFWith :: forall h. forall a f -> h (Path a f)
type family CalcPathFWith a f where
  CalcPathFWith a (K1 i a) = Pure 'InK1
  CalcPathFWith a (M1 i c f) = 'InM1 <$> CalcPathFWith a f
  CalcPathFWith a (l :*: r) =
    'InL <$> CalcPathFWith a l <|> 'InR <$> CalcPathFWith a r
  CalcPathFWith a (l :+: r) = 'Both <$> CalcPathFWith a l <*> CalcPathFWith a r
  CalcPathFWith a V1 = Pure 'InV1
  CalcPathFWith _ _ = Empty

data MyType a = LLL a Int | RRR Bool Int Double
  deriving (Read, Show, Eq, Ord, Generic)

-- >>> :kind! CalcPathFWith @[] Int (Rep (MyType Int))
-- CalcPathFWith @[] Int (Rep (MyType Int)) :: [Path
--                                                Int (Rep (MyType Int))]
-- = '[ 'InM1
--        ('Both
--           ('InM1 ('InL ('InM1 'InK1))) ('InM1 ('InR ('InL ('InM1 'InK1))))),
--      'InM1
--        ('Both
--           ('InM1 ('InR ('InM1 'InK1))) ('InM1 ('InR ('InL ('InM1 'InK1)))))]

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
