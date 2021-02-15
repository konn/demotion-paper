{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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

{- | A simple implementation of extensible record.
   Not for practical usage; at least we MUST not use linked-list implementation
   and should use a newtyped 'Int' as a witness for fast access.
-}
module Data.Record
  ( Record (..),
    Index (..),
    SIndex (..),
    FindIndex,
    FindIndex',
    UnionedRecord (..),
    sFindIndex,
    Member,
    SomeRecord (..),
    getRecField,
    walkIndex,
  )
where

import Data.Kind
import Data.Reflection
import Data.Type.Natural (Equality (Equal, NonEqual), type (===))
import Data.Type.Path
import Data.Type.Singletons
import GHC.TypeLits

data Record f keys where
  EmptyStore :: Record f '[]
  (:<) :: f k -> Record f ks -> Record f (k ': ks)

deriving instance All (ShowF f) keys => Show (Record f keys)

infixr 9 :<

data Index k ks where
  Here :: Index k (k ': ks)
  There :: Index k ks -> Index k (k' ': ks)

instance HasSing (Index k ks) where
  demote = demoteIndex
  promote Here = MkSomeSing SHere
  promote (There idx) = withPromoted idx $ MkSomeSing . SThere

type SIndex :: forall k ks. Index k ks -> Type
data SIndex index where
  SHere :: SIndex 'Here
  SThere :: SIndex index -> SIndex ( 'There index)

type instance Sing = SIndex

instance Known 'Here where
  sing = SHere

instance Known k => Known ( 'There k) where
  sing = SThere sing

type FindIndex :: forall k ks -> Maybe (Index k ks)
type family FindIndex k ks where
  FindIndex _ '[] = 'Nothing
  FindIndex k (k' ': ks) = FindIndexAux (k === k') k k' ks

type FindIndexAux :: Bool -> forall k k' ks -> Maybe (Index k (k' ': ks))
type family FindIndexAux eql k k' rest where
  FindIndexAux 'True _ _ _ = 'Just 'Here
  FindIndexAux 'False k _ ks = 'There `FMap` FindIndex k ks

walkIndex :: Index k ks -> Record f ks -> f k
walkIndex Here (v :< _) = v
walkIndex (There trail) (_ :< rest) = walkIndex trail rest

-- >>> :kind! FindIndex 5 '[24, 45, 1, 5]
-- FindIndex 5 '[24, 45, 1, 5] :: Maybe (Index 5 '[24, 45, 1, 5])
-- = 'Just ('There ('There ('There 'Here)))

demoteIndex :: SIndex (index :: Index k ks) -> Index k ks
demoteIndex SHere = Here
demoteIndex (SThere pth) = There $ demoteIndex pth

type FindIndex' k ks =
  FromJust
    ( 'Text "Key `" ':<>: 'ShowType k
        ':<>: 'Text "' is absent in the list: " ':$$: 'ShowType ks
    )
    (FindIndex k ks)

type Member k ks = Given (Index k ks)

data SomeRecord c f where
  MkSomeRecord :: All c keys => Sing keys -> Record f keys -> SomeRecord c f

sFindIndex ::
  SEqual a => Sing (k :: a) -> SList keys -> SMaybe (FindIndex k keys)
sFindIndex _ SNil = SNothing
sFindIndex k (SCons k' ks) =
  case k %~ k' of
    Equal -> SJust SHere
    NonEqual -> sFMapMaybe SThere $ sFindIndex k ks

getRecField :: forall key keys h. Given (Index key keys) => Record h keys -> h key
getRecField = walkIndex given

instance Known (FindIndex' k ks) => Given (Index k ks) where
  given = demote $ sing @(FindIndex' k ks)

instance (Given (Index a keys), h ~ h') => HasFactor (h' a) (Record h keys) where
  getFactor = getRecField

data UnionedRecord (h :: k -> Type) (ls :: [k]) (rs :: [k]) = UnionRec
  { recL :: Record h ls
  , recR :: Record h rs
  }
  deriving (Show)

newtype IndexUnion k ls rs = WrapIndexUnion
  {getUnionedIndex :: Either (Index k ls) (Index k rs)}

instance
  Known (UnionedIndex' k ls rs) =>
  Given (IndexUnion k ls rs)
  where
  given = WrapIndexUnion $ demote $ sing @(UnionedIndex' k ls rs)

type UnionedIndex' k ls rs =
  FromJust
    ( 'Text "A field of type `" ':<>: 'ShowType k ':<>: 'Text "' not found in either of fields:"
        ':$$: 'Text "\t Left: " ':<>: 'ShowType ls
        ':$$: 'Text "\tRight: " ':<>: 'ShowType rs
    )
    (UnionedIndex k ls rs)

type UnionedIndex k ls rs =
  'Left <$> FindIndex k ls <|> 'Right <$> FindIndex k rs

instance
  Given (IndexUnion k ls rs) =>
  HasFactor (h k) (UnionedRecord h ls rs)
  where
  getFactor (UnionRec l r) =
    case getUnionedIndex $ given @(IndexUnion k ls rs) of
      Left pth -> give pth $ getFactor l
      Right pth -> give pth $ getFactor r

{-
>>> import Data.Functor.Const
>>> theRec = Const "Hehe" :< Const "Foo" :< Const "buz" :< EmptyStore :: Record (Const String) '[5,42, 34]
>>> getFactor @(Const String 42) (Const "Hehe" :< Const "Foo" :< Const "buz" :< EmptyStore :: Record (Const String) '[5,42, 34])
Const "Foo"

>>> getFactor @(Const String 52) theRec
Key `52' is absent in the list:
'[5, 42, 34]

>>> anotherRec = Const "Phew" :< Const "Wow" :< Const "Cool" :< EmptyStore :: Record (Const String) '[94, 5, 2]
>>> getFactor @(Const String 5) anotherRec
Const "Wow"

>>> getFactor @(Const String 42) (UnionRec theRec anotherRec)
Const "Foo"

>>> getFactor @(Const String 2) (UnionRec theRec anotherRec)
Const "Cool"

>>> getFactor @(Const String 5) (UnionRec theRec anotherRec)
Const "Hehe"

Beware of reordering:
>>> getFactor @(Const String 5) (UnionRec anotherRec theRec)
Const "Wow"

>>> getFactor @(Const String 999) (UnionRec theRec anotherRec)
A field of type `999' not found in either of fields:
	 Left: '[5, 42, 34]
	Right: '[94, 5, 2]

-}
