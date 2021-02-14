{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Data.Type.PluginMachine where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.Type.Natural
  ( Equality (Equal, NonEqual),
    toNatural,
    type (===),
  )
import Data.Type.Singletons
import GHC.TypeLits
import Numeric.Natural (Natural)
import Type.Reflection (Typeable)
import Unsafe.Coerce (unsafeCoerce)

data Plugin = PluginDouble | PluginGreet
  deriving (Read, Show, Eq, Ord, Typeable)

data SPlugin (p :: Plugin) where
  SPluginDouble :: SPlugin 'PluginDouble
  SPluginGreet :: SPlugin 'PluginGreet

data family PluginStoreType (p :: Plugin)

data StoreKey
  = IntStore
  | NameStore
  | PluginStore Plugin
  | GlobalStore
  deriving (Typeable, Eq, Ord, Show)

type GlobalEnv = ()

type family StoreVal (key :: StoreKey) :: Type where
  StoreVal 'IntStore = Int
  StoreVal 'NameStore = String
  StoreVal ( 'PluginStore p) = PluginStoreType p
  StoreVal 'GlobalStore = GlobalEnv

data SStoreKey (key :: StoreKey) where
  SIntStore :: SStoreKey 'IntStore
  SNameStore :: SStoreKey 'NameStore
  SPluginStore :: SPlugin p -> SStoreKey ( 'PluginStore p)
  SGlobalStore :: SStoreKey 'GlobalStore

instance SEqual Plugin where
  SPluginDouble %~ SPluginDouble = Equal
  SPluginDouble %~ _ = unsafeCoerce $ NonEqual @0 @1
  SPluginGreet %~ SPluginGreet = Equal
  SPluginGreet %~ _ = unsafeCoerce $ NonEqual @0 @1

instance SEqual StoreKey where
  SIntStore %~ SIntStore = Equal
  SIntStore %~ _ = unsafeCoerce $ NonEqual @0 @1
  SNameStore %~ SNameStore = Equal
  SNameStore %~ _ = unsafeCoerce $ NonEqual @0 @1
  SGlobalStore %~ SGlobalStore = Equal
  SGlobalStore %~ _ = unsafeCoerce $ NonEqual @0 @1
  SPluginStore p %~ SPluginStore q =
    case p %~ q of
      Equal -> Equal
      NonEqual -> unsafeCoerce $ NonEqual @0 @1
  SPluginStore {} %~ _ = unsafeCoerce $ NonEqual @0 @1

type instance Sing = SStoreKey

type instance Sing = SPlugin

instance Known 'PluginDouble where
  sing = SPluginDouble

instance Known 'PluginGreet where
  sing = SPluginGreet

instance Known 'IntStore where
  sing = SIntStore

instance Known 'GlobalStore where
  sing = SGlobalStore

instance Known 'NameStore where
  sing = SNameStore

instance Known p => Known ( 'PluginStore p) where
  sing = SPluginStore sing

newtype StoreEntry k = MkStoreEntry {storeEntry :: StoreVal k}

type Store = Record StoreEntry

data Record f keys where
  EmptyStore :: Record f '[]
  (:<) :: f k -> Record f ks -> Record f (k ': ks)

deriving instance All (ShowF f) keys => Show (Record f keys)

infixr 9 :<

data Index k ks where
  Here :: Index k (k ': ks)
  There :: Index k ks -> Index k (k' ': ks)

type SIndex :: forall k ks. Index k ks -> Type
data SIndex index where
  SHere :: SIndex 'Here
  SThere :: SIndex index -> SIndex ( 'There index)

type instance Sing = SIndex

instance Known 'Here where
  sing = SHere

instance Known k => Known ( 'There k) where
  sing = SThere sing

type LookupIndex :: forall k ks -> Maybe (Index k ks)
type family LookupIndex k ks where
  LookupIndex _ '[] = 'Nothing
  LookupIndex k (k' ': ks) = LookupIndexAux (k === k') k k' ks

walkIndex' :: Index k ks -> Record f ks -> f k
walkIndex' Here (v :< _) = v
walkIndex' (There trail) (_ :< rest) = walkIndex' trail rest

walkIndex :: Index k ks -> Store ks -> StoreVal k
walkIndex = fmap storeEntry . walkIndex'

-- >>> :kind! LookupIndex 5 '[24, 45, 1, 5]
-- LookupIndex 5 '[24, 45, 1, 5] :: Maybe (Index 5 '[24, 45, 1, 5])
-- = 'Just ('There ('There ('There 'Here)))

type LookupIndexAux :: Bool -> forall k k' ks -> Maybe (Index k (k' ': ks))
type family LookupIndexAux eql k k' rest where
  LookupIndexAux 'True k k ks = 'Just 'Here
  LookupIndexAux 'False k _ ks = 'There `FMap` LookupIndex k ks

type family FMap (f :: k -> k') (n :: Maybe k) :: Maybe k' where
  FMap _ 'Nothing = 'Nothing
  FMap f ( 'Just a) = 'Just (f a)

demoteIndex :: SIndex (index :: Index k ks) -> Index k ks
demoteIndex SHere = Here
demoteIndex (SThere pth) = There $ demoteIndex pth

type LookupIndex' k ks =
  FromJust
    ( 'Text "Key `" ':<>: 'ShowType k
        ':<>: 'Text "' is absent in the list: " ':$$: 'ShowType ks
    )
    (LookupIndex k ks)

type family FromJust msg mb where
  FromJust err 'Nothing = TypeError err
  FromJust _ ( 'Just x) = x

type Member k ks = Known (LookupIndex' k ks)

class Show (PluginOutput p) => IsPlugin (p :: Plugin) where
  data PluginOutput p
  type Runnable p (keys :: [StoreKey]) :: Constraint
  process :: Runnable p keys => proxy p -> Store keys -> PluginOutput p

instance IsPlugin 'PluginDouble where
  newtype PluginOutput 'PluginDouble = OutputA Int
    deriving (Read, Show, Eq, Ord)
  type Runnable 'PluginDouble keys = Member 'IntStore keys
  process _ store = OutputA $ 2 * readStore @ 'IntStore store

readStore :: forall key keys. Member key keys => Store keys -> StoreVal key
readStore = walkIndex $ demoteIndex $ sing @(LookupIndex' key keys)

class (IsPlugin p, Runnable p keys) => RunsWith keys p

instance (IsPlugin p, Runnable p keys) => RunsWith keys p

type Outputs = Record PluginOutput

data instance PluginStoreType 'PluginGreet = GreetEnv
  { greetTarget :: String
  , greetTimes :: Int
  , greetOwner :: String
  }
  deriving (Show, Eq, Ord)

type Greetable keys =
  ( Known (LookupIndex ( 'PluginStore 'PluginGreet) keys)
  , Known (LookupIndex 'NameStore keys)
  )

makeGreet :: PluginStoreType 'PluginGreet -> String
makeGreet GreetEnv {..} =
  mconcat (replicate greetTimes "Hi, ")
    <> greetTarget
    <> ", from "
    <> greetOwner
    <> "!"

instance IsPlugin 'PluginGreet where
  type Runnable 'PluginGreet keys = Greetable keys
  newtype PluginOutput 'PluginGreet = GreetOutput String
    deriving (Read, Show, Eq, Ord)
  process _ (store :: Store keys) =
    case sing @(LookupIndex ( 'PluginStore 'PluginGreet) keys) of
      SJust pth ->
        GreetOutput $ makeGreet $ walkIndex (demoteIndex pth) store
      SNothing -> case sing @(LookupIndex 'NameStore keys) of
        SJust pth ->
          GreetOutput $
            makeGreet $
              GreetEnv (walkIndex (demoteIndex pth) store) 1 "PluginGreet"
        SNothing -> GreetOutput "I don't know who you are, anyway, Hi!"

type SPlugins ps = SList (ps :: [Plugin])

processStore ::
  forall ps keys.
  (All (RunsWith keys) ps) =>
  Store keys ->
  SPlugins ps ->
  Outputs ps
processStore _ SNil = EmptyStore
processStore store (SCons p ps) = process p store :< processStore store ps

-- >>> runMachine (MkStoreEntry @NameStore "Superman" :< MkStoreEntry @IntStore 42 :< EmptyStore) :: Outputs '[PluginDouble, PluginGreet]
-- OutputA 84 :< (GreetOutput "Hi, Superman, from PluginGreet!" :< EmptyStore)

sJustNat :: forall m. Known (m :: Maybe Nat) => Maybe Natural
sJustNat = demoteJustNat @m

demoteJustNat :: forall m. Known (m :: Maybe Nat) => Maybe Natural
demoteJustNat = case sing @m of
  SNothing -> Nothing
  SJust n -> Just $ toNatural n

sFMap :: (forall x. Sing x -> Sing (f x)) -> SMaybe may -> SMaybe (FMap f may)
sFMap _ SNothing = SNothing
sFMap f (SJust x) = SJust (f x)

sLookupIndex ::
  SEqual a => Sing (k :: a) -> SList keys -> SMaybe (LookupIndex k keys)
sLookupIndex _ SNil = SNothing
sLookupIndex k (SCons k' ks) =
  case k %~ k' of
    Equal -> SJust SHere
    NonEqual -> sFMap SThere $ sLookupIndex k ks

class IsPlugin p => DynamicPlugin p where
  deferDynamicPlugin ::
    Known keys => pxy p -> Proxy keys -> (Runnable p keys => r) -> Either String r

instance DynamicPlugin 'PluginDouble where
  deferDynamicPlugin _ (_ :: Proxy keys) act =
    case sLookupIndex SIntStore $ sing @keys of
      SNothing -> Left "PluginDouble requries IntStore key"
      SJust v -> withKnown v $ Right act

instance DynamicPlugin 'PluginGreet where
  deferDynamicPlugin _ (_ :: Proxy keys) act =
    let keys = sing @keys
     in withKnown (sLookupIndex (SPluginStore SPluginGreet) keys) $
          withKnown (sLookupIndex SNameStore keys) $
            Right act

data SomeDSum c f where
  MkSomeDSum :: c x => Sing x -> f x -> SomeDSum c f

data SomeRecord c f where
  MkSomeRecord ::
    All c keys =>
    Sing keys ->
    Record f keys ->
    SomeRecord c f

fromSomeDSums ::
  [SomeDSum c f] -> SomeRecord c f
fromSomeDSums [] = MkSomeRecord SNil EmptyStore
fromSomeDSums (MkSomeDSum sx v : rest) =
  case fromSomeDSums rest of
    MkSomeRecord sxs vs -> MkSomeRecord (sx `SCons` sxs) (v :< vs)

instance Promotable Plugin where
  promote = \case
    PluginDouble -> MkSomeSing SPluginDouble
    PluginGreet -> MkSomeSing SPluginGreet

data SomeDynamicPlugin where
  MkDyn :: DynamicPlugin p => Sing p -> SomeDynamicPlugin

data PluginsOn keys where
  MkSomePlugins :: All (RunsWith keys) ps => SPlugins ps -> PluginsOn keys

toSomeDyns :: forall keys. Known keys => [SomeDynamicPlugin] -> Either String (PluginsOn keys)
toSomeDyns [] = pure $ MkSomePlugins SNil
toSomeDyns (MkDyn (p :: SPlugin p) : rest) = do
  MkSomePlugins ps <- toSomeDyns @keys rest
  deferDynamicPlugin @p @keys Proxy Proxy (MkSomePlugins $ SCons p ps)

runDynamicPlugins ::
  forall keys.
  Known keys =>
  Store keys ->
  [SomeDynamicPlugin] ->
  Either String (SomeRecord (RunsWith keys) PluginOutput)
runDynamicPlugins store ps = do
  MkSomePlugins (sps :: SPlugins ps) <- toSomeDyns @keys ps
  pure $ MkSomeRecord sps $ processStore store sps
