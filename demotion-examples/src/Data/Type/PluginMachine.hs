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
import Data.Record
import Data.Type.Natural (Equality (Equal, NonEqual))
import Data.Type.Singletons
  ( All,
    Known (..),
    SEqual (..),
    SList (..),
    SMaybe (..),
    Sing,
    demote,
    withKnown,
  )
import Type.Reflection (Typeable)
import Unsafe.Coerce (unsafeCoerce)

data Plugin = Doubler | Greeter
  deriving (Read, Show, Eq, Ord, Typeable)

data SPlugin (p :: Plugin) where
  SDoubler :: SPlugin 'Doubler
  SGreeter :: SPlugin 'Greeter

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
  SDoubler %~ SDoubler = Equal
  SDoubler %~ _ = unsafeCoerce $ NonEqual @0 @1
  SGreeter %~ SGreeter = Equal
  SGreeter %~ _ = unsafeCoerce $ NonEqual @0 @1

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

instance Known 'Doubler where
  sing = SDoubler

instance Known 'Greeter where
  sing = SGreeter

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

walkIndex' :: Index k ks -> Store ks -> StoreVal k
walkIndex' = fmap storeEntry . walkIndex

class Show (PluginOutput p) => IsPlugin (p :: Plugin) where
  data PluginStoreType p
  data PluginOutput p
  type Runnable p (keys :: [StoreKey]) :: Constraint
  process :: Runnable p keys => proxy p -> Store keys -> PluginOutput p

instance IsPlugin 'Doubler where
  data PluginStoreType 'Doubler = DoubleStore
    deriving (Read, Show, Eq, Ord)
  newtype PluginOutput 'Doubler = OutputA Int
    deriving (Read, Show, Eq, Ord)
  type Runnable 'Doubler keys = Member 'IntStore keys
  process _ store = OutputA $ 2 * getStoreField @ 'IntStore store

getStoreField :: forall key keys. Member key keys => Store keys -> StoreVal key
getStoreField = storeEntry . getRecField @key

class (IsPlugin p, Runnable p keys) => RunsWith keys p

instance (IsPlugin p, Runnable p keys) => RunsWith keys p

type Outputs = Record PluginOutput

type Greetable keys =
  ( Known (FindIndex ( 'PluginStore 'Greeter) keys)
  , Greetable_ (FindIndex ( 'PluginStore 'Greeter) keys) keys
  )

type family Greetable_ m keys :: Constraint where
  Greetable_ ( 'Just path) _ = ()
  Greetable_ 'Nothing keys = Known (FindIndex 'NameStore keys)

makeGreet :: PluginStoreType 'Greeter -> String
makeGreet GreetEnv {..} =
  mconcat (replicate greetTimes "Hi, ")
    <> greetTarget
    <> ", from "
    <> greetOwner
    <> "!"

instance IsPlugin 'Greeter where
  data PluginStoreType 'Greeter = GreetEnv
    { greetTarget :: String
    , greetTimes :: Int
    , greetOwner :: String
    }
    deriving (Show, Eq, Ord)
  type Runnable 'Greeter keys = Greetable keys
  newtype PluginOutput 'Greeter = GreetOutput String
    deriving (Read, Show, Eq, Ord)
  process _ (store :: Store keys) =
    case sing @(FindIndex ( 'PluginStore 'Greeter) keys) of
      SJust pth ->
        GreetOutput $ makeGreet $ walkIndex' (demote pth) store
      SNothing -> case sing @(FindIndex 'NameStore keys) of
        SJust pth ->
          GreetOutput $
            makeGreet $
              GreetEnv (walkIndex' (demote pth) store) 1 "Greeter"
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

-- >>> processStore (MkStoreEntry @NameStore "Superman" :< MkStoreEntry @IntStore 42 :< EmptyStore) (sing @'[Doubler, Greeter])
-- OutputA 84 :< (GreetOutput "Hi, Superman, from Greeter!" :< EmptyStore)

class IsPlugin p => DynamicPlugin p where
  deferDynamicPlugin ::
    Known keys => pxy p -> Proxy keys -> (Runnable p keys => r) -> Either String r

instance DynamicPlugin 'Doubler where
  deferDynamicPlugin _ (_ :: Proxy keys) act =
    case sFindIndex SIntStore $ sing @keys of
      SNothing -> Left "Doubler requries IntStore key"
      SJust v -> withKnown v $ Right act

instance DynamicPlugin 'Greeter where
  deferDynamicPlugin _ (_ :: Proxy keys) act =
    let keys = sing @keys
     in case sFindIndex (SPluginStore SGreeter) keys of
          SJust pth -> withKnown pth $ Right act
          SNothing ->
            withKnown (sFindIndex SNameStore keys) $
              Right act

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
