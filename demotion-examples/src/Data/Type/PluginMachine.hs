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
    HasSing (..),
    Known (..),
    SEqual (..),
    SList (..),
    SMaybe (..),
    Sing,
    SomeSing (MkSomeSing),
    demote,
    sFMapMaybe,
    trustMeNonEqual,
    withKnown,
    withPromoted,
    type (<$>),
  )
import Type.Reflection (Typeable)
import Unsafe.Coerce (unsafeCoerce)

data Plugin = Doubler | Greeter
  deriving (Read, Show, Eq, Ord, Typeable)

instance HasSing Plugin where
  promote Doubler = MkSomeSing SDoubler
  promote Greeter = MkSomeSing SGreeter
  demote SDoubler = Doubler
  demote SGreeter = Greeter

data SPlugin (p :: Plugin) where
  SDoubler :: SPlugin 'Doubler
  SGreeter :: SPlugin 'Greeter

data StoreKey
  = IntStore
  | NameStore
  | PluginStore Plugin
  deriving (Typeable, Eq, Ord, Show)

type GlobalEnv = ()

type family StoreVal (key :: StoreKey) :: Type where
  StoreVal 'IntStore = Int
  StoreVal 'NameStore = String
  StoreVal ( 'PluginStore p) = PluginStoreType p

data SStoreKey (key :: StoreKey) where
  SIntStore :: SStoreKey 'IntStore
  SNameStore :: SStoreKey 'NameStore
  SPluginStore :: SPlugin p -> SStoreKey ( 'PluginStore p)

instance SEqual Plugin where
  SDoubler %~ SDoubler = Equal
  SDoubler %~ SGreeter = NonEqual
  SGreeter %~ SGreeter = Equal
  SGreeter %~ SDoubler = NonEqual

instance SEqual StoreKey where
  SIntStore %~ SIntStore = Equal
  SIntStore %~ SNameStore = NonEqual
  SIntStore %~ SPluginStore {} = NonEqual
  SNameStore %~ SNameStore = Equal
  SNameStore %~ SIntStore = NonEqual
  SNameStore %~ SPluginStore {} = NonEqual
  SPluginStore p %~ SPluginStore q =
    case p %~ q of
      Equal -> Equal
      NonEqual -> trustMeNonEqual
  SPluginStore {} %~ SIntStore = NonEqual
  SPluginStore {} %~ SNameStore = NonEqual

type instance Sing = SStoreKey

type instance Sing = SPlugin

instance Known 'Doubler where
  sing = SDoubler

instance Known 'Greeter where
  sing = SGreeter

instance Known 'IntStore where
  sing = SIntStore

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
processStore _ SNil = EmptyRecord
processStore store (SCons p ps) = process p store :< processStore store ps

{-
>>> processStore (MkStoreEntry @NameStore "Superman" :< MkStoreEntry @IntStore 42 :< EmptyRecord) (sing @'[Doubler, Greeter])
OutputA 84 :< (GreetOutput "Hi, Superman, from Greeter!" :< EmptyRecord)

>>> processStore (MkStoreEntry @NameStore "anonymous" :< EmptyRecord) (sing @'[ Doubler])
Key `'IntStore' is absent in the list:
'[ 'NameStore]

>>> processStore (MkStoreEntry @NameStore "Ignored" :< MkStoreEntry @(PluginStore Greeter) (GreetEnv "You" 3 "me") :< EmptyRecord) (sing @'[ 'Greeter])
GreetOutput "Hi, Hi, Hi, You, from me!" :< EmptyRecord
 -}
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

data PluginsOn keys where
  MkSomePlugins :: All (RunsWith keys) ps => SPlugins ps -> PluginsOn keys

toSomeDyns :: forall keys. Known keys => [Plugin] -> Either String (PluginsOn keys)
toSomeDyns [] = pure $ MkSomePlugins SNil
toSomeDyns (p : rest) = do
  MkSomePlugins ps <- toSomeDyns @keys rest
  withPromoted p $ \case
    SDoubler ->
      deferDynamicPlugin
        (Proxy @ 'Doubler)
        (Proxy @keys)
        (MkSomePlugins $ SCons SDoubler ps)
    SGreeter ->
      deferDynamicPlugin
        (Proxy @ 'Greeter)
        (Proxy @keys)
        (MkSomePlugins $ SCons SGreeter ps)

processStoreDynamic ::
  forall keys.
  Known keys =>
  Store keys ->
  [Plugin] ->
  Either String (SomeRecord (RunsWith keys) PluginOutput)
processStoreDynamic store ps = do
  MkSomePlugins (sps :: SPlugins ps) <- toSomeDyns @keys ps
  pure $ MkSomeRecord sps $ processStore store sps

showsPs :: forall store. SomeRecord (RunsWith store) PluginOutput -> [ShowS]
showsPs (MkSomeRecord _ EmptyRecord) = []
showsPs (MkSomeRecord (_ `SCons` xs) (s :< ss)) =
  shows s : showsPs @store (MkSomeRecord xs ss)

instance Show (SomeRecord (RunsWith store) PluginOutput) where
  showsPrec d x =
    showParen (d > 10) $
      foldr
        (\a b -> a . showString " :< " . b)
        (showString "EmptyRecord")
        (showsPs x)

{-
>>>  processStoreDynamic (MkStoreEntry @NameStore "Superman"        :< MkStoreEntry @IntStore 42        :< EmptyRecord) [Doubler, Greeter]
Right (OutputA 84 :< GreetOutput "Hi, Superman, from Greeter!" :< EmptyRecord)

>>> processStoreDynamic (MkStoreEntry @NameStore "anonymous"     :< EmptyRecord) [Doubler]
Left "Doubler requries IntStore key"

-}
