{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
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

import Control.Monad.Reader.Class (MonadReader)
import Control.Monad.Trans.Reader (Reader)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.Type.Equality (TestEquality)
import Data.Type.Natural
  ( Equality (Equal, NonEqual),
    SBool (SFalse, STrue),
    SNat,
    SOrdering (SEQ, SGT, SLT),
    sNat,
    toNatural,
    withKnownNat,
    type (===),
  )
import qualified Data.Type.Natural as TN
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

type family Sing :: k -> Type

type instance Sing = SStoreKey

type instance Sing = SPlugin

type instance Sing = SNat

type instance Sing = SList

data SList (xs :: [k]) where
  SNil :: SList '[]
  SCons :: Sing x -> SList xs -> SList (x ': xs)

data SMaybe (m :: Maybe k) where
  SNothing :: SMaybe 'Nothing
  SJust :: Sing a -> SMaybe ( 'Just a)

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

type instance Sing = SMaybe

class Known a where
  sing :: Sing a

instance KnownNat n => Known n where
  sing = sNat

instance Known '[] where
  sing = SNil

instance (Known x, Known xs) => Known (x ': xs) where
  sing = sing `SCons` sing

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

type family All c keys :: Constraint where
  All c '[] = ()
  All c (k ': ks) = (c k, All c ks)

class Show (f a) => ShowF f a

instance Show (f a) => ShowF f a

deriving instance All (ShowF f) keys => Show (Record f keys)

infixr 9 :<

data Path k ks where
  Here :: Path k (k ': ks)
  There :: Path k ks -> Path k (k' ': ks)

type SPath :: forall k ks. Path k ks -> Type
data SPath path where
  SHere :: SPath 'Here
  SThere :: SPath pth -> SPath ( 'There pth)

type instance Sing = SPath

instance Known 'Here where
  sing = SHere

instance Known k => Known ( 'There k) where
  sing = SThere sing

type LookupIndex :: forall k ks -> Maybe (Path k ks)
type family LookupIndex k ks where
  LookupIndex _ '[] = 'Nothing
  LookupIndex k (k' ': ks) = LookupIndexAux (k === k') k k' ks

type instance Sing = SBool

type instance Sing = SOrdering

class SEqual k where
  (%~) :: Sing (a :: k) -> Sing b -> Equality a b

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

walkPath' :: Path k ks -> Record f ks -> f k
walkPath' Here (v :< _) = v
walkPath' (There trail) (_ :< rest) = walkPath' trail rest

walkPath :: Path k ks -> Store ks -> StoreVal k
walkPath = fmap storeEntry . walkPath'

-- >>> :kind! LookupIndex 5 '[24, 45, 1, 5]
-- LookupIndex 5 '[24, 45, 1, 5] :: Maybe (Path 5 '[24, 45, 1, 5])
-- = 'Just ('There ('There ('There 'Here)))

type LookupIndexAux :: Bool -> forall k k' ks -> Maybe (Path k (k' ': ks))
type family LookupIndexAux eql k k' rest where
  LookupIndexAux 'True k k ks = 'Just 'Here
  LookupIndexAux 'False k _ ks = 'There `FMap` LookupIndex k ks

type family FMap (f :: k -> k') (n :: Maybe k) :: Maybe k' where
  FMap _ 'Nothing = 'Nothing
  FMap f ( 'Just a) = 'Just (f a)

demotePath :: SPath (path :: Path k ks) -> Path k ks
demotePath SHere = Here
demotePath (SThere pth) = There $ demotePath pth

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

newtype Machine (ps :: [Plugin]) (keys :: [StoreKey]) a = Machine {unMachine :: Reader (Store keys) a}
  deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadReader (Store keys)
    )

class IsPlugin (p :: Plugin) where
  data PluginOutput p
  type Runnable p (keys :: [StoreKey]) :: Constraint
  process :: Runnable p keys => proxy p -> Store keys -> PluginOutput p

instance IsPlugin 'PluginDouble where
  newtype PluginOutput 'PluginDouble = OutputA Int
    deriving (Read, Show, Eq, Ord)
  type Runnable 'PluginDouble keys = Member 'IntStore keys
  process _ store = OutputA $ 2 * readStore @ 'IntStore store

readStore :: forall key keys. Member key keys => Store keys -> StoreVal key
readStore = walkPath $ demotePath $ sing @(LookupIndex' key keys)

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
        GreetOutput $ makeGreet $ walkPath (demotePath pth) store
      SNothing -> case sing @(LookupIndex 'NameStore keys) of
        SJust pth ->
          GreetOutput $
            makeGreet $
              GreetEnv (walkPath (demotePath pth) store) 1 "PluginGreet"
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

newtype WithKnown a r = WithKnown {runWithKnown :: Known a => r}

withKnown :: forall a r. Sing a -> (Known a => r) -> r
withKnown sn act = unsafeCoerce (WithKnown @a @r act) sn

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
