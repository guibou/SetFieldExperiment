{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS -Wall #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Type based record update which supports polymorphic update on multiples fields
--
-- The idea is to do updates one at a time on the 'Rep' (from 'Generic') of the
-- structure, which accepts to be in a ill-shaped form.
--
-- The updates are applied with 'setField', on the 'Rep', so you must first
-- convert it to Rep and then back to the final object.
module HasField where

import GHC.Generics
import Prelude
import Data.Kind (Type)

-- * API

-- | Apply a generic setter based on Rep'
withSetters
  :: (Generic b, Generic a)
  => (Rep a x -> Rep b x)
  -- ^ The generic setters, combine calls to 'setField'
  -> a
  -- ^ Input record
  -> b
  -- ^ Output record, possibly with polymorphic updates (e.g. @a@ may not be
 -- equal to @b@, however they are usually alike (e.g. same type with different type parameters)
withSetters setters a = GHC.Generics.to . setters . GHC.Generics.from $ a

-- | @setField @"fieldName" newValue record@ is similar to @record { fieldName = newValue }@,
-- but can be combined with other 'setField'.
setField :: forall fieldName path rep v x. (Just path ~ GetFieldPath fieldName rep, SetPath path rep v) => v -> rep x -> ResultRep path rep v x
setField v x = setPath @path v x

-- * Internal

type family ResultRep (path :: [Dir]) rep t :: k -> Type where
  ResultRep path (M1 D c f) t = M1 D c (ResultRep path f t)
  ResultRep path (M1 C c f) t = M1 C c (ResultRep path f t)
  ResultRep (L ': xs) (a :*: b) t = ResultRep xs a t :*: b
  ResultRep ('R ': xs) (a :*: b) t = a :*: ResultRep xs b t
  ResultRep '[] (M1 S m (Rec0 b)) t = M1 S m (Rec0 t)

-- | Directions in the record field tree
data Dir = L | R

-- | Change the value in a record, following a path of Left / Right
class SetPath (path :: [Dir]) rep t where
  setPath :: t -> rep x -> (ResultRep path rep t) x

-- | Metadata
instance SetPath path f t => SetPath path (M1 D c f) t where
  setPath v (M1 m1) = M1 (setPath @path v m1)

-- | Metadata
instance SetPath path f t => SetPath path (M1 C c f) t where
  setPath v (M1 m1) = M1 (setPath @path v m1)

-- | Go on Left item
instance (SetPath xl a t) => SetPath (L ': xl) (a :*: b) t where
  setPath v (a :*: b) = setPath @xl v a :*: b

-- | Go on Right item
instance (SetPath xl b t) => SetPath ('R ': xl) (a :*: b) t where
  setPath v (a :*: b) = a :*: setPath @xl v b

-- | We found an item, update it
instance SetPath '[] (M1 S m (Rec0 b)) t where
  setPath v (M1 (K1 _)) = M1 $ K1 v

-- | Returns the path in a Rep of a record to locate a required field
type family GetFieldPath fieldName x where
  GetFieldPath fieldName (M1 D c f) = GetFieldPath fieldName f
  GetFieldPath fieldName (M1 C c f) = GetFieldPath fieldName f
  GetFieldPath fieldName (a :*: b) = MergePaths (Cons 'L (GetFieldPath fieldName a)) (Cons 'R (GetFieldPath fieldName b))
  GetFieldPath fieldName (M1 S (MetaSel (Just fieldName) pack strict lazy) (Rec0 b)) = Just '[]
  GetFieldPath fieldName (M1 S (MetaSel (Just fieldName') pack strict lazy) (Rec0 b)) = Nothing

type family Cons (t :: Dir) (jl :: Maybe [Dir]) :: Maybe [Dir] where
  Cons _ Nothing = Nothing
  Cons x (Just l) = Just (x ': l)

type family MergePaths a b where
  MergePaths Nothing a = a
  MergePaths a Nothing = a

-- * Examples

-- Polymorphic update on the 'Tortue' type
setBoth :: a -> a -> Tortue x -> Tortue a
setBoth ch' t' = withSetters (setField @"cheval" ch' . setField @"tortue" t')

-- | The same, but works on any type which have a @tortue@ and @cheval@ fields
--
-- TODO: work on the type constraint in order to have something simpler ;)
genericSetBoth :: (Generic c, Generic b
   , GetFieldPath "tortue" (Rep b) ~ Just pathTortue
   , SetPath pathTortue (Rep b) a
   , ResultRep pathTortue (Rep b) a ~ rep2
   , GetFieldPath "cheval" rep2 ~ Just pathCheval
   , SetPath pathCheval rep2 a
   , ResultRep pathCheval rep2 a ~ rep3
   , Rep c ~ rep3
   ) => a -> a -> b -> c
genericSetBoth ch' t' t = GHC.Generics.to $ setField @"cheval" ch' $ setField @"tortue" t' $ GHC.Generics.from t


-- * Examples
data Tortue t = Tortue {cheval :: t, tortue :: t} deriving (Show, Generic)
data Tartare = Tartare {cheval :: Int, tortue :: Int} deriving (Show, Generic)

lol :: Tortue Int
lol = Tortue {cheval = 10 :: Int, tortue = 20}

lil :: Tortue String
lil = genericSetBoth "toto" "titi" lol

lil' :: Tartare
lil' = genericSetBoth 100 200 (Tartare 20 50)


