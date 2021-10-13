{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# options -Wall -fno-warn-unticked-promoted-constructors #-}
{-# options -fprint-potential-instances #-}


module Data.Avro.Sum where

import           Data.Avro
import           Data.Avro.Encoding.FromAvro  (FromAvro (..))
import qualified Data.Avro.Encoding.FromAvro  as AV
import           Data.Avro.Encoding.ToAvro    (ToAvro (..))
import           Data.Avro.Internal.EncodeRaw (putI)
import           Data.Avro.Schema.Schema      as S
import           Data.ByteString.Builder      (Builder)
import           Data.List.NonEmpty           (NonEmpty (..))
import           Data.Tagged                  (Tagged (..))
import qualified Data.Vector                  as V
import           Data.Kind                    (Type, Constraint)
import           Data.Proxy                   (Proxy (..))
import           GHC.TypeLits                 (KnownNat, natVal, Nat, type (+))

-- | N-ary sum type. Used for modelling unions.
data NSum :: [Type] -> Type where
  -- | The contained element is the first one in the list of possibilities.
  --   It is "at the start" of the list.
  Start :: x -> NSum (x ': xs)
  -- | Add a new possibility in the list of types.
  Next :: NSum xs -> NSum (x ': xs)

type family All (c :: k -> Constraint) (xs :: [Type]) :: Constraint where
  All c '[]       = ()
  All c (x ': xs) = (c x, All c xs)

instance (All Eq xs) => Eq (NSum xs) where
  Start x == Start y = x == y
  Next  x == Next  y = x == y
  _       == _       = False

instance Show (NSum '[]) where
  show = \case

instance (Show x, Show (NSum xs)) => Show (NSum (x : xs)) where
  showsPrec d ns = case ns of
    Start x   -> showParen (d > precedence) $ showString "Start " . showsPrec (precedence + 1) x
    Next next -> showParen (d > precedence) $ showString "Next "  . showsPrec (precedence + 1) next

    where precedence = 10

------------------------ ToAvro ------------------------


instance (All ToAvro xs, Length xs ~ n, KnownNat n) => ToAvro (NSum xs) where
  toAvro :: Schema -> NSum xs -> Builder
  toAvro (S.Union opts) ns =
    if nsLength ns == V.length opts
      then putI (nsOffset ns) <> mkAvro (V.unsafeIndex opts $ nsOffset ns)
      else error $ "Unable to encode NSum as " <> show opts
    where
      mkAvro = extractAvroBuilder ns

      extractAvroBuilder :: All ToAvro ts => NSum ts -> Schema -> Builder
      extractAvroBuilder = \case
        Start x -> flip toAvro x
        Next n  -> extractAvroBuilder n

  toAvro s _ns = error $ "Unable to encode an NSum as " <> show s


type family Length (xs :: [k]) :: Nat where
  Length '[] = 0
  Length (x : xs) = 1 + (Length xs)

-- | The number of available types in the NSum
nsLength :: forall xs n. (Length xs ~ n, KnownNat n) => NSum xs -> Int
nsLength _ = fromIntegral $ natVal (Proxy @n)

-- | How many "moves" away from the first type in the list is the one in the NSum value
nsOffset :: NSum ts -> Int
nsOffset = \case
  Start _  -> 0
  Next ns -> succ (nsOffset ns)



------------------------ FromAvro ------------------------

instance (All FromAvro xs, HasShape xs) => FromAvro (NSum xs) where
  fromAvro :: AV.Value -> Either String (NSum xs)
  fromAvro = \case
    AV.Union _ i val -> runParsers (parsersFromAvro theShape) i val
    _ -> Left $ "Unable to decode an NSum: Not a Union value"

runParsers :: Parsers xs -> Int -> AV.Value -> Either String (NSum xs)
runParsers parsers i val = case parsers of
  PZero -> Left "No choices"
  PNext parser ps -> case compare i 0 of
    LT -> Left "Out of bounds"
    EQ -> Start <$> parser val
    GT -> Next <$> runParsers ps (pred i) val

-- | If all the xs have FromAvro, then we can have the vector (of size length xs)
--   of all its parsers.
--   The need for the 'Shape' singleton witness is a technicality: It gives no info
--   but it reflects the type-level data about the list to the value level.
--   This argument will be magicked away with a type class.
parsersFromAvro :: All FromAvro xs => Shape xs -> Parsers xs
parsersFromAvro = \case
  ShapeZ   -> PZero
  ShapeS s -> PNext fromAvro $ parsersFromAvro s

-- | The function type needed to satisfy the 'FromAvro' interface
type Parser a = AV.Value -> Either String a

-- | A parser for each element of the type list
data Parsers :: [Type] -> Type where
  PZero :: Parsers '[]
  PNext :: Parser x -> Parsers xs -> Parsers (x : xs)

-- | A value-level witness of the structure of the type-level list
--   See https://blog.jle.im/entry/introduction-to-singletons-1.html
data Shape :: [k] -> Type where
  ShapeZ :: Shape '[]
  ShapeS :: Shape xs -> Shape (x : xs)

-- | Automates the delivery of the 'Shape' singleton.
--   Inhabited by every possible list.
class HasShape (xs :: [k]) where theShape :: Shape xs

instance                HasShape '[]      where theShape = ShapeZ
instance HasShape xs => HasShape (x : xs) where theShape = ShapeS theShape


----------------------------- Utils ------------------------------

data Elem :: Type -> [Type] -> Type where
  Here :: Elem t (t : ts)
  There :: Elem t ts -> Elem t (y : ts)

class HasElem (t :: Type) (ts :: [Type]) where
  elementProof :: Elem t ts

instance HasElem t (t : ts) where
  elementProof = Here

instance {-# OVERLAPPABLE #-} HasElem t ts => HasElem t (x : ts) where
  elementProof = There elementProof

makeNSumExplicit :: Elem t ts -> t -> NSum ts
makeNSumExplicit Here x = Start x
makeNSumExplicit (There el) x = Next (makeNSumExplicit el x)

makeNSum :: HasElem t ts => t -> NSum ts
makeNSum = makeNSumExplicit elementProof


----------------------------- HasAvroSchema ------------------------------

instance forall x xs. (All HasAvroSchema (x : xs), HasShape xs) => HasAvroSchema (NSum (x : xs)) where
  schema = Tagged $ mkUnion $
    unTagged (schema @x) :| schemasToList (theSchemas @xs)

theSchemas :: (All HasAvroSchema xs, HasShape xs) => Schemas xs
theSchemas = schemasFromShape theShape

-- | The set of Tagged Schemas that match the list of types
--   Use of this type helps ensure the correctness of the HasAvroSchema instance.
data Schemas :: [Type] -> Type where
  SchemaZ :: Schemas '[]
  SchemaS :: Tagged x Schema -> Schemas xs -> Schemas (x : xs)

schemasToList :: Schemas xs -> [Schema]
schemasToList = \case
  SchemaZ               -> []
  SchemaS (Tagged s) ss -> s : schemasToList ss

schemasFromShape :: All HasAvroSchema xs => Shape xs -> Schemas xs
schemasFromShape = \case
  ShapeZ   -> SchemaZ
  ShapeS s -> SchemaS schema $ schemasFromShape s

