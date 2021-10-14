{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
module Avro.ToAvroSpec
( spec
)
where

import Avro.Data.Endpoint
import Avro.Data.Unions
import Data.Avro.Sum
import Data.Avro.EitherN
import Data.Avro.Encoding.ToAvro    (ToAvro (..))
import Data.Avro.HasAvroSchema

import Avro.TestUtils              (roundtripGen)
import HaskellWorks.Hspec.Hedgehog
import Hedgehog
import Test.Hspec
import Data.Int (Int32,Int64)
import Data.Text (Text)
import Data.Tagged (Tagged (..))
import Data.ByteString.Builder

{- HLINT ignore "Redundant do"        -}

spec :: Spec
spec = describe "Avro.ToAvroSpec" $ do
  describe "Should encode directly and decode via new value" $ do
    it "Unions" $ require $ property $ roundtripGen schema'Unions unionsGen
    it "Endpoint" $ require $ property $ roundtripGen schema'Endpoint endpointGen
    it "Sum types consistent" $ require $ property $ do
      u <- forAll unionsGen
      let u3 = unionsThree u
      toLazyByteString (toAvro (unTagged $ schema @(NSum '[Int32, Text, Int64])) u3) ===
        toLazyByteString (toAvro (unTagged $ schema @(Either3 Int32 Text Int64)) u3)

