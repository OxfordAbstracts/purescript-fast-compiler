module Test.Sample where

import DTS

import Data.Newtype (unwrap)
import Effect (Effect)
import Effect.Class.Console (log)
import Prelude (mempty, Unit, ($))

someModule :: TsModule
someModule = TsModule
  [ TsDeclTypeDef (TsName "Nums") Public mempty (TsTypeArray TsTypeNumber)
  , TsDeclValueDef (TsName "user") Public
      ( TsTypeRecord
          [ TsRecordField "name" { readonly: true, optional: false } TsTypeString
          , TsRecordField "age" { readonly: true, optional: false } TsTypeNumber
          ]
      )
  , TsDeclValueDef (TsName "fun") Public
      ( TsTypeFunction
          (TsTypeArgsQuant mempty)
          [ TsFnArg (TsName "x") TsTypeNumber
          , TsFnArg (TsName "y") TsTypeNumber
          ]
          TsTypeString
      )
  ]

main :: Effect Unit
main = do
  log $ unwrap $ printTsModule someModule

