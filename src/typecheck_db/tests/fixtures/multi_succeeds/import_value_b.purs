module Test.Multi.ValueB where

-- Uses `answer` after resolving through A's ModuleExports.
import Test.Multi.ValueA

double :: Int
double = answer
