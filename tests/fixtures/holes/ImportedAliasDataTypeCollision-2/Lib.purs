module ImportedAliasDataTypeCollision.Lib where

import ImportedAliasDataTypeCollision.DataTime (Time(..))

-- This module uses Time as the DATA TYPE.
-- Its exported value schemes contain Time (the data type).
mkTime :: Int -> Int -> Time
mkTime = Time
