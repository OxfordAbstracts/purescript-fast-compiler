-- | This is a lightweight interface to
-- | [address-rfc2821](https://www.npmjs.com/package/address-rfc2821).
-- | Use this module to parse email envelope strings.  (See
-- | [here](https://stackoverflow.com/questions/201323/how-can-i-validate-an-email-address-using-a-regular-expression)
-- | where it is recommended against using regular expressions to
-- | parse emails).

module Data.RFC2821
       (
         module Data.RFC2821.Internal
       ) where

import Data.RFC2821.Internal
