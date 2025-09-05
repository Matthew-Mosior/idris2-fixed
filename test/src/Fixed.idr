module Fixed

import Hedgehog
import Data.Fixed

prop_e0_show : Property
prop_e0_show = property1 $
 show (the Uni (MkFixed 12345)) === "12345.0"

prop_e1_show : Property
prop_e1_show = property1 $
 show (the Deci (MkFixed 12345)) === "1234.5"

prop_e2_show : Property
prop_e2_show = property1 $
 show (the Centi (MkFixed 12345)) === "123.45"

prop_e3_show : Property
prop_e3_show = property1 $
 show (the Milli (MkFixed 12345)) === "12.345"

prop_e6_show : Property
prop_e6_show = property1 $
 show (the Micro (MkFixed 12345)) === "0.012345"

prop_e9_show : Property
prop_e9_show = property1 $
 show (the Nano (MkFixed 12345)) === "0.000012345"

prop_e12_show : Property
prop_e12_show = property1 $
 show (the Pico (MkFixed 12345)) === "0.000000012345"

export
props : Group
props = MkGroup "Fixed"
  [ ("prop_e0_show",  prop_e0_show)
  , ("prop_e1_show",  prop_e1_show)
  , ("prop_e2_show",  prop_e2_show)
  , ("prop_e3_show",  prop_e3_show)
  , ("prop_e6_show",  prop_e6_show)
  , ("prop_e9_show",  prop_e9_show)
  , ("prop_e12_show", prop_e12_show)
  ]
