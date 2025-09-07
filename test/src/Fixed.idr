module Fixed

import Hedgehog
import Data.Fixed

prop_e0_show : Property
prop_e0_show = property1 $
 show (the Uni (MkFixed 12345)) === "12345.0"

prop_e0_neg_show : Property
prop_e0_neg_show = property1 $
 show (the Uni (negate $ MkFixed 12345)) === "-12345.0"

prop_e0_add : Property
prop_e0_add = property1 $
  show ((the Uni (MkFixed 12345)) + (the Uni (12345))) === "24690.0"

prop_e0_mult : Property
prop_e0_mult = property1 $
  show ((the Uni (MkFixed 12345)) * (the Uni (MkFixed 12345))) === "152399025.0"

prop_e0_div : Property
prop_e0_div = property1 $
  show ((the Uni (MkFixed 12345)) / (the Uni (MkFixed 12345))) === "1.0"

prop_e0_frominteger : Property
prop_e0_frominteger = property1 $
  show (the Uni (fromInteger (the Integer 12345))) === "12345.0"

prop_e1_show : Property
prop_e1_show = property1 $
 show (the Deci (MkFixed 12345)) === "1234.5"

prop_e1_neg_show : Property
prop_e1_neg_show = property1 $
 show (the Deci (negate $ MkFixed 12345)) === "-1234.5"

prop_e1_add : Property
prop_e1_add = property1 $
  show ((the Deci (MkFixed 12345)) + (the Deci (MkFixed 12345))) === "2469.0"

prop_e1_mult : Property
prop_e1_mult = property1 $
  show ((the Deci (MkFixed 12345)) * (the Deci (MkFixed 12345))) === "1523990.2"

prop_e1_div : Property
prop_e1_div = property1 $
  show ((the Deci (MkFixed 12345)) / (the Deci (MkFixed 12345))) === "1.0"

prop_e1_frominteger : Property
prop_e1_frominteger = property1 $
  show (the Deci (fromInteger (the Integer 12345))) === "12345.0"

prop_e2_show : Property
prop_e2_show = property1 $
 show (the Centi (MkFixed 12345)) === "123.45"

prop_e2_neg_show : Property
prop_e2_neg_show = property1 $
 show (the Centi (negate $ MkFixed 12345)) === "-123.45"

prop_e2_add : Property
prop_e2_add = property1 $
  show ((the Centi (MkFixed 12345)) + (the Centi (MkFixed 12345))) === "246.90"

prop_e2_mult : Property
prop_e2_mult = property1 $
  show ((the Centi (MkFixed 12345)) * (the Centi (MkFixed 12345))) === "15239.90"

prop_e2_div : Property
prop_e2_div = property1 $
  show ((the Centi (MkFixed 12345)) / (the Centi (MkFixed 12345))) === "1.00"

prop_e2_frominteger : Property
prop_e2_frominteger = property1 $
  show (the Centi (fromInteger (the Integer 12345))) === "12345.00"

prop_e3_show : Property
prop_e3_show = property1 $
 show (the Milli (MkFixed 12345)) === "12.345"

prop_e3_neg_show : Property
prop_e3_neg_show = property1 $
 show (the Milli (negate $ MkFixed 12345)) === "-12.345"

prop_e3_add : Property
prop_e3_add = property1 $
  show ((the Milli (MkFixed 12345)) + (the Milli (MkFixed 12345))) === "24.690"

prop_e3_mult : Property
prop_e3_mult = property1 $
  show ((the Milli (MkFixed 12345)) * (the Milli (MkFixed 12345))) === "152.399"

prop_e3_div : Property
prop_e3_div = property1 $
  show ((the Milli (MkFixed 12345)) / (the Milli (MkFixed 12345))) === "1.000"

prop_e3_frominteger : Property
prop_e3_frominteger = property1 $
  show (the Milli (fromInteger (the Integer 12345))) === "12345.000"

prop_e6_show : Property
prop_e6_show = property1 $
 show (the Micro (MkFixed 12345)) === "0.012345"

prop_e6_neg_show : Property
prop_e6_neg_show = property1 $
 show (the Micro (negate $ MkFixed 12345)) === "-0.012345"

prop_e6_add : Property
prop_e6_add = property1 $
  show ((the Micro (MkFixed 12345)) + (the Micro (MkFixed 12345))) === "0.024690"

prop_e6_mult : Property
prop_e6_mult = property1 $
  show ((the Micro (MkFixed 12345)) * (the Micro (MkFixed 12345))) === "0.000152"

prop_e6_div : Property
prop_e6_div = property1 $
  show ((the Micro (MkFixed 12345)) / (the Micro (MkFixed 12345))) === "1.000000"

prop_e6_frominteger : Property
prop_e6_frominteger = property1 $
  show (the Micro (fromInteger (the Integer 12345))) === "12345.000000"

prop_e9_show : Property
prop_e9_show = property1 $
 show (the Nano (MkFixed 12345)) === "0.000012345"

prop_e9_neg_show : Property
prop_e9_neg_show = property1 $
 show (the Nano (negate $ MkFixed 12345)) === "-0.000012345"

prop_e9_add : Property
prop_e9_add = property1 $
  show ((the Nano (MkFixed 12345)) + (the Nano (MkFixed 12345))) === "0.000024690"

prop_e9_mult : Property
prop_e9_mult = property1 $
  show ((the Nano (MkFixed 12345)) * (the Nano (MkFixed 12345))) === "0.000000000"

prop_e9_div : Property
prop_e9_div = property1 $
  show ((the Nano (MkFixed 12345)) / (the Nano (MkFixed 12345))) === "1.000000000"

prop_e9_frominteger : Property
prop_e9_frominteger = property1 $
  show (the Nano (fromInteger (the Integer 12345))) === "12345.000000000"

prop_e12_show : Property
prop_e12_show = property1 $
 show (the Pico (MkFixed 12345)) === "0.000000012345"

prop_e12_neg_show : Property
prop_e12_neg_show = property1 $
 show (the Pico (negate $ MkFixed 12345)) === "-0.000000012345"

prop_e12_add : Property
prop_e12_add = property1 $
  show ((the Pico (MkFixed 12345)) + (the Pico (MkFixed 12345))) === "0.000000024690"

prop_e12_mult : Property
prop_e12_mult = property1 $
  show ((the Pico (MkFixed 12345)) * (the Pico (MkFixed 12345))) === "0.000000000000"

prop_e12_div : Property
prop_e12_div = property1 $
  show ((the Pico (MkFixed 12345)) / (the Pico (MkFixed 12345))) === "1.000000000000"

prop_e12_frominteger : Property
prop_e12_frominteger = property1 $
  show (the Pico (fromInteger (the Integer 12345))) === "12345.000000000000"

export
props : Group
props = MkGroup "Fixed"
  [ ("prop_e0_show", prop_e0_show)
  , ("prop_e0_neg_show", prop_e0_neg_show)
  , ("prop_e0_add", prop_e0_add)
  , ("prop_e0_mult", prop_e0_mult)
  , ("prop_e0_div", prop_e0_div)
  , ("prop_e0_frominteger", prop_e0_frominteger)
  , ("prop_e1_show", prop_e1_show)
  , ("prop_e1_neg_show", prop_e1_neg_show)
  , ("prop_e1_add", prop_e1_add)
  , ("prop_e1_mult", prop_e1_mult)
  , ("prop_e1_div", prop_e1_div)
  , ("prop_e1_frominteger", prop_e1_frominteger)
  , ("prop_e2_show", prop_e2_show)
  , ("prop_e2_neg_show", prop_e2_neg_show)
  , ("prop_e2_add", prop_e2_add)
  , ("prop_e2_mult", prop_e2_mult)
  , ("prop_e2_div", prop_e2_div)
  , ("prop_e2_frominteger", prop_e2_frominteger)
  , ("prop_e3_show", prop_e3_show)
  , ("prop_e3_neg_show", prop_e3_neg_show)
  , ("prop_e3_add", prop_e3_add)
  , ("prop_e3_mult", prop_e3_mult)
  , ("prop_e3_div", prop_e3_div)
  , ("prop_e3_frominteger", prop_e3_frominteger)
  , ("prop_e6_show", prop_e6_show)
  , ("prop_e6_neg_show", prop_e6_neg_show)
  , ("prop_e6_add", prop_e6_add)
  , ("prop_e6_mult", prop_e6_mult)
  , ("prop_e6_div", prop_e6_div)
  , ("prop_e6_frominteger", prop_e6_frominteger)
  , ("prop_e9_show", prop_e9_show)
  , ("prop_e9_neg_show", prop_e9_neg_show)
  , ("prop_e9_add", prop_e9_add)
  , ("prop_e9_mult", prop_e9_mult)
  , ("prop_e9_div", prop_e9_div)
  , ("prop_e9_frominteger", prop_e9_frominteger)
  , ("prop_e12_show", prop_e12_show)
  , ("prop_e12_neg_show", prop_e12_neg_show)
  , ("prop_e12_add", prop_e12_add)
  , ("prop_e12_mult", prop_e12_mult)
  , ("prop_e12_div", prop_e12_div)
  , ("prop_e12_frominteger", prop_e12_frominteger)
  ]
