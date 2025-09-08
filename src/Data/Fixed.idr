module Data.Fixed

import Data.String

%hide Data.List.replicate

--------------------------------------------------------------------------------
--          Fixed
--------------------------------------------------------------------------------

||| The type of fixed-point fractional numbers.
public export
data Fixed : Type -> Type where
  MkFixed :  Integer
          -> Fixed a

--------------------------------------------------------------------------------
--          HasResolution
--------------------------------------------------------------------------------

||| Types which can be used as a resolution argument to `Fixed`
||| must implement the `HasResolution`  interface.
||| The resolution or scaling factor determines the number of digits in the fractional part.
public export
interface HasResolution a where
  resolution      :  a
                  -> Integer

--------------------------------------------------------------------------------
--          Show Utility
--------------------------------------------------------------------------------

||| Convert a fixed-point number to a string.
|||
||| This function takes a value-level phantom of the resolution type, a flag
||| indicating whether to remove trailing zeros in the fractional part, and a
||| `Fixed a` number. It produces a `String` representation of the number,
||| inserting a decimal point in the correct position according to the resolution.
|||
||| Negative numbers are properly prefixed with `"-"`.
showFixed  :  HasResolution a
           => (witness : a)
           -> Bool
           -> Fixed a
           -> String
showFixed witness choptrailingzeros fa@(MkFixed a) =
  case a < 0 of
    True  =>
      let fixed = assert_total $
                    showFixed witness
                              choptrailingzeros
                              (MkFixed (negate a))
        in "-" ++ fixed
    False =>
      let res     = resolution witness
          (i, d)  = divMod a
                           res
          digits  = cast {to=Int} (length (show res)) - 1
          maxnum  = pow 10
                        (cast {to=Double} digits)
          fracNum = divCeil (d * (cast {to=Integer} maxnum))
                            res
          dot     = withDot (showIntegerZeros choptrailingzeros (cast {to=Nat} digits) fracNum)
        in show i ++ dot
  where
    sigNum    :  Integer
              -> Integer
    sigNum n =
      case n < 0 of
        True  =>
          -1
        False =>
          case n == 0 of
            True  =>
              0
            False =>
              1
    divMod :  Integer
           -> Integer
           -> (Integer, Integer)
    divMod n d =
      let q  = div n d
          r  = mod n d
        in case sigNum r == negate (sigNum d) of
             True  =>
               (q - 1, r + d)
             False =>
               (q, r)
    chopZeros :  Integer
              -> String
    chopZeros 0 =
      ""
    chopZeros a =
      case mod a 10 == 0 of
        True  =>
          chopZeros (assert_smaller a (div a 10))
        False =>
          show a
    showIntegerZeros :  Bool
                     -> Nat
                     -> Integer
                     -> String
    showIntegerZeros True              _      0 =
      ""
    showIntegerZeros choptrailingzeros digits a =
      let s       = show a
          s'      = case choptrailingzeros of
                      True  =>
                        chopZeros a
                      False =>
                        s
          padding = replicate (digits `minus` (length s)) '0'
        in padding ++ s'
    withDot :  String
            -> String
    withDot "" =
      ""
    withDot s  =
      "." ++ s
    divCeil :  Integer
            -> Integer
            -> Integer
    divCeil x y =
      (x + y - 1) `div` y

--------------------------------------------------------------------------------
--          E0/Uni
--------------------------------------------------------------------------------

||| +------------+---------------------+------+------------+
||| | Resolution | Scaling Factor      | Type | show 12345 |
||| +============+=====================+======+============+
||| | E0         | 1\1                 | Uni  | 12345.0    |
||| +------------+---------------------+------+------------+
public export
data E0 : Type where
  MkE0 : E0

public export
Uni : Type
Uni = Fixed E0

public export
HasResolution E0 where
  resolution MkE0 = 1

public export
Num (Fixed E0) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE0))
  fromInteger i             = MkFixed (i * resolution MkE0)

public export
Num (Fixed E0) => Neg (Fixed E0) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b) 

public export
Fractional (Fixed E0) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE0) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE0 * resolution MkE0) a)

public export
(HasResolution E0) => Show (Fixed E0) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE0 False n

--------------------------------------------------------------------------------
--          E1/Deci
--------------------------------------------------------------------------------

||| +------------+---------------------+------+------------+
||| | Resolution | Scaling Factor      | Type | show 12345 |
||| +============+=====================+======+============+
||| | E1         | 1\10                | Deci | 1234.5     |
||| +------------+---------------------+------+------------+
public export
data E1 : Type where
  MkE1 : E1

public export
Deci : Type
Deci = Fixed E1

public export
HasResolution E1 where
  resolution MkE1 = 10

public export
Num (Fixed E1) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE1))
  fromInteger i             = MkFixed (i * resolution MkE1)

public export
Num (Fixed E1) => Neg (Fixed E1) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E1) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE1) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE1 * resolution MkE1) a)

public export
(HasResolution E1) => Show (Fixed E1) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE1 False n

--------------------------------------------------------------------------------
--          E2/Centi
--------------------------------------------------------------------------------

||| +------------+---------------------+-------+------------+
||| | Resolution | Scaling Factor      | Type  | show 12345 |
||| +============+=====================+=======+============+
||| | E2         | 1\100               | Centi | 123.45     |
||| +------------+---------------------+-------+------------+
public export
data E2 : Type where
  MkE2 : E2

public export
Centi : Type
Centi = Fixed E2

public export
HasResolution E2 where
  resolution MkE2 = 100

public export
Num (Fixed E2) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE2))
  fromInteger i             = MkFixed (i * resolution MkE2)

public export
Num (Fixed E2) => Neg (Fixed E2) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E2) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE2) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE2 * resolution MkE2) a)

public export
(HasResolution E2) => Show (Fixed E2) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE2 False n

--------------------------------------------------------------------------------
--          E3/Milli
--------------------------------------------------------------------------------

||| +------------+--------------------+-------+------------+
||| | Resolution | Scaling Factor     | Type  | show 12345 |
||| +============+====================+=======+============+
||| | E3         | 1\1000             | Milli | 12.345     |
||| +------------+--------------------+-------+------------+
public export
data E3 : Type where
  MkE3 : E3

public export
Milli : Type
Milli = Fixed E3

public export
HasResolution E3 where
  resolution MkE3 = 1000

public export
Num (Fixed E3) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE3))
  fromInteger i             = MkFixed (i * resolution MkE3)

public export
Num (Fixed E3) => Neg (Fixed E3) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E3) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE3) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE3 * resolution MkE3) a)

public export
(HasResolution E3) => Show (Fixed E3) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE3 False n

--------------------------------------------------------------------------------
--          E4/TenthMilli
--------------------------------------------------------------------------------

||| +------------+--------------------+------------+------------+
||| | Resolution | Scaling Factor     | Type       | show 12345 |
||| +============+====================+=======+=================+
||| | E4         | 1\10000            | TenthMilli | 1.2345     |
||| +------------+--------------------+------------+------------+
public export
data E4 : Type where
  MkE4 : E4

public export
TenthMilli : Type
TenthMilli = Fixed E4

public export
HasResolution E4 where
  resolution MkE4 = 10000

public export
Num (Fixed E4) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE4))
  fromInteger i             = MkFixed (i * resolution MkE4)

public export
Num (Fixed E4) => Neg (Fixed E4) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E4) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE4) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE4 * resolution MkE4) a)

public export
(HasResolution E4) => Show (Fixed E4) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE4 False n

--------------------------------------------------------------------------------
--          E5/HundredthMilli
--------------------------------------------------------------------------------

||| +------------+--------------------+------------------------+------------+
||| | Resolution | Scaling Factor     | Type                   | show 12345 |
||| +============+====================+========================+============+
||| | E5         | 1\100000           | HundredthMilli         | 0.12345    |
||| +------------+--------------------+------------------------+------------+
public export
data E5 : Type where
  MkE5 : E5

public export
HundredthMilli : Type
HundredthMilli = Fixed E5

public export
HasResolution E5 where
  resolution MkE5 = 100000

public export
Num (Fixed E5) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE5))
  fromInteger i             = MkFixed (i * resolution MkE5)

public export
Num (Fixed E5) => Neg (Fixed E5) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E5) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE5) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE5 * resolution MkE5) a)

public export
(HasResolution E5) => Show (Fixed E5) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE5 False n

--------------------------------------------------------------------------------
--          E6/Micro
--------------------------------------------------------------------------------

||| +------------+-------------------+-------+------------+
||| | Resolution | Scaling Factor    | Type  | show 12345 |
||| +============+===================+=======+============+
||| | E6         | 1\1000000         | Micro | 0.012345   |
||| +------------+-------------------+-------+------------+
public export
data E6 : Type where
  MkE6 : E6

public export
Micro : Type
Micro = Fixed E6

public export
HasResolution E6 where
  resolution MkE6 = 1000000

public export
Num (Fixed E6) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE6))
  fromInteger i             = MkFixed (i * resolution MkE6)

public export
Num (Fixed E6) => Neg (Fixed E6) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E6) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE6) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE6 * resolution MkE6) a)

public export
(HasResolution E6) => Show (Fixed E6) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE6 False n

--------------------------------------------------------------------------------
--          E7/DeciMicro
--------------------------------------------------------------------------------

||| +------------+-------------------+-----------+------------+
||| | Resolution | Scaling Factor    | Type      | show 12345 |
||| +============+===================+===========+============+
||| | E7         | 1\10000000        | DeciMicro | 0.0012345  |
||| +------------+-------------------+-----------+------------+
public export
data E7 : Type where
  MkE7 : E7

public export
DeciMicro : Type
DeciMicro = Fixed E7

public export
HasResolution E7 where
  resolution MkE7 = 10000000

public export
Num (Fixed E7) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE7))
  fromInteger i             = MkFixed (i * resolution MkE7)

public export
Num (Fixed E7) => Neg (Fixed E7) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E7) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE7) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE7 * resolution MkE7) a)

public export
(HasResolution E7) => Show (Fixed E7) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE7 False n

--------------------------------------------------------------------------------
--          E8/CentiMicro
--------------------------------------------------------------------------------

||| +------------+--------------------+------------+------------+
||| | Resolution | Scaling Factor     | Type       | show 12345 |
||| +============+====================+============+============+
||| | E8         | 1\100000000        | CentiMicro | 0.00012345 |
||| +------------+--------------------+------------+------------+
public export
data E8 : Type where
  MkE8 : E8

public export
CentiMicro : Type
CentiMicro = Fixed E8

public export
HasResolution E8 where
  resolution MkE8 = 100000000

public export
Num (Fixed E8) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE8))
  fromInteger i             = MkFixed (i * resolution MkE8)

public export
Num (Fixed E8) => Neg (Fixed E8) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E8) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE8) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE8 * resolution MkE8) a)

public export
(HasResolution E8) => Show (Fixed E8) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE8 False n

--------------------------------------------------------------------------------
--          E9/Nano
--------------------------------------------------------------------------------

||| +------------+------------------+------+-------------+
||| | Resolution | Scaling Factor   | Type | show 12345  |
||| +============+==================+======+=============+
||| | E9         | 1\1000000000     | Nano | 0.000012345 |
||| +------------+------------------+------+-------------+
public export
data E9 : Type where
  MkE9 : E9

public export
Nano : Type
Nano = Fixed E9

public export
HasResolution E9 where
  resolution MkE9 = 1000000000

public export
Num (Fixed E9) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE9))
  fromInteger i             = MkFixed (i * resolution MkE9)

public export
Num (Fixed E9) => Neg (Fixed E9) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E9) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE9) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE9 * resolution MkE9) a)

public export
(HasResolution E9) => Show (Fixed E9) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE9 False n

--------------------------------------------------------------------------------
--          E10/DeciNano
--------------------------------------------------------------------------------

||| +------------+-----------------+----------+--------------+
||| | Resolution | Scaling Factor  | Type     | show 12345   |
||| +============+=================+==========+==============+
||| | E10        | 1\10000000000   | DeciNano | 0.0000012345 |
||| +------------+-----------------+----------+--------------+
public export
data E10 : Type where
  MkE10 : E10

public export
DeciNano : Type
DeciNano = Fixed E10

public export
HasResolution E10 where
  resolution MkE10 = 10000000000

public export
Num (Fixed E10) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE10))
  fromInteger i             = MkFixed (i * resolution MkE10)

public export
Num (Fixed E10) => Neg (Fixed E10) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E10) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE10) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE10 * resolution MkE10) a)

public export
(HasResolution E10) => Show (Fixed E10) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE10 False n

--------------------------------------------------------------------------------
--          E11/CentiNano
--------------------------------------------------------------------------------

||| +------------+-----------------+-----------+---------------+
||| | Resolution | Scaling Factor  | Type      | show 12345    |
||| +============+=================+===========+===============+
||| | E11        | 1\100000000000  | CentiNano | 0.00000012345 |
||| +------------+-----------------+-----------+---------------+
public export
data E11 : Type where
  MkE11 : E11

public export
CentiNano : Type
CentiNano = Fixed E11

public export
HasResolution E11 where
  resolution MkE11 = 100000000000

public export
Num (Fixed E11) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE11))
  fromInteger i             = MkFixed (i * resolution MkE11)

public export
Num (Fixed E11) => Neg (Fixed E11) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E11) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE11) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE11 * resolution MkE11) a)

public export
(HasResolution E11) => Show (Fixed E11) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE11 False n

--------------------------------------------------------------------------------
--          E12/Pico
--------------------------------------------------------------------------------

||| +------------+-----------------+------+----------------+
||| | Resolution | Scaling Factor  | Type | show 12345     |
||| +============+=================+======+================+
||| | E12        | 1\1000000000000 | Pico | 0.000000012345 |
||| +------------+-----------------+------+----------------+
public export
data E12 : Type where
  MkE12 : E12

public export
Pico : Type
Pico = Fixed E12

public export
HasResolution E12 where
  resolution MkE12 = 1000000000000

public export
Num (Fixed E12) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution MkE12))
  fromInteger i             = MkFixed (i * resolution MkE12)

public export
Num (Fixed E12) => Neg (Fixed E12) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
Fractional (Fixed E12) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution MkE12) b)
  recip (MkFixed a)         = MkFixed (div (resolution MkE12 * resolution MkE12) a)

public export
(HasResolution E12) => Show (Fixed E12) where
  showPrec p n@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed MkE12 False n

--------------------------------------------------------------------------------
--          withResolution
--------------------------------------------------------------------------------

||| Execute a computation that requires the numeric resolution associated
||| with a phantom type `a`.
|||
||| The `HasResolution` constraint guarantees that values of type `a`
||| carry a fixed scaling factor (e.g. 10, 100, 1000). By supplying an
||| explicit `witness : a`, this function retrieves its resolution and
||| passes it to the continuation `f`.
|||
||| This is typically used when implementing arithmetic for `Fixed a`,
||| where calculations must be scaled by the appropriate resolution.
|||
||| @witness  the phantom value whose resolution is looked up
||| @f        a continuation expecting the resolution as an `Integer`
||| @return   the result of applying `f` to the resolution, in the context `b`
export
withResolution :  HasResolution a
               => (witness : a)
               -> (f : Integer -> b)
               -> b
withResolution witness f =
  f (resolution witness)
