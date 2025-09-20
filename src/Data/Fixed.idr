module Data.Fixed

import Data.String

%hide Data.List.replicate

--------------------------------------------------------------------------------
--          Fixed
--------------------------------------------------------------------------------

||| The type of fixed-point fractional numbers.
public export
data Fixed : (res : Integer) -> Type where
  MkFixed :  Integer
          -> Fixed res

--------------------------------------------------------------------------------
--          Show Utility
--------------------------------------------------------------------------------

||| Render a fixed-point value to a string, with optional trailing zero chopping.
|||
||| @chop  whether to drop trailing zeros from the fractional part
||| @fa    the fixed-point value, whose type index encodes resolution
private
showFixed :  {res : Integer}
          -> (chop : Bool)
          -> (fa : Fixed res)
          -> String
showFixed chop fa@(MkFixed a) =
  case a < 0 of
    True =>
      let fixed = assert_total $
                  showFixed {res}
                            chop
                            (MkFixed (negate a))
        in "-" ++ fixed
    False =>
      let (i, d)  = divMod a res
          digits  = cast {to=Int} (length (show res)) - 1
          maxnum  = pow 10 (cast {to=Double} digits)
          fracnum = divCeil (d * cast {to=Integer} maxnum) res
          dot     = withDot (showIntegerZeros chop (cast digits) fracnum)
       in show i ++ dot
  where
    sigNum :  Integer
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
      let q = div n d
          r = mod n d
        in case sigNum r == negate (sigNum d) of
             True  =>
               (q - 1, r + d)
             False =>
               (q, r)
    chopZeros :  Integer
              -> String
    chopZeros 0 =
      ""
    chopZeros x =
      case mod x 10 == 0 of
        True  =>
          chopZeros (assert_smaller x (div x 10))
        False =>
          show x
    showIntegerZeros :  Bool
                     -> Nat
                     -> Integer
                     -> String
    showIntegerZeros True _      0 =
      ""
    showIntegerZeros chop digits n =
      let s       = show n
          s'      = case chop of
                      True  =>
                        chopZeros n
                      False =>
                        s
          padding = replicate (digits `minus` length s) '0'
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
--          Interfaces
--------------------------------------------------------------------------------

public export
{n : Integer} -> Num (Fixed n) where
  (MkFixed a) + (MkFixed b) = MkFixed (a + b)
  (MkFixed a) * (MkFixed b) = MkFixed (div (a * b) n)
  fromInteger i             = MkFixed (i * n)

public export
{n : Integer} -> Neg (Fixed n) where
  negate (MkFixed a)          = MkFixed (negate a)
  (-) (MkFixed a) (MkFixed b) = MkFixed (a - b)

public export
{n : Integer} -> Fractional (Fixed n) where
  (MkFixed a) / (MkFixed b) = MkFixed (div (a * n) b)
  recip (MkFixed a)         = MkFixed (div (n * n) a)

public export
{n : Integer} -> Eq (Fixed n) where
  (MkFixed a) == (MkFixed b) = a == b

public export
{n : Integer} -> Ord (Fixed n) where
  compare (MkFixed a) (MkFixed b) = compare a b

public export
{n : Integer} -> Show (Fixed n) where
  showPrec p fixed@(MkFixed a) =
    showParens (p >= App && a < 0) $
      showFixed False fixed

--------------------------------------------------------------------------------
--          E0/Uni
--------------------------------------------------------------------------------

||| +------------+---------------------+------+------------+
||| | Resolution | Scaling Factor      | Type | show 12345 |
||| +============+=====================+======+============+
||| | E0         | 1\1                 | Uni  | 12345.0    |
||| +------------+---------------------+------+------------+
public export
Uni : Type
Uni = Fixed 1

--------------------------------------------------------------------------------
--          E1/Deci
--------------------------------------------------------------------------------

||| +------------+---------------------+------+------------+
||| | Resolution | Scaling Factor      | Type | show 12345 |
||| +============+=====================+======+============+
||| | E1         | 1\10                | Deci | 1234.5     |
||| +------------+---------------------+------+------------+
public export
Deci : Type
Deci = Fixed 10

--------------------------------------------------------------------------------
--          E2/Centi
--------------------------------------------------------------------------------

||| +------------+---------------------+-------+------------+
||| | Resolution | Scaling Factor      | Type  | show 12345 |
||| +============+=====================+=======+============+
||| | E2         | 1\100               | Centi | 123.45     |
||| +------------+---------------------+-------+------------+
public export
Centi : Type
Centi = Fixed 100

--------------------------------------------------------------------------------
--          E3/Milli
--------------------------------------------------------------------------------

||| +------------+--------------------+-------+------------+
||| | Resolution | Scaling Factor     | Type  | show 12345 |
||| +============+====================+=======+============+
||| | E3         | 1\1000             | Milli | 12.345     |
||| +------------+--------------------+-------+------------+
public export
Milli : Type
Milli = Fixed 1000

--------------------------------------------------------------------------------
--          E4/TenthMilli
--------------------------------------------------------------------------------

||| +------------+--------------------+------------+------------+
||| | Resolution | Scaling Factor     | Type       | show 12345 |
||| +============+====================+=======+=================+
||| | E4         | 1\10000            | TenthMilli | 1.2345     |
||| +------------+--------------------+------------+------------+
public export
TenthMilli : Type
TenthMilli = Fixed 10000

--------------------------------------------------------------------------------
--          E5/HundredthMilli
--------------------------------------------------------------------------------

||| +------------+--------------------+------------------------+------------+
||| | Resolution | Scaling Factor     | Type                   | show 12345 |
||| +============+====================+========================+============+
||| | E5         | 1\100000           | HundredthMilli         | 0.12345    |
||| +------------+--------------------+------------------------+------------+
public export
HundredthMilli : Type
HundredthMilli = Fixed 100000

--------------------------------------------------------------------------------
--          E6/Micro
--------------------------------------------------------------------------------

||| +------------+-------------------+-------+------------+
||| | Resolution | Scaling Factor    | Type  | show 12345 |
||| +============+===================+=======+============+
||| | E6         | 1\1000000         | Micro | 0.012345   |
||| +------------+-------------------+-------+------------+
public export
Micro : Type
Micro = Fixed 1000000

--------------------------------------------------------------------------------
--          E7/DeciMicro
--------------------------------------------------------------------------------

||| +------------+-------------------+-----------+------------+
||| | Resolution | Scaling Factor    | Type      | show 12345 |
||| +============+===================+===========+============+
||| | E7         | 1\10000000        | DeciMicro | 0.0012345  |
||| +------------+-------------------+-----------+------------+
public export
DeciMicro : Type
DeciMicro = Fixed 10000000

--------------------------------------------------------------------------------
--          E8/CentiMicro
--------------------------------------------------------------------------------

||| +------------+--------------------+------------+------------+
||| | Resolution | Scaling Factor     | Type       | show 12345 |
||| +============+====================+============+============+
||| | E8         | 1\100000000        | CentiMicro | 0.00012345 |
||| +------------+--------------------+------------+------------+
public export
CentiMicro : Type
CentiMicro = Fixed 100000000

--------------------------------------------------------------------------------
--          E9/Nano
--------------------------------------------------------------------------------

||| +------------+------------------+------+-------------+
||| | Resolution | Scaling Factor   | Type | show 12345  |
||| +============+==================+======+=============+
||| | E9         | 1\1000000000     | Nano | 0.000012345 |
||| +------------+------------------+------+-------------+
public export
Nano : Type
Nano = Fixed 1000000000

--------------------------------------------------------------------------------
--          E10/DeciNano
--------------------------------------------------------------------------------

||| +------------+-----------------+----------+--------------+
||| | Resolution | Scaling Factor  | Type     | show 12345   |
||| +============+=================+==========+==============+
||| | E10        | 1\10000000000   | DeciNano | 0.0000012345 |
||| +------------+-----------------+----------+--------------+
public export
DeciNano : Type
DeciNano = Fixed 10000000000

--------------------------------------------------------------------------------
--          E11/CentiNano
--------------------------------------------------------------------------------

||| +------------+-----------------+-----------+---------------+
||| | Resolution | Scaling Factor  | Type      | show 12345    |
||| +============+=================+===========+===============+
||| | E11        | 1\100000000000  | CentiNano | 0.00000012345 |
||| +------------+-----------------+-----------+---------------+
public export
CentiNano : Type
CentiNano = Fixed 100000000000

--------------------------------------------------------------------------------
--          E12/Pico
--------------------------------------------------------------------------------

||| +------------+-----------------+------+----------------+
||| | Resolution | Scaling Factor  | Type | show 12345     |
||| +============+=================+======+================+
||| | E12        | 1\1000000000000 | Pico | 0.000000012345 |
||| +------------+-----------------+------+----------------+
public export
Pico : Type
Pico = Fixed 1000000000000

--------------------------------------------------------------------------------
--          withResolution
--------------------------------------------------------------------------------

||| Run a computation with the resolution available as an `Integer`.
export
withResolution :  {res : Integer}
               -> (f : Integer -> b)
               -> b
withResolution f =
  f res
