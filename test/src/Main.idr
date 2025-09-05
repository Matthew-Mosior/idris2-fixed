module Main

import Fixed
import Hedgehog

%default total

main : IO ()
main = test
  [ Fixed.props 
  ]
