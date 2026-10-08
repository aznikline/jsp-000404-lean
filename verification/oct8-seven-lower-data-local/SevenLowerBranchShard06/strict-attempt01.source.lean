import Jsp000404.SevenLowerReplay

/-! SOURCE_ONLY literal certificate data; no kernel PASS is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerBranchShard06
open SevenLowerReplay
def cycle0000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 1 (![3, 2, 5, 1, 4]), .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![3, 2, 5, 1, 4]), .triangle 4 2, .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 2, 5, 1, 4]), .triangle 8 1, .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0003 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 5, 1, 4])]

def cycle0004 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 5, 1, 4])]

def cycle0005 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 1, 4]), .triangle 2 1]

def cycle0006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 1, 4]), .triangle 2 1]

def cycle0007 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![3, 2, 5, 1, 4]), .gapLower 0 1 (![3, 2, 5, 1, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0008 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 2, 5, 1, 4]), .triangle 6 1, .gapLower 0 1 (![3, 2, 5, 1, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0009 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 1 (![3, 2, 5, 1, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 5, 1, 4])]

def cycle0010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 1 (![3, 2, 5, 1, 4]), .corridorLower 0 3, .gapLower 0 5 (![3, 2, 5, 1, 4]), .triangle 2 1]

def cycle0011 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 2, 5, 1, 4]), .gapLower 0 2 (![3, 2, 5, 1, 4]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0012 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![3, 2, 5, 1, 4]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 5, 1, 4])]

def cycle0013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![3, 2, 5, 1, 4]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 1, 4]), .triangle 2 1]

def cycle0014 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![3, 2, 5, 1, 4]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 5, 1, 4])]

def cycle0015 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.gapLower 0 3 (![3, 2, 5, 1, 4]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 1, 4]), .triangle 2 1]

def cycle0016 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 1, 4]), .gapLower 0 4 (![3, 2, 5, 1, 4])]

def cycle0017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 3, 4, 0, 5]), .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0018 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .gapLower 1 1 (![2, 3, 4, 0, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0019 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 5 0]

def cycle0020 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 0, .triangle 9 0, .triangle 5 1]

def cycle0021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .gapLower 0 0 (![3, 2, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 2, 4, 1, 5]), .triangle 5 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 0, 5]), .triangle 3 0]

def cycle0023 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 2 (![3, 2, 4, 1, 5])]

def cycle0024 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .triangle 11 0, .triangle 5 0]

def cycle0025 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 1 1 (![3, 2, 4, 0, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0026 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2 (![3, 2, 4, 0, 5]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0027 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 3 (![3, 2, 4, 0, 5]), .triangle 11 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0028 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .gapLower 0 0 (![3, 2, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![3, 2, 4, 0, 5])]

def cycle0029 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 2, 4, 0, 5]), .triangle 3 0]

def cycle0030 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 2, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 4, 1, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![3, 2, 4, 1, 5])]

def cycle0033 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 2, 4, 1, 5]), .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0034 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 4, 1, 5])]

def cycle0035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 1, 5]), .triangle 9 1, .triangle 5 1]

def cycle0036 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 4, 1, 5]), .gapLower 0 0 (![3, 2, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0037 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![3, 2, 4, 1, 5]), .triangle 4 2, .gapLower 0 0 (![3, 2, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 2, 4, 1, 5]), .triangle 7 1, .gapLower 0 0 (![3, 2, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0039 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 4, 1, 5])]

def cycle0040 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 4, 1, 5])]

def cycle0041 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 1, 5]), .triangle 3 1]

def cycle0042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 1, 5]), .triangle 3 1]

def cycle0043 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 4, 1, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![3, 2, 4, 1, 5])]

def cycle0044 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 2, 4, 1, 5]), .triangle 5 1, .gapLower 0 1 (![3, 2, 4, 1, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0045 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 1 (![3, 2, 4, 1, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 4, 1, 5])]

def cycle0046 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 1 (![3, 2, 4, 1, 5]), .corridorLower 0 3, .gapLower 0 5 (![3, 2, 4, 1, 5]), .triangle 9 1, .triangle 5 1]

def cycle0047 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 2, 4, 1, 5]), .gapLower 0 2 (![3, 2, 4, 1, 5]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0048 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![3, 2, 4, 1, 5]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 4, 1, 5])]

def cycle0049 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![3, 2, 4, 1, 5]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 1, 5]), .triangle 3 1]

def cycle0050 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![3, 2, 4, 1, 5]), .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 4, 1, 5])]

def cycle0051 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.gapLower 0 3 (![3, 2, 4, 1, 5]), .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 1, 5]), .triangle 3 1]

def cycle0052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 1, 5]), .gapLower 0 4 (![3, 2, 4, 1, 5])]

def cycle0053 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 3, 4, 5, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0054 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0055 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 4, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 5 0]

def cycle0056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 0, .triangle 9 0, .triangle 5 1]

def cycle0057 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0058 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 14 0, .triangle 8 2, .triangle 9 1, .gapLower 0 2 (![3, 2, 4, 5, 1])]

def cycle0059 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 2 (![3, 2, 4, 5, 1])]

def cycle0060 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .gapLower 1 1 (![3, 2, 4, 5, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0061 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 2 (![3, 2, 4, 5, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0062 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 3 (![3, 2, 4, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0063 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 1 4 (![3, 2, 4, 5, 0]), .triangle 12 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0064 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 2, 4, 5, 0])]

def cycle0065 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 2, 4, 5, 1]), .gapLower 0 5 (![3, 2, 4, 5, 1])]

def cycle0066 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 2, 4, 5, 1]), .gapLower 0 5 (![3, 2, 4, 5, 1])]

def cycle0067 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 4, 5, 1]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0068 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![3, 2, 4, 5, 1])]

def cycle0069 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![3, 2, 4, 5, 1]), .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0070 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 4, 5, 1]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0071 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 5, 1])]

def cycle0072 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 4, 5, 1]), .gapLower 0 0 (![3, 2, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0073 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 4, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![3, 2, 4, 5, 1])]

def cycle0074 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![3, 2, 4, 5, 1]), .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0075 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 4, 5, 1]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0076 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 5, 1])]

def cycle0077 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 5, 1])]

def cycle0078 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 4, 5, 1]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![3, 2, 4, 5, 1])]

def cycle0079 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![3, 2, 4, 5, 1]), .triangle 5 1, .gapLower 0 1 (![3, 2, 4, 5, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 4, 5, 1]), .triangle 6 1, .gapLower 0 1 (![3, 2, 4, 5, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0081 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 1 (![3, 2, 4, 5, 1]), .corridorLower 0 3, .gapLower 0 5 (![3, 2, 4, 5, 1])]

def cycle0082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![3, 2, 4, 5, 1]), .gapLower 0 2 (![3, 2, 4, 5, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 4, 5, 1]), .triangle 9 1, .gapLower 0 2 (![3, 2, 4, 5, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0084 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 2 (![3, 2, 4, 5, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 5, 1])]

def cycle0085 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 4, 5, 1]), .gapLower 0 3 (![3, 2, 4, 5, 1]), .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0086 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![3, 2, 4, 5, 1]), .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 5, 1])]

def cycle0087 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 4, 5, 1]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 4, 5, 1])]

def cycle0088 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 5, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 2, .gapLower 2 3 (![1, 3, 0, 5, 4])]

def cycle0089 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 5, 4, 1]), .gapLower 0 0 (![3, 2, 5, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![1, 3, 0, 5, 4]), .triangle 6 0]

def cycle0090 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 5, 4, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 3, 0, 5, 4]), .triangle 5 0]

def cycle0091 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0092 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 3, 5, 4, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0093 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0094 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 3, 5, 4, 0]), .triangle 15 0, .corridorLower 4 5, .corridorUpper 2 4, .triangle 5 0, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0095 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0096 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 14 0, .gapLower 5 2 (![4, 0, 3, 1, 2]), .triangle 6 1]

def cycle0097 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 13 0, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![3, 2, 5, 4, 1])]

def cycle0098 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .triangle 11 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0099 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 10 0, .gapLower 2 0 (![3, 1, 0, 5, 4]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0100 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 2 1 (![3, 1, 0, 5, 4]), .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0101 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 2 (![3, 1, 0, 5, 4]), .triangle 10 2, .gapLower 1 0 (![3, 2, 5, 4, 0]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0102 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 5, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 2, .gapLower 2 3 (![3, 1, 0, 5, 4])]

def cycle0103 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 5, 4, 1]), .gapLower 0 0 (![3, 2, 5, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![3, 1, 0, 5, 4]), .triangle 6 0]

def cycle0104 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 5, 4, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 1, 0, 5, 4]), .triangle 5 0]

def cycle0105 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 1 1 (![3, 2, 5, 4, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0106 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 15 2, .gapLower 1 2 (![3, 2, 5, 4, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0107 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 3 (![3, 2, 5, 4, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0108 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 4 (![3, 2, 5, 4, 0]), .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0109 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 2, 5, 4, 0])]

def cycle0110 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 2, 5, 4, 1]), .gapLower 0 5 (![3, 2, 5, 4, 1])]

def cycle0111 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 2, 5, 4, 1]), .gapLower 0 5 (![3, 2, 5, 4, 1])]

def cycle0112 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 5, 4, 1]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0113 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![3, 2, 5, 4, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0114 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![3, 2, 5, 4, 1]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0115 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 5, 4, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0116 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 4, 1])]

def cycle0117 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 5, 4, 1]), .gapLower 0 0 (![3, 2, 5, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0118 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![3, 2, 5, 4, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0119 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![3, 2, 5, 4, 1]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0120 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 5, 4, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0121 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 4, 1])]

def cycle0122 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 4, 1])]

def cycle0123 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![3, 2, 5, 4, 1]), .gapLower 0 1 (![3, 2, 5, 4, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0124 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![3, 2, 5, 4, 1]), .triangle 6 1, .gapLower 0 1 (![3, 2, 5, 4, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0125 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 5, 4, 1]), .triangle 5 1, .gapLower 0 1 (![3, 2, 5, 4, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0126 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 1 (![3, 2, 5, 4, 1]), .corridorLower 0 3, .gapLower 0 5 (![3, 2, 5, 4, 1])]

def cycle0127 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![3, 2, 5, 4, 1]), .gapLower 0 2 (![3, 2, 5, 4, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0128 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 5, 4, 1]), .triangle 9 2, .gapLower 0 2 (![3, 2, 5, 4, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0129 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![3, 2, 5, 4, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 4, 1])]

def cycle0130 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 5, 4, 1]), .gapLower 0 3 (![3, 2, 5, 4, 1]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0131 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![3, 2, 5, 4, 1]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 4, 1])]

def cycle0132 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![3, 2, 5, 4, 1]), .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 4, 1])]

def cycle0133 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 3, 5, 0, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0134 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .triangle 14 1, .gapLower 1 1 (![2, 3, 5, 0, 4]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0135 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .gapLower 1 2 (![2, 3, 5, 0, 4]), .corridorLower 1 3, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0136 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 2 0 (![1, 3, 5, 0, 4]), .gapLower 2 5 (![1, 3, 5, 0, 4]), .triangle 5 0]

def cycle0137 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 17 1, .gapLower 2 1 (![1, 3, 5, 0, 4]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0138 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .gapLower 2 2 (![1, 3, 5, 0, 4]), .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0139 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 2 3 (![1, 3, 5, 0, 4]), .triangle 17 1, .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0140 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![1, 3, 5, 0, 4])]

def cycle0141 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 1, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 3, 5, 0, 4]), .triangle 5 0]

def cycle0142 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0143 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 1, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0144 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3]
    constant := ![(0), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 4 1, .triangle 10 2, .triangle 14 0, .triangle 8 0]

def cycle0145 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .triangle 12 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0146 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0147 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .triangle 17 1, .gapLower 2 0 (![3, 5, 1, 0, 4]), .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0148 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .gapLower 2 1 (![3, 5, 1, 0, 4]), .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0149 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 2 (![3, 5, 1, 0, 4]), .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0150 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 3 (![3, 5, 1, 0, 4]), .triangle 12 2, .triangle 14 1, .gapLower 1 0 (![3, 5, 2, 0, 4]), .gapLower 1 5 (![3, 5, 2, 0, 4]), .triangle 2 0]

def cycle0151 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![3, 5, 1, 0, 4])]

def cycle0152 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 1, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 1, 0, 4]), .triangle 5 0]

def cycle0153 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 17 0, .triangle 14 0, .gapLower 1 0 (![3, 5, 2, 0, 4]), .gapLower 1 5 (![3, 5, 2, 0, 4]), .triangle 2 0]

def cycle0154 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 2, .gapLower 1 1 (![3, 5, 2, 0, 4]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0155 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2 (![3, 5, 2, 0, 4]), .triangle 14 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0156 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![3, 5, 2, 0, 4]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0157 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![3, 5, 2, 0, 4])]

def cycle0158 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 5, 2, 0, 4]), .triangle 2 0]

def cycle0159 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0160 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 1 (![3, 5, 2, 1, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0161 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![3, 5, 2, 1, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0162 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 5, 2, 1, 4]), .triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0163 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 5, 2, 1, 4])]

def cycle0164 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 5, 2, 1, 4]), .triangle 2 1]

def cycle0165 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 1 (![3, 5, 2, 1, 4]), .gapLower 0 0 (![3, 5, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0166 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![3, 5, 2, 1, 4]), .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0167 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 5, 2, 1, 4]), .triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0168 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 5, 2, 1, 4])]

def cycle0169 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 5, 2, 1, 4])]

def cycle0170 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 5, 2, 1, 4]), .triangle 2 1]

def cycle0171 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 5, 2, 1, 4]), .triangle 2 1]

def cycle0172 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 5, 2, 1, 4]), .gapLower 0 1 (![3, 5, 2, 1, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0173 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 5, 2, 1, 4]), .triangle 6 2, .gapLower 0 1 (![3, 5, 2, 1, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0174 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 1 (![3, 5, 2, 1, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 5, 2, 1, 4])]

def cycle0175 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 1 (![3, 5, 2, 1, 4]), .corridorLower 0 3, .gapLower 0 5 (![3, 5, 2, 1, 4]), .triangle 2 1]

def cycle0176 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 5, 2, 1, 4]), .gapLower 0 2 (![3, 5, 2, 1, 4]), .triangle 8 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0177 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![3, 5, 2, 1, 4]), .triangle 8 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 5, 2, 1, 4])]

def cycle0178 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![3, 5, 2, 1, 4]), .corridorLower 0 5, .gapLower 0 5 (![3, 5, 2, 1, 4]), .triangle 2 1]

def cycle0179 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![3, 5, 2, 1, 4]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 5, 2, 1, 4])]

def cycle0180 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 3 (![3, 5, 2, 1, 4]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 5, 2, 1, 4]), .triangle 2 1]

def cycle0181 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 5, 2, 1, 4]), .gapLower 0 4 (![3, 5, 2, 1, 4])]

def cycle0182 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .triangle 12 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0183 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 3, 4, 5, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0184 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .triangle 15 1, .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0185 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .triangle 15 1, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0186 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0187 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 17 1, .gapLower 2 1 (![1, 3, 5, 0, 4]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0188 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![1, 3, 5, 0, 4])]

def cycle0189 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 4, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 3, 5, 0, 4]), .triangle 5 0]

def cycle0190 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0191 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 3, 5, 4, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0192 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .triangle 14 1, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0193 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .gapLower 1 2 (![2, 3, 5, 4, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0194 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 5, .distance 4 5, .theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 3 (![2, 3, 5, 4, 0]), .triangle 15 1, .corridorLower 4 5, .corridorUpper 2 4, .triangle 5 0, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0195 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 3, 5, 4, 0]), .triangle 15 0, .corridorLower 4 5, .corridorUpper 2 4, .triangle 5 0, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0196 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0197 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 3 (![3, 5, 2, 4, 1])]

def cycle0198 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 0, .triangle 17 1, .gapLower 2 0 (![3, 5, 1, 0, 4]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0199 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 0, .gapLower 2 1 (![3, 5, 1, 0, 4]), .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0200 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 2 2 (![3, 5, 1, 0, 4]), .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0201 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (-2), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 3 (![3, 5, 1, 0, 4]), .triangle 12 2, .triangle 14 1, .gapLower 1 0 (![3, 5, 2, 4, 0]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0202 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![3, 5, 1, 0, 4])]

def cycle0203 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 4, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 1, 0, 4]), .triangle 5 0]

def cycle0204 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 5, 2, 4, 0]), .triangle 11 1, .triangle 10 0, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 2, 4, 1]), .gapLower 0 5 (![3, 5, 2, 4, 1])]

def cycle0205 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 2, .gapLower 1 1 (![3, 5, 2, 4, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0206 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 1 2 (![3, 5, 2, 4, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0207 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 2 0, .gapLower 1 3 (![3, 5, 2, 4, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0208 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 1 4 (![3, 5, 2, 4, 0]), .triangle 11 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0209 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![3, 5, 2, 4, 0])]

def cycle0210 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 2, 4, 1]), .gapLower 0 5 (![3, 5, 2, 4, 1])]

def cycle0211 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 5, 2, 4, 1]), .gapLower 0 5 (![3, 5, 2, 4, 1])]

def cycle0212 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 1 (![3, 5, 2, 4, 1]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0213 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 5, 2, 4, 1]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0214 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![3, 5, 2, 4, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0215 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 5, 2, 4, 1]), .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0216 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 5, 2, 4, 1])]

def cycle0217 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 1 (![3, 5, 2, 4, 1]), .gapLower 0 0 (![3, 5, 2, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0218 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 5, 2, 4, 1]), .triangle 8 1, .gapLower 0 0 (![3, 5, 2, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0219 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![3, 5, 2, 4, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0220 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 5, 2, 4, 1]), .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0221 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 5, 2, 4, 1])]

def cycle0222 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 5, 2, 4, 1])]

def cycle0223 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 5, 2, 4, 1]), .gapLower 0 1 (![3, 5, 2, 4, 1]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0224 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![3, 5, 2, 4, 1]), .triangle 6 2, .gapLower 0 1 (![3, 5, 2, 4, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0225 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 5, 2, 4, 1]), .triangle 5 1, .triangle 6 2, .gapLower 0 1 (![3, 5, 2, 4, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0226 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 2, .gapLower 0 1 (![3, 5, 2, 4, 1]), .corridorLower 0 3, .gapLower 0 5 (![3, 5, 2, 4, 1])]

def cycle0227 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 5, 2, 4, 1]), .triangle 5 1, .gapLower 0 2 (![3, 5, 2, 4, 1]), .triangle 8 1, .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0228 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 2 (![3, 5, 2, 4, 1]), .corridorLower 0 5, .gapLower 0 5 (![3, 5, 2, 4, 1])]

def cycle0229 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 5, 2, 4, 1]), .gapLower 0 3 (![3, 5, 2, 4, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0230 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![3, 5, 2, 4, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 5, 2, 4, 1])]

def cycle0231 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![3, 5, 2, 4, 1]), .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 5, 2, 4, 1])]

def cycle0232 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 3, 4, 0, 5]), .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0233 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 0, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0234 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .gapLower 1 2 (![2, 3, 4, 0, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0235 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 2, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 10 0, .gapLower 2 0 (![1, 3, 4, 0, 5]), .gapLower 2 5 (![1, 3, 4, 0, 5]), .triangle 6 0]

def cycle0236 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .gapLower 2 1 (![1, 3, 4, 0, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0237 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .gapLower 2 2 (![1, 3, 4, 0, 5]), .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0238 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 2 3 (![1, 3, 4, 0, 5]), .triangle 16 1, .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0239 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .gapLower 2 4 (![1, 3, 4, 0, 5])]

def cycle0240 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 5, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 2, 1, 5]), .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 1, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 3, 4, 0, 5]), .triangle 6 0]

def cycle0241 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0242 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 2, 1, 5]), .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 0, 5]), .triangle 3 0]

def cycle0243 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![(0), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 4 1, .triangle 10 2, .triangle 13 0, .triangle 7 0]

def cycle0244 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0245 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0246 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 0, .triangle 16 1, .gapLower 2 0 (![3, 4, 1, 0, 5]), .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0247 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 0, .gapLower 2 1 (![3, 4, 1, 0, 5]), .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0248 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 2 (![3, 4, 1, 0, 5]), .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0249 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 3 (![3, 4, 1, 0, 5]), .triangle 11 2, .triangle 13 1, .gapLower 1 0 (![3, 4, 2, 0, 5]), .gapLower 1 5 (![3, 4, 2, 0, 5]), .triangle 3 0]

def cycle0250 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .gapLower 2 4 (![3, 4, 1, 0, 5])]

def cycle0251 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 5, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 2, 1, 5]), .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 1, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 1, 0, 5]), .triangle 6 0]

def cycle0252 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 16 0, .triangle 13 0, .gapLower 1 0 (![3, 4, 2, 0, 5]), .gapLower 1 5 (![3, 4, 2, 0, 5]), .triangle 3 0]

def cycle0253 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .gapLower 1 1 (![3, 4, 2, 0, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0254 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2 (![3, 4, 2, 0, 5]), .triangle 13 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0255 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![3, 4, 2, 0, 5]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0256 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![3, 4, 2, 0, 5])]

def cycle0257 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 4, 2, 0, 5]), .triangle 3 0]

def cycle0258 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0259 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 1 (![3, 4, 2, 1, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0260 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![3, 4, 2, 1, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0261 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 2, 1, 5]), .triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0262 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 4, 2, 1, 5])]

def cycle0263 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 4, 2, 1, 5]), .triangle 6 1]

def cycle0264 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 1 (![3, 4, 2, 1, 5]), .gapLower 0 0 (![3, 4, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0265 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![3, 4, 2, 1, 5]), .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0266 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 2, 1, 5]), .triangle 5 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0267 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 4, 2, 1, 5])]

def cycle0268 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 4, 2, 1, 5])]

def cycle0269 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 4, 2, 1, 5]), .triangle 3 1]

def cycle0270 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 4, 2, 1, 5]), .triangle 3 1]

def cycle0271 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 2, 1, 5]), .gapLower 0 1 (![3, 4, 2, 1, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0272 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 2, 1, 5]), .triangle 5 2, .gapLower 0 1 (![3, 4, 2, 1, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0273 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 1 (![3, 4, 2, 1, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 4, 2, 1, 5])]

def cycle0274 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 5 2, .gapLower 0 1 (![3, 4, 2, 1, 5]), .corridorLower 0 3, .gapLower 0 5 (![3, 4, 2, 1, 5]), .triangle 6 1]

def cycle0275 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 2, 1, 5]), .gapLower 0 2 (![3, 4, 2, 1, 5]), .triangle 7 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0276 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![3, 4, 2, 1, 5]), .triangle 7 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 4, 2, 1, 5])]

def cycle0277 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![3, 4, 2, 1, 5]), .corridorLower 0 4, .gapLower 0 5 (![3, 4, 2, 1, 5]), .triangle 3 1]

def cycle0278 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![3, 4, 2, 1, 5]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 4, 2, 1, 5])]

def cycle0279 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 3 (![3, 4, 2, 1, 5]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 4, 2, 1, 5]), .triangle 3 1]

def cycle0280 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 4, 2, 1, 5]), .gapLower 0 4 (![3, 4, 2, 1, 5])]

def cycle0281 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 3, 4, 5, 0]), .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0282 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0283 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0284 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .gapLower 2 4 (![1, 3, 4, 0, 5])]

def cycle0285 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 5, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 2, 5, 1]), .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 5, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 3, 4, 0, 5]), .triangle 6 0]

def cycle0286 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0287 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 3 (![3, 4, 2, 5, 1])]

def cycle0288 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 13 1, .triangle 14 0, .triangle 8 2, .gapLower 0 3 (![3, 4, 2, 5, 1])]

def cycle0289 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0290 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 11 0, .triangle 16 1, .gapLower 2 0 (![3, 4, 1, 0, 5]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0291 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 11 0, .gapLower 2 1 (![3, 4, 1, 0, 5]), .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0292 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 2 (![3, 4, 1, 0, 5]), .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0293 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (-2), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 3 (![3, 4, 1, 0, 5]), .triangle 11 2, .triangle 13 1, .gapLower 1 0 (![3, 4, 2, 5, 0]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0294 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .gapLower 2 4 (![3, 4, 1, 0, 5])]

def cycle0295 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 5, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 2, 5, 1]), .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 5, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 1, 0, 5]), .triangle 6 0]

def cycle0296 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 4, 2, 5, 0]), .triangle 12 1, .triangle 10 0, .triangle 16 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 2, 5, 1]), .gapLower 0 5 (![3, 4, 2, 5, 1])]

def cycle0297 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 11 2, .gapLower 1 1 (![3, 4, 2, 5, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0298 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 1 2 (![3, 4, 2, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0299 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 3 0, .gapLower 1 3 (![3, 4, 2, 5, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0300 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 1 4 (![3, 4, 2, 5, 0]), .triangle 12 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0301 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 4, 2, 5, 0])]

def cycle0302 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![3, 4, 2, 5, 1]), .gapLower 0 0 (![3, 4, 2, 5, 1]), .gapLower 0 5 (![3, 4, 2, 5, 1])]

def cycle0303 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 4, 2, 5, 1]), .gapLower 0 5 (![3, 4, 2, 5, 1])]

def cycle0304 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 2, 5, 1]), .gapLower 0 5 (![3, 4, 2, 5, 1])]

def cycle0305 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 1 (![3, 4, 2, 5, 1]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0306 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 2, 5, 1]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0307 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![3, 4, 2, 5, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0308 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 4, 2, 5, 1]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0309 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 4, 2, 5, 1])]

def cycle0310 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 1 (![3, 4, 2, 5, 1]), .gapLower 0 0 (![3, 4, 2, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0311 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 2, 5, 1]), .triangle 7 1, .gapLower 0 0 (![3, 4, 2, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0312 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![3, 4, 2, 5, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0313 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 4, 2, 5, 1]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0314 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 4, 2, 5, 1])]

def cycle0315 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 4, 2, 5, 1])]

def cycle0316 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 2, 5, 1]), .gapLower 0 1 (![3, 4, 2, 5, 1]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0317 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![3, 4, 2, 5, 1]), .triangle 5 2, .gapLower 0 1 (![3, 4, 2, 5, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0318 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 4, 2, 5, 1]), .triangle 9 1, .gapLower 0 1 (![3, 4, 2, 5, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0319 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 2, .gapLower 0 1 (![3, 4, 2, 5, 1]), .corridorLower 0 3, .gapLower 0 5 (![3, 4, 2, 5, 1])]

def cycle0320 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 4, 2, 5, 1]), .triangle 6 1, .gapLower 0 2 (![3, 4, 2, 5, 1]), .triangle 7 1, .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0321 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 2 (![3, 4, 2, 5, 1]), .corridorLower 0 4, .gapLower 0 5 (![3, 4, 2, 5, 1])]

def cycle0322 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 4, 2, 5, 1]), .gapLower 0 3 (![3, 4, 2, 5, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0323 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![3, 4, 2, 5, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 4, 2, 5, 1])]

def cycle0324 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![3, 4, 2, 5, 1]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 4, 2, 5, 1])]

def cycle0325 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0326 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 3, 4, 5, 0]), .corridorUpper 0 1]

def cycle0327 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .triangle 15 1, .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0328 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .triangle 15 1, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0329 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0330 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-1), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 18 1, .triangle 16 1, .triangle 10 0, .gapLower 2 0 (![1, 3, 4, 5, 0]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0331 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 18 1, .triangle 16 1, .gapLower 2 1 (![1, 3, 4, 5, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0332 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 18 1, .gapLower 2 2 (![1, 3, 4, 5, 0]), .triangle 10 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0333 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-2), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .gapLower 2 3 (![1, 3, 4, 5, 0]), .triangle 11 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0334 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 4 (![1, 3, 4, 5, 0]), .triangle 18 1, .triangle 16 1, .triangle 10 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0335 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 4, 5, 2, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 7 0]

def cycle0336 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![3, 4, 5, 2, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 9 0, .triangle 7 1]

def cycle0337 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0338 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4]
    constant := ![(0), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 5 1, .triangle 11 2, .triangle 15 0, .triangle 9 0]

def cycle0339 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0340 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0341 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0342 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0343 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .triangle 18 1, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 1, 0]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0344 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (0), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 1, 0]), .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0345 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .gapLower 2 2 (![3, 4, 5, 1, 0]), .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0346 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 3 (![3, 4, 5, 1, 0]), .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0347 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 4 (![3, 4, 5, 1, 0]), .triangle 12 2, .triangle 15 1, .triangle 13 1, .gapLower 1 0 (![3, 4, 5, 2, 0]), .corridorUpper 0 1]

def cycle0348 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false] }
  origin := ![.triangle 0 0, .triangle 12 2, .triangle 15 1, .triangle 13 1, .triangle 1 0]

def cycle0349 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 4, 5, 2, 0]), .gapLower 2 3 (![5, 3, 4, 1, 0]), .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 4, 5, 2, 1]), .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0350 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 4, 5, 2, 0]), .triangle 10 0, .triangle 16 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 5, 2, 1]), .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0351 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 2, .triangle 15 1, .gapLower 1 1 (![3, 4, 5, 2, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0352 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 2, .gapLower 1 2 (![3, 4, 5, 2, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0353 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 3 (![3, 4, 5, 2, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0354 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 1 4 (![3, 4, 5, 2, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0355 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 4, 5, 2, 0])]

def cycle0356 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-3), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![3, 4, 5, 2, 1]), .gapLower 0 0 (![3, 4, 5, 2, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0357 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 4, 5, 2, 1]), .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0358 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 5, 2, 1]), .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0359 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 1 (![3, 4, 5, 2, 1])]

def cycle0360 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 2 (![3, 4, 5, 2, 1]), .triangle 7 1, .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0361 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![3, 4, 5, 2, 1]), .triangle 9 1, .triangle 7 1, .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0362 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 4, 5, 2, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0363 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0364 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 4, 5, 2, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 1 (![3, 4, 5, 2, 1])]

def cycle0365 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 2 (![3, 4, 5, 2, 1]), .triangle 7 1, .triangle 4 1, .triangle 10 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0366 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 2 (![3, 4, 5, 2, 1]), .triangle 5 1, .triangle 11 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0367 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 2 (![3, 4, 5, 2, 1]), .triangle 5 1, .gapLower 2 1 (![3, 4, 5, 1, 0]), .corridorLower 2 3, .gapLower 2 5 (![3, 4, 5, 1, 0])]

def cycle0368 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 2 (![3, 4, 5, 2, 1]), .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 2, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 1, 0])]

def cycle0369 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![(0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 5 1, .triangle 18 0, .triangle 9 2, .gapLower 0 2 (![3, 4, 5, 2, 1])]

def cycle0370 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4]
    constant := ![(0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 5 1, .triangle 16 1, .triangle 17 0, .triangle 8 2, .gapLower 0 2 (![3, 4, 5, 2, 1])]

def cycle0371 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 4, 5, 2, 0]), .triangle 10 0, .triangle 16 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 5, 2, 1]), .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0372 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 2 (![3, 4, 5, 2, 1]), .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 4, 5, 2, 0])]

def cycle0373 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (-2), (0), (-2), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 15 0, .gapLower 5 2 (![2, 0, 4, 1, 3]), .gapLower 0 2 (![3, 4, 5, 2, 1]), .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 2, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0374 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (-2), (0), (-2), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 2 (![3, 4, 5, 2, 1]), .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 2, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0375 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 5, 2, 1]), .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0376 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![3, 4, 5, 2, 1]), .triangle 8 1, .triangle 4 1, .triangle 10 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0377 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![3, 4, 5, 2, 1]), .triangle 9 1, .triangle 5 1, .triangle 11 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0378 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![3, 4, 5, 2, 1]), .triangle 6 1, .triangle 12 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0379 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 0 2]
    constant := ![(-2), (0), (0), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 5, 2, 1]), .triangle 6 1, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 1, 0]), .corridorLower 2 3, .gapLower 2 5 (![3, 4, 5, 1, 0])]

def cycle0380 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 5, 2, 1]), .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 1, 0]), .corridorLower 2 4, .gapLower 2 5 (![3, 4, 5, 1, 0])]

def cycle0381 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 5, 2, 1]), .triangle 8 1, .gapLower 0 0 (![3, 4, 5, 2, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 1, 0])]

def cycle0382 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (0), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 4, 5, 2, 0]), .triangle 11 0, .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 4, 5, 2, 1]), .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0383 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![3, 4, 5, 2, 1]), .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 4, 5, 2, 0])]

def cycle0384 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-2), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 2, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0385 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 4, 5, 2, 1]), .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0386 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 4, 5, 2, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0387 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0388 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0389 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 2 (![3, 4, 5, 2, 1]), .gapLower 0 1 (![3, 4, 5, 2, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0390 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![3, 4, 5, 2, 1]), .triangle 9 1, .gapLower 0 1 (![3, 4, 5, 2, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0391 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 4, 5, 2, 1]), .triangle 6 2, .triangle 9 1, .gapLower 0 1 (![3, 4, 5, 2, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0392 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 9 1, .gapLower 0 1 (![3, 4, 5, 2, 1]), .corridorLower 0 3, .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0393 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![3, 4, 5, 2, 1]), .gapLower 0 2 (![3, 4, 5, 2, 1]), .triangle 7 1, .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0394 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 2 (![3, 4, 5, 2, 1]), .corridorLower 0 4, .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0395 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 1]
    strict := ![true, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![3, 4, 5, 2, 1]), .corridorLower 0 5, .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0396 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![3, 4, 5, 2, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 4, 5, 2, 1])]

def cycle0397 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0398 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0399 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0400 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0401 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 18 0, .triangle 16 1, .triangle 10 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0402 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 18 0, .triangle 15 0, .triangle 13 1, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0403 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0404 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 3, 5, 4, 0]), .corridorUpper 0 1]

def cycle0405 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 2, .triangle 13 1, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0406 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![2, 3, 5, 4, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0407 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 2, .gapLower 1 3 (![2, 3, 5, 4, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0408 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0409 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 4 (![3, 4, 2, 0, 5])]

def cycle0410 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .gapLower 1 0 (![3, 4, 2, 5, 0]), .corridorUpper 0 1]

def cycle0411 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 2, 5, 0]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 2, 5, 0])]

def cycle0412 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![3, 4, 2, 5, 0]), .gapLower 1 2 (![3, 4, 2, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0413 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![3, 4, 2, 5, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0414 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 2, 5, 0])]

def cycle0415 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .gapLower 1 0 (![3, 4, 5, 2, 0]), .corridorUpper 0 1]

def cycle0416 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 2, 0]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 2, 0])]

def cycle0417 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![3, 4, 5, 2, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0418 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 2, 0])]

def cycle0419 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 15 0, .triangle 18 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0420 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 0, .triangle 11 0, .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0421 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 5, 4, 2, 0]), .gapLower 2 3 (![5, 3, 4, 1, 0]), .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 4, 2, 1]), .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0422 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 5, 4, 2, 0]), .triangle 10 0, .triangle 16 0, .triangle 7 0, .gapLower 0 0 (![3, 5, 4, 2, 1]), .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0423 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 15 2, .gapLower 1 1 (![3, 5, 4, 2, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0424 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .gapLower 1 2 (![3, 5, 4, 2, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0425 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 3 (![3, 5, 4, 2, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0426 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 1 4 (![3, 5, 4, 2, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0427 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 5, 4, 2, 0])]

def cycle0428 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 4, 2, 1]), .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0429 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 5, 4, 2, 1]), .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0430 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 2, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0431 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .distance 3 4, .distance 0 4]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 2 (![3, 5, 4, 2, 1]), .triangle 9 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 7 2]

def cycle0432 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 3 (![3, 5, 4, 2, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 0 2]

def cycle0433 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 5, 4, 2, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0434 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0435 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 2, 1]), .triangle 4 1, .triangle 10 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0436 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 2, 1]), .gapLower 0 0 (![3, 5, 4, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 4, 2, 5, 0])]

def cycle0437 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 2, 1]), .gapLower 0 0 (![3, 5, 4, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 4, 5, 2, 0])]

def cycle0438 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![(0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 4 1, .triangle 17 0, .triangle 8 2, .gapLower 0 1 (![3, 5, 4, 2, 1])]

def cycle0439 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false] }
  origin := ![.triangle 4 1, .triangle 16 0, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 2, 1])]

def cycle0440 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 2, 1]), .gapLower 0 0 (![3, 5, 4, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 5, 4, 2, 0])]

def cycle0441 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (-2), (-2), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 1 (![3, 5, 4, 2, 1]), .gapLower 0 0 (![3, 5, 4, 2, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0442 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (0), (-2), (-2), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 2, 1]), .gapLower 0 0 (![3, 5, 4, 2, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0443 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 2 (![3, 5, 4, 2, 1]), .triangle 8 1, .triangle 4 1, .triangle 10 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0444 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 2 (![3, 5, 4, 2, 1]), .triangle 9 1, .triangle 15 0, .triangle 11 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0445 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 2 (![3, 5, 4, 2, 1]), .triangle 9 1, .triangle 18 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0446 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (0), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 5, 4, 2, 0]), .triangle 11 0, .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 4, 2, 1]), .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0447 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 2 (![3, 5, 4, 2, 1]), .triangle 8 1, .gapLower 0 0 (![3, 5, 4, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 5, 4, 2, 0])]

def cycle0448 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 4, 2, 1]), .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0449 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (-2), (0), (-2), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 2 (![3, 5, 4, 2, 1]), .triangle 8 1, .gapLower 0 0 (![3, 5, 4, 2, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0450 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 3 (![3, 5, 4, 2, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 0 2]

def cycle0451 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 5, 4, 2, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0452 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0453 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0454 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 2 (![3, 5, 4, 2, 1]), .gapLower 0 1 (![3, 5, 4, 2, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0455 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![3, 5, 4, 2, 1]), .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 2, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0456 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.gapLower 0 4 (![3, 5, 4, 2, 1]), .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 2, 1]), .triangle 4 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0457 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 2, 1]), .corridorLower 0 3, .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0458 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![3, 5, 4, 2, 1]), .gapLower 0 2 (![3, 5, 4, 2, 1]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0459 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![3, 5, 4, 2, 1]), .triangle 5 2, .gapLower 0 2 (![3, 5, 4, 2, 1]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0460 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 2 (![3, 5, 4, 2, 1]), .corridorLower 0 5, .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0461 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .zero, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 4 (![3, 5, 4, 2, 1]), .gapLower 0 3 (![3, 5, 4, 2, 1]), .triangle 9 0, .corridorLower 4 5, .thetaLower 4, .thetaUpper 1, .corridorUpper 0 1]

def cycle0462 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![3, 5, 4, 2, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0463 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![3, 5, 4, 2, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 5, 4, 2, 1])]

def cycle0464 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .triangle 3 0]

def cycle0465 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 5, 0, 4]), .gapLower 1 0 (![2, 3, 5, 0, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0466 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 5, 0, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0467 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 2 (![2, 3, 5, 0, 4]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0468 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 17 0, .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0469 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 17 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 5, 0, 4]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0470 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 0 (![5, 3, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0471 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 3, 2, 1, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0472 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 5, 3, 0, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0473 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 14 2, .gapLower 1 1 (![2, 5, 3, 0, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0474 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .gapLower 1 2 (![2, 5, 3, 0, 4]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0475 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![2, 5, 3, 0, 4]), .triangle 14 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0476 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 0 (![5, 3, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 5, 3, 0, 4])]

def cycle0477 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 3, 2, 1, 4]), .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 3, 0, 4]), .triangle 2 0]

def cycle0478 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 0 (![3, 2, 5, 0, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0479 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 2, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 2 (![3, 2, 5, 0, 4]), .gapLower 1 1 (![3, 2, 5, 0, 4]), .corridorLower 1 3, .gapLower 1 5 (![3, 2, 5, 0, 4]), .triangle 2 0]

def cycle0480 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .gapLower 1 2 (![3, 2, 5, 0, 4]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0481 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 0 (![5, 3, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![3, 2, 5, 0, 4])]

def cycle0482 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 3, 2, 1, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 2, 5, 0, 4]), .triangle 2 0]

def cycle0483 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 0 (![3, 5, 2, 0, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0484 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 1 (![3, 5, 2, 0, 4]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0485 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 0 (![5, 3, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![3, 5, 2, 0, 4])]

def cycle0486 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 3, 2, 1, 4]), .triangle 4 2, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 2, 0, 4]), .triangle 2 0]

def cycle0487 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 17 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0488 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 17 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0489 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 5, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .gapLower 1 1 (![5, 3, 2, 0, 4]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0490 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2 (![5, 3, 2, 0, 4]), .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0491 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![5, 3, 2, 0, 4]), .triangle 10 2, .triangle 14 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0492 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 0 (![5, 3, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![5, 3, 2, 0, 4])]

def cycle0493 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![5, 3, 2, 0, 4]), .triangle 2 0]

def cycle0494 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 1 (![5, 3, 2, 1, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0495 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 2, 1, 4]), .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0496 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 3, 2, 1, 4]), .triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0497 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 3, 2, 1, 4])]

def cycle0498 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, true, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 2, 1, 4]), .triangle 5 1]

def cycle0499 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 1 (![5, 3, 2, 1, 4]), .gapLower 0 0 (![5, 3, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0500 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![5, 3, 2, 1, 4]), .triangle 8 2, .gapLower 0 0 (![5, 3, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0501 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 3, 2, 1, 4]), .triangle 4 2, .triangle 8 2, .gapLower 0 0 (![5, 3, 2, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0502 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 3, 2, 1, 4])]

def cycle0503 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 3, 2, 1, 4])]

def cycle0504 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 3, 2, 1, 4]), .triangle 2 1]

def cycle0505 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 2, 1, 4]), .triangle 2 1]

def cycle0506 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 2, 1, 4]), .gapLower 0 1 (![5, 3, 2, 1, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0507 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 3, 2, 1, 4]), .triangle 4 2, .gapLower 0 1 (![5, 3, 2, 1, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0508 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 1 (![5, 3, 2, 1, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 3, 2, 1, 4])]

def cycle0509 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 1 (![5, 3, 2, 1, 4]), .corridorLower 0 5, .gapLower 0 5 (![5, 3, 2, 1, 4]), .triangle 5 1]

def cycle0510 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 3, 2, 1, 4]), .gapLower 0 2 (![5, 3, 2, 1, 4]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0511 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![5, 3, 2, 1, 4]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 3, 2, 1, 4])]

def cycle0512 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 2, 1, 4]), .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0513 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![5, 3, 2, 1, 4]), .triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 3, 2, 1, 4])]

def cycle0514 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, true, false, true] }
  origin := ![.gapLower 0 3 (![5, 3, 2, 1, 4]), .triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 2, 1, 4]), .triangle 2 1]

def cycle0515 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 3, 2, 1, 4]), .gapLower 0 4 (![5, 3, 2, 1, 4])]

def cycle0516 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0517 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .gapLower 1 0 (![2, 3, 4, 5, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0518 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0519 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0520 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0521 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 17 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0522 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0523 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 5, 4, 0]), .gapLower 1 0 (![2, 3, 5, 4, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0524 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0525 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 2 (![2, 3, 5, 4, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0526 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (0), (-1), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 1 4 (![2, 3, 5, 4, 0]), .triangle 15 0, .corridorLower 4 5, .corridorUpper 2 4, .triangle 5 0, .triangle 4 2, .triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0527 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0528 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 5, 3, 4, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0529 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 14 2, .gapLower 1 1 (![2, 5, 3, 4, 0]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0530 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .gapLower 1 2 (![2, 5, 3, 4, 0]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0531 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 3, 4, 0])]

def cycle0532 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 3 (![5, 3, 2, 4, 1])]

def cycle0533 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 4 (![3, 2, 4, 0, 5])]

def cycle0534 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 0 (![3, 2, 4, 5, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0535 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 2, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (0), (0), (-2), (0), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 2 (![3, 2, 4, 5, 0]), .gapLower 1 1 (![3, 2, 4, 5, 0]), .gapLower 3 1 (![2, 1, 5, 0, 4]), .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0536 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 2 (![3, 2, 4, 5, 0]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0537 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 3 (![3, 2, 4, 5, 0]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0538 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 4 (![3, 2, 4, 5, 0]), .triangle 15 1, .triangle 11 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0539 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .gapLower 1 5 (![3, 2, 4, 5, 0])]

def cycle0540 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 0 (![3, 2, 5, 4, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0541 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 2, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .gapLower 1 2 (![3, 2, 5, 4, 0]), .gapLower 1 1 (![3, 2, 5, 4, 0]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0542 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .gapLower 1 2 (![3, 2, 5, 4, 0]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0543 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (0), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 2, 5, 4, 0]), .triangle 15 0, .corridorLower 4 5, .corridorUpper 2 4, .triangle 5 0, .triangle 4 2, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .corridorUpper 0 1]

def cycle0544 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .gapLower 1 5 (![3, 2, 5, 4, 0])]

def cycle0545 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 0 (![3, 5, 2, 4, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0546 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 1 (![3, 5, 2, 4, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0547 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 2, 4, 0])]

def cycle0548 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 10 2, .triangle 14 0, .triangle 17 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0549 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 10 0, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0550 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 10 2, .gapLower 1 1 (![5, 3, 2, 4, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0551 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 1 2 (![5, 3, 2, 4, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0552 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .gapLower 1 3 (![5, 3, 2, 4, 0]), .triangle 10 2, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0553 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 4 (![5, 3, 2, 4, 0]), .triangle 13 1, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0554 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![5, 3, 2, 4, 0])]

def cycle0555 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 8 2, .gapLower 0 0 (![5, 3, 2, 4, 1]), .gapLower 0 5 (![5, 3, 2, 4, 1])]

def cycle0556 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 1 (![5, 3, 2, 4, 1]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0557 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 2, 4, 1]), .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0558 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![5, 3, 2, 4, 1]), .triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0559 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 2, 4, 1]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0560 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 3, 2, 4, 1])]

def cycle0561 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 1 (![5, 3, 2, 4, 1]), .gapLower 0 0 (![5, 3, 2, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0562 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 2, 4, 1]), .triangle 8 2, .gapLower 0 0 (![5, 3, 2, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0563 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![5, 3, 2, 4, 1]), .triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0564 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 2, 4, 1]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0565 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 3, 2, 4, 1])]

def cycle0566 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 2, 4, 1])]

def cycle0567 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 2, 4, 1]), .gapLower 0 1 (![5, 3, 2, 4, 1]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0568 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![5, 3, 2, 4, 1]), .triangle 4 2, .gapLower 0 1 (![5, 3, 2, 4, 1]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0569 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 2, 4, 1]), .triangle 7 1, .gapLower 0 1 (![5, 3, 2, 4, 1]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0570 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .gapLower 0 1 (![5, 3, 2, 4, 1]), .corridorLower 0 5, .gapLower 0 5 (![5, 3, 2, 4, 1])]

def cycle0571 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![5, 3, 2, 4, 1]), .gapLower 0 2 (![5, 3, 2, 4, 1]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0572 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 2, 4, 1]), .triangle 5 1, .gapLower 0 2 (![5, 3, 2, 4, 1]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0573 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 2, 4, 1]), .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0574 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 2, 4, 1]), .gapLower 0 3 (![5, 3, 2, 4, 1]), .triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0575 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![5, 3, 2, 4, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 2, 4, 1])]

def cycle0576 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 2, 4, 1]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 2, 4, 1])]

def cycle0577 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 7 1, .triangle 8 0, .triangle 14 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0578 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (-1), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 16 1, .triangle 17 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0579 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 16 0, .triangle 7 0, .triangle 8 2, .gapLower 0 0 (![5, 3, 4, 2, 1]), .gapLower 0 5 (![5, 3, 4, 2, 1])]

def cycle0580 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 7 1, .triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0581 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (-1), (-1), (3), (-1), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 2, .triangle 15 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 7 0, .triangle 8 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0582 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (-1), (-1), (3), (-1), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 2, .triangle 15 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 7 0, .triangle 8 0, .triangle 14 2, .gapLower 1 2 (![2, 3, 5, 4, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0583 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 7 1, .triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0584 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 2, .gapLower 1 4 (![2, 5, 3, 0, 4])]

def cycle0585 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 5, 3, 4, 0]), .corridorUpper 0 1]

def cycle0586 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 2, .triangle 13 1, .triangle 14 2, .gapLower 1 1 (![2, 5, 3, 4, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0587 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 5, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 13 1, .gapLower 1 2 (![2, 5, 3, 4, 0]), .triangle 14 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0588 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .gapLower 1 3 (![2, 5, 3, 4, 0]), .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0589 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 3, 4, 0])]

def cycle0590 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 7 1, .triangle 8 0, .triangle 14 2, .gapLower 1 4 (![3, 4, 2, 0, 5])]

def cycle0591 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 0 (![3, 4, 2, 5, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0592 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 1 (![3, 4, 2, 5, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0593 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (0), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .gapLower 1 3 (![3, 4, 2, 5, 0]), .gapLower 1 2 (![3, 4, 2, 5, 0]), .triangle 13 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0594 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .gapLower 1 3 (![3, 4, 2, 5, 0]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0595 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 7 1, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 2, 5, 0])]

def cycle0596 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 0 (![3, 4, 5, 2, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0597 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 1 (![3, 4, 5, 2, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0598 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .gapLower 1 2 (![3, 4, 5, 2, 0]), .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0599 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 7 1, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 2, 0])]

def cycle0600 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 0 (![3, 5, 4, 2, 0]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0601 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (3), (-1), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 15 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 7 0, .triangle 8 0, .triangle 14 2, .gapLower 1 1 (![3, 5, 4, 2, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0602 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 3 (![3, 5, 4, 2, 0]), .triangle 13 1, .corridorLower 1 3, .corridorUpper 0 1]

def cycle0603 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 5, 4, 2, 0]), .triangle 11 2, .triangle 15 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 7 0, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .corridorUpper 0 1]

def cycle0604 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 7 1, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 4, 2, 0])]

def cycle0605 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-1), (-1), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .triangle 10 2, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0606 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 13 1, .triangle 14 0, .triangle 17 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0607 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 11 0, .triangle 16 1, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0608 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 4 (![5, 3, 4, 2, 0]), .triangle 10 0, .triangle 16 0, .triangle 7 0, .triangle 8 2, .gapLower 0 0 (![5, 3, 4, 2, 1]), .gapLower 0 5 (![5, 3, 4, 2, 1])]

def cycle0609 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 13 1, .gapLower 1 1 (![5, 3, 4, 2, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0610 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .gapLower 1 2 (![5, 3, 4, 2, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0611 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 3 (![5, 3, 4, 2, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0612 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.gapLower 1 4 (![5, 3, 4, 2, 0]), .triangle 11 2, .triangle 13 1, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0613 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![5, 3, 4, 2, 0])]

def cycle0614 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 8 2, .gapLower 0 0 (![5, 3, 4, 2, 1]), .gapLower 0 5 (![5, 3, 4, 2, 1])]

def cycle0615 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 3, 4, 2, 1]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0616 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 2 (![5, 3, 4, 2, 1]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0617 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 3 (![5, 3, 4, 2, 1]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0618 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 4, 2, 1]), .triangle 5 2, .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0619 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 3, 4, 2, 1])]

def cycle0620 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 3, 4, 2, 1]), .gapLower 0 0 (![5, 3, 4, 2, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0621 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 2 (![5, 3, 4, 2, 1]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0622 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 3 (![5, 3, 4, 2, 1]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0623 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 4, 2, 1]), .triangle 5 2, .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0624 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 3, 4, 2, 1])]

def cycle0625 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 4, 2, 1])]

def cycle0626 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 2 (![5, 3, 4, 2, 1]), .gapLower 0 1 (![5, 3, 4, 2, 1]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0627 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 0 3 (![5, 3, 4, 2, 1]), .triangle 7 1, .gapLower 0 1 (![5, 3, 4, 2, 1]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0628 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 4, 2, 1]), .triangle 5 2, .triangle 7 1, .gapLower 0 1 (![5, 3, 4, 2, 1]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0629 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 7 1, .gapLower 0 1 (![5, 3, 4, 2, 1]), .corridorLower 0 5, .gapLower 0 5 (![5, 3, 4, 2, 1])]

def cycle0630 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![5, 3, 4, 2, 1]), .gapLower 0 2 (![5, 3, 4, 2, 1]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0631 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 4, 2, 1]), .triangle 5 2, .gapLower 0 2 (![5, 3, 4, 2, 1]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0632 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 2 (![5, 3, 4, 2, 1]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 4, 2, 1])]

def cycle0633 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 4, 2, 1]), .gapLower 0 3 (![5, 3, 4, 2, 1]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0634 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![5, 3, 4, 2, 1]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 4, 2, 1])]

def cycle0635 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 3, 4, 2, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 4, 2, 1])]

def cycle0636 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .triangle 2 0]

def cycle0637 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 16 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0638 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 16 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 0, 5]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0639 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 0 (![4, 3, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0640 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 2, 1, 5]), .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 0, 5]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 0, 5]), .triangle 3 0]

def cycle0641 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 4, 3, 0, 5]), .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0642 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 13 2, .gapLower 1 1 (![2, 4, 3, 0, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0643 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .gapLower 1 2 (![2, 4, 3, 0, 5]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0644 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![2, 4, 3, 0, 5]), .triangle 13 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0645 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 0 (![4, 3, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 4, 3, 0, 5])]

def cycle0646 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 2, 1, 5]), .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 3, 0, 5]), .triangle 3 0]

def cycle0647 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 2, 4, 0, 5]), .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0648 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 2 (![3, 2, 4, 0, 5]), .gapLower 1 1 (![3, 2, 4, 0, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0649 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 2 (![3, 2, 4, 0, 5]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0650 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 0 (![4, 3, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![3, 2, 4, 0, 5])]

def cycle0651 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 2, 1, 5]), .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 3 1 (![2, 1, 4, 0, 5]), .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 2, 4, 0, 5]), .triangle 3 0]

def cycle0652 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 4, 2, 0, 5]), .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0653 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 1 (![3, 4, 2, 0, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0654 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2 (![3, 4, 2, 0, 5]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0655 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 0 (![4, 3, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![3, 4, 2, 0, 5])]

def cycle0656 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 2, 1, 5]), .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 3 1 (![2, 1, 4, 0, 5]), .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 4, 2, 0, 5]), .triangle 3 0]

def cycle0657 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 16 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0658 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 16 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0659 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .gapLower 1 1 (![4, 3, 2, 0, 5]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0660 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2 (![4, 3, 2, 0, 5]), .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0661 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![4, 3, 2, 0, 5]), .triangle 10 2, .triangle 13 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0662 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 0 (![4, 3, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![4, 3, 2, 0, 5])]

def cycle0663 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![4, 3, 2, 0, 5]), .triangle 3 0]

def cycle0664 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 1 (![4, 3, 2, 1, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0665 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 2, 1, 5]), .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0666 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 2, 1, 5]), .triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0667 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 3, 2, 1, 5])]

def cycle0668 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, true, false, true] }
  origin := ![.triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 2, 1, 5]), .triangle 6 1]

def cycle0669 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 1 (![4, 3, 2, 1, 5]), .gapLower 0 0 (![4, 3, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0670 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![4, 3, 2, 1, 5]), .triangle 7 2, .gapLower 0 0 (![4, 3, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0671 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 2, 1, 5]), .triangle 4 2, .triangle 7 2, .gapLower 0 0 (![4, 3, 2, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0672 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 3, 2, 1, 5])]

def cycle0673 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 3, 2, 1, 5])]

def cycle0674 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 3, 2, 1, 5]), .triangle 3 1]

def cycle0675 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 2, 1, 5]), .triangle 3 1]

def cycle0676 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 2, 1, 5]), .gapLower 0 1 (![4, 3, 2, 1, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0677 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 2, 1, 5]), .triangle 4 2, .gapLower 0 1 (![4, 3, 2, 1, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0678 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 1 (![4, 3, 2, 1, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 3, 2, 1, 5])]

def cycle0679 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 1 (![4, 3, 2, 1, 5]), .corridorLower 0 4, .gapLower 0 5 (![4, 3, 2, 1, 5]), .triangle 6 1]

def cycle0680 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 2, 1, 5]), .gapLower 0 2 (![4, 3, 2, 1, 5]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0681 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![4, 3, 2, 1, 5]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 3, 2, 1, 5])]

def cycle0682 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 2, 1, 5]), .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0683 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 3, 2, 1, 5]), .triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 3, 2, 1, 5])]

def cycle0684 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, true, false, true] }
  origin := ![.gapLower 0 3 (![4, 3, 2, 1, 5]), .triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 2, 1, 5]), .triangle 3 1]

def cycle0685 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 3, 2, 1, 5]), .gapLower 0 4 (![4, 3, 2, 1, 5])]

def cycle0686 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0687 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 16 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0688 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0689 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 3, 2, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0690 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 4, 3, 5, 0]), .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0691 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 13 2, .gapLower 1 1 (![2, 4, 3, 5, 0]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0692 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .gapLower 1 2 (![2, 4, 3, 5, 0]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0693 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 3, 5, 0])]

def cycle0694 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 3 (![4, 3, 2, 5, 1])]

def cycle0695 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 3 (![4, 3, 2, 5, 1])]

def cycle0696 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 2, 4, 5, 0]), .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0697 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 2 (![3, 2, 4, 5, 0]), .gapLower 1 1 (![3, 2, 4, 5, 0]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0698 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 2 (![3, 2, 4, 5, 0]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0699 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 3 1 (![2, 1, 4, 0, 5]), .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 2, 4, 5, 0])]

def cycle0700 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![(0), (0), (0), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 2, 5, 1]), .gapLower 3 3 (![2, 1, 4, 0, 5]), .triangle 13 2, .triangle 11 1, .triangle 12 0, .triangle 6 0]

def cycle0701 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 4, 2, 5, 0]), .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0702 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 1 (![3, 4, 2, 5, 0]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0703 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 3 1 (![2, 1, 4, 0, 5]), .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 4, 2, 5, 0])]

def cycle0704 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 10 2, .triangle 13 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0705 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 10 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0706 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 10 2, .gapLower 1 1 (![4, 3, 2, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0707 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 1 2 (![4, 3, 2, 5, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0708 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .gapLower 1 3 (![4, 3, 2, 5, 0]), .triangle 10 2, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0709 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 4 (![4, 3, 2, 5, 0]), .triangle 14 1, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0710 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![4, 3, 2, 5, 0])]

def cycle0711 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 1 (![4, 3, 2, 5, 1]), .gapLower 0 0 (![4, 3, 2, 5, 1]), .gapLower 0 5 (![4, 3, 2, 5, 1])]

def cycle0712 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![5, 4, 3, 2, 0]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 3, 2, 5, 1]), .gapLower 0 5 (![4, 3, 2, 5, 1])]

def cycle0713 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 1 (![4, 3, 2, 5, 1]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0714 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 2, 5, 1]), .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0715 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![4, 3, 2, 5, 1]), .triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0716 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 3, 2, 5, 1]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0717 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 3, 2, 5, 1])]

def cycle0718 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 1 (![4, 3, 2, 5, 1]), .gapLower 0 0 (![4, 3, 2, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0719 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 2, 5, 1]), .triangle 7 2, .gapLower 0 0 (![4, 3, 2, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0720 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![4, 3, 2, 5, 1]), .triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0721 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 3, 2, 5, 1]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0722 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 3, 2, 5, 1])]

def cycle0723 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 2, 5, 1])]

def cycle0724 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 2, 5, 1]), .gapLower 0 1 (![4, 3, 2, 5, 1]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0725 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![4, 3, 2, 5, 1]), .triangle 4 2, .gapLower 0 1 (![4, 3, 2, 5, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0726 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 3, 2, 5, 1]), .triangle 8 1, .gapLower 0 1 (![4, 3, 2, 5, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0727 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 2, .gapLower 0 1 (![4, 3, 2, 5, 1]), .corridorLower 0 4, .gapLower 0 5 (![4, 3, 2, 5, 1])]

def cycle0728 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![4, 3, 2, 5, 1]), .gapLower 0 2 (![4, 3, 2, 5, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0729 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 3, 2, 5, 1]), .triangle 6 1, .gapLower 0 2 (![4, 3, 2, 5, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0730 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 2, 5, 1]), .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0731 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 3, 2, 5, 1]), .gapLower 0 3 (![4, 3, 2, 5, 1]), .triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0732 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![4, 3, 2, 5, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 2, 5, 1])]

def cycle0733 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 3, 2, 5, 1]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 2, 5, 1])]

def cycle0734 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 8 1, .triangle 7 0, .triangle 13 2, .triangle 2 0]

def cycle0735 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 16 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0736 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 16 0, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0737 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 8 1, .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0738 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 2 (![4, 3, 5, 2, 1])]

def cycle0739 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .gapLower 1 4 (![2, 4, 3, 0, 5])]

def cycle0740 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 4, 3, 5, 0]), .corridorUpper 0 1]

def cycle0741 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .triangle 14 1, .triangle 13 2, .gapLower 1 1 (![2, 4, 3, 5, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0742 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .triangle 14 1, .gapLower 1 2 (![2, 4, 3, 5, 0]), .triangle 13 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0743 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .gapLower 1 3 (![2, 4, 3, 5, 0]), .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0744 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 3, 5, 0])]

def cycle0745 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 5, 4, 3, 0]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 3, 5, 2, 1]), .gapLower 0 5 (![4, 3, 5, 2, 1])]

def cycle0746 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 8 1, .triangle 7 0, .triangle 13 2, .gapLower 1 4 (![3, 5, 2, 0, 4])]

def cycle0747 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 5, 2, 4, 0]), .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0748 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 3 (![3, 5, 2, 4, 0]), .triangle 12 2, .gapLower 1 1 (![3, 5, 2, 4, 0]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0749 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 1 5, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 3 (![3, 5, 2, 4, 0]), .gapLower 1 2 (![3, 5, 2, 4, 0]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0750 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 3 (![3, 5, 2, 4, 0]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0751 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 8 1, .triangle 7 0, .triangle 13 2, .gapLower 1 3 (![3, 5, 2, 4, 0]), .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![3, 5, 2, 4, 0])]

def cycle0752 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 4, 5, 2, 0]), .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0753 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 1 (![3, 4, 5, 2, 0]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0754 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 8 1, .triangle 7 0, .triangle 13 0, .gapLower 3 1 (![2, 1, 4, 0, 5]), .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 4, 5, 2, 0])]

def cycle0755 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 3]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 3 3 (![2, 1, 4, 0, 5]), .triangle 13 2, .triangle 15 0, .gapLower 5 2 (![2, 0, 4, 1, 3]), .triangle 8 1]

def cycle0756 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-1), (-1), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .triangle 10 2, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0757 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 12 2, .triangle 14 1, .triangle 13 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0758 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0759 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 2, .triangle 14 1, .gapLower 1 1 (![4, 3, 5, 2, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0760 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 2, .gapLower 1 2 (![4, 3, 5, 2, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0761 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 3 (![4, 3, 5, 2, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0762 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.gapLower 1 4 (![4, 3, 5, 2, 0]), .triangle 12 2, .triangle 14 1, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0763 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![4, 3, 5, 2, 0])]

def cycle0764 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-3), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 1 (![4, 3, 5, 2, 1]), .gapLower 0 0 (![4, 3, 5, 2, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0765 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![5, 4, 3, 2, 0]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 3, 5, 2, 1]), .gapLower 0 5 (![4, 3, 5, 2, 1])]

def cycle0766 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 3, 5, 2, 1]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0767 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 0 2 (![4, 3, 5, 2, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0768 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 3, 5, 2, 1]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0769 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 3, 5, 2, 1]), .triangle 6 2, .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0770 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, true, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 5, 2, 1])]

def cycle0771 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 3, 5, 2, 1]), .gapLower 0 0 (![4, 3, 5, 2, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0772 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 0 2 (![4, 3, 5, 2, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0773 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 3, 5, 2, 1]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0774 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 3, 5, 2, 1]), .triangle 6 2, .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0775 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 3, 5, 2, 1])]

def cycle0776 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 5, 2, 1])]

def cycle0777 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 0 2 (![4, 3, 5, 2, 1]), .gapLower 0 1 (![4, 3, 5, 2, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0778 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 3, 5, 2, 1]), .triangle 8 1, .gapLower 0 1 (![4, 3, 5, 2, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0779 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 3, 5, 2, 1]), .triangle 6 2, .triangle 8 1, .gapLower 0 1 (![4, 3, 5, 2, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0780 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 8 1, .gapLower 0 1 (![4, 3, 5, 2, 1]), .corridorLower 0 4, .gapLower 0 5 (![4, 3, 5, 2, 1])]

def cycle0781 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 3, 5, 2, 1]), .gapLower 0 2 (![4, 3, 5, 2, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0782 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 3, 5, 2, 1]), .triangle 6 2, .gapLower 0 2 (![4, 3, 5, 2, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0783 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 2 (![4, 3, 5, 2, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 5, 2, 1])]

def cycle0784 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 4 (![4, 3, 5, 2, 1]), .gapLower 0 3 (![4, 3, 5, 2, 1]), .triangle 8 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0785 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![4, 3, 5, 2, 1]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 5, 2, 1])]

def cycle0786 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 3, 5, 2, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 5, 2, 1])]

def cycle0787 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0788 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .gapLower 1 0 (![2, 3, 4, 5, 0]), .corridorUpper 0 1]

def cycle0789 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0790 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0791 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0792 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 16 0, .triangle 10 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0793 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0794 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 3, 5, 4, 0]), .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 3, 2, 1]), .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0795 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 13 0, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0796 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 14 0, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0797 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 4, 5, 3, 0]), .corridorUpper 0 1]

def cycle0798 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 2, .triangle 14 2, .triangle 15 1, .gapLower 1 1 (![2, 4, 5, 3, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0799 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![2, 4, 5, 3, 0]), .triangle 13 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0800 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-1), (0), (-2), (0), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .gapLower 1 3 (![2, 4, 5, 3, 0]), .triangle 15 1, .triangle 13 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0801 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0802 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 5, 4, 3, 0]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 3, 2, 1]), .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0803 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 4 (![3, 2, 4, 0, 5])]

def cycle0804 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 2, 4, 5, 0]), .corridorUpper 0 1]

def cycle0805 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 2 (![3, 2, 4, 5, 0]), .gapLower 1 1 (![3, 2, 4, 5, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0806 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 2 (![3, 2, 4, 5, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0807 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 3 (![3, 2, 4, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0808 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .gapLower 1 5 (![3, 2, 4, 5, 0])]

def cycle0809 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![3, 2, 5, 4, 0]), .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 3, 2, 1]), .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0810 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .gapLower 1 4 (![3, 5, 2, 0, 4])]

def cycle0811 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 5, 2, 4, 0]), .corridorUpper 0 1]

def cycle0812 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .gapLower 1 3 (![3, 5, 2, 4, 0]), .triangle 12 2, .gapLower 1 1 (![3, 5, 2, 4, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0813 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .gapLower 1 3 (![3, 5, 2, 4, 0]), .gapLower 1 2 (![3, 5, 2, 4, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0814 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .gapLower 1 3 (![3, 5, 2, 4, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0815 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 2, 4, 0])]

def cycle0816 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 4 (![3, 4, 2, 0, 5])]

def cycle0817 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 4, 2, 5, 0]), .corridorUpper 0 1]

def cycle0818 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 1 (![3, 4, 2, 5, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0819 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 3 (![3, 4, 2, 5, 0]), .gapLower 1 2 (![3, 4, 2, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0820 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 3 (![3, 4, 2, 5, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0821 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 2, 5, 0])]

def cycle0822 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 4, 5, 2, 0]), .corridorUpper 0 1]

def cycle0823 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 1 (![3, 4, 5, 2, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0824 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 14 2, .gapLower 1 2 (![3, 4, 5, 2, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0825 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 2, 0])]

def cycle0826 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0827 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 2, .gapLower 1 1 (![4, 5, 3, 2, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0828 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .gapLower 1 2 (![4, 5, 3, 2, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0829 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 3 (![4, 5, 3, 2, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0830 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 4 (![4, 5, 3, 2, 0]), .triangle 10 2, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0831 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![4, 5, 3, 2, 0])]

def cycle0832 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![5, 4, 3, 2, 0]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 3, 2, 1]), .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0833 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, true, false] }
  origin := ![.triangle 4 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 2, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0834 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (-3), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false] }
  origin := ![.triangle 4 2, .gapLower 0 2 (![4, 5, 3, 2, 1]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0835 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 5, 3, 2, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0836 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 5, 3, 2, 1]), .triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0837 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0838 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 2, 1]), .triangle 7 1, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0839 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 2, 1]), .gapLower 0 0 (![4, 5, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0840 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-1), (0), (-2), (-2), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 2, .triangle 13 2, .triangle 15 0, .gapLower 5 2 (![3, 0, 4, 1, 2]), .gapLower 0 1 (![4, 5, 3, 2, 1]), .gapLower 0 0 (![4, 5, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0841 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 2, 1]), .triangle 7 1, .triangle 13 0, .corridorLower 1 3, .corridorUpper 0 1]

def cycle0842 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 2, 1]), .triangle 7 1, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0843 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 2, 1]), .gapLower 0 0 (![4, 5, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![4, 5, 3, 2, 0])]

def cycle0844 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (0), (-2), (-2), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 1 (![4, 5, 3, 2, 1]), .gapLower 0 0 (![4, 5, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0845 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 2 (![4, 5, 3, 2, 1]), .triangle 9 1, .triangle 7 1, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0846 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, true, false] }
  origin := ![.triangle 4 2, .gapLower 0 2 (![4, 5, 3, 2, 1]), .triangle 8 1, .triangle 14 0, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0847 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 2 (![4, 5, 3, 2, 1]), .triangle 9 1, .gapLower 0 0 (![4, 5, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0848 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 3, 2, 1]), .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0849 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 2 (![4, 5, 3, 2, 1]), .triangle 9 1, .triangle 7 1, .triangle 13 0, .corridorLower 1 3, .corridorUpper 0 1]

def cycle0850 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 2 (![4, 5, 3, 2, 1]), .triangle 9 1, .gapLower 0 0 (![4, 5, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![4, 5, 3, 2, 0])]

def cycle0851 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 3, 2, 1]), .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0852 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 5, 3, 2, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0853 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 5, 3, 2, 1]), .triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0854 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0855 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0856 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 4 2, .gapLower 0 2 (![4, 5, 3, 2, 1]), .gapLower 0 1 (![4, 5, 3, 2, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0857 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 5, 3, 2, 1]), .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 2, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0858 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 5, 3, 2, 1]), .triangle 4 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 2, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0859 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 2, 1]), .corridorLower 0 4, .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0860 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 5, 3, 2, 1]), .gapLower 0 2 (![4, 5, 3, 2, 1]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 0 2]

def cycle0861 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 5, 3, 2, 1]), .triangle 4 2, .gapLower 0 2 (![4, 5, 3, 2, 1]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0862 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 2 (![4, 5, 3, 2, 1]), .corridorLower 0 5, .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0863 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 5, 3, 2, 1]), .gapLower 0 3 (![4, 5, 3, 2, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0864 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![4, 5, 3, 2, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0865 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 5, 3, 2, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 5, 3, 2, 1])]

def cycle0866 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0867 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .gapLower 1 1 (![2, 3, 4, 5, 0]), .gapLower 1 0 (![2, 3, 4, 5, 0]), .corridorUpper 0 1]

def cycle0868 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0869 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0870 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0871 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0872 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 5, 4, 0]), .gapLower 1 0 (![2, 3, 5, 4, 0]), .corridorUpper 0 1]

def cycle0873 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0874 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![2, 3, 5, 4, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0875 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .gapLower 1 3 (![2, 3, 5, 4, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0876 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0877 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 4 (![2, 4, 3, 0, 5])]

def cycle0878 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 3, 5, 0]), .gapLower 1 0 (![2, 4, 3, 5, 0]), .corridorUpper 0 1]

def cycle0879 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 3, 5, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 3, 5, 0])]

def cycle0880 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![2, 4, 3, 5, 0]), .gapLower 1 2 (![2, 4, 3, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0881 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![2, 4, 3, 5, 0]), .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0882 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 3, 5, 0])]

def cycle0883 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 5, 3, 0]), .gapLower 1 0 (![2, 4, 5, 3, 0]), .corridorUpper 0 1]

def cycle0884 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 5, 3, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0885 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (0), (-1), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, true, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![2, 4, 5, 3, 0]), .triangle 13 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0886 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0887 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 5, 4, 3, 0]), .corridorUpper 0 1]

def cycle0888 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![2, 5, 4, 3, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0889 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![2, 5, 4, 3, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0890 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .gapLower 1 3 (![2, 5, 4, 3, 0]), .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 0 2]

def cycle0891 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 4, 3, 0])]

def cycle0892 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 11 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0893 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 2, 5, 4, 0]), .corridorUpper 0 1]

def cycle0894 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![3, 2, 5, 4, 0]), .gapLower 1 1 (![3, 2, 5, 4, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0895 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![3, 2, 5, 4, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0896 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .gapLower 1 3 (![3, 2, 5, 4, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0897 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .gapLower 1 5 (![3, 2, 5, 4, 0])]

def cycle0898 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 4 (![3, 4, 2, 0, 5])]

def cycle0899 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 2, 5, 0]), .gapLower 1 0 (![3, 4, 2, 5, 0]), .corridorUpper 0 1]

def cycle0900 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 2, 5, 0]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 2, 5, 0])]

def cycle0901 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![3, 4, 2, 5, 0]), .gapLower 1 2 (![3, 4, 2, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0902 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![3, 4, 2, 5, 0]), .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0903 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 2, 5, 0])]

def cycle0904 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 2, 0]), .gapLower 1 0 (![3, 4, 5, 2, 0]), .corridorUpper 0 1]

def cycle0905 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 2, 0]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 2, 0])]

def cycle0906 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![3, 4, 5, 2, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0907 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 2, 0])]

def cycle0908 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 5, 4, 2, 0]), .corridorUpper 0 1]

def cycle0909 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![3, 5, 4, 2, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0910 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 2, .gapLower 1 2 (![3, 5, 4, 2, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0911 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 4, 2, 0])]

def cycle0912 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 4 (![4, 3, 2, 0, 5])]

def cycle0913 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 0 (![4, 3, 2, 5, 0]), .corridorUpper 0 1]

def cycle0914 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 2, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![4, 3, 2, 5, 0]), .triangle 10 2, .gapLower 1 1 (![4, 3, 2, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0915 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![4, 3, 2, 5, 0]), .gapLower 1 2 (![4, 3, 2, 5, 0]), .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0916 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (0), (-1), (0), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, true, false, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![4, 3, 2, 5, 0]), .triangle 10 2, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0917 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .corridorLower 1 4, .gapLower 1 5 (![4, 3, 2, 5, 0])]

def cycle0918 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 0 (![4, 3, 5, 2, 0]), .corridorUpper 0 1]

def cycle0919 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![4, 3, 5, 2, 0]), .gapLower 1 1 (![4, 3, 5, 2, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0920 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![4, 3, 5, 2, 0]), .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0921 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .corridorLower 1 4, .gapLower 1 5 (![4, 3, 5, 2, 0])]

def cycle0922 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 0 (![4, 5, 3, 2, 0]), .corridorUpper 0 1]

def cycle0923 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(0), (0), (-1), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, true, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 1 (![4, 5, 3, 2, 0]), .triangle 13 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def cycle0924 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 3, 2, 0])]

def cycle0925 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 2, .gapLower 1 1 (![5, 4, 3, 2, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0926 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .gapLower 1 2 (![5, 4, 3, 2, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0927 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 3 (![5, 4, 3, 2, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0928 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, true, true, false] }
  origin := ![.gapLower 1 4 (![5, 4, 3, 2, 0]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0929 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 2, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![5, 4, 3, 2, 0])]

def cycle0930 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 0 3]
    constant := ![(0), (-3), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false] }
  origin := ![.triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 0 3]

def cycle0931 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 0 3]
    constant := ![(-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 0 2 (![5, 4, 3, 2, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 0 3]

def cycle0932 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 3 (![5, 4, 3, 2, 1]), .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 0 2]

def cycle0933 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (0), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 4, 3, 2, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0934 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, true, true, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 3, 2, 1])]

def cycle0935 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-1), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, true, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .triangle 9 1, .triangle 15 0, .triangle 13 1, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0936 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .gapLower 0 0 (![5, 4, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0937 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .triangle 9 1, .triangle 15 0, .triangle 11 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0938 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .gapLower 0 0 (![5, 4, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 5, 4, 3, 0])]

def cycle0939 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-1), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .triangle 9 1, .triangle 15 0, .triangle 11 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def cycle0940 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .gapLower 0 0 (![5, 4, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 2, 5, 4, 0])]

def cycle0941 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .gapLower 0 0 (![5, 4, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 5, 2, 4, 0])]

def cycle0942 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .triangle 9 1, .triangle 15 0, .corridorLower 1 4, .corridorUpper 0 1]

def cycle0943 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .gapLower 0 0 (![5, 4, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 5, 4, 2, 0])]

def cycle0944 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .gapLower 0 0 (![5, 4, 3, 2, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![5, 4, 3, 2, 0])]

def cycle0945 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 0 3]
    constant := ![(-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 0 2 (![5, 4, 3, 2, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 0 3]

def cycle0946 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 3 (![5, 4, 3, 2, 1]), .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 0 2]

def cycle0947 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 4, 3, 2, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0948 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 4, 3, 2, 1])]

def cycle0949 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 3, 2, 1])]

def cycle0950 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 0 3]
    constant := ![(-2), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false] }
  origin := ![.gapLower 0 2 (![5, 4, 3, 2, 1]), .gapLower 0 1 (![5, 4, 3, 2, 1]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 0 3]

def cycle0951 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 3 (![5, 4, 3, 2, 1]), .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 0 2]

def cycle0952 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 4 (![5, 4, 3, 2, 1]), .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0953 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 2, 1]), .corridorLower 0 5, .gapLower 0 5 (![5, 4, 3, 2, 1])]

def cycle0954 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3 (![5, 4, 3, 2, 1]), .gapLower 0 2 (![5, 4, 3, 2, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 0 2]

def cycle0955 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .zero, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 4 (![5, 4, 3, 2, 1]), .triangle 4 2, .gapLower 0 2 (![5, 4, 3, 2, 1]), .triangle 9 0, .corridorLower 4 5, .thetaLower 4, .thetaUpper 1, .corridorUpper 0 1]

def cycle0956 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, true, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 2 (![5, 4, 3, 2, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 3, 2, 1])]

def cycle0957 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 4, 3, 2, 1]), .gapLower 0 3 (![5, 4, 3, 2, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0958 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 3 (![5, 4, 3, 2, 1]), .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 3, 2, 1])]

def cycle0959 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 4, 3, 2, 1]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 3, 2, 1])]

def cycles : CycleLibrary
  | 0 => some cycle0000
  | 1 => some cycle0001
  | 2 => some cycle0002
  | 3 => some cycle0003
  | 4 => some cycle0004
  | 5 => some cycle0005
  | 6 => some cycle0006
  | 7 => some cycle0007
  | 8 => some cycle0008
  | 9 => some cycle0009
  | 10 => some cycle0010
  | 11 => some cycle0011
  | 12 => some cycle0012
  | 13 => some cycle0013
  | 14 => some cycle0014
  | 15 => some cycle0015
  | 16 => some cycle0016
  | 17 => some cycle0017
  | 18 => some cycle0018
  | 19 => some cycle0019
  | 20 => some cycle0020
  | 21 => some cycle0021
  | 22 => some cycle0022
  | 23 => some cycle0023
  | 24 => some cycle0024
  | 25 => some cycle0025
  | 26 => some cycle0026
  | 27 => some cycle0027
  | 28 => some cycle0028
  | 29 => some cycle0029
  | 30 => some cycle0030
  | 31 => some cycle0031
  | 32 => some cycle0032
  | 33 => some cycle0033
  | 34 => some cycle0034
  | 35 => some cycle0035
  | 36 => some cycle0036
  | 37 => some cycle0037
  | 38 => some cycle0038
  | 39 => some cycle0039
  | 40 => some cycle0040
  | 41 => some cycle0041
  | 42 => some cycle0042
  | 43 => some cycle0043
  | 44 => some cycle0044
  | 45 => some cycle0045
  | 46 => some cycle0046
  | 47 => some cycle0047
  | 48 => some cycle0048
  | 49 => some cycle0049
  | 50 => some cycle0050
  | 51 => some cycle0051
  | 52 => some cycle0052
  | 53 => some cycle0053
  | 54 => some cycle0054
  | 55 => some cycle0055
  | 56 => some cycle0056
  | 57 => some cycle0057
  | 58 => some cycle0058
  | 59 => some cycle0059
  | 60 => some cycle0060
  | 61 => some cycle0061
  | 62 => some cycle0062
  | 63 => some cycle0063
  | 64 => some cycle0064
  | 65 => some cycle0065
  | 66 => some cycle0066
  | 67 => some cycle0067
  | 68 => some cycle0068
  | 69 => some cycle0069
  | 70 => some cycle0070
  | 71 => some cycle0071
  | 72 => some cycle0072
  | 73 => some cycle0073
  | 74 => some cycle0074
  | 75 => some cycle0075
  | 76 => some cycle0076
  | 77 => some cycle0077
  | 78 => some cycle0078
  | 79 => some cycle0079
  | 80 => some cycle0080
  | 81 => some cycle0081
  | 82 => some cycle0082
  | 83 => some cycle0083
  | 84 => some cycle0084
  | 85 => some cycle0085
  | 86 => some cycle0086
  | 87 => some cycle0087
  | 88 => some cycle0088
  | 89 => some cycle0089
  | 90 => some cycle0090
  | 91 => some cycle0091
  | 92 => some cycle0092
  | 93 => some cycle0093
  | 94 => some cycle0094
  | 95 => some cycle0095
  | 96 => some cycle0096
  | 97 => some cycle0097
  | 98 => some cycle0098
  | 99 => some cycle0099
  | 100 => some cycle0100
  | 101 => some cycle0101
  | 102 => some cycle0102
  | 103 => some cycle0103
  | 104 => some cycle0104
  | 105 => some cycle0105
  | 106 => some cycle0106
  | 107 => some cycle0107
  | 108 => some cycle0108
  | 109 => some cycle0109
  | 110 => some cycle0110
  | 111 => some cycle0111
  | 112 => some cycle0112
  | 113 => some cycle0113
  | 114 => some cycle0114
  | 115 => some cycle0115
  | 116 => some cycle0116
  | 117 => some cycle0117
  | 118 => some cycle0118
  | 119 => some cycle0119
  | 120 => some cycle0120
  | 121 => some cycle0121
  | 122 => some cycle0122
  | 123 => some cycle0123
  | 124 => some cycle0124
  | 125 => some cycle0125
  | 126 => some cycle0126
  | 127 => some cycle0127
  | 128 => some cycle0128
  | 129 => some cycle0129
  | 130 => some cycle0130
  | 131 => some cycle0131
  | 132 => some cycle0132
  | 133 => some cycle0133
  | 134 => some cycle0134
  | 135 => some cycle0135
  | 136 => some cycle0136
  | 137 => some cycle0137
  | 138 => some cycle0138
  | 139 => some cycle0139
  | 140 => some cycle0140
  | 141 => some cycle0141
  | 142 => some cycle0142
  | 143 => some cycle0143
  | 144 => some cycle0144
  | 145 => some cycle0145
  | 146 => some cycle0146
  | 147 => some cycle0147
  | 148 => some cycle0148
  | 149 => some cycle0149
  | 150 => some cycle0150
  | 151 => some cycle0151
  | 152 => some cycle0152
  | 153 => some cycle0153
  | 154 => some cycle0154
  | 155 => some cycle0155
  | 156 => some cycle0156
  | 157 => some cycle0157
  | 158 => some cycle0158
  | 159 => some cycle0159
  | 160 => some cycle0160
  | 161 => some cycle0161
  | 162 => some cycle0162
  | 163 => some cycle0163
  | 164 => some cycle0164
  | 165 => some cycle0165
  | 166 => some cycle0166
  | 167 => some cycle0167
  | 168 => some cycle0168
  | 169 => some cycle0169
  | 170 => some cycle0170
  | 171 => some cycle0171
  | 172 => some cycle0172
  | 173 => some cycle0173
  | 174 => some cycle0174
  | 175 => some cycle0175
  | 176 => some cycle0176
  | 177 => some cycle0177
  | 178 => some cycle0178
  | 179 => some cycle0179
  | 180 => some cycle0180
  | 181 => some cycle0181
  | 182 => some cycle0182
  | 183 => some cycle0183
  | 184 => some cycle0184
  | 185 => some cycle0185
  | 186 => some cycle0186
  | 187 => some cycle0187
  | 188 => some cycle0188
  | 189 => some cycle0189
  | 190 => some cycle0190
  | 191 => some cycle0191
  | 192 => some cycle0192
  | 193 => some cycle0193
  | 194 => some cycle0194
  | 195 => some cycle0195
  | 196 => some cycle0196
  | 197 => some cycle0197
  | 198 => some cycle0198
  | 199 => some cycle0199
  | 200 => some cycle0200
  | 201 => some cycle0201
  | 202 => some cycle0202
  | 203 => some cycle0203
  | 204 => some cycle0204
  | 205 => some cycle0205
  | 206 => some cycle0206
  | 207 => some cycle0207
  | 208 => some cycle0208
  | 209 => some cycle0209
  | 210 => some cycle0210
  | 211 => some cycle0211
  | 212 => some cycle0212
  | 213 => some cycle0213
  | 214 => some cycle0214
  | 215 => some cycle0215
  | 216 => some cycle0216
  | 217 => some cycle0217
  | 218 => some cycle0218
  | 219 => some cycle0219
  | 220 => some cycle0220
  | 221 => some cycle0221
  | 222 => some cycle0222
  | 223 => some cycle0223
  | 224 => some cycle0224
  | 225 => some cycle0225
  | 226 => some cycle0226
  | 227 => some cycle0227
  | 228 => some cycle0228
  | 229 => some cycle0229
  | 230 => some cycle0230
  | 231 => some cycle0231
  | 232 => some cycle0232
  | 233 => some cycle0233
  | 234 => some cycle0234
  | 235 => some cycle0235
  | 236 => some cycle0236
  | 237 => some cycle0237
  | 238 => some cycle0238
  | 239 => some cycle0239
  | 240 => some cycle0240
  | 241 => some cycle0241
  | 242 => some cycle0242
  | 243 => some cycle0243
  | 244 => some cycle0244
  | 245 => some cycle0245
  | 246 => some cycle0246
  | 247 => some cycle0247
  | 248 => some cycle0248
  | 249 => some cycle0249
  | 250 => some cycle0250
  | 251 => some cycle0251
  | 252 => some cycle0252
  | 253 => some cycle0253
  | 254 => some cycle0254
  | 255 => some cycle0255
  | 256 => some cycle0256
  | 257 => some cycle0257
  | 258 => some cycle0258
  | 259 => some cycle0259
  | 260 => some cycle0260
  | 261 => some cycle0261
  | 262 => some cycle0262
  | 263 => some cycle0263
  | 264 => some cycle0264
  | 265 => some cycle0265
  | 266 => some cycle0266
  | 267 => some cycle0267
  | 268 => some cycle0268
  | 269 => some cycle0269
  | 270 => some cycle0270
  | 271 => some cycle0271
  | 272 => some cycle0272
  | 273 => some cycle0273
  | 274 => some cycle0274
  | 275 => some cycle0275
  | 276 => some cycle0276
  | 277 => some cycle0277
  | 278 => some cycle0278
  | 279 => some cycle0279
  | 280 => some cycle0280
  | 281 => some cycle0281
  | 282 => some cycle0282
  | 283 => some cycle0283
  | 284 => some cycle0284
  | 285 => some cycle0285
  | 286 => some cycle0286
  | 287 => some cycle0287
  | 288 => some cycle0288
  | 289 => some cycle0289
  | 290 => some cycle0290
  | 291 => some cycle0291
  | 292 => some cycle0292
  | 293 => some cycle0293
  | 294 => some cycle0294
  | 295 => some cycle0295
  | 296 => some cycle0296
  | 297 => some cycle0297
  | 298 => some cycle0298
  | 299 => some cycle0299
  | 300 => some cycle0300
  | 301 => some cycle0301
  | 302 => some cycle0302
  | 303 => some cycle0303
  | 304 => some cycle0304
  | 305 => some cycle0305
  | 306 => some cycle0306
  | 307 => some cycle0307
  | 308 => some cycle0308
  | 309 => some cycle0309
  | 310 => some cycle0310
  | 311 => some cycle0311
  | 312 => some cycle0312
  | 313 => some cycle0313
  | 314 => some cycle0314
  | 315 => some cycle0315
  | 316 => some cycle0316
  | 317 => some cycle0317
  | 318 => some cycle0318
  | 319 => some cycle0319
  | 320 => some cycle0320
  | 321 => some cycle0321
  | 322 => some cycle0322
  | 323 => some cycle0323
  | 324 => some cycle0324
  | 325 => some cycle0325
  | 326 => some cycle0326
  | 327 => some cycle0327
  | 328 => some cycle0328
  | 329 => some cycle0329
  | 330 => some cycle0330
  | 331 => some cycle0331
  | 332 => some cycle0332
  | 333 => some cycle0333
  | 334 => some cycle0334
  | 335 => some cycle0335
  | 336 => some cycle0336
  | 337 => some cycle0337
  | 338 => some cycle0338
  | 339 => some cycle0339
  | 340 => some cycle0340
  | 341 => some cycle0341
  | 342 => some cycle0342
  | 343 => some cycle0343
  | 344 => some cycle0344
  | 345 => some cycle0345
  | 346 => some cycle0346
  | 347 => some cycle0347
  | 348 => some cycle0348
  | 349 => some cycle0349
  | 350 => some cycle0350
  | 351 => some cycle0351
  | 352 => some cycle0352
  | 353 => some cycle0353
  | 354 => some cycle0354
  | 355 => some cycle0355
  | 356 => some cycle0356
  | 357 => some cycle0357
  | 358 => some cycle0358
  | 359 => some cycle0359
  | 360 => some cycle0360
  | 361 => some cycle0361
  | 362 => some cycle0362
  | 363 => some cycle0363
  | 364 => some cycle0364
  | 365 => some cycle0365
  | 366 => some cycle0366
  | 367 => some cycle0367
  | 368 => some cycle0368
  | 369 => some cycle0369
  | 370 => some cycle0370
  | 371 => some cycle0371
  | 372 => some cycle0372
  | 373 => some cycle0373
  | 374 => some cycle0374
  | 375 => some cycle0375
  | 376 => some cycle0376
  | 377 => some cycle0377
  | 378 => some cycle0378
  | 379 => some cycle0379
  | 380 => some cycle0380
  | 381 => some cycle0381
  | 382 => some cycle0382
  | 383 => some cycle0383
  | 384 => some cycle0384
  | 385 => some cycle0385
  | 386 => some cycle0386
  | 387 => some cycle0387
  | 388 => some cycle0388
  | 389 => some cycle0389
  | 390 => some cycle0390
  | 391 => some cycle0391
  | 392 => some cycle0392
  | 393 => some cycle0393
  | 394 => some cycle0394
  | 395 => some cycle0395
  | 396 => some cycle0396
  | 397 => some cycle0397
  | 398 => some cycle0398
  | 399 => some cycle0399
  | 400 => some cycle0400
  | 401 => some cycle0401
  | 402 => some cycle0402
  | 403 => some cycle0403
  | 404 => some cycle0404
  | 405 => some cycle0405
  | 406 => some cycle0406
  | 407 => some cycle0407
  | 408 => some cycle0408
  | 409 => some cycle0409
  | 410 => some cycle0410
  | 411 => some cycle0411
  | 412 => some cycle0412
  | 413 => some cycle0413
  | 414 => some cycle0414
  | 415 => some cycle0415
  | 416 => some cycle0416
  | 417 => some cycle0417
  | 418 => some cycle0418
  | 419 => some cycle0419
  | 420 => some cycle0420
  | 421 => some cycle0421
  | 422 => some cycle0422
  | 423 => some cycle0423
  | 424 => some cycle0424
  | 425 => some cycle0425
  | 426 => some cycle0426
  | 427 => some cycle0427
  | 428 => some cycle0428
  | 429 => some cycle0429
  | 430 => some cycle0430
  | 431 => some cycle0431
  | 432 => some cycle0432
  | 433 => some cycle0433
  | 434 => some cycle0434
  | 435 => some cycle0435
  | 436 => some cycle0436
  | 437 => some cycle0437
  | 438 => some cycle0438
  | 439 => some cycle0439
  | 440 => some cycle0440
  | 441 => some cycle0441
  | 442 => some cycle0442
  | 443 => some cycle0443
  | 444 => some cycle0444
  | 445 => some cycle0445
  | 446 => some cycle0446
  | 447 => some cycle0447
  | 448 => some cycle0448
  | 449 => some cycle0449
  | 450 => some cycle0450
  | 451 => some cycle0451
  | 452 => some cycle0452
  | 453 => some cycle0453
  | 454 => some cycle0454
  | 455 => some cycle0455
  | 456 => some cycle0456
  | 457 => some cycle0457
  | 458 => some cycle0458
  | 459 => some cycle0459
  | 460 => some cycle0460
  | 461 => some cycle0461
  | 462 => some cycle0462
  | 463 => some cycle0463
  | 464 => some cycle0464
  | 465 => some cycle0465
  | 466 => some cycle0466
  | 467 => some cycle0467
  | 468 => some cycle0468
  | 469 => some cycle0469
  | 470 => some cycle0470
  | 471 => some cycle0471
  | 472 => some cycle0472
  | 473 => some cycle0473
  | 474 => some cycle0474
  | 475 => some cycle0475
  | 476 => some cycle0476
  | 477 => some cycle0477
  | 478 => some cycle0478
  | 479 => some cycle0479
  | 480 => some cycle0480
  | 481 => some cycle0481
  | 482 => some cycle0482
  | 483 => some cycle0483
  | 484 => some cycle0484
  | 485 => some cycle0485
  | 486 => some cycle0486
  | 487 => some cycle0487
  | 488 => some cycle0488
  | 489 => some cycle0489
  | 490 => some cycle0490
  | 491 => some cycle0491
  | 492 => some cycle0492
  | 493 => some cycle0493
  | 494 => some cycle0494
  | 495 => some cycle0495
  | 496 => some cycle0496
  | 497 => some cycle0497
  | 498 => some cycle0498
  | 499 => some cycle0499
  | 500 => some cycle0500
  | 501 => some cycle0501
  | 502 => some cycle0502
  | 503 => some cycle0503
  | 504 => some cycle0504
  | 505 => some cycle0505
  | 506 => some cycle0506
  | 507 => some cycle0507
  | 508 => some cycle0508
  | 509 => some cycle0509
  | 510 => some cycle0510
  | 511 => some cycle0511
  | 512 => some cycle0512
  | 513 => some cycle0513
  | 514 => some cycle0514
  | 515 => some cycle0515
  | 516 => some cycle0516
  | 517 => some cycle0517
  | 518 => some cycle0518
  | 519 => some cycle0519
  | 520 => some cycle0520
  | 521 => some cycle0521
  | 522 => some cycle0522
  | 523 => some cycle0523
  | 524 => some cycle0524
  | 525 => some cycle0525
  | 526 => some cycle0526
  | 527 => some cycle0527
  | 528 => some cycle0528
  | 529 => some cycle0529
  | 530 => some cycle0530
  | 531 => some cycle0531
  | 532 => some cycle0532
  | 533 => some cycle0533
  | 534 => some cycle0534
  | 535 => some cycle0535
  | 536 => some cycle0536
  | 537 => some cycle0537
  | 538 => some cycle0538
  | 539 => some cycle0539
  | 540 => some cycle0540
  | 541 => some cycle0541
  | 542 => some cycle0542
  | 543 => some cycle0543
  | 544 => some cycle0544
  | 545 => some cycle0545
  | 546 => some cycle0546
  | 547 => some cycle0547
  | 548 => some cycle0548
  | 549 => some cycle0549
  | 550 => some cycle0550
  | 551 => some cycle0551
  | 552 => some cycle0552
  | 553 => some cycle0553
  | 554 => some cycle0554
  | 555 => some cycle0555
  | 556 => some cycle0556
  | 557 => some cycle0557
  | 558 => some cycle0558
  | 559 => some cycle0559
  | 560 => some cycle0560
  | 561 => some cycle0561
  | 562 => some cycle0562
  | 563 => some cycle0563
  | 564 => some cycle0564
  | 565 => some cycle0565
  | 566 => some cycle0566
  | 567 => some cycle0567
  | 568 => some cycle0568
  | 569 => some cycle0569
  | 570 => some cycle0570
  | 571 => some cycle0571
  | 572 => some cycle0572
  | 573 => some cycle0573
  | 574 => some cycle0574
  | 575 => some cycle0575
  | 576 => some cycle0576
  | 577 => some cycle0577
  | 578 => some cycle0578
  | 579 => some cycle0579
  | 580 => some cycle0580
  | 581 => some cycle0581
  | 582 => some cycle0582
  | 583 => some cycle0583
  | 584 => some cycle0584
  | 585 => some cycle0585
  | 586 => some cycle0586
  | 587 => some cycle0587
  | 588 => some cycle0588
  | 589 => some cycle0589
  | 590 => some cycle0590
  | 591 => some cycle0591
  | 592 => some cycle0592
  | 593 => some cycle0593
  | 594 => some cycle0594
  | 595 => some cycle0595
  | 596 => some cycle0596
  | 597 => some cycle0597
  | 598 => some cycle0598
  | 599 => some cycle0599
  | 600 => some cycle0600
  | 601 => some cycle0601
  | 602 => some cycle0602
  | 603 => some cycle0603
  | 604 => some cycle0604
  | 605 => some cycle0605
  | 606 => some cycle0606
  | 607 => some cycle0607
  | 608 => some cycle0608
  | 609 => some cycle0609
  | 610 => some cycle0610
  | 611 => some cycle0611
  | 612 => some cycle0612
  | 613 => some cycle0613
  | 614 => some cycle0614
  | 615 => some cycle0615
  | 616 => some cycle0616
  | 617 => some cycle0617
  | 618 => some cycle0618
  | 619 => some cycle0619
  | 620 => some cycle0620
  | 621 => some cycle0621
  | 622 => some cycle0622
  | 623 => some cycle0623
  | 624 => some cycle0624
  | 625 => some cycle0625
  | 626 => some cycle0626
  | 627 => some cycle0627
  | 628 => some cycle0628
  | 629 => some cycle0629
  | 630 => some cycle0630
  | 631 => some cycle0631
  | 632 => some cycle0632
  | 633 => some cycle0633
  | 634 => some cycle0634
  | 635 => some cycle0635
  | 636 => some cycle0636
  | 637 => some cycle0637
  | 638 => some cycle0638
  | 639 => some cycle0639
  | 640 => some cycle0640
  | 641 => some cycle0641
  | 642 => some cycle0642
  | 643 => some cycle0643
  | 644 => some cycle0644
  | 645 => some cycle0645
  | 646 => some cycle0646
  | 647 => some cycle0647
  | 648 => some cycle0648
  | 649 => some cycle0649
  | 650 => some cycle0650
  | 651 => some cycle0651
  | 652 => some cycle0652
  | 653 => some cycle0653
  | 654 => some cycle0654
  | 655 => some cycle0655
  | 656 => some cycle0656
  | 657 => some cycle0657
  | 658 => some cycle0658
  | 659 => some cycle0659
  | 660 => some cycle0660
  | 661 => some cycle0661
  | 662 => some cycle0662
  | 663 => some cycle0663
  | 664 => some cycle0664
  | 665 => some cycle0665
  | 666 => some cycle0666
  | 667 => some cycle0667
  | 668 => some cycle0668
  | 669 => some cycle0669
  | 670 => some cycle0670
  | 671 => some cycle0671
  | 672 => some cycle0672
  | 673 => some cycle0673
  | 674 => some cycle0674
  | 675 => some cycle0675
  | 676 => some cycle0676
  | 677 => some cycle0677
  | 678 => some cycle0678
  | 679 => some cycle0679
  | 680 => some cycle0680
  | 681 => some cycle0681
  | 682 => some cycle0682
  | 683 => some cycle0683
  | 684 => some cycle0684
  | 685 => some cycle0685
  | 686 => some cycle0686
  | 687 => some cycle0687
  | 688 => some cycle0688
  | 689 => some cycle0689
  | 690 => some cycle0690
  | 691 => some cycle0691
  | 692 => some cycle0692
  | 693 => some cycle0693
  | 694 => some cycle0694
  | 695 => some cycle0695
  | 696 => some cycle0696
  | 697 => some cycle0697
  | 698 => some cycle0698
  | 699 => some cycle0699
  | 700 => some cycle0700
  | 701 => some cycle0701
  | 702 => some cycle0702
  | 703 => some cycle0703
  | 704 => some cycle0704
  | 705 => some cycle0705
  | 706 => some cycle0706
  | 707 => some cycle0707
  | 708 => some cycle0708
  | 709 => some cycle0709
  | 710 => some cycle0710
  | 711 => some cycle0711
  | 712 => some cycle0712
  | 713 => some cycle0713
  | 714 => some cycle0714
  | 715 => some cycle0715
  | 716 => some cycle0716
  | 717 => some cycle0717
  | 718 => some cycle0718
  | 719 => some cycle0719
  | 720 => some cycle0720
  | 721 => some cycle0721
  | 722 => some cycle0722
  | 723 => some cycle0723
  | 724 => some cycle0724
  | 725 => some cycle0725
  | 726 => some cycle0726
  | 727 => some cycle0727
  | 728 => some cycle0728
  | 729 => some cycle0729
  | 730 => some cycle0730
  | 731 => some cycle0731
  | 732 => some cycle0732
  | 733 => some cycle0733
  | 734 => some cycle0734
  | 735 => some cycle0735
  | 736 => some cycle0736
  | 737 => some cycle0737
  | 738 => some cycle0738
  | 739 => some cycle0739
  | 740 => some cycle0740
  | 741 => some cycle0741
  | 742 => some cycle0742
  | 743 => some cycle0743
  | 744 => some cycle0744
  | 745 => some cycle0745
  | 746 => some cycle0746
  | 747 => some cycle0747
  | 748 => some cycle0748
  | 749 => some cycle0749
  | 750 => some cycle0750
  | 751 => some cycle0751
  | 752 => some cycle0752
  | 753 => some cycle0753
  | 754 => some cycle0754
  | 755 => some cycle0755
  | 756 => some cycle0756
  | 757 => some cycle0757
  | 758 => some cycle0758
  | 759 => some cycle0759
  | 760 => some cycle0760
  | 761 => some cycle0761
  | 762 => some cycle0762
  | 763 => some cycle0763
  | 764 => some cycle0764
  | 765 => some cycle0765
  | 766 => some cycle0766
  | 767 => some cycle0767
  | 768 => some cycle0768
  | 769 => some cycle0769
  | 770 => some cycle0770
  | 771 => some cycle0771
  | 772 => some cycle0772
  | 773 => some cycle0773
  | 774 => some cycle0774
  | 775 => some cycle0775
  | 776 => some cycle0776
  | 777 => some cycle0777
  | 778 => some cycle0778
  | 779 => some cycle0779
  | 780 => some cycle0780
  | 781 => some cycle0781
  | 782 => some cycle0782
  | 783 => some cycle0783
  | 784 => some cycle0784
  | 785 => some cycle0785
  | 786 => some cycle0786
  | 787 => some cycle0787
  | 788 => some cycle0788
  | 789 => some cycle0789
  | 790 => some cycle0790
  | 791 => some cycle0791
  | 792 => some cycle0792
  | 793 => some cycle0793
  | 794 => some cycle0794
  | 795 => some cycle0795
  | 796 => some cycle0796
  | 797 => some cycle0797
  | 798 => some cycle0798
  | 799 => some cycle0799
  | 800 => some cycle0800
  | 801 => some cycle0801
  | 802 => some cycle0802
  | 803 => some cycle0803
  | 804 => some cycle0804
  | 805 => some cycle0805
  | 806 => some cycle0806
  | 807 => some cycle0807
  | 808 => some cycle0808
  | 809 => some cycle0809
  | 810 => some cycle0810
  | 811 => some cycle0811
  | 812 => some cycle0812
  | 813 => some cycle0813
  | 814 => some cycle0814
  | 815 => some cycle0815
  | 816 => some cycle0816
  | 817 => some cycle0817
  | 818 => some cycle0818
  | 819 => some cycle0819
  | 820 => some cycle0820
  | 821 => some cycle0821
  | 822 => some cycle0822
  | 823 => some cycle0823
  | 824 => some cycle0824
  | 825 => some cycle0825
  | 826 => some cycle0826
  | 827 => some cycle0827
  | 828 => some cycle0828
  | 829 => some cycle0829
  | 830 => some cycle0830
  | 831 => some cycle0831
  | 832 => some cycle0832
  | 833 => some cycle0833
  | 834 => some cycle0834
  | 835 => some cycle0835
  | 836 => some cycle0836
  | 837 => some cycle0837
  | 838 => some cycle0838
  | 839 => some cycle0839
  | 840 => some cycle0840
  | 841 => some cycle0841
  | 842 => some cycle0842
  | 843 => some cycle0843
  | 844 => some cycle0844
  | 845 => some cycle0845
  | 846 => some cycle0846
  | 847 => some cycle0847
  | 848 => some cycle0848
  | 849 => some cycle0849
  | 850 => some cycle0850
  | 851 => some cycle0851
  | 852 => some cycle0852
  | 853 => some cycle0853
  | 854 => some cycle0854
  | 855 => some cycle0855
  | 856 => some cycle0856
  | 857 => some cycle0857
  | 858 => some cycle0858
  | 859 => some cycle0859
  | 860 => some cycle0860
  | 861 => some cycle0861
  | 862 => some cycle0862
  | 863 => some cycle0863
  | 864 => some cycle0864
  | 865 => some cycle0865
  | 866 => some cycle0866
  | 867 => some cycle0867
  | 868 => some cycle0868
  | 869 => some cycle0869
  | 870 => some cycle0870
  | 871 => some cycle0871
  | 872 => some cycle0872
  | 873 => some cycle0873
  | 874 => some cycle0874
  | 875 => some cycle0875
  | 876 => some cycle0876
  | 877 => some cycle0877
  | 878 => some cycle0878
  | 879 => some cycle0879
  | 880 => some cycle0880
  | 881 => some cycle0881
  | 882 => some cycle0882
  | 883 => some cycle0883
  | 884 => some cycle0884
  | 885 => some cycle0885
  | 886 => some cycle0886
  | 887 => some cycle0887
  | 888 => some cycle0888
  | 889 => some cycle0889
  | 890 => some cycle0890
  | 891 => some cycle0891
  | 892 => some cycle0892
  | 893 => some cycle0893
  | 894 => some cycle0894
  | 895 => some cycle0895
  | 896 => some cycle0896
  | 897 => some cycle0897
  | 898 => some cycle0898
  | 899 => some cycle0899
  | 900 => some cycle0900
  | 901 => some cycle0901
  | 902 => some cycle0902
  | 903 => some cycle0903
  | 904 => some cycle0904
  | 905 => some cycle0905
  | 906 => some cycle0906
  | 907 => some cycle0907
  | 908 => some cycle0908
  | 909 => some cycle0909
  | 910 => some cycle0910
  | 911 => some cycle0911
  | 912 => some cycle0912
  | 913 => some cycle0913
  | 914 => some cycle0914
  | 915 => some cycle0915
  | 916 => some cycle0916
  | 917 => some cycle0917
  | 918 => some cycle0918
  | 919 => some cycle0919
  | 920 => some cycle0920
  | 921 => some cycle0921
  | 922 => some cycle0922
  | 923 => some cycle0923
  | 924 => some cycle0924
  | 925 => some cycle0925
  | 926 => some cycle0926
  | 927 => some cycle0927
  | 928 => some cycle0928
  | 929 => some cycle0929
  | 930 => some cycle0930
  | 931 => some cycle0931
  | 932 => some cycle0932
  | 933 => some cycle0933
  | 934 => some cycle0934
  | 935 => some cycle0935
  | 936 => some cycle0936
  | 937 => some cycle0937
  | 938 => some cycle0938
  | 939 => some cycle0939
  | 940 => some cycle0940
  | 941 => some cycle0941
  | 942 => some cycle0942
  | 943 => some cycle0943
  | 944 => some cycle0944
  | 945 => some cycle0945
  | 946 => some cycle0946
  | 947 => some cycle0947
  | 948 => some cycle0948
  | 949 => some cycle0949
  | 950 => some cycle0950
  | 951 => some cycle0951
  | 952 => some cycle0952
  | 953 => some cycle0953
  | 954 => some cycle0954
  | 955 => some cycle0955
  | 956 => some cycle0956
  | 957 => some cycle0957
  | 958 => some cycle0958
  | 959 => some cycle0959
  | _ => none

def nodes : NodeLibrary
  | 0 => some (.leaf 6049)
  | 1 => some (.leaf 6050)
  | 2 => some (.leaf 6051)
  | 3 => some (.leaf 6052)
  | 4 => some (.leaf 6053)
  | 5 => some (.leaf 6054)
  | 6 => some (.leaf 6055)
  | 7 => some (.leaf 6056)
  | 8 => some (.triangle 10 9222 9223)
  | 9 => some (.leaf 6057)
  | 10 => some (.leaf 6058)
  | 11 => some (.triangle 10 9225 9226)
  | 12 => some (.leaf 6059)
  | 13 => some (.leaf 6060)
  | 14 => some (.leaf 6061)
  | 15 => some (.leaf 6062)
  | 16 => some (.leaf 6063)
  | 17 => some (.leaf 6064)
  | 18 => some (.leaf 6065)
  | 19 => some (.leaf 6066)
  | 20 => some (.leaf 6067)
  | 21 => some (.leaf 6068)
  | 22 => some (.heavy (![9213, 9214, 9215, 9216, 9217, 9218, 9219, 9220, 9221, 9224, 9227, 9228, 9229, 9230, 9231, 9232, 9233, 9234, 9235, 9236, 9237]))
  | 23 => some (.leaf 6069)
  | 24 => some (.leaf 6070)
  | 25 => some (.leaf 6071)
  | 26 => some (.leaf 6072)
  | 27 => some (.leaf 6073)
  | 28 => some (.leaf 6074)
  | 29 => some (.leaf 6075)
  | 30 => some (.leaf 6076)
  | 31 => some (.positive 1 (![9241, 9242, 9243, 9244, 9245, 9246]))
  | 32 => some (.triangle 18 1165 9247)
  | 33 => some (.leaf 6077)
  | 34 => some (.leaf 6078)
  | 35 => some (.leaf 6079)
  | 36 => some (.positive 0 (![9239, 9240, 9248, 9249, 9250, 9251]))
  | 37 => some (.triangle 15 1161 9252)
  | 38 => some (.triangle 1 9208 9253)
  | 39 => some (.leaf 6080)
  | 40 => some (.leaf 6081)
  | 41 => some (.leaf 6082)
  | 42 => some (.leaf 6083)
  | 43 => some (.leaf 6084)
  | 44 => some (.leaf 6085)
  | 45 => some (.positive 1 (![9255, 9256, 9257, 9258, 9259, 9260]))
  | 46 => some (.triangle 18 1165 9261)
  | 47 => some (.leaf 6086)
  | 48 => some (.leaf 6087)
  | 49 => some (.leaf 6088)
  | 50 => some (.leaf 6089)
  | 51 => some (.leaf 6090)
  | 52 => some (.positive 0 (![9262, 9263, 9264, 9265, 9266, 9267]))
  | 53 => some (.triangle 15 1161 9268)
  | 54 => some (.triangle 10 9254 9269)
  | 55 => some (.leaf 6091)
  | 56 => some (.leaf 6092)
  | 57 => some (.leaf 6093)
  | 58 => some (.leaf 6094)
  | 59 => some (.leaf 6095)
  | 60 => some (.leaf 6096)
  | 61 => some (.leaf 6097)
  | 62 => some (.leaf 6098)
  | 63 => some (.leaf 6099)
  | 64 => some (.triangle 10 9278 9279)
  | 65 => some (.leaf 6100)
  | 66 => some (.leaf 6101)
  | 67 => some (.triangle 10 9281 9282)
  | 68 => some (.leaf 6102)
  | 69 => some (.leaf 6103)
  | 70 => some (.triangle 10 9284 9285)
  | 71 => some (.leaf 6104)
  | 72 => some (.leaf 6105)
  | 73 => some (.leaf 6106)
  | 74 => some (.leaf 6107)
  | 75 => some (.leaf 6108)
  | 76 => some (.leaf 6109)
  | 77 => some (.leaf 6110)
  | 78 => some (.leaf 6111)
  | 79 => some (.leaf 6112)
  | 80 => some (.leaf 6113)
  | 81 => some (.heavy (![9270, 9271, 9272, 9273, 9274, 9275, 9276, 9277, 9280, 9283, 9286, 9287, 9288, 9289, 9290, 9291, 9292, 9293, 9294, 9295, 9296]))
  | 82 => some (.triangle 9 9238 9297)
  | 83 => some (.leaf 6114)
  | 84 => some (.leaf 6115)
  | 85 => some (.leaf 6116)
  | 86 => some (.leaf 6117)
  | 87 => some (.leaf 6118)
  | 88 => some (.leaf 6119)
  | 89 => some (.leaf 6120)
  | 90 => some (.leaf 6121)
  | 91 => some (.leaf 6122)
  | 92 => some (.positive 1 (![9302, 9303, 9304, 9305, 9306, 9307]))
  | 93 => some (.triangle 18 9301 9308)
  | 94 => some (.leaf 6123)
  | 95 => some (.leaf 6124)
  | 96 => some (.positive 0 (![9299, 9300, 7356, 9309, 9310, 9311]))
  | 97 => some (.leaf 6125)
  | 98 => some (.triangle 14 9312 9313)
  | 99 => some (.leaf 6126)
  | 100 => some (.triangle 12 9314 9315)
  | 101 => some (.leaf 6127)
  | 102 => some (.leaf 6128)
  | 103 => some (.leaf 6129)
  | 104 => some (.leaf 6130)
  | 105 => some (.leaf 6131)
  | 106 => some (.leaf 6132)
  | 107 => some (.positive 1 (![9317, 9318, 9319, 9320, 9321, 9322]))
  | 108 => some (.triangle 18 9301 9323)
  | 109 => some (.leaf 6133)
  | 110 => some (.leaf 6134)
  | 111 => some (.leaf 6135)
  | 112 => some (.leaf 6136)
  | 113 => some (.leaf 6137)
  | 114 => some (.positive 0 (![9324, 9325, 9326, 9327, 9328, 9329]))
  | 115 => some (.triangle 12 9330 6528)
  | 116 => some (.leaf 6138)
  | 117 => some (.triangle 14 9331 9332)
  | 118 => some (.triangle 10 9316 9333)
  | 119 => some (.leaf 6139)
  | 120 => some (.leaf 6140)
  | 121 => some (.leaf 6141)
  | 122 => some (.leaf 6142)
  | 123 => some (.leaf 6143)
  | 124 => some (.leaf 6144)
  | 125 => some (.leaf 6145)
  | 126 => some (.leaf 6146)
  | 127 => some (.leaf 6147)
  | 128 => some (.leaf 6148)
  | 129 => some (.triangle 10 9343 9344)
  | 130 => some (.leaf 6149)
  | 131 => some (.leaf 6150)
  | 132 => some (.triangle 10 9346 9347)
  | 133 => some (.leaf 6151)
  | 134 => some (.leaf 6152)
  | 135 => some (.leaf 6153)
  | 136 => some (.leaf 6154)
  | 137 => some (.leaf 6155)
  | 138 => some (.leaf 6156)
  | 139 => some (.leaf 6157)
  | 140 => some (.leaf 6158)
  | 141 => some (.leaf 6159)
  | 142 => some (.leaf 6160)
  | 143 => some (.heavy (![9334, 9335, 9336, 9337, 9338, 9339, 9340, 9341, 9342, 9345, 9348, 9349, 9350, 9351, 9352, 9353, 9354, 9355, 9356, 9357, 9358]))
  | 144 => some (.triangle 3 9298 9359)
  | 145 => some (.leaf 6161)
  | 146 => some (.leaf 6162)
  | 147 => some (.leaf 6163)
  | 148 => some (.leaf 6164)
  | 149 => some (.triangle 18 9363 9364)
  | 150 => some (.leaf 6165)
  | 151 => some (.leaf 6166)
  | 152 => some (.positive 0 (![9361, 9362, 7467, 9365, 9366, 9367]))
  | 153 => some (.leaf 6167)
  | 154 => some (.triangle 13 9368 9369)
  | 155 => some (.leaf 6168)
  | 156 => some (.triangle 11 9370 9371)
  | 157 => some (.leaf 6169)
  | 158 => some (.leaf 6170)
  | 159 => some (.leaf 6171)
  | 160 => some (.leaf 6172)
  | 161 => some (.leaf 6173)
  | 162 => some (.positive 0 (![9365, 9373, 9374, 9375, 9376, 9377]))
  | 163 => some (.triangle 11 9378 6780)
  | 164 => some (.leaf 6174)
  | 165 => some (.triangle 13 9379 9380)
  | 166 => some (.triangle 10 9372 9381)
  | 167 => some (.leaf 6175)
  | 168 => some (.leaf 6176)
  | 169 => some (.leaf 6177)
  | 170 => some (.leaf 6178)
  | 171 => some (.leaf 6179)
  | 172 => some (.leaf 6180)
  | 173 => some (.leaf 6181)
  | 174 => some (.leaf 6182)
  | 175 => some (.leaf 6183)
  | 176 => some (.leaf 6184)
  | 177 => some (.triangle 10 9391 9392)
  | 178 => some (.leaf 6185)
  | 179 => some (.leaf 6186)
  | 180 => some (.triangle 10 9394 9395)
  | 181 => some (.leaf 6187)
  | 182 => some (.leaf 6188)
  | 183 => some (.leaf 6189)
  | 184 => some (.leaf 6190)
  | 185 => some (.leaf 6191)
  | 186 => some (.leaf 6192)
  | 187 => some (.leaf 6193)
  | 188 => some (.leaf 6194)
  | 189 => some (.leaf 6195)
  | 190 => some (.leaf 6196)
  | 191 => some (.heavy (![9382, 9383, 9384, 9385, 9386, 9387, 9388, 9389, 9390, 9393, 9396, 9397, 9398, 9399, 9400, 9401, 9402, 9403, 9404, 9405, 9406]))
  | 192 => some (.leaf 6197)
  | 193 => some (.leaf 6198)
  | 194 => some (.leaf 6199)
  | 195 => some (.leaf 6200)
  | 196 => some (.triangle 18 9410 9411)
  | 197 => some (.leaf 6201)
  | 198 => some (.positive 0 (![9408, 9409, 7567, 7568, 9412, 9413]))
  | 199 => some (.triangle 15 9414 4448)
  | 200 => some (.leaf 6202)
  | 201 => some (.triangle 14 9415 9416)
  | 202 => some (.leaf 6203)
  | 203 => some (.triangle 13 9417 9418)
  | 204 => some (.triangle 12 9419 9315)
  | 205 => some (.triangle 11 9420 9371)
  | 206 => some (.leaf 6204)
  | 207 => some (.leaf 6205)
  | 208 => some (.leaf 6206)
  | 209 => some (.leaf 6207)
  | 210 => some (.leaf 6208)
  | 211 => some (.positive 0 (![9412, 9422, 9423, 9424, 9425, 9426]))
  | 212 => some (.triangle 15 9427 4448)
  | 213 => some (.triangle 12 9428 6528)
  | 214 => some (.triangle 11 9429 6780)
  | 215 => some (.leaf 6209)
  | 216 => some (.triangle 14 9430 9431)
  | 217 => some (.leaf 6210)
  | 218 => some (.triangle 13 9432 9433)
  | 219 => some (.triangle 10 9421 9434)
  | 220 => some (.leaf 6211)
  | 221 => some (.leaf 6212)
  | 222 => some (.leaf 6213)
  | 223 => some (.leaf 6214)
  | 224 => some (.leaf 6215)
  | 225 => some (.leaf 6216)
  | 226 => some (.leaf 6217)
  | 227 => some (.leaf 6218)
  | 228 => some (.leaf 6219)
  | 229 => some (.leaf 6220)
  | 230 => some (.leaf 6221)
  | 231 => some (.triangle 10 9445 9446)
  | 232 => some (.leaf 6222)
  | 233 => some (.leaf 6223)
  | 234 => some (.leaf 6224)
  | 235 => some (.leaf 6225)
  | 236 => some (.leaf 6226)
  | 237 => some (.leaf 6227)
  | 238 => some (.leaf 6228)
  | 239 => some (.leaf 6229)
  | 240 => some (.leaf 6230)
  | 241 => some (.leaf 6231)
  | 242 => some (.heavy (![9435, 9436, 9437, 9438, 9439, 9440, 9441, 9442, 9443, 9444, 9447, 9448, 9449, 9450, 9451, 9452, 9453, 9454, 9455, 9456, 9457]))
  | 243 => some (.triangle 3 9407 9458)
  | 244 => some (.leaf 6232)
  | 245 => some (.leaf 6233)
  | 246 => some (.leaf 6234)
  | 247 => some (.positive 1 (![9241, 9242, 9243, 9460, 9461, 9462]))
  | 248 => some (.triangle 18 1165 9463)
  | 249 => some (.leaf 6235)
  | 250 => some (.positive 0 (![9408, 7709, 7710, 7711, 9464, 9465]))
  | 251 => some (.triangle 3 7707 9466)
  | 252 => some (.leaf 6236)
  | 253 => some (.leaf 6237)
  | 254 => some (.leaf 6238)
  | 255 => some (.leaf 6239)
  | 256 => some (.positive 0 (![9468, 9469, 7719, 7720, 9470, 9471]))
  | 257 => some (.triangle 15 9467 9472)
  | 258 => some (.leaf 6240)
  | 259 => some (.triangle 14 9473 9474)
  | 260 => some (.leaf 6241)
  | 261 => some (.triangle 13 9475 9476)
  | 262 => some (.triangle 12 9477 9315)
  | 263 => some (.triangle 11 9478 9371)
  | 264 => some (.leaf 6242)
  | 265 => some (.leaf 6243)
  | 266 => some (.leaf 6244)
  | 267 => some (.leaf 6245)
  | 268 => some (.leaf 6246)
  | 269 => some (.leaf 6247)
  | 270 => some (.leaf 6248)
  | 271 => some (.positive 1 (![9481, 9482, 9483, 9484, 9485, 9486]))
  | 272 => some (.triangle 18 1165 9487)
  | 273 => some (.leaf 6249)
  | 274 => some (.leaf 6250)
  | 275 => some (.leaf 6251)
  | 276 => some (.leaf 6252)
  | 277 => some (.leaf 6253)
  | 278 => some (.positive 0 (![9488, 9489, 9490, 9491, 9492, 9493]))
  | 279 => some (.triangle 15 9480 9494)
  | 280 => some (.triangle 12 9495 6528)
  | 281 => some (.triangle 11 9496 6780)
  | 282 => some (.leaf 6254)
  | 283 => some (.triangle 14 9497 9498)
  | 284 => some (.leaf 6255)
  | 285 => some (.triangle 13 9499 9500)
  | 286 => some (.triangle 10 9479 9501)
  | 287 => some (.leaf 6256)
  | 288 => some (.leaf 6257)
  | 289 => some (.leaf 6258)
  | 290 => some (.leaf 6259)
  | 291 => some (.leaf 6260)
  | 292 => some (.leaf 6261)
  | 293 => some (.leaf 6262)
  | 294 => some (.leaf 6263)
  | 295 => some (.leaf 6264)
  | 296 => some (.leaf 6265)
  | 297 => some (.leaf 6266)
  | 298 => some (.triangle 10 9512 9513)
  | 299 => some (.leaf 6267)
  | 300 => some (.leaf 6268)
  | 301 => some (.leaf 6269)
  | 302 => some (.leaf 6270)
  | 303 => some (.leaf 6271)
  | 304 => some (.leaf 6272)
  | 305 => some (.leaf 6273)
  | 306 => some (.leaf 6274)
  | 307 => some (.leaf 6275)
  | 308 => some (.leaf 6276)
  | 309 => some (.heavy (![9502, 9503, 9504, 9505, 9506, 9507, 9508, 9509, 9510, 9511, 9514, 9515, 9516, 9517, 9518, 9519, 9520, 9521, 9522, 9523, 9524]))
  | 310 => some (.triangle 9 9459 9525)
  | 311 => some (.triangle 2 9360 9526)
  | 312 => some (.leaf 6277)
  | 313 => some (.leaf 6278)
  | 314 => some (.leaf 6279)
  | 315 => some (.leaf 6280)
  | 316 => some (.leaf 6281)
  | 317 => some (.leaf 6282)
  | 318 => some (.leaf 6283)
  | 319 => some (.leaf 6284)
  | 320 => some (.leaf 6285)
  | 321 => some (.positive 1 (![9531, 9532, 9533, 9534, 9535, 9536]))
  | 322 => some (.triangle 17 9537 2452)
  | 323 => some (.leaf 6286)
  | 324 => some (.leaf 6287)
  | 325 => some (.positive 0 (![9528, 9529, 9530, 9538, 9539, 9540]))
  | 326 => some (.triangle 3 8252 9541)
  | 327 => some (.leaf 6288)
  | 328 => some (.triangle 14 9542 9543)
  | 329 => some (.triangle 1 9208 9544)
  | 330 => some (.leaf 6289)
  | 331 => some (.triangle 12 9545 9546)
  | 332 => some (.leaf 6290)
  | 333 => some (.leaf 6291)
  | 334 => some (.leaf 6292)
  | 335 => some (.leaf 6293)
  | 336 => some (.leaf 6294)
  | 337 => some (.leaf 6295)
  | 338 => some (.leaf 6296)
  | 339 => some (.positive 1 (![9549, 9550, 9551, 9552, 9553, 9554]))
  | 340 => some (.leaf 6297)
  | 341 => some (.triangle 17 9555 9556)
  | 342 => some (.leaf 6298)
  | 343 => some (.leaf 6299)
  | 344 => some (.leaf 6300)
  | 345 => some (.leaf 6301)
  | 346 => some (.leaf 6302)
  | 347 => some (.positive 0 (![9557, 9558, 9559, 9560, 9561, 9562]))
  | 348 => some (.triangle 12 9548 9563)
  | 349 => some (.leaf 6303)
  | 350 => some (.triangle 14 9564 9565)
  | 351 => some (.triangle 10 9547 9566)
  | 352 => some (.leaf 6304)
  | 353 => some (.leaf 6305)
  | 354 => some (.leaf 6306)
  | 355 => some (.leaf 6307)
  | 356 => some (.leaf 6308)
  | 357 => some (.leaf 6309)
  | 358 => some (.leaf 6310)
  | 359 => some (.leaf 6311)
  | 360 => some (.leaf 6312)
  | 361 => some (.leaf 6313)
  | 362 => some (.triangle 10 9576 9577)
  | 363 => some (.leaf 6314)
  | 364 => some (.leaf 6315)
  | 365 => some (.triangle 10 9579 9580)
  | 366 => some (.leaf 6316)
  | 367 => some (.leaf 6317)
  | 368 => some (.leaf 6318)
  | 369 => some (.leaf 6319)
  | 370 => some (.leaf 6320)
  | 371 => some (.leaf 6321)
  | 372 => some (.leaf 6322)
  | 373 => some (.leaf 6323)
  | 374 => some (.leaf 6324)
  | 375 => some (.leaf 6325)
  | 376 => some (.heavy (![9567, 9568, 9569, 9570, 9571, 9572, 9573, 9574, 9575, 9578, 9581, 9582, 9583, 9584, 9585, 9586, 9587, 9588, 9589, 9590, 9591]))
  | 377 => some (.leaf 6326)
  | 378 => some (.leaf 6327)
  | 379 => some (.leaf 6328)
  | 380 => some (.leaf 6329)
  | 381 => some (.leaf 6330)
  | 382 => some (.leaf 6331)
  | 383 => some (.leaf 6332)
  | 384 => some (.leaf 6333)
  | 385 => some (.positive 1 (![9531, 9598, 9533, 9534, 9599, 9600]))
  | 386 => some (.triangle 17 9601 2452)
  | 387 => some (.leaf 6334)
  | 388 => some (.positive 0 (![9594, 9595, 9596, 9597, 9602, 9603]))
  | 389 => some (.triangle 3 9593 9604)
  | 390 => some (.leaf 6335)
  | 391 => some (.leaf 6336)
  | 392 => some (.leaf 6337)
  | 393 => some (.leaf 6338)
  | 394 => some (.leaf 6339)
  | 395 => some (.leaf 6340)
  | 396 => some (.positive 0 (![9606, 9607, 9608, 9609, 9610, 9611]))
  | 397 => some (.triangle 15 9605 9612)
  | 398 => some (.triangle 14 9613 9543)
  | 399 => some (.leaf 6341)
  | 400 => some (.triangle 13 9614 9615)
  | 401 => some (.triangle 12 9616 9546)
  | 402 => some (.triangle 11 9617 9371)
  | 403 => some (.leaf 6342)
  | 404 => some (.leaf 6343)
  | 405 => some (.leaf 6344)
  | 406 => some (.leaf 6345)
  | 407 => some (.leaf 6346)
  | 408 => some (.leaf 6347)
  | 409 => some (.positive 1 (![9619, 9620, 9621, 9622, 9623, 9624]))
  | 410 => some (.leaf 6348)
  | 411 => some (.triangle 17 9625 9626)
  | 412 => some (.leaf 6349)
  | 413 => some (.leaf 6350)
  | 414 => some (.leaf 6351)
  | 415 => some (.leaf 6352)
  | 416 => some (.leaf 6353)
  | 417 => some (.positive 0 (![9627, 9628, 9629, 9630, 9631, 9632]))
  | 418 => some (.triangle 12 9548 9633)
  | 419 => some (.triangle 11 9634 6780)
  | 420 => some (.leaf 6354)
  | 421 => some (.triangle 14 9635 9636)
  | 422 => some (.leaf 6355)
  | 423 => some (.triangle 13 9637 9638)
  | 424 => some (.triangle 10 9618 9639)
  | 425 => some (.leaf 6356)
  | 426 => some (.leaf 6357)
  | 427 => some (.leaf 6358)
  | 428 => some (.leaf 6359)
  | 429 => some (.leaf 6360)
  | 430 => some (.leaf 6361)
  | 431 => some (.leaf 6362)
  | 432 => some (.leaf 6363)
  | 433 => some (.leaf 6364)
  | 434 => some (.leaf 6365)
  | 435 => some (.leaf 6366)
  | 436 => some (.triangle 10 9650 9651)
  | 437 => some (.leaf 6367)
  | 438 => some (.leaf 6368)
  | 439 => some (.leaf 6369)
  | 440 => some (.leaf 6370)
  | 441 => some (.leaf 6371)
  | 442 => some (.leaf 6372)
  | 443 => some (.leaf 6373)
  | 444 => some (.leaf 6374)
  | 445 => some (.leaf 6375)
  | 446 => some (.heavy (![9640, 9641, 9642, 9643, 9644, 9645, 9646, 9647, 9648, 9649, 9652, 9653, 9654, 9655, 9656, 9648, 9657, 9658, 9659, 9660, 9661]))
  | 447 => some (.triangle 2 9592 9662)
  | 448 => some (.triangle 6 9527 9663)
  | 449 => some (.leaf 6376)
  | 450 => some (.leaf 6377)
  | 451 => some (.leaf 6378)
  | 452 => some (.leaf 6379)
  | 453 => some (.leaf 6380)
  | 454 => some (.leaf 6381)
  | 455 => some (.leaf 6382)
  | 456 => some (.leaf 6383)
  | 457 => some (.leaf 6384)
  | 458 => some (.positive 1 (![9668, 9669, 9670, 9671, 9672, 9673]))
  | 459 => some (.triangle 16 9674 2536)
  | 460 => some (.leaf 6385)
  | 461 => some (.leaf 6386)
  | 462 => some (.positive 0 (![9665, 9666, 9667, 9675, 9676, 9677]))
  | 463 => some (.triangle 2 8604 9678)
  | 464 => some (.leaf 6387)
  | 465 => some (.triangle 13 9679 9680)
  | 466 => some (.triangle 1 9208 9681)
  | 467 => some (.leaf 6388)
  | 468 => some (.triangle 11 9682 9683)
  | 469 => some (.leaf 6389)
  | 470 => some (.leaf 6390)
  | 471 => some (.leaf 6391)
  | 472 => some (.leaf 6392)
  | 473 => some (.leaf 6393)
  | 474 => some (.leaf 6394)
  | 475 => some (.leaf 6395)
  | 476 => some (.positive 1 (![9686, 9687, 9688, 9689, 9690, 9691]))
  | 477 => some (.leaf 6396)
  | 478 => some (.triangle 16 9692 9693)
  | 479 => some (.leaf 6397)
  | 480 => some (.leaf 6398)
  | 481 => some (.leaf 6399)
  | 482 => some (.leaf 6400)
  | 483 => some (.leaf 6401)
  | 484 => some (.positive 0 (![9694, 9695, 9696, 9697, 9698, 9699]))
  | 485 => some (.triangle 11 9685 9700)
  | 486 => some (.leaf 6402)
  | 487 => some (.triangle 13 9701 9702)
  | 488 => some (.triangle 10 9684 9703)
  | 489 => some (.leaf 6403)
  | 490 => some (.leaf 6404)
  | 491 => some (.leaf 6405)
  | 492 => some (.leaf 6406)
  | 493 => some (.leaf 6407)
  | 494 => some (.leaf 6408)
  | 495 => some (.leaf 6409)
  | 496 => some (.leaf 6410)
  | 497 => some (.leaf 6411)
  | 498 => some (.leaf 6412)
  | 499 => some (.triangle 10 9713 9714)
  | 500 => some (.leaf 6413)
  | 501 => some (.leaf 6414)
  | 502 => some (.triangle 10 9716 9717)
  | 503 => some (.leaf 6415)
  | 504 => some (.leaf 6416)
  | 505 => some (.leaf 6417)
  | 506 => some (.leaf 6418)
  | 507 => some (.leaf 6419)
  | 508 => some (.leaf 6420)
  | 509 => some (.leaf 6421)
  | 510 => some (.leaf 6422)
  | 511 => some (.leaf 6423)
  | 512 => some (.leaf 6424)
  | 513 => some (.heavy (![9704, 9705, 9706, 9707, 9708, 9709, 9710, 9711, 9712, 9715, 9718, 9719, 9720, 9721, 9722, 9723, 9724, 9725, 9726, 9727, 9728]))
  | 514 => some (.leaf 6425)
  | 515 => some (.leaf 6426)
  | 516 => some (.leaf 6427)
  | 517 => some (.leaf 6428)
  | 518 => some (.leaf 6429)
  | 519 => some (.positive 1 (![9668, 9669, 9670, 9671, 9733, 9734]))
  | 520 => some (.triangle 16 9735 2536)
  | 521 => some (.leaf 6430)
  | 522 => some (.positive 0 (![9730, 9731, 9732, 7568, 9736, 9737]))
  | 523 => some (.leaf 6431)
  | 524 => some (.triangle 15 9738 9739)
  | 525 => some (.leaf 6432)
  | 526 => some (.triangle 14 9740 9741)
  | 527 => some (.triangle 13 9742 9680)
  | 528 => some (.triangle 12 9743 9315)
  | 529 => some (.triangle 11 9744 9683)
  | 530 => some (.leaf 6433)
  | 531 => some (.leaf 6434)
  | 532 => some (.leaf 6435)
  | 533 => some (.leaf 6436)
  | 534 => some (.leaf 6437)
  | 535 => some (.leaf 6438)
  | 536 => some (.leaf 6439)
  | 537 => some (.positive 1 (![9747, 9748, 9749, 9750, 9751, 9752]))
  | 538 => some (.leaf 6440)
  | 539 => some (.triangle 16 9753 9754)
  | 540 => some (.leaf 6441)
  | 541 => some (.leaf 6442)
  | 542 => some (.leaf 6443)
  | 543 => some (.leaf 6444)
  | 544 => some (.leaf 6445)
  | 545 => some (.positive 0 (![9755, 9756, 9757, 9758, 9759, 9760]))
  | 546 => some (.triangle 12 9761 6528)
  | 547 => some (.leaf 6446)
  | 548 => some (.triangle 15 9762 9763)
  | 549 => some (.triangle 11 9746 9764)
  | 550 => some (.leaf 6447)
  | 551 => some (.triangle 14 9765 9766)
  | 552 => some (.leaf 6448)
  | 553 => some (.triangle 13 9767 9768)
  | 554 => some (.triangle 10 9745 9769)
  | 555 => some (.leaf 6449)
  | 556 => some (.leaf 6450)
  | 557 => some (.leaf 6451)
  | 558 => some (.leaf 6452)
  | 559 => some (.leaf 6453)
  | 560 => some (.leaf 6454)
  | 561 => some (.leaf 6455)
  | 562 => some (.leaf 6456)
  | 563 => some (.leaf 6457)
  | 564 => some (.leaf 6458)
  | 565 => some (.leaf 6459)
  | 566 => some (.triangle 10 9780 9781)
  | 567 => some (.leaf 6460)
  | 568 => some (.leaf 6461)
  | 569 => some (.leaf 6462)
  | 570 => some (.leaf 6463)
  | 571 => some (.leaf 6464)
  | 572 => some (.leaf 6465)
  | 573 => some (.leaf 6466)
  | 574 => some (.leaf 6467)
  | 575 => some (.leaf 6468)
  | 576 => some (.heavy (![9770, 9771, 9772, 9773, 9774, 9775, 9776, 9777, 9778, 9779, 9782, 9783, 9784, 9785, 9786, 9778, 9787, 9788, 9789, 9790, 9791]))
  | 577 => some (.triangle 3 9729 9792)
  | 578 => some (.leaf 6469)
  | 579 => some (.leaf 6470)
  | 580 => some (.leaf 6471)
  | 581 => some (.leaf 6472)
  | 582 => some (.leaf 6473)
  | 583 => some (.leaf 6474)
  | 584 => some (.leaf 6475)
  | 585 => some (.leaf 6476)
  | 586 => some (.leaf 6477)
  | 587 => some (.leaf 6478)
  | 588 => some (.leaf 6479)
  | 589 => some (.leaf 6480)
  | 590 => some (.triangle 19 9804 9805)
  | 591 => some (.positive 1 (![9799, 9800, 9801, 9802, 9803, 9806]))
  | 592 => some (.triangle 18 9807 2170)
  | 593 => some (.triangle 17 9808 2452)
  | 594 => some (.triangle 16 9809 2536)
  | 595 => some (.leaf 6481)
  | 596 => some (.positive 0 (![9795, 9796, 9797, 9798, 9810, 9811]))
  | 597 => some (.triangle 3 9794 9812)
  | 598 => some (.leaf 6482)
  | 599 => some (.triangle 15 9813 9814)
  | 600 => some (.triangle 2 8604 9815)
  | 601 => some (.triangle 14 9816 9543)
  | 602 => some (.triangle 13 9817 9680)
  | 603 => some (.triangle 1 9208 9818)
  | 604 => some (.leaf 6483)
  | 605 => some (.triangle 12 9819 9820)
  | 606 => some (.leaf 6484)
  | 607 => some (.triangle 11 9821 9822)
  | 608 => some (.leaf 6485)
  | 609 => some (.leaf 6486)
  | 610 => some (.leaf 6487)
  | 611 => some (.leaf 6488)
  | 612 => some (.leaf 6489)
  | 613 => some (.leaf 6490)
  | 614 => some (.leaf 6491)
  | 615 => some (.leaf 6492)
  | 616 => some (.triangle 1 9831 9806)
  | 617 => some (.positive 1 (![9826, 9827, 9828, 9829, 9830, 9832]))
  | 618 => some (.triangle 18 9833 2170)
  | 619 => some (.leaf 6493)
  | 620 => some (.triangle 17 9834 9835)
  | 621 => some (.leaf 6494)
  | 622 => some (.triangle 16 9836 9837)
  | 623 => some (.leaf 6495)
  | 624 => some (.leaf 6496)
  | 625 => some (.leaf 6497)
  | 626 => some (.leaf 6498)
  | 627 => some (.leaf 6499)
  | 628 => some (.positive 0 (![9838, 9839, 9840, 9841, 9842, 9843]))
  | 629 => some (.triangle 12 9825 9844)
  | 630 => some (.leaf 6500)
  | 631 => some (.triangle 15 9845 9846)
  | 632 => some (.triangle 11 9824 9847)
  | 633 => some (.leaf 6501)
  | 634 => some (.triangle 14 9848 9849)
  | 635 => some (.leaf 6502)
  | 636 => some (.triangle 13 9850 9851)
  | 637 => some (.triangle 10 9823 9852)
  | 638 => some (.leaf 6503)
  | 639 => some (.leaf 6504)
  | 640 => some (.leaf 6505)
  | 641 => some (.leaf 6506)
  | 642 => some (.leaf 6507)
  | 643 => some (.leaf 6508)
  | 644 => some (.leaf 6509)
  | 645 => some (.leaf 6510)
  | 646 => some (.leaf 6511)
  | 647 => some (.leaf 6512)
  | 648 => some (.positive 1 (![9826, 9862, 9828, 9829, 9830, 9863]))
  | 649 => some (.leaf 6513)
  | 650 => some (.triangle 18 9864 9865)
  | 651 => some (.leaf 6514)
  | 652 => some (.triangle 17 9866 9867)
  | 653 => some (.leaf 6515)
  | 654 => some (.triangle 16 9868 9869)
  | 655 => some (.leaf 6516)
  | 656 => some (.positive 0 (![9870, 9839, 9840, 9841, 9842, 9871]))
  | 657 => some (.triangle 12 9825 9872)
  | 658 => some (.leaf 6517)
  | 659 => some (.triangle 15 9873 9874)
  | 660 => some (.triangle 11 9861 9875)
  | 661 => some (.leaf 6518)
  | 662 => some (.triangle 14 9876 9877)
  | 663 => some (.leaf 6519)
  | 664 => some (.triangle 13 9878 9879)
  | 665 => some (.triangle 10 9860 9880)
  | 666 => some (.leaf 6520)
  | 667 => some (.leaf 6521)
  | 668 => some (.leaf 6522)
  | 669 => some (.leaf 6523)
  | 670 => some (.leaf 6524)
  | 671 => some (.leaf 6525)
  | 672 => some (.positive 1 (![9826, 9885, 9886, 9829, 9830, 9887]))
  | 673 => some (.triangle 18 9888 2170)
  | 674 => some (.leaf 6526)
  | 675 => some (.triangle 17 9889 9890)
  | 676 => some (.triangle 16 9891 9869)
  | 677 => some (.leaf 6527)
  | 678 => some (.positive 0 (![9892, 9839, 9840, 9841, 9842, 9893]))
  | 679 => some (.triangle 12 9884 9894)
  | 680 => some (.leaf 6528)
  | 681 => some (.triangle 15 9895 9896)
  | 682 => some (.triangle 11 9883 9897)
  | 683 => some (.leaf 6529)
  | 684 => some (.triangle 14 9898 9899)
  | 685 => some (.triangle 13 9900 9879)
  | 686 => some (.triangle 10 9882 9901)
  | 687 => some (.leaf 6530)
  | 688 => some (.leaf 6531)
  | 689 => some (.leaf 6532)
  | 690 => some (.triangle 10 9904 9905)
  | 691 => some (.leaf 6533)
  | 692 => some (.leaf 6534)
  | 693 => some (.leaf 6535)
  | 694 => some (.leaf 6536)
  | 695 => some (.leaf 6537)
  | 696 => some (.leaf 6538)
  | 697 => some (.leaf 6539)
  | 698 => some (.leaf 6540)
  | 699 => some (.heavy (![9853, 9854, 9855, 9856, 9857, 9858, 9859, 9881, 9902, 9903, 9906, 9907, 9908, 9909, 9910, 9911, 9903, 9912, 9903, 9913, 9914]))
  | 700 => some (.triangle 6 9793 9915)
  | 701 => some (.leaf 6541)
  | 702 => some (.leaf 6542)
  | 703 => some (.leaf 6543)
  | 704 => some (.leaf 6544)
  | 705 => some (.leaf 6545)
  | 706 => some (.leaf 6546)
  | 707 => some (.triangle 18 9921 9922)
  | 708 => some (.triangle 17 9923 2452)
  | 709 => some (.triangle 16 9924 2536)
  | 710 => some (.leaf 6547)
  | 711 => some (.positive 0 (![9795, 9918, 9919, 9920, 9925, 9926]))
  | 712 => some (.triangle 3 9917 9927)
  | 713 => some (.leaf 6548)
  | 714 => some (.leaf 6549)
  | 715 => some (.leaf 6550)
  | 716 => some (.leaf 6551)
  | 717 => some (.leaf 6552)
  | 718 => some (.positive 0 (![9929, 9930, 9931, 9932, 7721, 9933]))
  | 719 => some (.triangle 15 9928 9934)
  | 720 => some (.triangle 2 8604 9935)
  | 721 => some (.triangle 14 9936 9543)
  | 722 => some (.triangle 13 9937 9680)
  | 723 => some (.triangle 1 9208 9938)
  | 724 => some (.triangle 12 9939 9820)
  | 725 => some (.triangle 11 9940 9822)
  | 726 => some (.leaf 6553)
  | 727 => some (.leaf 6554)
  | 728 => some (.leaf 6555)
  | 729 => some (.leaf 6556)
  | 730 => some (.leaf 6557)
  | 731 => some (.leaf 6558)
  | 732 => some (.positive 0 (![9943, 9944, 9945, 9946, 9759, 9947]))
  | 733 => some (.triangle 3 9942 9948)
  | 734 => some (.leaf 6559)
  | 735 => some (.leaf 6560)
  | 736 => some (.leaf 6561)
  | 737 => some (.leaf 6562)
  | 738 => some (.positive 0 (![9950, 9951, 9952, 9841, 9842, 9953]))
  | 739 => some (.triangle 12 9949 9954)
  | 740 => some (.leaf 6563)
  | 741 => some (.leaf 6564)
  | 742 => some (.triangle 18 9956 9957)
  | 743 => some (.leaf 6565)
  | 744 => some (.triangle 17 9958 9959)
  | 745 => some (.leaf 6566)
  | 746 => some (.triangle 16 9960 9961)
  | 747 => some (.leaf 6567)
  | 748 => some (.leaf 6568)
  | 749 => some (.leaf 6569)
  | 750 => some (.leaf 6570)
  | 751 => some (.leaf 6571)
  | 752 => some (.positive 0 (![9962, 9963, 9964, 9965, 9966, 9967]))
  | 753 => some (.triangle 15 9955 9968)
  | 754 => some (.triangle 11 9824 9969)
  | 755 => some (.leaf 6572)
  | 756 => some (.triangle 14 9970 9971)
  | 757 => some (.leaf 6573)
  | 758 => some (.triangle 13 9972 9973)
  | 759 => some (.triangle 10 9941 9974)
  | 760 => some (.leaf 6574)
  | 761 => some (.leaf 6575)
  | 762 => some (.leaf 6576)
  | 763 => some (.leaf 6577)
  | 764 => some (.leaf 6578)
  | 765 => some (.leaf 6579)
  | 766 => some (.leaf 6580)
  | 767 => some (.positive 0 (![9943, 9944, 9945, 9946, 9759, 9982]))
  | 768 => some (.triangle 3 9942 9983)
  | 769 => some (.leaf 6581)
  | 770 => some (.positive 0 (![9950, 9951, 9952, 9841, 9842, 9985]))
  | 771 => some (.triangle 12 9984 9986)
  | 772 => some (.leaf 6582)
  | 773 => some (.triangle 17 9958 9988)
  | 774 => some (.leaf 6583)
  | 775 => some (.triangle 16 9989 9990)
  | 776 => some (.leaf 6584)
  | 777 => some (.positive 0 (![9991, 9963, 9964, 9965, 9966, 9992]))
  | 778 => some (.triangle 15 9987 9993)
  | 779 => some (.triangle 11 9824 9994)
  | 780 => some (.leaf 6585)
  | 781 => some (.triangle 14 9995 9996)
  | 782 => some (.leaf 6586)
  | 783 => some (.triangle 13 9997 9998)
  | 784 => some (.triangle 10 9981 9999)
  | 785 => some (.leaf 6587)
  | 786 => some (.leaf 6588)
  | 787 => some (.leaf 6589)
  | 788 => some (.triangle 18 10003 9957)
  | 789 => some (.leaf 6590)
  | 790 => some (.triangle 17 10004 10005)
  | 791 => some (.triangle 16 10006 2536)
  | 792 => some (.leaf 6591)
  | 793 => some (.positive 0 (![10007, 9963, 9964, 9965, 9966, 10008]))
  | 794 => some (.triangle 15 10002 10009)
  | 795 => some (.triangle 11 9824 10010)
  | 796 => some (.leaf 6592)
  | 797 => some (.triangle 14 10011 10012)
  | 798 => some (.leaf 6593)
  | 799 => some (.triangle 13 10013 10014)
  | 800 => some (.triangle 10 10001 10015)
  | 801 => some (.leaf 6594)
  | 802 => some (.leaf 6595)
  | 803 => some (.leaf 6596)
  | 804 => some (.leaf 6597)
  | 805 => some (.triangle 10 10019 10020)
  | 806 => some (.leaf 6598)
  | 807 => some (.leaf 6599)
  | 808 => some (.leaf 6600)
  | 809 => some (.leaf 6601)
  | 810 => some (.leaf 6602)
  | 811 => some (.leaf 6603)
  | 812 => some (.leaf 6604)
  | 813 => some (.leaf 6605)
  | 814 => some (.leaf 6606)
  | 815 => some (.leaf 6607)
  | 816 => some (.heavy (![9975, 9976, 9977, 9978, 9979, 9980, 10000, 10016, 10017, 10018, 10021, 10022, 10023, 10024, 10025, 10026, 10027, 10028, 10029, 10030, 10031]))
  | 817 => some (.triangle 9 9916 10032)
  | 818 => some (.triangle 5 9664 10033)
  | 819 => some (.leaf 6608)
  | 820 => some (.leaf 6609)
  | 821 => some (.leaf 6610)
  | 822 => some (.leaf 6611)
  | 823 => some (.leaf 6612)
  | 824 => some (.leaf 6613)
  | 825 => some (.triangle 17 10039 10040)
  | 826 => some (.leaf 6614)
  | 827 => some (.leaf 6615)
  | 828 => some (.positive 0 (![10036, 10037, 10038, 10041, 10042, 10043]))
  | 829 => some (.triangle 3 10035 10044)
  | 830 => some (.leaf 6616)
  | 831 => some (.leaf 6617)
  | 832 => some (.leaf 6618)
  | 833 => some (.leaf 6619)
  | 834 => some (.leaf 6620)
  | 835 => some (.leaf 6621)
  | 836 => some (.positive 0 (![10046, 10047, 10048, 10049, 10050, 10051]))
  | 837 => some (.triangle 14 10045 10052)
  | 838 => some (.triangle 1 9208 10053)
  | 839 => some (.triangle 12 10054 9546)
  | 840 => some (.leaf 6622)
  | 841 => some (.leaf 6623)
  | 842 => some (.leaf 6624)
  | 843 => some (.leaf 6625)
  | 844 => some (.leaf 6626)
  | 845 => some (.positive 0 (![10056, 10057, 10058, 9327, 10059, 10060]))
  | 846 => some (.triangle 3 10035 10061)
  | 847 => some (.leaf 6627)
  | 848 => some (.leaf 6628)
  | 849 => some (.leaf 6629)
  | 850 => some (.leaf 6630)
  | 851 => some (.positive 0 (![10063, 10064, 9559, 9560, 10065, 10066]))
  | 852 => some (.triangle 12 10062 10067)
  | 853 => some (.leaf 6631)
  | 854 => some (.leaf 6632)
  | 855 => some (.triangle 17 10069 10070)
  | 856 => some (.leaf 6633)
  | 857 => some (.leaf 6634)
  | 858 => some (.leaf 6635)
  | 859 => some (.leaf 6636)
  | 860 => some (.leaf 6637)
  | 861 => some (.positive 0 (![10071, 10072, 10073, 10074, 10075, 10076]))
  | 862 => some (.triangle 14 10068 10077)
  | 863 => some (.triangle 10 10055 10078)
  | 864 => some (.leaf 6638)
  | 865 => some (.leaf 6639)
  | 866 => some (.leaf 6640)
  | 867 => some (.leaf 6641)
  | 868 => some (.leaf 6642)
  | 869 => some (.leaf 6643)
  | 870 => some (.leaf 6644)
  | 871 => some (.leaf 6645)
  | 872 => some (.leaf 6646)
  | 873 => some (.leaf 6647)
  | 874 => some (.triangle 10 10088 10089)
  | 875 => some (.leaf 6648)
  | 876 => some (.leaf 6649)
  | 877 => some (.triangle 10 10091 10092)
  | 878 => some (.leaf 6650)
  | 879 => some (.leaf 6651)
  | 880 => some (.leaf 6652)
  | 881 => some (.leaf 6653)
  | 882 => some (.leaf 6654)
  | 883 => some (.leaf 6655)
  | 884 => some (.leaf 6656)
  | 885 => some (.leaf 6657)
  | 886 => some (.leaf 6658)
  | 887 => some (.leaf 6659)
  | 888 => some (.heavy (![10079, 10080, 10081, 10082, 10083, 10084, 10085, 10086, 10087, 10090, 10093, 10094, 10095, 10096, 10097, 10098, 10099, 10100, 10101, 10102, 10103]))
  | 889 => some (.leaf 6660)
  | 890 => some (.leaf 6661)
  | 891 => some (.leaf 6662)
  | 892 => some (.leaf 6663)
  | 893 => some (.leaf 6664)
  | 894 => some (.leaf 6665)
  | 895 => some (.triangle 17 10039 10110)
  | 896 => some (.leaf 6666)
  | 897 => some (.positive 0 (![10106, 10107, 10108, 10109, 10111, 10112]))
  | 898 => some (.triangle 3 10105 10113)
  | 899 => some (.leaf 6667)
  | 900 => some (.leaf 6668)
  | 901 => some (.leaf 6669)
  | 902 => some (.leaf 6670)
  | 903 => some (.leaf 6671)
  | 904 => some (.positive 0 (![10115, 10116, 10117, 7720, 10118, 10119]))
  | 905 => some (.triangle 15 10114 10120)
  | 906 => some (.leaf 6672)
  | 907 => some (.leaf 6673)
  | 908 => some (.leaf 6674)
  | 909 => some (.leaf 6675)
  | 910 => some (.positive 0 (![10122, 10123, 10124, 7877, 7878, 10125]))
  | 911 => some (.triangle 14 10121 10126)
  | 912 => some (.leaf 6676)
  | 913 => some (.triangle 13 10127 10128)
  | 914 => some (.triangle 12 10129 9546)
  | 915 => some (.triangle 11 10130 9371)
  | 916 => some (.leaf 6677)
  | 917 => some (.leaf 6678)
  | 918 => some (.leaf 6679)
  | 919 => some (.leaf 6680)
  | 920 => some (.leaf 6681)
  | 921 => some (.leaf 6682)
  | 922 => some (.leaf 6683)
  | 923 => some (.positive 0 (![10133, 10134, 10135, 10136, 10137, 10138]))
  | 924 => some (.triangle 3 10132 10139)
  | 925 => some (.leaf 6684)
  | 926 => some (.leaf 6685)
  | 927 => some (.leaf 6686)
  | 928 => some (.leaf 6687)
  | 929 => some (.leaf 6688)
  | 930 => some (.positive 0 (![10141, 10142, 10143, 9491, 10144, 10145]))
  | 931 => some (.triangle 15 10140 10146)
  | 932 => some (.leaf 6689)
  | 933 => some (.leaf 6690)
  | 934 => some (.leaf 6691)
  | 935 => some (.positive 0 (![10148, 10149, 9629, 9630, 9631, 10150]))
  | 936 => some (.triangle 12 10147 10151)
  | 937 => some (.triangle 11 10152 6780)
  | 938 => some (.leaf 6692)
  | 939 => some (.leaf 6693)
  | 940 => some (.triangle 17 10154 10155)
  | 941 => some (.leaf 6694)
  | 942 => some (.leaf 6695)
  | 943 => some (.leaf 6696)
  | 944 => some (.leaf 6697)
  | 945 => some (.leaf 6698)
  | 946 => some (.positive 0 (![10156, 10157, 10158, 10159, 10160, 10161]))
  | 947 => some (.triangle 11 10162 6780)
  | 948 => some (.triangle 14 10153 10163)
  | 949 => some (.leaf 6699)
  | 950 => some (.triangle 13 10164 10165)
  | 951 => some (.triangle 10 10131 10166)
  | 952 => some (.leaf 6700)
  | 953 => some (.leaf 6701)
  | 954 => some (.leaf 6702)
  | 955 => some (.leaf 6703)
  | 956 => some (.leaf 6704)
  | 957 => some (.leaf 6705)
  | 958 => some (.leaf 6706)
  | 959 => some (.leaf 6707)
  | 960 => some (.leaf 6708)
  | 961 => some (.leaf 6709)
  | 962 => some (.leaf 6710)
  | 963 => some (.triangle 10 10177 10178)
  | 964 => some (.leaf 6711)
  | 965 => some (.leaf 6712)
  | 966 => some (.leaf 6713)
  | 967 => some (.leaf 6714)
  | 968 => some (.leaf 6715)
  | 969 => some (.leaf 6716)
  | 970 => some (.leaf 6717)
  | 971 => some (.leaf 6718)
  | 972 => some (.leaf 6719)
  | 973 => some (.leaf 6720)
  | 974 => some (.heavy (![10167, 10168, 10169, 10170, 10171, 10172, 10173, 10174, 10175, 10176, 10179, 10180, 10181, 10182, 10183, 10184, 10185, 10186, 10187, 10188, 10189]))
  | 975 => some (.triangle 2 10104 10190)
  | 976 => some (.leaf 6721)
  | 977 => some (.leaf 6722)
  | 978 => some (.triangle 17 10039 10193)
  | 979 => some (.leaf 6723)
  | 980 => some (.triangle 16 10194 10195)
  | 981 => some (.leaf 6724)
  | 982 => some (.positive 0 (![10106, 7856, 7857, 7858, 10196, 10197]))
  | 983 => some (.triangle 3 10192 10198)
  | 984 => some (.leaf 6725)
  | 985 => some (.leaf 6726)
  | 986 => some (.leaf 6727)
  | 987 => some (.positive 0 (![10115, 10200, 10201, 9932, 7869, 10202]))
  | 988 => some (.triangle 15 10199 10203)
  | 989 => some (.triangle 2 8604 10204)
  | 990 => some (.leaf 6728)
  | 991 => some (.leaf 6729)
  | 992 => some (.leaf 6730)
  | 993 => some (.leaf 6731)
  | 994 => some (.leaf 6732)
  | 995 => some (.leaf 6733)
  | 996 => some (.positive 0 (![10207, 10208, 10209, 10210, 7878, 10211]))
  | 997 => some (.triangle 2 10206 10212)
  | 998 => some (.triangle 14 10205 10213)
  | 999 => some (.triangle 13 10214 9680)
  | 1000 => some (.triangle 1 9208 10215)
  | 1001 => some (.triangle 12 10216 9820)
  | 1002 => some (.triangle 11 10217 9822)
  | 1003 => some (.leaf 6734)
  | 1004 => some (.leaf 6735)
  | 1005 => some (.leaf 6736)
  | 1006 => some (.leaf 6737)
  | 1007 => some (.leaf 6738)
  | 1008 => some (.leaf 6739)
  | 1009 => some (.positive 0 (![10220, 10221, 10222, 10223, 9759, 10224]))
  | 1010 => some (.triangle 3 10219 10225)
  | 1011 => some (.leaf 6740)
  | 1012 => some (.leaf 6741)
  | 1013 => some (.leaf 6742)
  | 1014 => some (.leaf 6743)
  | 1015 => some (.positive 0 (![10227, 10228, 10229, 9841, 9842, 10230]))
  | 1016 => some (.triangle 12 10226 10231)
  | 1017 => some (.leaf 6744)
  | 1018 => some (.leaf 6745)
  | 1019 => some (.leaf 6746)
  | 1020 => some (.leaf 6747)
  | 1021 => some (.leaf 6748)
  | 1022 => some (.positive 0 (![10233, 10234, 9964, 10235, 10236, 10237]))
  | 1023 => some (.triangle 15 10232 10238)
  | 1024 => some (.triangle 11 9824 10239)
  | 1025 => some (.leaf 6749)
  | 1026 => some (.leaf 6750)
  | 1027 => some (.leaf 6751)
  | 1028 => some (.triangle 17 10242 10243)
  | 1029 => some (.leaf 6752)
  | 1030 => some (.triangle 16 10244 10245)
  | 1031 => some (.leaf 6753)
  | 1032 => some (.leaf 6754)
  | 1033 => some (.leaf 6755)
  | 1034 => some (.leaf 6756)
  | 1035 => some (.leaf 6757)
  | 1036 => some (.positive 0 (![10246, 10247, 10248, 10249, 10250, 10251]))
  | 1037 => some (.triangle 11 10241 10252)
  | 1038 => some (.triangle 14 10240 10253)
  | 1039 => some (.leaf 6758)
  | 1040 => some (.triangle 13 10254 10255)
  | 1041 => some (.triangle 10 10218 10256)
  | 1042 => some (.leaf 6759)
  | 1043 => some (.leaf 6760)
  | 1044 => some (.leaf 6761)
  | 1045 => some (.leaf 6762)
  | 1046 => some (.leaf 6763)
  | 1047 => some (.leaf 6764)
  | 1048 => some (.leaf 6765)
  | 1049 => some (.leaf 6766)
  | 1050 => some (.leaf 6767)
  | 1051 => some (.leaf 6768)
  | 1052 => some (.leaf 6769)
  | 1053 => some (.triangle 10 10267 10268)
  | 1054 => some (.leaf 6770)
  | 1055 => some (.leaf 6771)
  | 1056 => some (.leaf 6772)
  | 1057 => some (.leaf 6773)
  | 1058 => some (.leaf 6774)
  | 1059 => some (.leaf 6775)
  | 1060 => some (.leaf 6776)
  | 1061 => some (.leaf 6777)
  | 1062 => some (.leaf 6778)
  | 1063 => some (.leaf 6779)
  | 1064 => some (.heavy (![10257, 10258, 10259, 10260, 10261, 10262, 10263, 10264, 10265, 10266, 10269, 10270, 10271, 10272, 10273, 10274, 10275, 10276, 10277, 10278, 10279]))
  | 1065 => some (.triangle 5 10191 10280)
  | 1066 => some (.triangle 8 10034 10281)
  | 1067 => some (.leaf 6780)
  | 1068 => some (.leaf 6781)
  | 1069 => some (.leaf 6782)
  | 1070 => some (.triangle 16 10284 10285)
  | 1071 => some (.leaf 6783)
  | 1072 => some (.leaf 6784)
  | 1073 => some (.positive 0 (![7919, 7920, 7921, 10286, 10287, 10288]))
  | 1074 => some (.triangle 2 10283 10289)
  | 1075 => some (.leaf 6785)
  | 1076 => some (.leaf 6786)
  | 1077 => some (.leaf 6787)
  | 1078 => some (.leaf 6788)
  | 1079 => some (.leaf 6789)
  | 1080 => some (.leaf 6790)
  | 1081 => some (.positive 0 (![10291, 10292, 10293, 10294, 10295, 10296]))
  | 1082 => some (.triangle 13 10290 10297)
  | 1083 => some (.triangle 1 9208 10298)
  | 1084 => some (.triangle 11 10299 9683)
  | 1085 => some (.leaf 6791)
  | 1086 => some (.leaf 6792)
  | 1087 => some (.leaf 6793)
  | 1088 => some (.leaf 6794)
  | 1089 => some (.leaf 6795)
  | 1090 => some (.positive 0 (![10301, 10302, 10303, 9375, 10304, 10305]))
  | 1091 => some (.triangle 2 10283 10306)
  | 1092 => some (.leaf 6796)
  | 1093 => some (.leaf 6797)
  | 1094 => some (.leaf 6798)
  | 1095 => some (.leaf 6799)
  | 1096 => some (.leaf 6800)
  | 1097 => some (.positive 0 (![10308, 10309, 10310, 9697, 10311, 10312]))
  | 1098 => some (.triangle 11 10307 10313)
  | 1099 => some (.leaf 6801)
  | 1100 => some (.leaf 6802)
  | 1101 => some (.triangle 16 10315 10316)
  | 1102 => some (.leaf 6803)
  | 1103 => some (.leaf 6804)
  | 1104 => some (.leaf 6805)
  | 1105 => some (.leaf 6806)
  | 1106 => some (.leaf 6807)
  | 1107 => some (.positive 0 (![10317, 10318, 10319, 10320, 10321, 10322]))
  | 1108 => some (.triangle 13 10314 10323)
  | 1109 => some (.triangle 10 10300 10324)
  | 1110 => some (.leaf 6808)
  | 1111 => some (.leaf 6809)
  | 1112 => some (.leaf 6810)
  | 1113 => some (.leaf 6811)
  | 1114 => some (.leaf 6812)
  | 1115 => some (.leaf 6813)
  | 1116 => some (.leaf 6814)
  | 1117 => some (.leaf 6815)
  | 1118 => some (.leaf 6816)
  | 1119 => some (.leaf 6817)
  | 1120 => some (.triangle 10 10334 10335)
  | 1121 => some (.leaf 6818)
  | 1122 => some (.leaf 6819)
  | 1123 => some (.triangle 10 10337 10338)
  | 1124 => some (.leaf 6820)
  | 1125 => some (.leaf 6821)
  | 1126 => some (.leaf 6822)
  | 1127 => some (.leaf 6823)
  | 1128 => some (.leaf 6824)
  | 1129 => some (.leaf 6825)
  | 1130 => some (.leaf 6826)
  | 1131 => some (.leaf 6827)
  | 1132 => some (.leaf 6828)
  | 1133 => some (.leaf 6829)
  | 1134 => some (.heavy (![10325, 10326, 10327, 10328, 10329, 10330, 10331, 10332, 10333, 10336, 10339, 10340, 10341, 10342, 10343, 10344, 10345, 10346, 10347, 10348, 10349]))
  | 1135 => some (.leaf 6830)
  | 1136 => some (.leaf 6831)
  | 1137 => some (.triangle 16 10351 10352)
  | 1138 => some (.leaf 6832)
  | 1139 => some (.positive 0 (![7968, 7969, 7970, 7568, 10353, 10354]))
  | 1140 => some (.leaf 6833)
  | 1141 => some (.triangle 15 10355 10356)
  | 1142 => some (.triangle 14 10357 5899)
  | 1143 => some (.leaf 6834)
  | 1144 => some (.leaf 6835)
  | 1145 => some (.leaf 6836)
  | 1146 => some (.leaf 6837)
  | 1147 => some (.positive 0 (![10359, 10360, 10361, 7982, 7983, 10362]))
  | 1148 => some (.leaf 6838)
  | 1149 => some (.triangle 14 10363 10364)
  | 1150 => some (.leaf 6839)
  | 1151 => some (.triangle 15 10365 10366)
  | 1152 => some (.triangle 13 10358 10367)
  | 1153 => some (.triangle 12 10368 9315)
  | 1154 => some (.triangle 11 10369 9683)
  | 1155 => some (.leaf 6840)
  | 1156 => some (.leaf 6841)
  | 1157 => some (.leaf 6842)
  | 1158 => some (.leaf 6843)
  | 1159 => some (.positive 0 (![10371, 10372, 10373, 9424, 10137, 10374]))
  | 1160 => some (.triangle 15 10375 10356)
  | 1161 => some (.leaf 6844)
  | 1162 => some (.triangle 12 10376 10377)
  | 1163 => some (.leaf 6845)
  | 1164 => some (.leaf 6846)
  | 1165 => some (.leaf 6847)
  | 1166 => some (.positive 0 (![10379, 10380, 9757, 9758, 9759, 10381]))
  | 1167 => some (.triangle 12 10382 6528)
  | 1168 => some (.triangle 15 10383 10356)
  | 1169 => some (.triangle 11 10378 10384)
  | 1170 => some (.triangle 14 10385 5899)
  | 1171 => some (.leaf 6848)
  | 1172 => some (.leaf 6849)
  | 1173 => some (.triangle 16 10387 10388)
  | 1174 => some (.leaf 6850)
  | 1175 => some (.leaf 6851)
  | 1176 => some (.leaf 6852)
  | 1177 => some (.leaf 6853)
  | 1178 => some (.leaf 6854)
  | 1179 => some (.positive 0 (![10389, 10390, 10391, 10392, 10393, 10394]))
  | 1180 => some (.triangle 12 10395 6528)
  | 1181 => some (.leaf 6855)
  | 1182 => some (.triangle 14 10396 10397)
  | 1183 => some (.leaf 6856)
  | 1184 => some (.triangle 15 10398 10399)
  | 1185 => some (.triangle 13 10386 10400)
  | 1186 => some (.triangle 10 10370 10401)
  | 1187 => some (.leaf 6857)
  | 1188 => some (.leaf 6858)
  | 1189 => some (.leaf 6859)
  | 1190 => some (.leaf 6860)
  | 1191 => some (.leaf 6861)
  | 1192 => some (.leaf 6862)
  | 1193 => some (.leaf 6863)
  | 1194 => some (.leaf 6864)
  | 1195 => some (.leaf 6865)
  | 1196 => some (.leaf 6866)
  | 1197 => some (.leaf 6867)
  | 1198 => some (.triangle 10 10412 10413)
  | 1199 => some (.leaf 6868)
  | 1200 => some (.leaf 6869)
  | 1201 => some (.leaf 6870)
  | 1202 => some (.leaf 6871)
  | 1203 => some (.leaf 6872)
  | 1204 => some (.leaf 6873)
  | 1205 => some (.leaf 6874)
  | 1206 => some (.leaf 6875)
  | 1207 => some (.leaf 6876)
  | 1208 => some (.leaf 6877)
  | 1209 => some (.heavy (![10402, 10403, 10404, 10405, 10406, 10407, 10408, 10409, 10410, 10411, 10414, 10415, 10416, 10417, 10418, 10419, 10420, 10421, 10422, 10423, 10424]))
  | 1210 => some (.triangle 3 10350 10425)
  | 1211 => some (.leaf 6878)
  | 1212 => some (.leaf 6879)
  | 1213 => some (.leaf 6880)
  | 1214 => some (.triangle 16 10428 10429)
  | 1215 => some (.leaf 6881)
  | 1216 => some (.positive 0 (![7968, 7969, 7970, 9798, 10430, 10431]))
  | 1217 => some (.triangle 3 9794 10432)
  | 1218 => some (.leaf 6882)
  | 1219 => some (.triangle 15 10433 10434)
  | 1220 => some (.triangle 2 10427 10435)
  | 1221 => some (.triangle 14 10436 5899)
  | 1222 => some (.leaf 6883)
  | 1223 => some (.leaf 6884)
  | 1224 => some (.leaf 6885)
  | 1225 => some (.leaf 6886)
  | 1226 => some (.leaf 6887)
  | 1227 => some (.leaf 6888)
  | 1228 => some (.positive 0 (![10439, 10440, 10441, 10442, 7983, 10443]))
  | 1229 => some (.triangle 3 10438 10444)
  | 1230 => some (.triangle 14 10445 9543)
  | 1231 => some (.leaf 6889)
  | 1232 => some (.triangle 15 10446 10447)
  | 1233 => some (.triangle 13 10437 10448)
  | 1234 => some (.triangle 1 9208 10449)
  | 1235 => some (.triangle 12 10450 9820)
  | 1236 => some (.triangle 11 10451 9822)
  | 1237 => some (.leaf 6890)
  | 1238 => some (.leaf 6891)
  | 1239 => some (.leaf 6892)
  | 1240 => some (.leaf 6893)
  | 1241 => some (.leaf 6894)
  | 1242 => some (.leaf 6895)
  | 1243 => some (.positive 0 (![10454, 10455, 10456, 10457, 9631, 10458]))
  | 1244 => some (.triangle 2 10453 10459)
  | 1245 => some (.triangle 12 9825 10460)
  | 1246 => some (.leaf 6896)
  | 1247 => some (.leaf 6897)
  | 1248 => some (.leaf 6898)
  | 1249 => some (.positive 0 (![10462, 10463, 9840, 9841, 9842, 10464]))
  | 1250 => some (.triangle 12 9825 10465)
  | 1251 => some (.leaf 6899)
  | 1252 => some (.triangle 15 10466 10467)
  | 1253 => some (.triangle 11 10461 10468)
  | 1254 => some (.triangle 14 10469 5899)
  | 1255 => some (.leaf 6900)
  | 1256 => some (.leaf 6901)
  | 1257 => some (.leaf 6902)
  | 1258 => some (.triangle 16 10472 10473)
  | 1259 => some (.leaf 6903)
  | 1260 => some (.leaf 6904)
  | 1261 => some (.leaf 6905)
  | 1262 => some (.leaf 6906)
  | 1263 => some (.leaf 6907)
  | 1264 => some (.positive 0 (![10474, 10475, 10476, 10477, 10478, 10479]))
  | 1265 => some (.triangle 12 10471 10480)
  | 1266 => some (.leaf 6908)
  | 1267 => some (.triangle 14 10481 10482)
  | 1268 => some (.leaf 6909)
  | 1269 => some (.triangle 15 10483 10484)
  | 1270 => some (.triangle 13 10470 10485)
  | 1271 => some (.triangle 10 10452 10486)
  | 1272 => some (.leaf 6910)
  | 1273 => some (.leaf 6911)
  | 1274 => some (.leaf 6912)
  | 1275 => some (.leaf 6913)
  | 1276 => some (.leaf 6914)
  | 1277 => some (.leaf 6915)
  | 1278 => some (.leaf 6916)
  | 1279 => some (.leaf 6917)
  | 1280 => some (.leaf 6918)
  | 1281 => some (.leaf 6919)
  | 1282 => some (.leaf 6920)
  | 1283 => some (.triangle 10 10497 10498)
  | 1284 => some (.leaf 6921)
  | 1285 => some (.leaf 6922)
  | 1286 => some (.leaf 6923)
  | 1287 => some (.leaf 6924)
  | 1288 => some (.leaf 6925)
  | 1289 => some (.leaf 6926)
  | 1290 => some (.leaf 6927)
  | 1291 => some (.leaf 6928)
  | 1292 => some (.leaf 6929)
  | 1293 => some (.leaf 6930)
  | 1294 => some (.heavy (![10487, 10488, 10489, 10490, 10491, 10492, 10493, 10494, 10495, 10496, 10499, 10500, 10501, 10502, 10503, 10504, 10505, 10506, 10507, 10508, 10509]))
  | 1295 => some (.triangle 6 10426 10510)
  | 1296 => some (.leaf 6931)
  | 1297 => some (.leaf 6932)
  | 1298 => some (.leaf 6933)
  | 1299 => some (.leaf 6934)
  | 1300 => some (.leaf 6935)
  | 1301 => some (.leaf 6936)
  | 1302 => some (.triangle 16 10517 10429)
  | 1303 => some (.leaf 6937)
  | 1304 => some (.positive 0 (![10513, 10514, 10515, 10516, 10518, 10519]))
  | 1305 => some (.triangle 3 10512 10520)
  | 1306 => some (.leaf 6938)
  | 1307 => some (.triangle 15 10521 10522)
  | 1308 => some (.triangle 2 10283 10523)
  | 1309 => some (.leaf 6939)
  | 1310 => some (.triangle 14 10524 10525)
  | 1311 => some (.leaf 6940)
  | 1312 => some (.leaf 6941)
  | 1313 => some (.leaf 6942)
  | 1314 => some (.leaf 6943)
  | 1315 => some (.leaf 6944)
  | 1316 => some (.leaf 6945)
  | 1317 => some (.positive 0 (![10528, 10529, 10530, 10531, 8044, 10532]))
  | 1318 => some (.triangle 14 10527 10533)
  | 1319 => some (.leaf 6946)
  | 1320 => some (.triangle 15 10534 10535)
  | 1321 => some (.triangle 13 10526 10536)
  | 1322 => some (.triangle 1 9208 10537)
  | 1323 => some (.triangle 12 10538 9820)
  | 1324 => some (.triangle 11 10539 9822)
  | 1325 => some (.leaf 6947)
  | 1326 => some (.leaf 6948)
  | 1327 => some (.leaf 6949)
  | 1328 => some (.leaf 6950)
  | 1329 => some (.leaf 6951)
  | 1330 => some (.leaf 6952)
  | 1331 => some (.positive 0 (![10542, 10543, 10544, 10545, 9425, 10546]))
  | 1332 => some (.triangle 3 10541 10547)
  | 1333 => some (.leaf 6953)
  | 1334 => some (.triangle 15 10548 10549)
  | 1335 => some (.triangle 2 10283 10550)
  | 1336 => some (.leaf 6954)
  | 1337 => some (.leaf 6955)
  | 1338 => some (.leaf 6956)
  | 1339 => some (.leaf 6957)
  | 1340 => some (.leaf 6958)
  | 1341 => some (.leaf 6959)
  | 1342 => some (.positive 0 (![10553, 10554, 10555, 10556, 9631, 10557]))
  | 1343 => some (.triangle 2 10552 10558)
  | 1344 => some (.triangle 12 10551 10559)
  | 1345 => some (.leaf 6960)
  | 1346 => some (.leaf 6961)
  | 1347 => some (.leaf 6962)
  | 1348 => some (.leaf 6963)
  | 1349 => some (.leaf 6964)
  | 1350 => some (.leaf 6965)
  | 1351 => some (.positive 0 (![10562, 10563, 10564, 10565, 9759, 10566]))
  | 1352 => some (.triangle 3 10561 10567)
  | 1353 => some (.leaf 6966)
  | 1354 => some (.leaf 6967)
  | 1355 => some (.leaf 6968)
  | 1356 => some (.leaf 6969)
  | 1357 => some (.positive 0 (![10569, 10570, 10571, 9841, 9842, 10572]))
  | 1358 => some (.triangle 12 10568 10573)
  | 1359 => some (.triangle 15 10574 8035)
  | 1360 => some (.triangle 11 10560 10575)
  | 1361 => some (.triangle 14 10576 10525)
  | 1362 => some (.leaf 6970)
  | 1363 => some (.triangle 16 10578 10473)
  | 1364 => some (.leaf 6971)
  | 1365 => some (.leaf 6972)
  | 1366 => some (.leaf 6973)
  | 1367 => some (.leaf 6974)
  | 1368 => some (.leaf 6975)
  | 1369 => some (.positive 0 (![10579, 10580, 10581, 10582, 10583, 10584]))
  | 1370 => some (.triangle 14 10527 10585)
  | 1371 => some (.leaf 6976)
  | 1372 => some (.triangle 15 10586 10587)
  | 1373 => some (.triangle 13 10577 10588)
  | 1374 => some (.triangle 10 10540 10589)
  | 1375 => some (.leaf 6977)
  | 1376 => some (.leaf 6978)
  | 1377 => some (.leaf 6979)
  | 1378 => some (.leaf 6980)
  | 1379 => some (.leaf 6981)
  | 1380 => some (.leaf 6982)
  | 1381 => some (.leaf 6983)
  | 1382 => some (.positive 0 (![10528, 10529, 10530, 10531, 8044, 10597]))
  | 1383 => some (.triangle 14 10527 10598)
  | 1384 => some (.leaf 6984)
  | 1385 => some (.triangle 15 10599 10600)
  | 1386 => some (.triangle 13 10596 10601)
  | 1387 => some (.triangle 1 9208 10602)
  | 1388 => some (.triangle 12 10603 9820)
  | 1389 => some (.triangle 11 10604 9822)
  | 1390 => some (.leaf 6985)
  | 1391 => some (.leaf 6986)
  | 1392 => some (.triangle 16 10607 10473)
  | 1393 => some (.leaf 6987)
  | 1394 => some (.positive 0 (![10608, 10580, 10581, 10582, 10583, 10609]))
  | 1395 => some (.triangle 14 10527 10610)
  | 1396 => some (.leaf 6988)
  | 1397 => some (.triangle 15 10611 10612)
  | 1398 => some (.triangle 13 10606 10613)
  | 1399 => some (.triangle 10 10605 10614)
  | 1400 => some (.leaf 6989)
  | 1401 => some (.leaf 6990)
  | 1402 => some (.leaf 6991)
  | 1403 => some (.positive 0 (![10528, 10529, 10530, 10531, 8044, 10618]))
  | 1404 => some (.triangle 14 10617 10619)
  | 1405 => some (.leaf 6992)
  | 1406 => some (.triangle 15 10620 10621)
  | 1407 => some (.triangle 13 10616 10622)
  | 1408 => some (.triangle 1 9208 10623)
  | 1409 => some (.triangle 12 10624 9820)
  | 1410 => some (.triangle 11 10625 9822)
  | 1411 => some (.leaf 6993)
  | 1412 => some (.leaf 6994)
  | 1413 => some (.positive 0 (![10579, 10580, 10581, 10582, 10583, 10628]))
  | 1414 => some (.triangle 14 10617 10629)
  | 1415 => some (.leaf 6995)
  | 1416 => some (.triangle 15 10630 10631)
  | 1417 => some (.triangle 13 10627 10632)
  | 1418 => some (.triangle 10 10626 10633)
  | 1419 => some (.leaf 6996)
  | 1420 => some (.leaf 6997)
  | 1421 => some (.leaf 6998)
  | 1422 => some (.leaf 6999)
  | 1423 => some (.triangle 10 10637 10638)
  | 1424 => some (.leaf 7000)
  | 1425 => some (.leaf 7001)
  | 1426 => some (.leaf 7002)
  | 1427 => some (.leaf 7003)
  | 1428 => some (.leaf 7004)
  | 1429 => some (.leaf 7005)
  | 1430 => some (.leaf 7006)
  | 1431 => some (.leaf 7007)
  | 1432 => some (.leaf 7008)
  | 1433 => some (.leaf 7009)
  | 1434 => some (.heavy (![10590, 10591, 10592, 10593, 10594, 10595, 10615, 10634, 10635, 10636, 10639, 10640, 10641, 10642, 10643, 10644, 10645, 10646, 10647, 10648, 10649]))
  | 1435 => some (.triangle 8 10511 10650)
  | 1436 => some (.leaf 7010)
  | 1437 => some (.leaf 7011)
  | 1438 => some (.leaf 7012)
  | 1439 => some (.leaf 7013)
  | 1440 => some (.leaf 7014)
  | 1441 => some (.leaf 7015)
  | 1442 => some (.positive 0 (![10653, 10654, 10655, 10656, 10518, 10657]))
  | 1443 => some (.triangle 3 10652 10658)
  | 1444 => some (.leaf 7016)
  | 1445 => some (.leaf 7017)
  | 1446 => some (.leaf 7018)
  | 1447 => some (.leaf 7019)
  | 1448 => some (.leaf 7020)
  | 1449 => some (.positive 0 (![10660, 10661, 10662, 10663, 7721, 10664]))
  | 1450 => some (.triangle 15 10659 10665)
  | 1451 => some (.triangle 2 10283 10666)
  | 1452 => some (.triangle 14 10667 10525)
  | 1453 => some (.leaf 7021)
  | 1454 => some (.leaf 7022)
  | 1455 => some (.leaf 7023)
  | 1456 => some (.leaf 7024)
  | 1457 => some (.leaf 7025)
  | 1458 => some (.leaf 7026)
  | 1459 => some (.positive 0 (![10670, 10671, 10672, 10673, 7983, 10674]))
  | 1460 => some (.triangle 3 10669 10675)
  | 1461 => some (.leaf 7027)
  | 1462 => some (.leaf 7028)
  | 1463 => some (.leaf 7029)
  | 1464 => some (.leaf 7030)
  | 1465 => some (.positive 0 (![10677, 10678, 10679, 10531, 8044, 10680]))
  | 1466 => some (.triangle 14 10676 10681)
  | 1467 => some (.leaf 7031)
  | 1468 => some (.leaf 7032)
  | 1469 => some (.leaf 7033)
  | 1470 => some (.leaf 7034)
  | 1471 => some (.leaf 7035)
  | 1472 => some (.positive 0 (![10683, 10684, 10685, 10686, 8158, 10687]))
  | 1473 => some (.triangle 15 10682 10688)
  | 1474 => some (.triangle 13 10668 10689)
  | 1475 => some (.triangle 1 9208 10690)
  | 1476 => some (.triangle 12 10691 9820)
  | 1477 => some (.triangle 11 10692 9822)
  | 1478 => some (.leaf 7036)
  | 1479 => some (.leaf 7037)
  | 1480 => some (.leaf 7038)
  | 1481 => some (.leaf 7039)
  | 1482 => some (.leaf 7040)
  | 1483 => some (.leaf 7041)
  | 1484 => some (.positive 0 (![10695, 10696, 10697, 10698, 9492, 10699]))
  | 1485 => some (.triangle 15 10694 10700)
  | 1486 => some (.triangle 2 10283 10701)
  | 1487 => some (.triangle 12 10702 10559)
  | 1488 => some (.leaf 7042)
  | 1489 => some (.leaf 7043)
  | 1490 => some (.leaf 7044)
  | 1491 => some (.leaf 7045)
  | 1492 => some (.leaf 7046)
  | 1493 => some (.leaf 7047)
  | 1494 => some (.positive 0 (![10705, 10706, 10707, 10708, 9759, 10709]))
  | 1495 => some (.triangle 3 10704 10710)
  | 1496 => some (.leaf 7048)
  | 1497 => some (.leaf 7049)
  | 1498 => some (.leaf 7050)
  | 1499 => some (.leaf 7051)
  | 1500 => some (.positive 0 (![10712, 10713, 10714, 9841, 9842, 10715]))
  | 1501 => some (.triangle 12 10711 10716)
  | 1502 => some (.leaf 7052)
  | 1503 => some (.leaf 7053)
  | 1504 => some (.leaf 7054)
  | 1505 => some (.leaf 7055)
  | 1506 => some (.positive 0 (![10718, 10719, 10720, 9965, 9966, 10721]))
  | 1507 => some (.triangle 15 10717 10722)
  | 1508 => some (.triangle 11 10703 10723)
  | 1509 => some (.triangle 14 10724 10525)
  | 1510 => some (.leaf 7056)
  | 1511 => some (.leaf 7057)
  | 1512 => some (.leaf 7058)
  | 1513 => some (.leaf 7059)
  | 1514 => some (.leaf 7060)
  | 1515 => some (.leaf 7061)
  | 1516 => some (.positive 0 (![10727, 10728, 10729, 10730, 10393, 10731]))
  | 1517 => some (.triangle 3 10726 10732)
  | 1518 => some (.leaf 7062)
  | 1519 => some (.leaf 7063)
  | 1520 => some (.leaf 7064)
  | 1521 => some (.leaf 7065)
  | 1522 => some (.positive 0 (![10734, 10735, 10736, 10477, 10478, 10737]))
  | 1523 => some (.triangle 12 10733 10738)
  | 1524 => some (.leaf 7066)
  | 1525 => some (.leaf 7067)
  | 1526 => some (.leaf 7068)
  | 1527 => some (.positive 0 (![10740, 10741, 10581, 10582, 10583, 10742]))
  | 1528 => some (.triangle 14 10739 10743)
  | 1529 => some (.leaf 7069)
  | 1530 => some (.leaf 7070)
  | 1531 => some (.leaf 7071)
  | 1532 => some (.leaf 7072)
  | 1533 => some (.leaf 7073)
  | 1534 => some (.positive 0 (![10579, 10745, 10746, 10747, 10748, 10749]))
  | 1535 => some (.triangle 15 10744 10750)
  | _ => none

end Jsp404.SevenLowerBranchShard06
