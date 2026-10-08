import Jsp000404.SevenLowerReplay

/-! SOURCE_ONLY literal certificate data; no kernel PASS is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerBranchShard05
open SevenLowerReplay
def cycle0000 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 5, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (3), (-1), (-1), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 3 (![2, 3, 5, 4, 0]), .triangle 15 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 7 0, .triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0001 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (-1), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 4 (![2, 3, 5, 4, 0]), .triangle 15 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 7 0, .triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 5, 3, 4, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 8 2, .triangle 6 1]

def cycle0004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 14 2, .gapLower 1 1 (![2, 5, 3, 4, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 2 (![2, 5, 3, 4, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0006 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 3 (![2, 5, 3, 4, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 4 (![2, 5, 3, 4, 0]), .triangle 13 1, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0008 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![2, 5, 3, 4, 0])]

def cycle0009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 4, 1])]

def cycle0010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 5, 3, 4, 1]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 5, 3, 4, 1]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0012 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 5, 3, 4, 1]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0013 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 3, 4, 1])]

def cycle0014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 3, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 4, 1])]

def cycle0015 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 5, 3, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![2, 5, 3, 4, 1]), .triangle 6 1]

def cycle0016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 5, 3, 4, 1]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 5, 3, 4, 1]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0018 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 3, 4, 1])]

def cycle0019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 5, 3, 4, 1])]

def cycle0020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 4, 1]), .gapLower 0 0 (![2, 5, 3, 4, 1]), .gapLower 0 5 (![2, 5, 3, 4, 1])]

def cycle0021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .triangle 6 0, .gapLower 0 0 (![2, 5, 3, 4, 1]), .gapLower 0 5 (![2, 5, 3, 4, 1])]

def cycle0022 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .triangle 5 0, .gapLower 0 0 (![2, 5, 3, 4, 1]), .gapLower 0 5 (![2, 5, 3, 4, 1])]

def cycle0023 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .gapLower 0 0 (![2, 5, 3, 4, 1]), .gapLower 0 5 (![2, 5, 3, 4, 1])]

def cycle0024 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![2, 5, 3, 4, 1]), .gapLower 0 1 (![2, 5, 3, 4, 1])]

def cycle0025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 5, 3, 4, 1]), .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 4, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 5, 3, 4, 1]), .triangle 7 1, .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 4, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 4, 1]), .corridorLower 0 2, .gapLower 0 5 (![2, 5, 3, 4, 1])]

def cycle0028 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 5, 3, 4, 1]), .gapLower 0 2 (![2, 5, 3, 4, 1]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0029 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 5, 3, 4, 1]), .triangle 7 1, .gapLower 0 2 (![2, 5, 3, 4, 1]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0030 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 2 (![2, 5, 3, 4, 1]), .corridorLower 0 5, .gapLower 0 5 (![2, 5, 3, 4, 1])]

def cycle0031 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 5, 3, 4, 1]), .gapLower 0 3 (![2, 5, 3, 4, 1]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0032 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 5, 3, 4, 1]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 5, 3, 4, 1])]

def cycle0033 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 5, 3, 4, 1]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 5, 3, 4, 1])]

def cycle0034 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 0, 5]), .gapLower 1 0 (![2, 3, 4, 0, 5]), .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0035 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 0, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0036 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 2 (![2, 3, 4, 0, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 5 0]

def cycle0038 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 3, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 5 1]

def cycle0039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 4, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 4, 3, 1, 5]), .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 0, 5]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 0, 5]), .triangle 3 0]

def cycle0041 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 2, .gapLower 1 1 (![2, 4, 3, 0, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 2 (![2, 4, 3, 0, 5]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0043 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![2, 4, 3, 0, 5]), .triangle 13 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 0 (![2, 4, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 4, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 4, 3, 0, 5])]

def cycle0045 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![2, 4, 3, 0, 5]), .triangle 3 0]

def cycle0046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .triangle 7 2, .gapLower 0 1 (![2, 4, 3, 1, 5])]

def cycle0047 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![2, 4, 3, 1, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0048 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 4, 3, 1, 5]), .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0049 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 4, 3, 1, 5])]

def cycle0050 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, true, false, true] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 4, 3, 1, 5]), .triangle 3 1]

def cycle0051 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 4, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .triangle 7 2, .gapLower 0 1 (![2, 4, 3, 1, 5])]

def cycle0052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![2, 4, 3, 1, 5]), .triangle 5 1, .gapLower 0 0 (![2, 4, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0053 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 4, 3, 1, 5]), .triangle 4 1, .gapLower 0 0 (![2, 4, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0054 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 4, 3, 1, 5])]

def cycle0055 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 4, 3, 1, 5])]

def cycle0056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 3, 1, 5]), .triangle 3 1]

def cycle0057 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, true, false, true] }
  origin := ![.triangle 1 0, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 4, 3, 1, 5]), .triangle 3 1]

def cycle0058 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![2, 4, 3, 1, 5]), .gapLower 0 1 (![2, 4, 3, 1, 5])]

def cycle0059 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 4, 3, 1, 5]), .triangle 7 2, .gapLower 0 1 (![2, 4, 3, 1, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0060 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 1 (![2, 4, 3, 1, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 4, 3, 1, 5])]

def cycle0061 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 2, .gapLower 0 5 (![2, 4, 3, 1, 5]), .triangle 8 1, .triangle 7 2, .gapLower 0 1 (![2, 4, 3, 1, 5])]

def cycle0062 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 4, 3, 1, 5]), .gapLower 0 2 (![2, 4, 3, 1, 5]), .triangle 5 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0063 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![2, 4, 3, 1, 5]), .triangle 5 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 4, 3, 1, 5])]

def cycle0064 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![2, 4, 3, 1, 5]), .corridorLower 0 4, .gapLower 0 5 (![2, 4, 3, 1, 5]), .triangle 3 1]

def cycle0065 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![2, 4, 3, 1, 5]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 4, 3, 1, 5])]

def cycle0066 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 4, 3, 1, 5]), .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0067 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 3, 1, 5]), .gapLower 0 4 (![2, 4, 3, 1, 5])]

def cycle0068 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .gapLower 1 0 (![2, 3, 4, 5, 0]), .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0069 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0071 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 3, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 5 0]

def cycle0072 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 3, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 5 1]

def cycle0073 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0074 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 3 (![2, 4, 3, 5, 1])]

def cycle0075 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 13 2, .gapLower 1 1 (![2, 4, 3, 5, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0076 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 1 2 (![2, 4, 3, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0077 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 3 (![2, 4, 3, 5, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0078 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 4 (![2, 4, 3, 5, 0]), .triangle 14 1, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0079 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![2, 4, 3, 5, 0])]

def cycle0080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![2, 4, 3, 5, 1]), .gapLower 0 0 (![2, 4, 3, 5, 1]), .gapLower 0 5 (![2, 4, 3, 5, 1])]

def cycle0081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .triangle 7 2, .gapLower 0 1 (![2, 4, 3, 5, 1])]

def cycle0082 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 4, 3, 5, 1]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 4, 3, 5, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0084 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 4, 3, 5, 1]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0085 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 4, 3, 5, 1])]

def cycle0086 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 4, 3, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .triangle 7 2, .gapLower 0 1 (![2, 4, 3, 5, 1])]

def cycle0087 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 3, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![2, 4, 3, 5, 1]), .triangle 5 1]

def cycle0088 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 4, 3, 5, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0089 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 4, 3, 5, 1]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0090 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 3, 5, 1])]

def cycle0091 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 4, 3, 5, 1])]

def cycle0092 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .triangle 6 0, .gapLower 0 0 (![2, 4, 3, 5, 1]), .gapLower 0 5 (![2, 4, 3, 5, 1])]

def cycle0093 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .triangle 5 0, .gapLower 0 0 (![2, 4, 3, 5, 1]), .gapLower 0 5 (![2, 4, 3, 5, 1])]

def cycle0094 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .gapLower 0 0 (![2, 4, 3, 5, 1]), .gapLower 0 5 (![2, 4, 3, 5, 1])]

def cycle0095 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![2, 4, 3, 5, 1]), .gapLower 0 1 (![2, 4, 3, 5, 1])]

def cycle0096 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 4, 3, 5, 1]), .triangle 7 2, .gapLower 0 1 (![2, 4, 3, 5, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0097 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 4, 3, 5, 1]), .triangle 9 1, .gapLower 0 1 (![2, 4, 3, 5, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0098 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 2, .gapLower 0 1 (![2, 4, 3, 5, 1]), .corridorLower 0 2, .gapLower 0 5 (![2, 4, 3, 5, 1])]

def cycle0099 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 4, 3, 5, 1]), .gapLower 0 2 (![2, 4, 3, 5, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0100 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 4, 3, 5, 1]), .triangle 8 1, .gapLower 0 2 (![2, 4, 3, 5, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0101 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 2 (![2, 4, 3, 5, 1]), .corridorLower 0 4, .gapLower 0 5 (![2, 4, 3, 5, 1])]

def cycle0102 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 4, 3, 5, 1]), .gapLower 0 3 (![2, 4, 3, 5, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0103 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 4, 3, 5, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 4, 3, 5, 1])]

def cycle0104 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 4, 3, 5, 1]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 4, 3, 5, 1])]

def cycle0105 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0106 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 10 1, .gapLower 1 0 (![2, 3, 4, 5, 0]), .corridorUpper 0 1]

def cycle0107 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0108 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0109 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0110 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 3, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 5 0]

def cycle0111 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 5 1]

def cycle0112 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0113 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 4]
    constant := ![(0), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 7 1, .triangle 13 2, .triangle 15 0, .triangle 9 0]

def cycle0114 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0115 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 3]
    constant := ![(-1), (-1), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 8 0, .triangle 14 0, .triangle 13 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 2]

def cycle0116 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 14 2, .triangle 15 1, .gapLower 1 1 (![2, 4, 5, 3, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0117 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 14 2, .gapLower 1 2 (![2, 4, 5, 3, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0118 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 3 (![2, 4, 5, 3, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0119 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 1 4 (![2, 4, 5, 3, 0]), .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0120 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0121 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-3), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![2, 4, 5, 3, 1]), .gapLower 0 0 (![2, 4, 5, 3, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0122 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 1 (![2, 4, 5, 3, 1])]

def cycle0123 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 3]
    constant := ![(0), (-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 8 2, .gapLower 0 2 (![2, 4, 5, 3, 1]), .triangle 7 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 2]

def cycle0124 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 0 3]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 3 (![2, 4, 5, 3, 1]), .triangle 8 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 4 2]

def cycle0125 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 4, 5, 3, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0126 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 5, 3, 1])]

def cycle0127 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 3, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 1 (![2, 4, 5, 3, 1])]

def cycle0128 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 2 (![2, 4, 5, 3, 1]), .triangle 7 1, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0129 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 2 (![2, 4, 5, 3, 1]), .triangle 5 1, .triangle 0 1, .gapLower 1 0 (![2, 4, 5, 3, 0]), .corridorUpper 0 1]

def cycle0130 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 2 (![2, 4, 5, 3, 1]), .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 3, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0131 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (-2), (0), (-2), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 2, .triangle 15 0, .gapLower 5 2 (![3, 0, 4, 1, 2]), .gapLower 0 2 (![2, 4, 5, 3, 1]), .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 3, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0132 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.triangle 0 1, .triangle 12 0, .triangle 6 2, .gapLower 0 2 (![2, 4, 5, 3, 1]), .triangle 5 1]

def cycle0133 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![2, 4, 5, 3, 1]), .triangle 9 1, .triangle 7 1, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0134 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![2, 4, 5, 3, 1]), .triangle 8 1, .triangle 14 0, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0135 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![2, 4, 5, 3, 1]), .triangle 9 1, .triangle 5 1, .triangle 0 1, .gapLower 1 0 (![2, 4, 5, 3, 0]), .corridorUpper 0 1]

def cycle0136 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![2, 4, 5, 3, 1]), .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 3, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0137 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-2), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 3, 1]), .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0138 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 4, 5, 3, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0139 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 5, 3, 1])]

def cycle0140 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 4, 5, 3, 1])]

def cycle0141 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .triangle 6 0, .gapLower 0 0 (![2, 4, 5, 3, 1]), .gapLower 0 5 (![2, 4, 5, 3, 1])]

def cycle0142 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .triangle 5 0, .gapLower 0 0 (![2, 4, 5, 3, 1]), .gapLower 0 5 (![2, 4, 5, 3, 1])]

def cycle0143 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .gapLower 0 0 (![2, 4, 5, 3, 1]), .gapLower 0 5 (![2, 4, 5, 3, 1])]

def cycle0144 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 2 (![2, 4, 5, 3, 1]), .gapLower 0 1 (![2, 4, 5, 3, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0145 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![2, 4, 5, 3, 1]), .triangle 9 1, .gapLower 0 1 (![2, 4, 5, 3, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0146 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 4, 5, 3, 1]), .triangle 8 2, .triangle 9 1, .gapLower 0 1 (![2, 4, 5, 3, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0147 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .triangle 9 1, .gapLower 0 1 (![2, 4, 5, 3, 1]), .corridorLower 0 2, .gapLower 0 5 (![2, 4, 5, 3, 1])]

def cycle0148 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![2, 4, 5, 3, 1]), .gapLower 0 2 (![2, 4, 5, 3, 1]), .triangle 5 1, .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0149 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 4, 5, 3, 1]), .triangle 8 2, .gapLower 0 2 (![2, 4, 5, 3, 1]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0150 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 2 (![2, 4, 5, 3, 1]), .corridorLower 0 4, .gapLower 0 5 (![2, 4, 5, 3, 1])]

def cycle0151 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 4, 5, 3, 1]), .gapLower 0 3 (![2, 4, 5, 3, 1]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0152 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 1]
    strict := ![true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![2, 4, 5, 3, 1]), .corridorLower 0 5, .gapLower 0 5 (![2, 4, 5, 3, 1])]

def cycle0153 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 4, 5, 3, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 4, 5, 3, 1])]

def cycle0154 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0155 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .triangle 10 1, .gapLower 1 0 (![2, 3, 4, 5, 0]), .corridorUpper 0 1]

def cycle0156 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0157 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0158 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0159 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .gapLower 1 1 (![2, 3, 4, 5, 0]), .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0160 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 19 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0161 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 19 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0162 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0163 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0164 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0165 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 0]

def cycle0166 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0167 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 10 1, .gapLower 1 0 (![2, 3, 5, 4, 0]), .corridorUpper 0 1]

def cycle0168 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0169 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![2, 3, 5, 4, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0170 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 2, .gapLower 1 3 (![2, 3, 5, 4, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0171 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0172 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 4 (![2, 4, 3, 0, 5])]

def cycle0173 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 11 1, .gapLower 1 0 (![2, 4, 3, 5, 0]), .corridorUpper 0 1]

def cycle0174 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 3, 5, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 3, 5, 0])]

def cycle0175 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![2, 4, 3, 5, 0]), .gapLower 1 2 (![2, 4, 3, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0176 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 3]
    constant := ![(0), (-1), (0), (-2), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, true] }
  origin := ![.triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![2, 4, 3, 5, 0]), .triangle 13 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 2]

def cycle0177 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 3, 5, 0])]

def cycle0178 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 11 1, .gapLower 1 0 (![2, 4, 5, 3, 0]), .corridorUpper 0 1]

def cycle0179 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 5, 3, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0180 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![2, 4, 5, 3, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0181 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0182 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 13 2, .triangle 15 0, .triangle 19 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0183 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 19 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0184 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1 (![1, 0, 5, 4, 3]), .gapLower 1 0 (![2, 5, 4, 3, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0185 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![2, 5, 4, 3, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0186 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 2, .gapLower 1 2 (![2, 5, 4, 3, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0187 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 3 (![2, 5, 4, 3, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0188 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.gapLower 1 4 (![2, 5, 4, 3, 0]), .triangle 13 2, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0189 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.triangle 1 0, .triangle 13 2, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![2, 5, 4, 3, 0])]

def cycle0190 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0191 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 3]
    constant := ![(0), (-3), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, true] }
  origin := ![.triangle 7 2, .gapLower 0 2 (![2, 5, 4, 3, 1]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 2]

def cycle0192 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 3]
    constant := ![(-3), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 3 (![2, 5, 4, 3, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 2]

def cycle0193 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 5, 4, 3, 1]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0194 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 4, 3, 1])]

def cycle0195 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .triangle 0 1, .gapLower 1 0 (![2, 3, 4, 5, 0]), .corridorUpper 0 1]

def cycle0196 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .gapLower 2 1 (![1, 0, 5, 4, 3]), .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0197 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0198 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 19 0, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0199 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 19 0, .triangle 15 0, .triangle 13 1, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0200 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 2, .gapLower 0 1 (![2, 5, 4, 3, 1])]

def cycle0201 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1])]

def cycle0202 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1])]

def cycle0203 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0204 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .triangle 0 1, .gapLower 1 0 (![2, 3, 5, 4, 0]), .corridorUpper 0 1]

def cycle0205 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0206 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .triangle 0 1, .gapLower 1 0 (![2, 4, 3, 5, 0]), .corridorUpper 0 1]

def cycle0207 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 4, 3, 5, 0])]

def cycle0208 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .triangle 0 1, .gapLower 1 0 (![2, 4, 5, 3, 0]), .corridorUpper 0 1]

def cycle0209 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0210 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .triangle 0 1, .gapLower 1 0 (![2, 5, 4, 3, 0]), .corridorUpper 0 1]

def cycle0211 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 5, 4, 3, 0])]

def cycle0212 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 0 1, .triangle 12 0, .triangle 6 2, .gapLower 0 1 (![2, 5, 4, 3, 1])]

def cycle0213 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false] }
  origin := ![.triangle 0 1, .triangle 11 0, .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1])]

def cycle0214 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(0), (-1), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false] }
  origin := ![.triangle 0 1, .triangle 10 0, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1])]

def cycle0215 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, true, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 2 (![2, 5, 4, 3, 1]), .triangle 9 1, .triangle 15 0, .triangle 13 1, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0216 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .gapLower 1 1 (![2, 3, 5, 4, 0]), .gapLower 1 0 (![2, 3, 5, 4, 0]), .corridorUpper 0 1]

def cycle0217 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 2 (![2, 5, 4, 3, 1]), .triangle 6 1, .gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0218 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 2 (![2, 5, 4, 3, 1]), .triangle 9 1, .triangle 15 0, .corridorLower 1 4, .corridorUpper 0 1]

def cycle0219 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 2 (![2, 5, 4, 3, 1]), .triangle 6 1, .triangle 0 1, .gapLower 1 0 (![2, 5, 4, 3, 0]), .corridorUpper 0 1]

def cycle0220 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 2 (![2, 5, 4, 3, 1]), .triangle 6 1, .gapLower 0 0 (![2, 5, 4, 3, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 5, 4, 3, 0])]

def cycle0221 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 3]
    constant := ![(-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 3 (![2, 5, 4, 3, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 2]

def cycle0222 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 5, 4, 3, 1]), .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0223 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 4, 3, 1])]

def cycle0224 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 5, 4, 3, 1])]

def cycle0225 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .triangle 6 0, .gapLower 0 0 (![2, 5, 4, 3, 1]), .gapLower 0 5 (![2, 5, 4, 3, 1])]

def cycle0226 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .triangle 5 0, .gapLower 0 0 (![2, 5, 4, 3, 1]), .gapLower 0 5 (![2, 5, 4, 3, 1])]

def cycle0227 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .gapLower 0 0 (![2, 5, 4, 3, 1]), .gapLower 0 5 (![2, 5, 4, 3, 1])]

def cycle0228 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 2 (![2, 5, 4, 3, 1]), .gapLower 0 1 (![2, 5, 4, 3, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0229 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![2, 5, 4, 3, 1]), .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0230 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 5, 4, 3, 1]), .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0231 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 3, 1]), .corridorLower 0 2, .gapLower 0 5 (![2, 5, 4, 3, 1])]

def cycle0232 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 3]
    constant := ![(-2), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 3 (![2, 5, 4, 3, 1]), .gapLower 0 2 (![2, 5, 4, 3, 1]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 2]

def cycle0233 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 5, 4, 3, 1]), .triangle 7 2, .gapLower 0 2 (![2, 5, 4, 3, 1]), .triangle 6 1, .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0234 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 2 (![2, 5, 4, 3, 1]), .corridorLower 0 5, .gapLower 0 5 (![2, 5, 4, 3, 1])]

def cycle0235 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .zero, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 4 (![2, 5, 4, 3, 1]), .gapLower 0 3 (![2, 5, 4, 3, 1]), .triangle 9 0, .corridorLower 4 5, .thetaLower 4, .thetaUpper 1, .corridorUpper 0 1]

def cycle0236 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![2, 5, 4, 3, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 5, 4, 3, 1])]

def cycle0237 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 5, 4, 3, 1]), .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 5, 4, 3, 1])]

def cycle0238 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .triangle 3 0]

def cycle0239 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 2, 1, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0240 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 2, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0241 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 0 (![5, 2, 1, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0242 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 0 (![5, 2, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0243 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![5, 2, 1, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0244 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 3, 4]), .triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0245 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![5, 2, 1, 3, 4])]

def cycle0246 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 1, 3, 4]), .triangle 1 1]

def cycle0247 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, false, true, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 3, 4]), .triangle 7 1, .triangle 1 1]

def cycle0248 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![5, 2, 1, 3, 4]), .gapLower 0 0 (![5, 2, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0249 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 3, 4]), .triangle 6 2, .gapLower 0 0 (![5, 2, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0250 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 0 (![5, 2, 1, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![5, 2, 1, 3, 4])]

def cycle0251 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 1, 3, 4]), .triangle 1 1]

def cycle0252 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 1, 3, 4]), .triangle 1 1]

def cycle0253 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 6 0, .triangle 12 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 3, 4]), .triangle 5 1]

def cycle0254 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.triangle 0 0, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 3, 4]), .triangle 7 1, .triangle 1 1]

def cycle0255 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 3, 4]), .gapLower 0 1 (![5, 2, 1, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0256 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![5, 2, 1, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![5, 2, 1, 3, 4])]

def cycle0257 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![5, 2, 1, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 1, 3, 4]), .triangle 1 1]

def cycle0258 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![5, 2, 1, 3, 4]), .corridorLower 0 5, .gapLower 0 5 (![5, 2, 1, 3, 4]), .triangle 7 1, .triangle 1 1]

def cycle0259 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 3, 4]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![5, 2, 1, 3, 4])]

def cycle0260 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 3, 4]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 1, 3, 4]), .triangle 1 1]

def cycle0261 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 3, 4]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 3, 4]), .triangle 7 1, .triangle 1 1]

def cycle0262 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 1, 3, 4]), .gapLower 0 3 (![5, 2, 1, 3, 4])]

def cycle0263 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 3, 4]), .triangle 7 1, .gapLower 0 3 (![5, 2, 1, 3, 4])]

def cycle0264 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 3, 4]), .gapLower 0 4 (![5, 2, 1, 3, 4]), .triangle 4 1]

def cycle0265 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 5, 0, 4, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0266 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .gapLower 1 1 (![2, 5, 0, 4, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 0]

def cycle0267 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 2 0 (![1, 5, 0, 4, 3]), .gapLower 2 5 (![1, 5, 0, 4, 3]), .triangle 4 0]

def cycle0268 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .gapLower 2 1 (![1, 5, 0, 4, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 0]

def cycle0269 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 2 (![1, 5, 0, 4, 3]), .triangle 12 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0270 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 5, 0, 4, 3])]

def cycle0271 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (4), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 2 0 (![1, 5, 0, 4, 3]), .gapLower 2 5 (![1, 5, 0, 4, 3]), .gapLower 2 4 (![1, 5, 0, 4, 3]), .triangle 5 0]

def cycle0272 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 5, 0, 4, 3]), .triangle 4 0]

def cycle0273 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0274 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 5, 0, 4, 3]), .triangle 2 0]

def cycle0275 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 0]

def cycle0276 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .gapLower 2 0 (![5, 1, 0, 4, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0277 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 1 (![5, 1, 0, 4, 3]), .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0278 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 1 5, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 2 (![5, 1, 0, 4, 3]), .triangle 12 2, .gapLower 1 0 (![5, 2, 0, 4, 3]), .gapLower 1 5 (![5, 2, 0, 4, 3]), .triangle 1 0]

def cycle0279 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![5, 1, 0, 4, 3])]

def cycle0280 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![5, 1, 0, 4, 3]), .triangle 5 0]

def cycle0281 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 1, 0, 4, 3]), .triangle 4 0]

def cycle0282 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 1 (![5, 2, 0, 4, 3]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0283 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2 (![5, 2, 0, 4, 3]), .triangle 12 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0284 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![5, 2, 0, 4, 3])]

def cycle0285 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 4, 3]), .triangle 6 2, .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![5, 2, 0, 4, 3]), .triangle 2 0]

def cycle0286 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![5, 2, 0, 4, 3]), .triangle 1 0]

def cycle0287 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![5, 2, 1, 4, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0288 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 4, 3]), .triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0289 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![5, 2, 1, 4, 3])]

def cycle0290 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 1, 4, 3]), .triangle 2 1]

def cycle0291 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 4, 3]), .triangle 1 1]

def cycle0292 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![5, 2, 1, 4, 3]), .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0293 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 4, 3]), .triangle 6 2, .gapLower 0 0 (![5, 2, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0294 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![5, 2, 1, 4, 3])]

def cycle0295 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![5, 2, 1, 4, 3])]

def cycle0296 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 1, 4, 3]), .triangle 2 1]

def cycle0297 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 1, 4, 3]), .triangle 2 1]

def cycle0298 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 6 0, .triangle 12 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 4, 3]), .triangle 4 1]

def cycle0299 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 4, 3]), .triangle 1 1]

def cycle0300 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 4, 3]), .gapLower 0 1 (![5, 2, 1, 4, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0301 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![5, 2, 1, 4, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![5, 2, 1, 4, 3])]

def cycle0302 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![5, 2, 1, 4, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 1, 4, 3]), .triangle 2 1]

def cycle0303 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![5, 2, 1, 4, 3]), .corridorLower 0 5, .gapLower 0 5 (![5, 2, 1, 4, 3]), .triangle 1 1]

def cycle0304 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 4, 3]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![5, 2, 1, 4, 3])]

def cycle0305 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 4, 3]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 1, 4, 3]), .triangle 2 1]

def cycle0306 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 2 (![5, 2, 1, 4, 3]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 4, 3]), .triangle 1 1]

def cycle0307 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 1, 4, 3]), .gapLower 0 3 (![5, 2, 1, 4, 3])]

def cycle0308 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 4, 3]), .triangle 7 2, .gapLower 0 3 (![5, 2, 1, 4, 3])]

def cycle0309 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 1, 4, 3]), .gapLower 0 4 (![5, 2, 1, 4, 3]), .triangle 5 1]

def cycle0310 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .triangle 12 2, .triangle 3 0]

def cycle0311 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 4, 5, 0, 3]), .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0312 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .triangle 12 2, .triangle 15 1, .gapLower 1 1 (![2, 4, 5, 0, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0313 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .triangle 12 2, .gapLower 1 2 (![2, 4, 5, 0, 3]), .corridorLower 1 4, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0314 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 4, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0315 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .triangle 12 0, .gapLower 2 0 (![1, 5, 0, 4, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0316 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .gapLower 2 1 (![1, 5, 0, 4, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0317 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 2 2 (![1, 5, 0, 4, 3]), .triangle 12 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0318 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 5, 0, 4, 3])]

def cycle0319 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 4, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 5, 0, 4, 3]), .triangle 4 0]

def cycle0320 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 2, .gapLower 0 0 (![5, 2, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0321 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0322 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 0, .gapLower 2 0 (![5, 1, 0, 4, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0323 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 2 1 (![5, 1, 0, 4, 3]), .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0324 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 1 2, .distance 1 5, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 2 2 (![5, 1, 0, 4, 3]), .triangle 12 2, .gapLower 1 0 (![5, 2, 4, 0, 3]), .gapLower 1 5 (![5, 2, 4, 0, 3]), .triangle 1 0]

def cycle0325 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![5, 1, 0, 4, 3])]

def cycle0326 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![5, 1, 0, 4, 3]), .triangle 5 0]

def cycle0327 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 4, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 1, 0, 4, 3]), .triangle 4 0]

def cycle0328 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 1 1 (![5, 2, 4, 0, 3]), .corridorLower 1 5, .gapLower 1 5 (![5, 2, 4, 0, 3]), .triangle 1 0]

def cycle0329 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2 (![5, 2, 4, 0, 3]), .triangle 12 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0330 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![5, 2, 4, 0, 3]), .triangle 11 1, .triangle 12 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0331 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 2, .gapLower 0 0 (![5, 2, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![5, 2, 4, 0, 3])]

def cycle0332 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![5, 2, 4, 0, 3]), .triangle 1 0]

def cycle0333 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 1 (![5, 2, 4, 1, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0334 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![5, 2, 4, 1, 3]), .triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0335 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 2, 4, 1, 3]), .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0336 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 4, 1, 3])]

def cycle0337 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, false, true] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 1, 3]), .triangle 1 1]

def cycle0338 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 1 (![5, 2, 4, 1, 3]), .gapLower 0 0 (![5, 2, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0339 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![5, 2, 4, 1, 3]), .triangle 6 2, .gapLower 0 0 (![5, 2, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0340 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 2, 4, 1, 3]), .triangle 5 1, .triangle 6 2, .gapLower 0 0 (![5, 2, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0341 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 4, 1, 3])]

def cycle0342 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 4, 1, 3])]

def cycle0343 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 1, 3]), .triangle 1 1]

def cycle0344 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 1, 3]), .triangle 1 1]

def cycle0345 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![5, 2, 4, 1, 3]), .gapLower 0 1 (![5, 2, 4, 1, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0346 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 2, 4, 1, 3]), .triangle 5 1, .gapLower 0 1 (![5, 2, 4, 1, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0347 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 1 (![5, 2, 4, 1, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 4, 1, 3])]

def cycle0348 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 1 (![5, 2, 4, 1, 3]), .corridorLower 0 5, .gapLower 0 5 (![5, 2, 4, 1, 3]), .triangle 1 1]

def cycle0349 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 2, 4, 1, 3]), .gapLower 0 2 (![5, 2, 4, 1, 3]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0350 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![5, 2, 4, 1, 3]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 4, 1, 3])]

def cycle0351 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![5, 2, 4, 1, 3]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 1, 3]), .triangle 1 1]

def cycle0352 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![5, 2, 4, 1, 3]), .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 2, 4, 1, 3])]

def cycle0353 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.gapLower 0 3 (![5, 2, 4, 1, 3]), .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 1, 3]), .triangle 1 1]

def cycle0354 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 1, 3]), .gapLower 0 4 (![5, 2, 4, 1, 3])]

def cycle0355 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 0, .triangle 12 2, .triangle 3 0]

def cycle0356 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 3, 5, 0, 4]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0357 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .triangle 14 1, .gapLower 1 1 (![2, 3, 5, 0, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0358 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .gapLower 1 2 (![2, 3, 5, 0, 4]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0359 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0360 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 3, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0361 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 2, .gapLower 0 0 (![5, 2, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0362 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 2, 3, 1, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0363 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 5, 3, 0, 4]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0364 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .gapLower 1 1 (![2, 5, 3, 0, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0365 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (0), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![2, 5, 3, 0, 4]), .triangle 14 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 0 (![5, 2, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0366 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 2, .gapLower 0 0 (![5, 2, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 5, 3, 0, 4])]

def cycle0367 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 2, 3, 1, 4]), .triangle 4 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 3, 0, 4]), .triangle 2 0]

def cycle0368 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 1 5, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 1 1 (![5, 2, 3, 0, 4]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0369 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 2 (![5, 2, 3, 0, 4]), .triangle 12 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0370 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![5, 2, 3, 0, 4]), .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0371 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 2, .gapLower 0 0 (![5, 2, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![5, 2, 3, 0, 4])]

def cycle0372 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![5, 2, 3, 0, 4]), .triangle 2 0]

def cycle0373 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 2, 3, 1, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0374 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![5, 2, 3, 1, 4])]

def cycle0375 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 2, 3, 1, 4]), .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0376 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 3, 1, 4])]

def cycle0377 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 1, 4]), .triangle 7 1, .triangle 4 1]

def cycle0378 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 2, 3, 1, 4]), .gapLower 0 0 (![5, 2, 3, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0379 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![5, 2, 3, 1, 4]), .triangle 6 2, .gapLower 0 0 (![5, 2, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0380 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 2, 3, 1, 4]), .triangle 4 1, .triangle 6 2, .gapLower 0 0 (![5, 2, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0381 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 3, 1, 4])]

def cycle0382 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 3, 1, 4])]

def cycle0383 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 6 0, .triangle 12 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 1, 4]), .triangle 5 1]

def cycle0384 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 1, 4]), .triangle 2 1]

def cycle0385 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 2, 3, 1, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![5, 2, 3, 1, 4])]

def cycle0386 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 2, 3, 1, 4]), .triangle 4 1, .gapLower 0 1 (![5, 2, 3, 1, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0387 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 1 (![5, 2, 3, 1, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 3, 1, 4])]

def cycle0388 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 1 (![5, 2, 3, 1, 4]), .corridorLower 0 5, .gapLower 0 5 (![5, 2, 3, 1, 4]), .triangle 7 1, .triangle 4 1]

def cycle0389 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 2, 3, 1, 4]), .gapLower 0 2 (![5, 2, 3, 1, 4]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0390 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![5, 2, 3, 1, 4]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 3, 1, 4])]

def cycle0391 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![5, 2, 3, 1, 4]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 1, 4]), .triangle 2 1]

def cycle0392 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![5, 2, 3, 1, 4]), .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 2, 3, 1, 4])]

def cycle0393 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.gapLower 0 3 (![5, 2, 3, 1, 4]), .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 1, 4]), .triangle 2 1]

def cycle0394 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 1, 4]), .gapLower 0 4 (![5, 2, 3, 1, 4])]

def cycle0395 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .triangle 6 0, .triangle 12 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0396 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 3, 4, 5, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0397 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .triangle 15 1, .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0398 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .triangle 15 1, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0399 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0400 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 3, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0401 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 3, 4, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0402 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0403 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 3, 5, 4, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0404 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .triangle 14 1, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0405 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .gapLower 1 2 (![2, 3, 5, 4, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0406 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 3, 5, 4, 0]), .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0407 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0408 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 5, 3, 4, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0409 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .gapLower 1 1 (![2, 5, 3, 4, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0410 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 3 (![2, 5, 3, 4, 0]), .triangle 14 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 4 0, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0411 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 5, 3, 4, 0]), .triangle 13 1, .triangle 14 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 4 0, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0412 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 3, 4, 0])]

def cycle0413 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .gapLower 1 1 (![5, 2, 3, 4, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0414 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 2 (![5, 2, 3, 4, 0]), .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0415 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.triangle 2 0, .gapLower 1 3 (![5, 2, 3, 4, 0]), .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0416 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 4 (![5, 2, 3, 4, 0]), .triangle 13 1, .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0417 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![5, 2, 3, 4, 0])]

def cycle0418 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 2, 3, 4, 1]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0419 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![5, 2, 3, 4, 1])]

def cycle0420 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![5, 2, 3, 4, 1]), .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0421 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 3, 4, 1]), .triangle 7 1, .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0422 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 4, 1])]

def cycle0423 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 2, 3, 4, 1]), .gapLower 0 0 (![5, 2, 3, 4, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0424 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 3, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![5, 2, 3, 4, 1])]

def cycle0425 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![5, 2, 3, 4, 1]), .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0426 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 3, 4, 1]), .triangle 7 1, .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0427 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 4, 1])]

def cycle0428 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 4, 1])]

def cycle0429 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .triangle 5 0, .triangle 6 2, .gapLower 0 0 (![5, 2, 3, 4, 1]), .gapLower 0 5 (![5, 2, 3, 4, 1])]

def cycle0430 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .triangle 6 2, .gapLower 0 0 (![5, 2, 3, 4, 1]), .gapLower 0 5 (![5, 2, 3, 4, 1])]

def cycle0431 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 2, 3, 4, 1]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![5, 2, 3, 4, 1])]

def cycle0432 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 5, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![5, 2, 3, 4, 1]), .triangle 4 1, .gapLower 0 1 (![5, 2, 3, 4, 1]), .triangle 6 1, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0433 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 3, 4, 1]), .triangle 5 1, .gapLower 0 1 (![5, 2, 3, 4, 1]), .triangle 6 1, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0434 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 0 1 (![5, 2, 3, 4, 1]), .corridorLower 0 5, .gapLower 0 5 (![5, 2, 3, 4, 1])]

def cycle0435 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![5, 2, 3, 4, 1]), .gapLower 0 2 (![5, 2, 3, 4, 1]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0436 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 3, 4, 1]), .triangle 7 1, .gapLower 0 2 (![5, 2, 3, 4, 1]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0437 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 2 (![5, 2, 3, 4, 1]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 4, 1])]

def cycle0438 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 3, 4, 1]), .gapLower 0 3 (![5, 2, 3, 4, 1]), .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0439 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![5, 2, 3, 4, 1]), .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 4, 1])]

def cycle0440 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 3, 4, 1]), .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 3, 4, 1])]

def cycle0441 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 0, .triangle 12 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0442 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .gapLower 2 1 (![1, 5, 0, 4, 3]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0443 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 4, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 5, 0, 4, 3])]

def cycle0444 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 4, 3, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 5, 0, 4, 3]), .triangle 4 0]

def cycle0445 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0446 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0447 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 14 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 4 0, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0448 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (0), (-1), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .triangle 14 1, .triangle 13 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 0]

def cycle0449 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 4, 5, 3, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0450 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .triangle 15 1, .gapLower 1 1 (![2, 4, 5, 3, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0451 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (0), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .gapLower 1 2 (![2, 4, 5, 3, 0]), .triangle 13 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 0]

def cycle0452 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 4, 5, 3, 0]), .triangle 13 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 0, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0453 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0454 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .gapLower 1 0 (![2, 5, 4, 3, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0455 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 2, .gapLower 1 1 (![2, 5, 4, 3, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0456 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 3 (![2, 5, 4, 3, 0]), .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0457 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 5, 4, 3, 0]), .triangle 13 2, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0458 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 4, 3, 0])]

def cycle0459 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0460 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .gapLower 2 0 (![5, 1, 0, 4, 3]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0461 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 2 1 (![5, 1, 0, 4, 3]), .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0462 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 1 5, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 2 (![5, 1, 0, 4, 3]), .triangle 12 2, .gapLower 1 0 (![5, 2, 4, 3, 0]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0463 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 4, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![5, 1, 0, 4, 3])]

def cycle0464 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 4, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![5, 1, 0, 4, 3]), .triangle 5 0]

def cycle0465 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 0 (![5, 2, 4, 3, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 1, 0, 4, 3]), .triangle 4 0]

def cycle0466 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 1 1 (![5, 2, 4, 3, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0467 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 13 2, .gapLower 1 2 (![5, 2, 4, 3, 0]), .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0468 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 3 (![5, 2, 4, 3, 0]), .triangle 11 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0469 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 1 4 (![5, 2, 4, 3, 0]), .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0470 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![5, 2, 4, 3, 0])]

def cycle0471 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 2, 4, 3, 1]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0472 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 2 (![5, 2, 4, 3, 1]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0473 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![5, 2, 4, 3, 1]), .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0474 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 4, 3, 1]), .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0475 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 3, 1])]

def cycle0476 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 2, 4, 3, 1]), .gapLower 0 0 (![5, 2, 4, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0477 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 2 (![5, 2, 4, 3, 1]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0478 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![5, 2, 4, 3, 1]), .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0479 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 4, 3, 1]), .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0480 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 0, .triangle 12 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 3, 1])]

def cycle0481 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 3, 1])]

def cycle0482 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .triangle 5 0, .triangle 6 2, .gapLower 0 0 (![5, 2, 4, 3, 1]), .gapLower 0 5 (![5, 2, 4, 3, 1])]

def cycle0483 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .triangle 6 2, .gapLower 0 0 (![5, 2, 4, 3, 1]), .gapLower 0 5 (![5, 2, 4, 3, 1])]

def cycle0484 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 5, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 2 (![5, 2, 4, 3, 1]), .gapLower 0 1 (![5, 2, 4, 3, 1]), .triangle 6 1, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0485 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 5, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![5, 2, 4, 3, 1]), .triangle 5 1, .gapLower 0 1 (![5, 2, 4, 3, 1]), .triangle 6 1, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0486 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 4, 3, 1]), .triangle 4 1, .gapLower 0 1 (![5, 2, 4, 3, 1]), .triangle 6 1, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0487 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 1 (![5, 2, 4, 3, 1]), .corridorLower 0 5, .gapLower 0 5 (![5, 2, 4, 3, 1])]

def cycle0488 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![5, 2, 4, 3, 1]), .gapLower 0 2 (![5, 2, 4, 3, 1]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0489 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 4, 3, 1]), .triangle 7 2, .gapLower 0 2 (![5, 2, 4, 3, 1]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0490 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 2 (![5, 2, 4, 3, 1]), .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 3, 1])]

def cycle0491 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 4, 3, 1]), .gapLower 0 3 (![5, 2, 4, 3, 1]), .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0492 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![5, 2, 4, 3, 1]), .triangle 5 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 3, 1])]

def cycle0493 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 2, 4, 3, 1]), .triangle 4 1, .triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 2, 4, 3, 1])]

def cycle0494 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 2, .triangle 2 0]

def cycle0495 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 2, 1, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0496 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 2, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0497 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 0 (![4, 2, 1, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0498 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 0 (![4, 2, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0499 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![4, 2, 1, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0500 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 3, 5]), .triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0501 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![4, 2, 1, 3, 5])]

def cycle0502 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 1, 3, 5]), .triangle 1 1]

def cycle0503 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 3, 5]), .triangle 6 1]

def cycle0504 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![4, 2, 1, 3, 5]), .gapLower 0 0 (![4, 2, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0505 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 3, 5]), .triangle 5 2, .gapLower 0 0 (![4, 2, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0506 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 0 (![4, 2, 1, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![4, 2, 1, 3, 5])]

def cycle0507 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 1, 3, 5]), .triangle 1 1]

def cycle0508 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 1, 3, 5]), .triangle 1 1]

def cycle0509 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 3, 5]), .triangle 8 1, .triangle 1 1]

def cycle0510 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 3, 5]), .triangle 8 1, .triangle 1 1]

def cycle0511 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 3, 5]), .gapLower 0 1 (![4, 2, 1, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0512 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![4, 2, 1, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![4, 2, 1, 3, 5])]

def cycle0513 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![4, 2, 1, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 1, 3, 5]), .triangle 1 1]

def cycle0514 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![4, 2, 1, 3, 5]), .corridorLower 0 4, .gapLower 0 5 (![4, 2, 1, 3, 5]), .triangle 8 1, .triangle 1 1]

def cycle0515 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 3, 5]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![4, 2, 1, 3, 5])]

def cycle0516 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 3, 5]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 1, 3, 5]), .triangle 1 1]

def cycle0517 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 3, 5]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 3, 5]), .triangle 8 1, .triangle 1 1]

def cycle0518 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 1, 3, 5]), .gapLower 0 3 (![4, 2, 1, 3, 5])]

def cycle0519 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 3, 5]), .triangle 8 1, .gapLower 0 3 (![4, 2, 1, 3, 5])]

def cycle0520 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 3, 5]), .gapLower 0 4 (![4, 2, 1, 3, 5]), .triangle 4 1]

def cycle0521 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .gapLower 1 0 (![2, 4, 0, 5, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0522 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 2, .gapLower 1 1 (![2, 4, 0, 5, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 1 0]

def cycle0523 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .gapLower 2 0 (![1, 4, 0, 5, 3]), .gapLower 2 5 (![1, 4, 0, 5, 3]), .triangle 4 0]

def cycle0524 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .gapLower 2 1 (![1, 4, 0, 5, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 1 0]

def cycle0525 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 2 (![1, 4, 0, 5, 3]), .triangle 11 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0526 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![1, 4, 0, 5, 3])]

def cycle0527 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 1, 5, 3]), .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 4, 0, 5, 3]), .triangle 6 0]

def cycle0528 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 4, 0, 5, 3]), .triangle 4 0]

def cycle0529 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0530 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 5, 3]), .triangle 5 2, .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 0, 5, 3]), .triangle 3 0]

def cycle0531 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 1 0]

def cycle0532 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 0, .gapLower 2 0 (![4, 1, 0, 5, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0533 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 1 (![4, 1, 0, 5, 3]), .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0534 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 2 (![4, 1, 0, 5, 3]), .triangle 11 2, .gapLower 1 0 (![4, 2, 0, 5, 3]), .gapLower 1 5 (![4, 2, 0, 5, 3]), .triangle 1 0]

def cycle0535 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![4, 1, 0, 5, 3])]

def cycle0536 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 1, 5, 3]), .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![4, 1, 0, 5, 3]), .triangle 6 0]

def cycle0537 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 1, 0, 5, 3]), .triangle 4 0]

def cycle0538 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 1 (![4, 2, 0, 5, 3]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0539 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2 (![4, 2, 0, 5, 3]), .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0540 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 2, .gapLower 1 3 (![4, 2, 0, 5, 3])]

def cycle0541 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 5, 3]), .triangle 5 2, .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![4, 2, 0, 5, 3]), .triangle 3 0]

def cycle0542 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![4, 2, 0, 5, 3]), .triangle 1 0]

def cycle0543 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![4, 2, 1, 5, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0544 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 5, 3]), .triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0545 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![4, 2, 1, 5, 3])]

def cycle0546 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 1, 5, 3]), .triangle 6 1]

def cycle0547 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 5, 3]), .triangle 1 1]

def cycle0548 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![4, 2, 1, 5, 3]), .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0549 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 5, 3]), .triangle 5 2, .gapLower 0 0 (![4, 2, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0550 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![4, 2, 1, 5, 3])]

def cycle0551 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![4, 2, 1, 5, 3])]

def cycle0552 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 1, 5, 3]), .triangle 6 1]

def cycle0553 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 1, 5, 3]), .triangle 3 1]

def cycle0554 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 5, 3]), .triangle 4 1]

def cycle0555 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 5, 3]), .triangle 1 1]

def cycle0556 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 5, 3]), .gapLower 0 1 (![4, 2, 1, 5, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0557 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![4, 2, 1, 5, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![4, 2, 1, 5, 3])]

def cycle0558 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![4, 2, 1, 5, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 1, 5, 3]), .triangle 3 1]

def cycle0559 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![4, 2, 1, 5, 3]), .corridorLower 0 4, .gapLower 0 5 (![4, 2, 1, 5, 3]), .triangle 1 1]

def cycle0560 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 5, 3]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![4, 2, 1, 5, 3])]

def cycle0561 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 5, 3]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 1, 5, 3]), .triangle 3 1]

def cycle0562 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 2 (![4, 2, 1, 5, 3]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 5, 3]), .triangle 1 1]

def cycle0563 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 1, 5, 3]), .gapLower 0 3 (![4, 2, 1, 5, 3])]

def cycle0564 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 5, 3]), .triangle 8 2, .gapLower 0 3 (![4, 2, 1, 5, 3])]

def cycle0565 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 1, 5, 3]), .gapLower 0 4 (![4, 2, 1, 5, 3]), .triangle 6 1]

def cycle0566 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .triangle 11 0, .gapLower 1 0 (![2, 4, 5, 0, 3]), .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0567 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .triangle 11 2, .gapLower 1 1 (![2, 4, 5, 0, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0568 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 4 0]

def cycle0569 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .triangle 11 0, .gapLower 2 0 (![1, 4, 0, 5, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0570 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .gapLower 2 1 (![1, 4, 0, 5, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0571 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![1, 4, 0, 5, 3]), .triangle 11 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0572 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![1, 4, 0, 5, 3])]

def cycle0573 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 5, 1, 3]), .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 4, 0, 5, 3]), .triangle 6 0]

def cycle0574 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 4, 0, 5, 3]), .triangle 4 0]

def cycle0575 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 2, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0576 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0577 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 2 (![4, 2, 5, 1, 3])]

def cycle0578 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .triangle 12 0, .triangle 6 0]

def cycle0579 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 11 0, .gapLower 2 0 (![4, 1, 0, 5, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0580 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 1 (![4, 1, 0, 5, 3]), .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0581 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![4, 1, 0, 5, 3]), .triangle 11 2, .gapLower 1 0 (![4, 2, 5, 0, 3]), .gapLower 1 5 (![4, 2, 5, 0, 3]), .triangle 1 0]

def cycle0582 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![4, 1, 0, 5, 3])]

def cycle0583 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 5, 1, 3]), .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![4, 1, 0, 5, 3]), .triangle 6 0]

def cycle0584 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 1, 0, 5, 3]), .triangle 4 0]

def cycle0585 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 1 1 (![4, 2, 5, 0, 3]), .corridorLower 1 4, .gapLower 1 5 (![4, 2, 5, 0, 3]), .triangle 1 0]

def cycle0586 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 2 (![4, 2, 5, 0, 3]), .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0587 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 3 (![4, 2, 5, 0, 3]), .triangle 12 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0588 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 2, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![4, 2, 5, 0, 3])]

def cycle0589 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 2, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![4, 2, 5, 0, 3]), .triangle 1 0]

def cycle0590 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0591 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 1 (![4, 2, 5, 1, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0592 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![4, 2, 5, 1, 3]), .triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0593 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 2, 5, 1, 3]), .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0594 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 5, 1, 3])]

def cycle0595 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 1, 3]), .triangle 1 1]

def cycle0596 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 1 (![4, 2, 5, 1, 3]), .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0597 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![4, 2, 5, 1, 3]), .triangle 5 2, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0598 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 2, 5, 1, 3]), .triangle 9 1, .gapLower 0 0 (![4, 2, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0599 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 5, 1, 3])]

def cycle0600 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 5, 1, 3])]

def cycle0601 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 1, 3]), .triangle 1 1]

def cycle0602 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 1, 3]), .triangle 1 1]

def cycle0603 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![4, 2, 5, 1, 3]), .gapLower 0 1 (![4, 2, 5, 1, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0604 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 2, 5, 1, 3]), .triangle 6 1, .gapLower 0 1 (![4, 2, 5, 1, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0605 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 1 (![4, 2, 5, 1, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 5, 1, 3])]

def cycle0606 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 1 (![4, 2, 5, 1, 3]), .corridorLower 0 4, .gapLower 0 5 (![4, 2, 5, 1, 3]), .triangle 1 1]

def cycle0607 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 2, 5, 1, 3]), .gapLower 0 2 (![4, 2, 5, 1, 3]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0608 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![4, 2, 5, 1, 3]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 5, 1, 3])]

def cycle0609 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![4, 2, 5, 1, 3]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 1, 3]), .triangle 1 1]

def cycle0610 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 2, 5, 1, 3]), .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 2, 5, 1, 3])]

def cycle0611 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.gapLower 0 3 (![4, 2, 5, 1, 3]), .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 1, 3]), .triangle 1 1]

def cycle0612 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 1, 3]), .gapLower 0 4 (![4, 2, 5, 1, 3])]

def cycle0613 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .triangle 11 2, .triangle 2 0]

def cycle0614 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .gapLower 1 0 (![2, 3, 4, 0, 5]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0615 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 0, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0616 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .gapLower 1 2 (![2, 3, 4, 0, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0617 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 4 0]

def cycle0618 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 3, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .triangle 8 0, .triangle 4 1]

def cycle0619 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 2, .gapLower 0 0 (![4, 2, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0620 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 2, 3, 1, 5]), .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 0, 5]), .triangle 3 0]

def cycle0621 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .gapLower 1 0 (![2, 4, 3, 0, 5]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0622 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .gapLower 1 1 (![2, 4, 3, 0, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0623 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (3), (-1), (0), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 2 (![2, 4, 3, 0, 5]), .gapLower 4 1 (![3, 1, 2, 0, 5]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 0 (![4, 2, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0624 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (0), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![2, 4, 3, 0, 5]), .triangle 13 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 0 (![4, 2, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0625 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 2, .gapLower 0 0 (![4, 2, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 4, 3, 0, 5])]

def cycle0626 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 2, 3, 1, 5]), .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 3, 0, 5]), .triangle 3 0]

def cycle0627 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 1 4, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 1 1 (![4, 2, 3, 0, 5]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0628 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 2 (![4, 2, 3, 0, 5]), .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0629 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![4, 2, 3, 0, 5]), .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0630 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 2, .gapLower 0 0 (![4, 2, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![4, 2, 3, 0, 5])]

def cycle0631 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![4, 2, 3, 0, 5]), .triangle 3 0]

def cycle0632 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 3, 1, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0633 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![4, 2, 3, 1, 5])]

def cycle0634 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 2, 3, 1, 5]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0635 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 3, 1, 5])]

def cycle0636 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 1, 5]), .triangle 6 1]

def cycle0637 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 3, 1, 5]), .gapLower 0 0 (![4, 2, 3, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0638 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![4, 2, 3, 1, 5]), .triangle 5 2, .gapLower 0 0 (![4, 2, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0639 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 2, 3, 1, 5]), .triangle 4 1, .triangle 5 2, .gapLower 0 0 (![4, 2, 3, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0640 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 3, 1, 5])]

def cycle0641 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 3, 1, 5])]

def cycle0642 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 1, 5]), .triangle 3 1]

def cycle0643 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 1, 5]), .triangle 3 1]

def cycle0644 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 3, 1, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![4, 2, 3, 1, 5])]

def cycle0645 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 2, 3, 1, 5]), .triangle 4 1, .gapLower 0 1 (![4, 2, 3, 1, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0646 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 1 (![4, 2, 3, 1, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 3, 1, 5])]

def cycle0647 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 1 (![4, 2, 3, 1, 5]), .corridorLower 0 4, .gapLower 0 5 (![4, 2, 3, 1, 5]), .triangle 8 1, .triangle 4 1]

def cycle0648 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 2, 3, 1, 5]), .gapLower 0 2 (![4, 2, 3, 1, 5]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0649 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![4, 2, 3, 1, 5]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 3, 1, 5])]

def cycle0650 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![4, 2, 3, 1, 5]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 1, 5]), .triangle 3 1]

def cycle0651 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 2, 3, 1, 5]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 2, 3, 1, 5])]

def cycle0652 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.gapLower 0 3 (![4, 2, 3, 1, 5]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 1, 5]), .triangle 3 1]

def cycle0653 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 1, 5]), .gapLower 0 4 (![4, 2, 3, 1, 5])]

def cycle0654 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .gapLower 1 0 (![2, 3, 4, 5, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0655 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0656 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0657 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 3, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 4 0]

def cycle0658 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 3, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .triangle 8 0, .triangle 4 1]

def cycle0659 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0660 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 2, 3, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0661 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 13 1, .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![4, 2, 3, 5, 1])]

def cycle0662 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .gapLower 1 0 (![2, 4, 3, 5, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0663 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .gapLower 1 1 (![2, 4, 3, 5, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0664 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 3 (![2, 4, 3, 5, 0]), .triangle 13 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 0, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0665 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 4, 3, 5, 0]), .triangle 14 1, .triangle 13 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 0, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0666 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 3, 5, 0])]

def cycle0667 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 1 1 (![4, 2, 3, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0668 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 1 2 (![4, 2, 3, 5, 0]), .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0669 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.triangle 3 0, .gapLower 1 3 (![4, 2, 3, 5, 0]), .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0670 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 1 4 (![4, 2, 3, 5, 0]), .triangle 12 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0671 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![4, 2, 3, 5, 0])]

def cycle0672 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![5, 4, 2, 3, 0]), .triangle 10 1, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 2, 3, 5, 1]), .gapLower 0 5 (![4, 2, 3, 5, 1])]

def cycle0673 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 3, 5, 1]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0674 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![4, 2, 3, 5, 1])]

def cycle0675 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![4, 2, 3, 5, 1]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0676 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 3, 5, 1]), .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0677 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 5, 1])]

def cycle0678 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 3, 5, 1]), .gapLower 0 0 (![4, 2, 3, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0679 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 3, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![4, 2, 3, 5, 1])]

def cycle0680 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![4, 2, 3, 5, 1]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0681 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 3, 5, 1]), .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0682 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 5, 1])]

def cycle0683 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 5, 1])]

def cycle0684 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .triangle 5 2, .gapLower 0 0 (![4, 2, 3, 5, 1]), .gapLower 0 5 (![4, 2, 3, 5, 1])]

def cycle0685 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 3, 5, 1]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![4, 2, 3, 5, 1])]

def cycle0686 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![4, 2, 3, 5, 1]), .triangle 4 1, .gapLower 0 1 (![4, 2, 3, 5, 1]), .triangle 5 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0687 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 3, 5, 1]), .triangle 6 1, .gapLower 0 1 (![4, 2, 3, 5, 1]), .triangle 5 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0688 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .gapLower 0 1 (![4, 2, 3, 5, 1]), .corridorLower 0 4, .gapLower 0 5 (![4, 2, 3, 5, 1])]

def cycle0689 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![4, 2, 3, 5, 1]), .gapLower 0 2 (![4, 2, 3, 5, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0690 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 3, 5, 1]), .triangle 8 1, .gapLower 0 2 (![4, 2, 3, 5, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0691 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 2 (![4, 2, 3, 5, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 5, 1])]

def cycle0692 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 3, 5, 1]), .gapLower 0 3 (![4, 2, 3, 5, 1]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0693 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![4, 2, 3, 5, 1]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 5, 1])]

def cycle0694 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 3, 5, 1]), .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 3, 5, 1])]

def cycle0695 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0696 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .gapLower 2 1 (![1, 4, 0, 5, 3]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0697 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 5, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![1, 4, 0, 5, 3])]

def cycle0698 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 5, 3, 1]), .gapLower 0 0 (![4, 2, 5, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 4, 0, 5, 3]), .triangle 6 0]

def cycle0699 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 5, 3, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 4, 0, 5, 3]), .triangle 4 0]

def cycle0700 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .triangle 6 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0701 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 3, 5, 4, 0]), .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 2, 5, 3, 1]), .gapLower 0 5 (![4, 2, 5, 3, 1])]

def cycle0702 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (0), (-1), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 13 1, .triangle 14 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 4 0]

def cycle0703 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 0, .triangle 13 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 0, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0704 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .gapLower 1 0 (![2, 4, 5, 3, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0705 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .gapLower 1 1 (![2, 4, 5, 3, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0706 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 4, 5, 3, 0]), .triangle 13 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 0, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0707 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .triangle 6 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0708 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 15 0, .triangle 9 2, .triangle 6 1]

def cycle0709 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 0, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0710 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .gapLower 2 0 (![4, 1, 0, 5, 3]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0711 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 2 1 (![4, 1, 0, 5, 3]), .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0712 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 2 (![4, 1, 0, 5, 3]), .triangle 11 2, .gapLower 1 0 (![4, 2, 5, 3, 0]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0713 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 5, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![4, 1, 0, 5, 3])]

def cycle0714 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 5, 3, 1]), .gapLower 0 0 (![4, 2, 5, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![4, 1, 0, 5, 3]), .triangle 6 0]

def cycle0715 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 0 (![4, 2, 5, 3, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 1, 0, 5, 3]), .triangle 4 0]

def cycle0716 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 1 1 (![4, 2, 5, 3, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0717 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 14 2, .gapLower 1 2 (![4, 2, 5, 3, 0]), .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0718 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 3 (![4, 2, 5, 3, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0719 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 4 (![4, 2, 5, 3, 0]), .triangle 14 2, .triangle 12 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0720 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![4, 2, 5, 3, 0])]

def cycle0721 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![5, 4, 2, 3, 0]), .triangle 10 1, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 2, 5, 3, 1]), .gapLower 0 5 (![4, 2, 5, 3, 1])]

def cycle0722 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 5, 3, 1]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0723 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 2 (![4, 2, 5, 3, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0724 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![4, 2, 5, 3, 1]), .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0725 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 5, 3, 1]), .triangle 8 2, .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0726 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 3, 1])]

def cycle0727 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 2, 5, 3, 1]), .gapLower 0 0 (![4, 2, 5, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0728 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 2 (![4, 2, 5, 3, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0729 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![4, 2, 5, 3, 1]), .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0730 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 5, 3, 1]), .triangle 8 2, .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0731 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 3, 1])]

def cycle0732 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 3, 1])]

def cycle0733 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .triangle 5 2, .gapLower 0 0 (![4, 2, 5, 3, 1]), .gapLower 0 5 (![4, 2, 5, 3, 1])]

def cycle0734 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 2 (![4, 2, 5, 3, 1]), .gapLower 0 1 (![4, 2, 5, 3, 1]), .triangle 5 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0735 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![4, 2, 5, 3, 1]), .triangle 6 1, .gapLower 0 1 (![4, 2, 5, 3, 1]), .triangle 5 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0736 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 5, 3, 1]), .triangle 4 1, .gapLower 0 1 (![4, 2, 5, 3, 1]), .triangle 5 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0737 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 1 (![4, 2, 5, 3, 1]), .corridorLower 0 4, .gapLower 0 5 (![4, 2, 5, 3, 1])]

def cycle0738 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![4, 2, 5, 3, 1]), .gapLower 0 2 (![4, 2, 5, 3, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0739 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 5, 3, 1]), .triangle 8 2, .gapLower 0 2 (![4, 2, 5, 3, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0740 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 2 (![4, 2, 5, 3, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 3, 1])]

def cycle0741 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 5, 3, 1]), .gapLower 0 3 (![4, 2, 5, 3, 1]), .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0742 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![4, 2, 5, 3, 1]), .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 3, 1])]

def cycle0743 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 2, 5, 3, 1]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 2, 5, 3, 1])]

def cycle0744 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .gapLower 1 0 (![2, 4, 5, 0, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0745 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .triangle 15 1, .gapLower 1 1 (![2, 4, 5, 0, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0746 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 12 2, .gapLower 1 2 (![2, 4, 5, 0, 3]), .corridorLower 1 4, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0747 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .triangle 11 0, .gapLower 2 0 (![1, 4, 5, 0, 3]), .gapLower 2 5 (![1, 4, 5, 0, 3]), .triangle 4 0]

def cycle0748 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 18 1, .gapLower 2 1 (![1, 4, 5, 0, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0749 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .gapLower 2 2 (![1, 4, 5, 0, 3]), .triangle 11 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0750 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 2 3 (![1, 4, 5, 0, 3]), .triangle 18 1, .triangle 11 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0751 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 4, 5, 0, 3])]

def cycle0752 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 4, 5, 0, 3]), .triangle 4 0]

def cycle0753 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0754 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0755 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0756 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0757 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 0, .triangle 12 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0758 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 12 0, .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0759 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .triangle 18 1, .gapLower 2 0 (![4, 5, 1, 0, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0760 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .gapLower 2 1 (![4, 5, 1, 0, 3]), .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0761 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 2 (![4, 5, 1, 0, 3]), .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0762 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 1 5, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 3 (![4, 5, 1, 0, 3]), .triangle 12 2, .triangle 15 1, .gapLower 1 0 (![4, 5, 2, 0, 3]), .gapLower 1 5 (![4, 5, 2, 0, 3]), .triangle 1 0]

def cycle0763 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![4, 5, 1, 0, 3])]

def cycle0764 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 1, 0, 3]), .triangle 4 0]

def cycle0765 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0766 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 2, .gapLower 1 1 (![4, 5, 2, 0, 3]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0767 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2 (![4, 5, 2, 0, 3]), .triangle 15 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0768 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![4, 5, 2, 0, 3]), .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0769 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![4, 5, 2, 0, 3])]

def cycle0770 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![4, 5, 2, 0, 3]), .triangle 1 0]

def cycle0771 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0772 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 1 (![4, 5, 2, 1, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0773 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![4, 5, 2, 1, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0774 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 5, 2, 1, 3]), .triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0775 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 5, 2, 1, 3])]

def cycle0776 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 5, 2, 1, 3]), .triangle 1 1]

def cycle0777 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 1 (![4, 5, 2, 1, 3]), .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0778 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![4, 5, 2, 1, 3]), .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0779 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 5, 2, 1, 3]), .triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0780 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 5, 2, 1, 3])]

def cycle0781 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 5, 2, 1, 3])]

def cycle0782 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 5, 2, 1, 3]), .triangle 4 1]

def cycle0783 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 5, 2, 1, 3]), .triangle 1 1]

def cycle0784 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 5, 2, 1, 3]), .gapLower 0 1 (![4, 5, 2, 1, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0785 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 5, 2, 1, 3]), .triangle 6 2, .gapLower 0 1 (![4, 5, 2, 1, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0786 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 1 (![4, 5, 2, 1, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 5, 2, 1, 3])]

def cycle0787 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 0 2, .triangle 6 2, .gapLower 0 1 (![4, 5, 2, 1, 3]), .corridorLower 0 4, .gapLower 0 5 (![4, 5, 2, 1, 3]), .triangle 1 1]

def cycle0788 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 5, 2, 1, 3]), .gapLower 0 2 (![4, 5, 2, 1, 3]), .triangle 9 1, .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0789 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![4, 5, 2, 1, 3]), .triangle 9 1, .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 5, 2, 1, 3])]

def cycle0790 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 5, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![4, 5, 2, 1, 3]), .corridorLower 0 5, .gapLower 0 5 (![4, 5, 2, 1, 3]), .triangle 1 1]

def cycle0791 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 5, 2, 1, 3]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 5, 2, 1, 3])]

def cycle0792 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 3 (![4, 5, 2, 1, 3]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 5, 2, 1, 3]), .triangle 1 1]

def cycle0793 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 5, 2, 1, 3]), .gapLower 0 4 (![4, 5, 2, 1, 3])]

def cycle0794 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .gapLower 2 1 (![1, 4, 5, 0, 3]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0795 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 4, 5, 0, 3])]

def cycle0796 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 3, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 4, 5, 0, 3]), .triangle 4 0]

def cycle0797 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 2, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0798 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0799 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![2, 3, 5, 4, 0]), .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 2, 3, 1]), .gapLower 0 5 (![4, 5, 2, 3, 1])]

def cycle0800 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 5, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (3), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 3 (![2, 4, 5, 3, 0]), .gapLower 5 1 (![3, 1, 2, 0, 4]), .corridorLower 3 5, .corridorUpper 2 3, .triangle 4 0, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0801 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 3, 0])]

def cycle0802 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 2, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0803 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 11 0, .triangle 12 0, .corridorLower 2 5, .gapLower 2 5 (![5, 1, 4, 0, 3]), .triangle 4 0]

def cycle0804 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .triangle 18 1, .gapLower 2 0 (![4, 5, 1, 0, 3]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0805 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .gapLower 2 1 (![4, 5, 1, 0, 3]), .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0806 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 2 2 (![4, 5, 1, 0, 3]), .corridorLower 2 5, .thetaOrder 1, .corridorUpper 0 1]

def cycle0807 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (-2), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 3 (![4, 5, 1, 0, 3]), .triangle 12 2, .triangle 15 1, .gapLower 1 0 (![4, 5, 2, 3, 0]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0808 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![4, 5, 1, 0, 3])]

def cycle0809 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 3, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 1, 0, 3]), .triangle 4 0]

def cycle0810 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![4, 5, 2, 3, 0]), .triangle 10 1, .triangle 11 0, .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 2, 3, 1]), .gapLower 0 5 (![4, 5, 2, 3, 1])]

def cycle0811 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 2, .gapLower 1 1 (![4, 5, 2, 3, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0812 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 1 2 (![4, 5, 2, 3, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0813 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 3 (![4, 5, 2, 3, 0]), .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0814 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 1 4 (![4, 5, 2, 3, 0]), .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0815 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![4, 5, 2, 3, 0])]

def cycle0816 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![5, 4, 2, 3, 0]), .triangle 10 1, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 2, 3, 1]), .gapLower 0 5 (![4, 5, 2, 3, 1])]

def cycle0817 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 1 (![4, 5, 2, 3, 1]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0818 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 5, 2, 3, 1]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0819 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![4, 5, 2, 3, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0820 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 5, 2, 3, 1]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0821 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 5, 2, 3, 1])]

def cycle0822 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 1 (![4, 5, 2, 3, 1]), .gapLower 0 0 (![4, 5, 2, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0823 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 5, 2, 3, 1]), .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0824 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![4, 5, 2, 3, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0825 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 5, 2, 3, 1]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0826 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![4, 5, 2, 3, 1])]

def cycle0827 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 5, 2, 3, 1])]

def cycle0828 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 2, 3, 1]), .gapLower 0 5 (![4, 5, 2, 3, 1])]

def cycle0829 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 5, 2, 3, 1]), .gapLower 0 1 (![4, 5, 2, 3, 1]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0830 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![4, 5, 2, 3, 1]), .triangle 6 2, .gapLower 0 1 (![4, 5, 2, 3, 1]), .triangle 5 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0831 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 5, 2, 3, 1]), .triangle 4 1, .triangle 6 2, .gapLower 0 1 (![4, 5, 2, 3, 1]), .triangle 5 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0832 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 6 2, .gapLower 0 1 (![4, 5, 2, 3, 1]), .corridorLower 0 4, .gapLower 0 5 (![4, 5, 2, 3, 1])]

def cycle0833 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 2 (![4, 5, 2, 3, 1]), .corridorLower 0 5, .gapLower 0 5 (![4, 5, 2, 3, 1])]

def cycle0834 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 0 4 (![4, 5, 2, 3, 1]), .gapLower 0 3 (![4, 5, 2, 3, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0835 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![4, 5, 2, 3, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 5, 2, 3, 1])]

def cycle0836 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![4, 5, 2, 3, 1]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 5, 2, 3, 1])]

def cycle0837 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 2, .triangle 3 0]

def cycle0838 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 5, 0, 3]), .gapLower 1 0 (![2, 4, 5, 0, 3]), .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0839 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 18 0, .triangle 11 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0840 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 18 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 5, 0, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0841 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0842 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 5, 0, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0843 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (0), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 11 2, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0844 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 0, .gapLower 1 0 (![4, 2, 5, 0, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0845 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![4, 2, 5, 0, 3]), .gapLower 1 1 (![4, 2, 5, 0, 3]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0846 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![4, 2, 5, 0, 3]), .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0847 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![4, 2, 5, 0, 3])]

def cycle0848 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 2, 1, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![4, 2, 5, 0, 3]), .triangle 1 0]

def cycle0849 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 0, .gapLower 1 0 (![4, 5, 2, 0, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0850 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 1 (![4, 5, 2, 0, 3]), .corridorLower 1 4, .gapLower 1 5 (![4, 5, 2, 0, 3]), .triangle 1 0]

def cycle0851 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![4, 5, 2, 0, 3])]

def cycle0852 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 15 0, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 2, 0, 3]), .triangle 1 0]

def cycle0853 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 11 2, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0854 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 1 (![5, 4, 2, 1, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0855 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 2, 1, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0856 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![5, 4, 2, 1, 3]), .triangle 5 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0857 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 4, 2, 1, 3])]

def cycle0858 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 2, 1, 3]), .triangle 1 1]

def cycle0859 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 1 (![5, 4, 2, 1, 3]), .gapLower 0 0 (![5, 4, 2, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0860 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 2, 1, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0861 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![5, 4, 2, 1, 3]), .triangle 5 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0862 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 4, 2, 1, 3])]

def cycle0863 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 4, 2, 1, 3]), .triangle 4 1]

def cycle0864 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 2, 1, 3]), .triangle 1 1]

def cycle0865 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![5, 4, 2, 1, 3]), .gapLower 0 1 (![5, 4, 2, 1, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0866 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 0 3 (![5, 4, 2, 1, 3]), .triangle 5 2, .gapLower 0 1 (![5, 4, 2, 1, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0867 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 1 (![5, 4, 2, 1, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 4, 2, 1, 3])]

def cycle0868 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .gapLower 0 1 (![5, 4, 2, 1, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0869 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![5, 4, 2, 1, 3]), .gapLower 0 2 (![5, 4, 2, 1, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0870 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2 (![5, 4, 2, 1, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 4, 2, 1, 3])]

def cycle0871 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3 (![5, 4, 2, 1, 3]), .triangle 5 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 4, 2, 1, 3])]

def cycle0872 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 4, 2, 1, 3]), .gapLower 0 4 (![5, 4, 2, 1, 3])]

def cycle0873 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0874 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0875 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0876 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0877 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 18 0, .triangle 11 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0878 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 18 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0879 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0880 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 5 0, .triangle 11 2, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0881 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 4 0]

def cycle0882 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 4 (![4, 2, 3, 0, 5])]

def cycle0883 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 0, .gapLower 1 0 (![4, 2, 3, 5, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0884 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 3, .distance 1 2, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (0), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![4, 2, 3, 5, 0]), .triangle 10 1, .gapLower 1 1 (![4, 2, 3, 5, 0]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0885 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![4, 2, 3, 5, 0]), .gapLower 1 2 (![4, 2, 3, 5, 0]), .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0886 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![4, 2, 3, 5, 0]), .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0887 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 4 (![4, 2, 3, 5, 0]), .triangle 14 1, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0888 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 2, .triangle 9 0, .triangle 15 0, .corridorLower 1 4, .gapLower 1 5 (![4, 2, 3, 5, 0])]

def cycle0889 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 0, .gapLower 1 0 (![4, 2, 5, 3, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0890 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![4, 2, 5, 3, 0]), .gapLower 1 1 (![4, 2, 5, 3, 0]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0891 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![4, 2, 5, 3, 0]), .triangle 11 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0892 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (0), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 4 (![4, 2, 5, 3, 0]), .triangle 14 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .triangle 9 0, .triangle 15 0, .corridorLower 1 4, .corridorUpper 0 1]

def cycle0893 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 2, .triangle 9 0, .triangle 15 0, .corridorLower 1 4, .gapLower 1 5 (![4, 2, 5, 3, 0])]

def cycle0894 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 0, .gapLower 1 0 (![4, 5, 2, 3, 0]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0895 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 15 2, .gapLower 1 1 (![4, 5, 2, 3, 0]), .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0896 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 2, .triangle 9 0, .triangle 15 0, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 2, 3, 0])]

def cycle0897 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 2, .triangle 15 0, .triangle 18 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0898 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 5 0, .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0899 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![(0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 11 2, .gapLower 1 1 (![5, 4, 2, 3, 0]), .triangle 15 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 0]

def cycle0900 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 2 (![5, 4, 2, 3, 0]), .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 0]

def cycle0901 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 3 (![5, 4, 2, 3, 0]), .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0902 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 1 4 (![5, 4, 2, 3, 0]), .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0903 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![5, 4, 2, 3, 0])]

def cycle0904 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 1 (![5, 4, 2, 3, 1]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0905 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 2, 3, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0906 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 2, .gapLower 0 3 (![5, 4, 2, 3, 1])]

def cycle0907 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 4, 2, 3, 1]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0908 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 2, 3, 1])]

def cycle0909 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 1 (![5, 4, 2, 3, 1]), .gapLower 0 0 (![5, 4, 2, 3, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0910 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 2, 3, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0911 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 2, .gapLower 0 3 (![5, 4, 2, 3, 1])]

def cycle0912 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 0 4 (![5, 4, 2, 3, 1]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def cycle0913 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 0, .triangle 11 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![5, 4, 2, 3, 1])]

def cycle0914 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 2, 3, 1])]

def cycle0915 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .triangle 5 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 2, 3, 1]), .gapLower 0 5 (![5, 4, 2, 3, 1])]

def cycle0916 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 2, 3, 1]), .gapLower 0 1 (![5, 4, 2, 3, 1]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0917 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 1 (![5, 4, 2, 3, 1]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 2, .gapLower 0 3 (![5, 4, 2, 3, 1])]

def cycle0918 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (-1), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 4 (![5, 4, 2, 3, 1]), .triangle 4 1, .triangle 5 2, .gapLower 0 1 (![5, 4, 2, 3, 1]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 1, .corridorUpper 0 1]

def cycle0919 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 5 2, .gapLower 0 1 (![5, 4, 2, 3, 1]), .corridorLower 0 5, .gapLower 0 5 (![5, 4, 2, 3, 1])]

def cycle0920 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 2 (![5, 4, 2, 3, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 2, .gapLower 0 3 (![5, 4, 2, 3, 1])]

def cycle0921 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 4, 2, 3, 1]), .gapLower 0 3 (![5, 4, 2, 3, 1]), .triangle 5 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0922 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 3 (![5, 4, 2, 3, 1]), .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 2, 3, 1])]

def cycle0923 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 4 (![5, 4, 2, 3, 1]), .triangle 4 1, .triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 2, 3, 1])]

def cycle0924 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 2, .triangle 1 0]

def cycle0925 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 0 (![3, 2, 1, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0926 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 0 (![3, 2, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0927 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![3, 2, 1, 4, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0928 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 4, 5]), .triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0929 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![3, 2, 1, 4, 5])]

def cycle0930 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 1, 4, 5]), .triangle 5 1]

def cycle0931 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 4, 5]), .triangle 6 1]

def cycle0932 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![3, 2, 1, 4, 5]), .gapLower 0 0 (![3, 2, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0933 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 4, 5]), .triangle 4 2, .gapLower 0 0 (![3, 2, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0934 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 0 (![3, 2, 1, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![3, 2, 1, 4, 5])]

def cycle0935 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 1, 4, 5]), .triangle 5 1]

def cycle0936 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 1, 4, 5]), .triangle 2 1]

def cycle0937 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, true, true] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 4, 5]), .triangle 9 1, .triangle 2 1]

def cycle0938 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 4, 5]), .triangle 9 1, .triangle 2 1]

def cycle0939 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 4, 5]), .gapLower 0 1 (![3, 2, 1, 4, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0940 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![3, 2, 1, 4, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![3, 2, 1, 4, 5])]

def cycle0941 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![3, 2, 1, 4, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 1, 4, 5]), .triangle 2 1]

def cycle0942 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![3, 2, 1, 4, 5]), .corridorLower 0 3, .gapLower 0 5 (![3, 2, 1, 4, 5]), .triangle 9 1, .triangle 2 1]

def cycle0943 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 4, 5]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![3, 2, 1, 4, 5])]

def cycle0944 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 4, 5]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 1, 4, 5]), .triangle 2 1]

def cycle0945 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 4, 5]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 4, 5]), .triangle 9 1, .triangle 2 1]

def cycle0946 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 2, 1, 4, 5]), .gapLower 0 3 (![3, 2, 1, 4, 5])]

def cycle0947 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 4, 5]), .triangle 9 1, .gapLower 0 3 (![3, 2, 1, 4, 5])]

def cycle0948 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 4, 5]), .gapLower 0 4 (![3, 2, 1, 4, 5]), .triangle 5 1]

def cycle0949 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 3, 0, 5, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0950 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .gapLower 1 1 (![2, 3, 0, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0951 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .gapLower 2 0 (![1, 3, 0, 5, 4]), .gapLower 2 5 (![1, 3, 0, 5, 4]), .triangle 5 0]

def cycle0952 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 1 (![1, 3, 0, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0953 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 2 (![1, 3, 0, 5, 4]), .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0954 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 2, .gapLower 2 3 (![1, 3, 0, 5, 4])]

def cycle0955 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 1, 5, 4]), .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![1, 3, 0, 5, 4]), .triangle 6 0]

def cycle0956 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 1, 5, 4]), .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 3, 0, 5, 4]), .triangle 5 0]

def cycle0957 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 3 (![2, 3, 0, 5, 4])]

def cycle0958 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 5, 4]), .triangle 4 2, .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 0, 5, 4]), .triangle 3 0]

def cycle0959 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 5, 4]), .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 0, 5, 4]), .triangle 2 0]

def cycle0960 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .gapLower 2 0 (![3, 1, 0, 5, 4]), .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0961 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 1 (![3, 1, 0, 5, 4]), .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0962 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 2 (![3, 1, 0, 5, 4]), .triangle 10 2, .gapLower 1 0 (![3, 2, 0, 5, 4]), .gapLower 1 5 (![3, 2, 0, 5, 4]), .triangle 2 0]

def cycle0963 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 2, .gapLower 2 3 (![3, 1, 0, 5, 4])]

def cycle0964 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 1, 5, 4]), .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![3, 1, 0, 5, 4]), .triangle 6 0]

def cycle0965 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 1, 5, 4]), .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 1, 0, 5, 4]), .triangle 5 0]

def cycle0966 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 1 (![3, 2, 0, 5, 4]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0967 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2 (![3, 2, 0, 5, 4]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0968 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 3 (![3, 2, 0, 5, 4])]

def cycle0969 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 5, 4]), .triangle 4 2, .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![3, 2, 0, 5, 4]), .triangle 3 0]

def cycle0970 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![3, 2, 0, 5, 4]), .triangle 2 0]

def cycle0971 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![3, 2, 1, 5, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0972 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 5, 4]), .triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0973 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![3, 2, 1, 5, 4])]

def cycle0974 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 1, 5, 4]), .triangle 6 1]

def cycle0975 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 5, 4]), .triangle 5 1]

def cycle0976 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![3, 2, 1, 5, 4]), .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0977 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 5, 4]), .triangle 4 2, .gapLower 0 0 (![3, 2, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0978 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![3, 2, 1, 5, 4])]

def cycle0979 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![3, 2, 1, 5, 4])]

def cycle0980 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 1, 5, 4]), .triangle 6 1]

def cycle0981 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 1, 5, 4]), .triangle 3 1]

def cycle0982 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 5, 4]), .triangle 2 1]

def cycle0983 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 5, 4]), .triangle 2 1]

def cycle0984 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 5, 4]), .gapLower 0 1 (![3, 2, 1, 5, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0985 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![3, 2, 1, 5, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![3, 2, 1, 5, 4])]

def cycle0986 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![3, 2, 1, 5, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 1, 5, 4]), .triangle 3 1]

def cycle0987 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 1 (![3, 2, 1, 5, 4]), .corridorLower 0 3, .gapLower 0 5 (![3, 2, 1, 5, 4]), .triangle 2 1]

def cycle0988 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 5, 4]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![3, 2, 1, 5, 4])]

def cycle0989 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 5, 4]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 1, 5, 4]), .triangle 3 1]

def cycle0990 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 2 (![3, 2, 1, 5, 4]), .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 5, 4]), .triangle 2 1]

def cycle0991 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 1, 5, 4]), .gapLower 0 3 (![3, 2, 1, 5, 4])]

def cycle0992 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, false, true, false] }
  origin := ![.triangle 0 2, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 5, 4]), .triangle 9 2, .gapLower 0 3 (![3, 2, 1, 5, 4])]

def cycle0993 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 1, 5, 4]), .gapLower 0 4 (![3, 2, 1, 5, 4]), .triangle 6 1]

def cycle0994 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 10 0, .gapLower 1 0 (![2, 3, 5, 0, 4]), .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0995 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 10 2, .gapLower 1 1 (![2, 3, 5, 0, 4]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0996 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 5 0]

def cycle0997 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 10 0, .gapLower 2 0 (![1, 3, 0, 5, 4]), .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0998 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .gapLower 2 1 (![1, 3, 0, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0999 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![1, 3, 0, 5, 4]), .triangle 10 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1000 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 2, .gapLower 2 3 (![1, 3, 0, 5, 4])]

def cycle1001 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 5, 1, 4]), .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![1, 3, 0, 5, 4]), .triangle 6 0]

def cycle1002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 3, 0, 5, 4]), .triangle 5 0]

def cycle1003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 2, .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle1004 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 10 0, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle1005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.triangle 4 0, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 2 (![3, 2, 5, 1, 4])]

def cycle1006 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 10 0, .triangle 12 0, .triangle 6 0]

def cycle1007 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 10 0, .gapLower 2 0 (![3, 1, 0, 5, 4]), .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1008 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 1 (![3, 1, 0, 5, 4]), .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![3, 1, 0, 5, 4]), .triangle 10 2, .gapLower 1 0 (![3, 2, 5, 0, 4]), .gapLower 1 5 (![3, 2, 5, 0, 4]), .triangle 2 0]

def cycle1010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 4 2, .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 2, .gapLower 2 3 (![3, 1, 0, 5, 4])]

def cycle1011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 5, 1, 4]), .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![3, 1, 0, 5, 4]), .triangle 6 0]

def cycle1012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 2, 5, 1, 4]), .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 1, 0, 5, 4]), .triangle 5 0]

def cycle1013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 1 1 (![3, 2, 5, 0, 4]), .corridorLower 1 3, .gapLower 1 5 (![3, 2, 5, 0, 4]), .triangle 2 0]

def cycle1014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 2 (![3, 2, 5, 0, 4]), .triangle 10 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1015 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 3 (![3, 2, 5, 0, 4]), .triangle 12 1, .triangle 10 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1016 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 2, .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![3, 2, 5, 0, 4])]

def cycle1017 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 2, .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 2, 5, 0, 4]), .triangle 2 0]

def cycle1018 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 2, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 1 (![3, 2, 5, 1, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1020 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![3, 2, 5, 1, 4]), .triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1021 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 2, 5, 1, 4]), .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1022 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 2, 5, 1, 4])]

def cycle1023 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 2, 5, 1, 4]), .triangle 2 1]

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
  | 960 => some cycle0960
  | 961 => some cycle0961
  | 962 => some cycle0962
  | 963 => some cycle0963
  | 964 => some cycle0964
  | 965 => some cycle0965
  | 966 => some cycle0966
  | 967 => some cycle0967
  | 968 => some cycle0968
  | 969 => some cycle0969
  | 970 => some cycle0970
  | 971 => some cycle0971
  | 972 => some cycle0972
  | 973 => some cycle0973
  | 974 => some cycle0974
  | 975 => some cycle0975
  | 976 => some cycle0976
  | 977 => some cycle0977
  | 978 => some cycle0978
  | 979 => some cycle0979
  | 980 => some cycle0980
  | 981 => some cycle0981
  | 982 => some cycle0982
  | 983 => some cycle0983
  | 984 => some cycle0984
  | 985 => some cycle0985
  | 986 => some cycle0986
  | 987 => some cycle0987
  | 988 => some cycle0988
  | 989 => some cycle0989
  | 990 => some cycle0990
  | 991 => some cycle0991
  | 992 => some cycle0992
  | 993 => some cycle0993
  | 994 => some cycle0994
  | 995 => some cycle0995
  | 996 => some cycle0996
  | 997 => some cycle0997
  | 998 => some cycle0998
  | 999 => some cycle0999
  | 1000 => some cycle1000
  | 1001 => some cycle1001
  | 1002 => some cycle1002
  | 1003 => some cycle1003
  | 1004 => some cycle1004
  | 1005 => some cycle1005
  | 1006 => some cycle1006
  | 1007 => some cycle1007
  | 1008 => some cycle1008
  | 1009 => some cycle1009
  | 1010 => some cycle1010
  | 1011 => some cycle1011
  | 1012 => some cycle1012
  | 1013 => some cycle1013
  | 1014 => some cycle1014
  | 1015 => some cycle1015
  | 1016 => some cycle1016
  | 1017 => some cycle1017
  | 1018 => some cycle1018
  | 1019 => some cycle1019
  | 1020 => some cycle1020
  | 1021 => some cycle1021
  | 1022 => some cycle1022
  | 1023 => some cycle1023
  | _ => none

def nodes : NodeLibrary
  | 0 => some (.positive 1 (![7677, 7678, 7644, 7645, 7646, 7679]))
  | 1 => some (.triangle 18 7676 7680)
  | 2 => some (.triangle 16 7672 7681)
  | 3 => some (.positive 0 (![7659, 7660, 7661, 7662, 7663, 7682]))
  | 4 => some (.leaf 5001)
  | 5 => some (.triangle 15 7683 7684)
  | 6 => some (.triangle 14 7685 5170)
  | 7 => some (.leaf 5002)
  | 8 => some (.triangle 13 7686 7687)
  | 9 => some (.leaf 5003)
  | 10 => some (.triangle 12 7688 7689)
  | 11 => some (.leaf 5004)
  | 12 => some (.triangle 11 7690 7691)
  | 13 => some (.leaf 5005)
  | 14 => some (.triangle 10 7692 7693)
  | 15 => some (.leaf 5006)
  | 16 => some (.leaf 5007)
  | 17 => some (.leaf 5008)
  | 18 => some (.leaf 5009)
  | 19 => some (.leaf 5010)
  | 20 => some (.leaf 5011)
  | 21 => some (.leaf 5012)
  | 22 => some (.leaf 5013)
  | 23 => some (.leaf 5014)
  | 24 => some (.leaf 5015)
  | 25 => some (.heavy (![7575, 7576, 7577, 7578, 7579, 7580, 7581, 7582, 7612, 7658, 7694, 7695, 7696, 7697, 7698, 7699, 7700, 7701, 7702, 7703, 7704]))
  | 26 => some (.triangle 3 7562 7705)
  | 27 => some (.leaf 5016)
  | 28 => some (.leaf 5017)
  | 29 => some (.leaf 5018)
  | 30 => some (.leaf 5019)
  | 31 => some (.leaf 5020)
  | 32 => some (.leaf 5021)
  | 33 => some (.leaf 5022)
  | 34 => some (.triangle 16 7712 7713)
  | 35 => some (.leaf 5023)
  | 36 => some (.positive 0 (![7708, 7709, 7710, 7711, 7714, 7715]))
  | 37 => some (.triangle 3 7707 7716)
  | 38 => some (.leaf 5024)
  | 39 => some (.leaf 5025)
  | 40 => some (.leaf 5026)
  | 41 => some (.leaf 5027)
  | 42 => some (.leaf 5028)
  | 43 => some (.positive 0 (![7714, 7718, 7719, 7720, 7721, 7722]))
  | 44 => some (.triangle 15 7717 7723)
  | 45 => some (.triangle 14 7724 5170)
  | 46 => some (.triangle 13 7725 5358)
  | 47 => some (.triangle 12 7726 6528)
  | 48 => some (.triangle 11 7727 6780)
  | 49 => some (.triangle 10 7728 7184)
  | 50 => some (.leaf 5029)
  | 51 => some (.leaf 5030)
  | 52 => some (.leaf 5031)
  | 53 => some (.leaf 5032)
  | 54 => some (.leaf 5033)
  | 55 => some (.leaf 5034)
  | 56 => some (.leaf 5035)
  | 57 => some (.leaf 5036)
  | 58 => some (.leaf 5037)
  | 59 => some (.leaf 5038)
  | 60 => some (.leaf 5039)
  | 61 => some (.leaf 5040)
  | 62 => some (.leaf 5041)
  | 63 => some (.positive 1 (![7737, 7738, 7739, 7740, 7741, 7742]))
  | 64 => some (.triangle 18 1165 7743)
  | 65 => some (.leaf 5042)
  | 66 => some (.triangle 17 7744 7745)
  | 67 => some (.leaf 5043)
  | 68 => some (.triangle 16 7746 7747)
  | 69 => some (.leaf 5044)
  | 70 => some (.positive 0 (![7736, 7709, 7710, 7711, 7748, 7749]))
  | 71 => some (.triangle 3 7707 7750)
  | 72 => some (.leaf 5045)
  | 73 => some (.leaf 5046)
  | 74 => some (.leaf 5047)
  | 75 => some (.positive 0 (![7752, 7753, 7719, 7720, 7721, 7754]))
  | 76 => some (.triangle 15 7751 7755)
  | 77 => some (.leaf 5048)
  | 78 => some (.triangle 14 7756 7757)
  | 79 => some (.leaf 5049)
  | 80 => some (.triangle 13 7758 7759)
  | 81 => some (.leaf 5050)
  | 82 => some (.triangle 12 7760 7761)
  | 83 => some (.leaf 5051)
  | 84 => some (.triangle 11 7762 7763)
  | 85 => some (.triangle 10 7764 7184)
  | 86 => some (.leaf 5052)
  | 87 => some (.leaf 5053)
  | 88 => some (.leaf 5054)
  | 89 => some (.leaf 5055)
  | 90 => some (.positive 0 (![7767, 7768, 7719, 7720, 7721, 7769]))
  | 91 => some (.triangle 15 7766 7770)
  | 92 => some (.triangle 14 7771 5170)
  | 93 => some (.triangle 13 7772 5358)
  | 94 => some (.triangle 12 7773 6528)
  | 95 => some (.leaf 5056)
  | 96 => some (.triangle 11 7774 7775)
  | 97 => some (.triangle 10 7776 7184)
  | 98 => some (.leaf 5057)
  | 99 => some (.leaf 5058)
  | 100 => some (.leaf 5059)
  | 101 => some (.triangle 15 7779 7780)
  | 102 => some (.triangle 14 7781 5170)
  | 103 => some (.leaf 5060)
  | 104 => some (.triangle 13 7782 7783)
  | 105 => some (.leaf 5061)
  | 106 => some (.triangle 12 7784 7785)
  | 107 => some (.leaf 5062)
  | 108 => some (.triangle 11 7786 7787)
  | 109 => some (.leaf 5063)
  | 110 => some (.triangle 10 7788 7789)
  | 111 => some (.leaf 5064)
  | 112 => some (.leaf 5065)
  | 113 => some (.leaf 5066)
  | 114 => some (.leaf 5067)
  | 115 => some (.leaf 5068)
  | 116 => some (.leaf 5069)
  | 117 => some (.leaf 5070)
  | 118 => some (.leaf 5071)
  | 119 => some (.leaf 5072)
  | 120 => some (.leaf 5073)
  | 121 => some (.heavy (![7729, 7730, 7731, 7732, 7733, 7734, 7735, 7765, 7777, 7778, 7790, 7791, 7792, 7793, 7794, 7795, 7796, 7797, 7798, 7799, 7800]))
  | 122 => some (.triangle 9 7706 7801)
  | 123 => some (.triangle 2 7462 7802)
  | 124 => some (.leaf 5074)
  | 125 => some (.leaf 5075)
  | 126 => some (.leaf 5076)
  | 127 => some (.leaf 5077)
  | 128 => some (.leaf 5078)
  | 129 => some (.triangle 16 7807 7808)
  | 130 => some (.leaf 5079)
  | 131 => some (.leaf 5080)
  | 132 => some (.positive 0 (![7804, 7805, 7806, 7809, 7810, 7811]))
  | 133 => some (.triangle 3 5667 7812)
  | 134 => some (.leaf 5081)
  | 135 => some (.triangle 16 7807 7814)
  | 136 => some (.leaf 5082)
  | 137 => some (.leaf 5083)
  | 138 => some (.leaf 5084)
  | 139 => some (.leaf 5085)
  | 140 => some (.leaf 5086)
  | 141 => some (.positive 0 (![7815, 7816, 7817, 7818, 7819, 7820]))
  | 142 => some (.triangle 14 7813 7821)
  | 143 => some (.triangle 12 7822 6528)
  | 144 => some (.triangle 10 7823 7184)
  | 145 => some (.leaf 5087)
  | 146 => some (.leaf 5088)
  | 147 => some (.leaf 5089)
  | 148 => some (.leaf 5090)
  | 149 => some (.leaf 5091)
  | 150 => some (.leaf 5092)
  | 151 => some (.leaf 5093)
  | 152 => some (.leaf 5094)
  | 153 => some (.leaf 5095)
  | 154 => some (.leaf 5096)
  | 155 => some (.triangle 14 7833 7834)
  | 156 => some (.triangle 12 7835 6528)
  | 157 => some (.triangle 10 7836 7184)
  | 158 => some (.leaf 5097)
  | 159 => some (.leaf 5098)
  | 160 => some (.triangle 14 7838 7839)
  | 161 => some (.triangle 12 7840 6528)
  | 162 => some (.triangle 10 7841 7184)
  | 163 => some (.leaf 5099)
  | 164 => some (.leaf 5100)
  | 165 => some (.leaf 5101)
  | 166 => some (.leaf 5102)
  | 167 => some (.leaf 5103)
  | 168 => some (.leaf 5104)
  | 169 => some (.leaf 5105)
  | 170 => some (.leaf 5106)
  | 171 => some (.leaf 5107)
  | 172 => some (.leaf 5108)
  | 173 => some (.heavy (![7824, 7825, 7826, 7827, 7828, 7829, 7830, 7831, 7832, 7837, 7842, 7843, 7844, 7845, 7846, 7847, 7848, 7849, 7850, 7851, 7852]))
  | 174 => some (.leaf 5109)
  | 175 => some (.leaf 5110)
  | 176 => some (.leaf 5111)
  | 177 => some (.leaf 5112)
  | 178 => some (.leaf 5113)
  | 179 => some (.leaf 5114)
  | 180 => some (.leaf 5115)
  | 181 => some (.triangle 16 7859 7860)
  | 182 => some (.leaf 5116)
  | 183 => some (.positive 0 (![7855, 7856, 7857, 7858, 7861, 7862]))
  | 184 => some (.triangle 3 7854 7863)
  | 185 => some (.leaf 5117)
  | 186 => some (.leaf 5118)
  | 187 => some (.leaf 5119)
  | 188 => some (.leaf 5120)
  | 189 => some (.leaf 5121)
  | 190 => some (.leaf 5122)
  | 191 => some (.positive 0 (![7865, 7866, 7867, 7868, 7869, 7870]))
  | 192 => some (.triangle 15 7864 7871)
  | 193 => some (.leaf 5123)
  | 194 => some (.triangle 16 7859 7873)
  | 195 => some (.leaf 5124)
  | 196 => some (.leaf 5125)
  | 197 => some (.leaf 5126)
  | 198 => some (.leaf 5127)
  | 199 => some (.leaf 5128)
  | 200 => some (.positive 0 (![7874, 7875, 7876, 7877, 7878, 7879]))
  | 201 => some (.triangle 14 7872 7880)
  | 202 => some (.triangle 13 7881 5358)
  | 203 => some (.triangle 12 7882 6528)
  | 204 => some (.triangle 11 7883 6780)
  | 205 => some (.triangle 10 7884 7184)
  | 206 => some (.leaf 5129)
  | 207 => some (.leaf 5130)
  | 208 => some (.leaf 5131)
  | 209 => some (.leaf 5132)
  | 210 => some (.leaf 5133)
  | 211 => some (.leaf 5134)
  | 212 => some (.leaf 5135)
  | 213 => some (.leaf 5136)
  | 214 => some (.leaf 5137)
  | 215 => some (.leaf 5138)
  | 216 => some (.leaf 5139)
  | 217 => some (.triangle 14 7895 7896)
  | 218 => some (.leaf 5140)
  | 219 => some (.triangle 13 7897 7898)
  | 220 => some (.leaf 5141)
  | 221 => some (.triangle 12 7899 7900)
  | 222 => some (.leaf 5142)
  | 223 => some (.triangle 11 7901 7902)
  | 224 => some (.leaf 5143)
  | 225 => some (.triangle 10 7903 7904)
  | 226 => some (.leaf 5144)
  | 227 => some (.leaf 5145)
  | 228 => some (.leaf 5146)
  | 229 => some (.leaf 5147)
  | 230 => some (.leaf 5148)
  | 231 => some (.leaf 5149)
  | 232 => some (.leaf 5150)
  | 233 => some (.leaf 5151)
  | 234 => some (.leaf 5152)
  | 235 => some (.leaf 5153)
  | 236 => some (.heavy (![7885, 7886, 7887, 7888, 7889, 7890, 7891, 7892, 7893, 7894, 7905, 7906, 7907, 7908, 7909, 7910, 7911, 7912, 7913, 7914, 7915]))
  | 237 => some (.triangle 2 7853 7916)
  | 238 => some (.triangle 8 7803 7917)
  | 239 => some (.leaf 5154)
  | 240 => some (.leaf 5155)
  | 241 => some (.leaf 5156)
  | 242 => some (.leaf 5157)
  | 243 => some (.leaf 5158)
  | 244 => some (.triangle 18 7922 7923)
  | 245 => some (.triangle 16 1426 7924)
  | 246 => some (.leaf 5159)
  | 247 => some (.leaf 5160)
  | 248 => some (.positive 0 (![7919, 7920, 7921, 7925, 7926, 7927]))
  | 249 => some (.triangle 2 5796 7928)
  | 250 => some (.leaf 5161)
  | 251 => some (.leaf 5162)
  | 252 => some (.leaf 5163)
  | 253 => some (.leaf 5164)
  | 254 => some (.leaf 5165)
  | 255 => some (.positive 0 (![7925, 7930, 7931, 7932, 7933, 7934]))
  | 256 => some (.triangle 13 7929 7935)
  | 257 => some (.triangle 11 7936 6780)
  | 258 => some (.triangle 10 7937 7184)
  | 259 => some (.leaf 5166)
  | 260 => some (.leaf 5167)
  | 261 => some (.leaf 5168)
  | 262 => some (.leaf 5169)
  | 263 => some (.leaf 5170)
  | 264 => some (.leaf 5171)
  | 265 => some (.leaf 5172)
  | 266 => some (.leaf 5173)
  | 267 => some (.leaf 5174)
  | 268 => some (.leaf 5175)
  | 269 => some (.triangle 13 7947 7948)
  | 270 => some (.triangle 11 7949 6780)
  | 271 => some (.triangle 10 7950 7184)
  | 272 => some (.leaf 5176)
  | 273 => some (.leaf 5177)
  | 274 => some (.triangle 13 7952 7953)
  | 275 => some (.triangle 11 7954 6780)
  | 276 => some (.triangle 10 7955 7184)
  | 277 => some (.leaf 5178)
  | 278 => some (.leaf 5179)
  | 279 => some (.leaf 5180)
  | 280 => some (.leaf 5181)
  | 281 => some (.leaf 5182)
  | 282 => some (.leaf 5183)
  | 283 => some (.leaf 5184)
  | 284 => some (.leaf 5185)
  | 285 => some (.leaf 5186)
  | 286 => some (.leaf 5187)
  | 287 => some (.heavy (![7938, 7939, 7940, 7941, 7942, 7943, 7944, 7945, 7946, 7951, 7956, 7957, 7958, 7959, 7960, 7961, 7962, 7963, 7964, 7965, 7966]))
  | 288 => some (.leaf 5188)
  | 289 => some (.leaf 5189)
  | 290 => some (.leaf 5190)
  | 291 => some (.leaf 5191)
  | 292 => some (.leaf 5192)
  | 293 => some (.triangle 18 7971 7972)
  | 294 => some (.triangle 16 1426 7973)
  | 295 => some (.leaf 5193)
  | 296 => some (.positive 0 (![7968, 7969, 7970, 7568, 7974, 7975]))
  | 297 => some (.leaf 5194)
  | 298 => some (.triangle 15 7976 7977)
  | 299 => some (.triangle 14 7978 5899)
  | 300 => some (.leaf 5195)
  | 301 => some (.leaf 5196)
  | 302 => some (.leaf 5197)
  | 303 => some (.leaf 5198)
  | 304 => some (.leaf 5199)
  | 305 => some (.positive 0 (![7974, 7980, 7981, 7982, 7983, 7984]))
  | 306 => some (.triangle 14 7985 5170)
  | 307 => some (.leaf 5200)
  | 308 => some (.triangle 15 7986 7987)
  | 309 => some (.triangle 13 7979 7988)
  | 310 => some (.triangle 12 7989 6528)
  | 311 => some (.triangle 11 7990 6780)
  | 312 => some (.triangle 10 7991 7184)
  | 313 => some (.leaf 5201)
  | 314 => some (.leaf 5202)
  | 315 => some (.leaf 5203)
  | 316 => some (.leaf 5204)
  | 317 => some (.leaf 5205)
  | 318 => some (.leaf 5206)
  | 319 => some (.leaf 5207)
  | 320 => some (.leaf 5208)
  | 321 => some (.leaf 5209)
  | 322 => some (.leaf 5210)
  | 323 => some (.leaf 5211)
  | 324 => some (.triangle 13 8002 8003)
  | 325 => some (.leaf 5212)
  | 326 => some (.triangle 12 8004 8005)
  | 327 => some (.leaf 5213)
  | 328 => some (.triangle 11 8006 8007)
  | 329 => some (.leaf 5214)
  | 330 => some (.triangle 10 8008 8009)
  | 331 => some (.leaf 5215)
  | 332 => some (.leaf 5216)
  | 333 => some (.leaf 5217)
  | 334 => some (.leaf 5218)
  | 335 => some (.leaf 5219)
  | 336 => some (.leaf 5220)
  | 337 => some (.leaf 5221)
  | 338 => some (.leaf 5222)
  | 339 => some (.leaf 5223)
  | 340 => some (.leaf 5224)
  | 341 => some (.heavy (![7992, 7993, 7994, 7995, 7996, 7997, 7998, 7999, 8000, 8001, 8010, 8011, 8012, 8013, 8014, 8015, 8016, 8017, 8018, 8019, 8020]))
  | 342 => some (.triangle 3 7967 8021)
  | 343 => some (.leaf 5225)
  | 344 => some (.leaf 5226)
  | 345 => some (.leaf 5227)
  | 346 => some (.leaf 5228)
  | 347 => some (.leaf 5229)
  | 348 => some (.leaf 5230)
  | 349 => some (.leaf 5231)
  | 350 => some (.triangle 18 8028 8029)
  | 351 => some (.triangle 16 1426 8030)
  | 352 => some (.leaf 5232)
  | 353 => some (.positive 0 (![8024, 8025, 8026, 8027, 8031, 8032]))
  | 354 => some (.triangle 3 8023 8033)
  | 355 => some (.leaf 5233)
  | 356 => some (.triangle 15 8034 8035)
  | 357 => some (.triangle 2 5796 8036)
  | 358 => some (.leaf 5234)
  | 359 => some (.triangle 14 8037 8038)
  | 360 => some (.leaf 5235)
  | 361 => some (.leaf 5236)
  | 362 => some (.leaf 5237)
  | 363 => some (.leaf 5238)
  | 364 => some (.leaf 5239)
  | 365 => some (.leaf 5240)
  | 366 => some (.positive 0 (![8031, 8041, 8042, 8043, 8044, 8045]))
  | 367 => some (.triangle 14 8040 8046)
  | 368 => some (.leaf 5241)
  | 369 => some (.triangle 15 8047 8048)
  | 370 => some (.triangle 13 8039 8049)
  | 371 => some (.triangle 12 8050 6528)
  | 372 => some (.triangle 11 8051 6780)
  | 373 => some (.triangle 10 8052 7184)
  | 374 => some (.leaf 5242)
  | 375 => some (.leaf 5243)
  | 376 => some (.leaf 5244)
  | 377 => some (.leaf 5245)
  | 378 => some (.leaf 5246)
  | 379 => some (.leaf 5247)
  | 380 => some (.leaf 5248)
  | 381 => some (.leaf 5249)
  | 382 => some (.leaf 5250)
  | 383 => some (.positive 0 (![8061, 8041, 8042, 8043, 8044, 8062]))
  | 384 => some (.triangle 14 8040 8063)
  | 385 => some (.leaf 5251)
  | 386 => some (.triangle 15 8064 8065)
  | 387 => some (.triangle 13 8060 8066)
  | 388 => some (.leaf 5252)
  | 389 => some (.triangle 12 8067 8068)
  | 390 => some (.triangle 11 8069 6780)
  | 391 => some (.triangle 10 8070 7184)
  | 392 => some (.leaf 5253)
  | 393 => some (.leaf 5254)
  | 394 => some (.leaf 5255)
  | 395 => some (.leaf 5256)
  | 396 => some (.positive 0 (![8074, 8041, 8042, 8043, 8044, 8075]))
  | 397 => some (.triangle 14 8073 8076)
  | 398 => some (.leaf 5257)
  | 399 => some (.triangle 15 8077 8078)
  | 400 => some (.triangle 13 8072 8079)
  | 401 => some (.triangle 12 8080 6528)
  | 402 => some (.triangle 11 8081 6780)
  | 403 => some (.triangle 10 8082 7184)
  | 404 => some (.leaf 5258)
  | 405 => some (.leaf 5259)
  | 406 => some (.leaf 5260)
  | 407 => some (.triangle 13 8085 8086)
  | 408 => some (.leaf 5261)
  | 409 => some (.triangle 12 8087 8088)
  | 410 => some (.leaf 5262)
  | 411 => some (.triangle 11 8089 8090)
  | 412 => some (.leaf 5263)
  | 413 => some (.triangle 10 8091 8092)
  | 414 => some (.leaf 5264)
  | 415 => some (.leaf 5265)
  | 416 => some (.leaf 5266)
  | 417 => some (.leaf 5267)
  | 418 => some (.leaf 5268)
  | 419 => some (.leaf 5269)
  | 420 => some (.leaf 5270)
  | 421 => some (.leaf 5271)
  | 422 => some (.leaf 5272)
  | 423 => some (.leaf 5273)
  | 424 => some (.heavy (![8053, 8054, 8055, 8056, 8057, 8058, 8059, 8071, 8083, 8084, 8093, 8094, 8095, 8096, 8097, 8098, 8099, 8100, 8101, 8102, 8103]))
  | 425 => some (.triangle 8 8022 8104)
  | 426 => some (.leaf 5274)
  | 427 => some (.leaf 5275)
  | 428 => some (.leaf 5276)
  | 429 => some (.leaf 5277)
  | 430 => some (.leaf 5278)
  | 431 => some (.leaf 5279)
  | 432 => some (.leaf 5280)
  | 433 => some (.leaf 5281)
  | 434 => some (.triangle 19 8112 8113)
  | 435 => some (.leaf 5282)
  | 436 => some (.leaf 5283)
  | 437 => some (.leaf 5284)
  | 438 => some (.leaf 5285)
  | 439 => some (.positive 1 (![8111, 8114, 8115, 8116, 8117, 8118]))
  | 440 => some (.triangle 18 1165 8119)
  | 441 => some (.triangle 16 1426 8120)
  | 442 => some (.leaf 5286)
  | 443 => some (.positive 0 (![8107, 8108, 8109, 8110, 8121, 8122]))
  | 444 => some (.triangle 3 8106 8123)
  | 445 => some (.leaf 5287)
  | 446 => some (.leaf 5288)
  | 447 => some (.leaf 5289)
  | 448 => some (.leaf 5290)
  | 449 => some (.leaf 5291)
  | 450 => some (.positive 0 (![8125, 8126, 8127, 8128, 7721, 8129]))
  | 451 => some (.triangle 15 8124 8130)
  | 452 => some (.triangle 2 5796 8131)
  | 453 => some (.triangle 14 8132 8038)
  | 454 => some (.leaf 5292)
  | 455 => some (.leaf 5293)
  | 456 => some (.leaf 5294)
  | 457 => some (.leaf 5295)
  | 458 => some (.leaf 5296)
  | 459 => some (.leaf 5297)
  | 460 => some (.positive 0 (![8135, 8136, 8137, 8138, 7983, 8139]))
  | 461 => some (.triangle 3 8134 8140)
  | 462 => some (.leaf 5298)
  | 463 => some (.leaf 5299)
  | 464 => some (.leaf 5300)
  | 465 => some (.leaf 5301)
  | 466 => some (.positive 0 (![8142, 8143, 8144, 8043, 8044, 8145]))
  | 467 => some (.triangle 14 8141 8146)
  | 468 => some (.leaf 5302)
  | 469 => some (.leaf 5303)
  | 470 => some (.triangle 19 8148 8149)
  | 471 => some (.leaf 5304)
  | 472 => some (.positive 1 (![8150, 8151, 8115, 8116, 8117, 8118]))
  | 473 => some (.triangle 18 1165 8152)
  | 474 => some (.triangle 16 1426 8153)
  | 475 => some (.leaf 5305)
  | 476 => some (.leaf 5306)
  | 477 => some (.leaf 5307)
  | 478 => some (.leaf 5308)
  | 479 => some (.leaf 5309)
  | 480 => some (.positive 0 (![8154, 8155, 8156, 8157, 8158, 8159]))
  | 481 => some (.triangle 15 8147 8160)
  | 482 => some (.triangle 13 8133 8161)
  | 483 => some (.triangle 12 8162 6528)
  | 484 => some (.triangle 11 8163 6780)
  | 485 => some (.triangle 10 8164 7184)
  | 486 => some (.leaf 5310)
  | 487 => some (.leaf 5311)
  | 488 => some (.leaf 5312)
  | 489 => some (.leaf 5313)
  | 490 => some (.leaf 5314)
  | 491 => some (.leaf 5315)
  | 492 => some (.leaf 5316)
  | 493 => some (.leaf 5317)
  | 494 => some (.leaf 5318)
  | 495 => some (.leaf 5319)
  | 496 => some (.triangle 19 8174 8175)
  | 497 => some (.leaf 5320)
  | 498 => some (.leaf 5321)
  | 499 => some (.leaf 5322)
  | 500 => some (.positive 1 (![8172, 8173, 8176, 8177, 8178, 8179]))
  | 501 => some (.triangle 18 1165 8180)
  | 502 => some (.triangle 16 1426 8181)
  | 503 => some (.leaf 5323)
  | 504 => some (.positive 0 (![8171, 8108, 8109, 8110, 8182, 8183]))
  | 505 => some (.triangle 3 8106 8184)
  | 506 => some (.leaf 5324)
  | 507 => some (.leaf 5325)
  | 508 => some (.positive 0 (![8186, 8126, 8127, 8128, 7721, 8187]))
  | 509 => some (.triangle 15 8185 8188)
  | 510 => some (.triangle 2 5796 8189)
  | 511 => some (.triangle 14 8190 8038)
  | 512 => some (.leaf 5326)
  | 513 => some (.leaf 5327)
  | 514 => some (.positive 0 (![8192, 8136, 8137, 8138, 7983, 8193]))
  | 515 => some (.triangle 3 8134 8194)
  | 516 => some (.leaf 5328)
  | 517 => some (.leaf 5329)
  | 518 => some (.positive 0 (![8196, 8143, 8144, 8043, 8044, 8197]))
  | 519 => some (.triangle 14 8195 8198)
  | 520 => some (.leaf 5330)
  | 521 => some (.leaf 5331)
  | 522 => some (.positive 0 (![8200, 8155, 8156, 8157, 8158, 8201]))
  | 523 => some (.triangle 15 8199 8202)
  | 524 => some (.triangle 13 8191 8203)
  | 525 => some (.leaf 5332)
  | 526 => some (.triangle 12 8204 8205)
  | 527 => some (.leaf 5333)
  | 528 => some (.triangle 11 8206 8207)
  | 529 => some (.leaf 5334)
  | 530 => some (.triangle 10 8208 8209)
  | 531 => some (.leaf 5335)
  | 532 => some (.leaf 5336)
  | 533 => some (.leaf 5337)
  | 534 => some (.positive 0 (![8212, 8126, 8127, 8128, 7721, 8213]))
  | 535 => some (.triangle 15 8211 8214)
  | 536 => some (.triangle 2 5796 8215)
  | 537 => some (.triangle 14 8216 8038)
  | 538 => some (.leaf 5338)
  | 539 => some (.leaf 5339)
  | 540 => some (.leaf 5340)
  | 541 => some (.positive 0 (![8219, 8155, 8156, 8157, 8158, 8220]))
  | 542 => some (.triangle 15 8218 8221)
  | 543 => some (.triangle 13 8217 8222)
  | 544 => some (.triangle 12 8223 6528)
  | 545 => some (.triangle 11 8224 6780)
  | 546 => some (.triangle 10 8225 7184)
  | 547 => some (.leaf 5341)
  | 548 => some (.leaf 5342)
  | 549 => some (.leaf 5343)
  | 550 => some (.leaf 5344)
  | 551 => some (.triangle 13 8229 8230)
  | 552 => some (.leaf 5345)
  | 553 => some (.triangle 12 8231 8232)
  | 554 => some (.leaf 5346)
  | 555 => some (.triangle 11 8233 8234)
  | 556 => some (.leaf 5347)
  | 557 => some (.triangle 10 8235 8236)
  | 558 => some (.leaf 5348)
  | 559 => some (.leaf 5349)
  | 560 => some (.leaf 5350)
  | 561 => some (.leaf 5351)
  | 562 => some (.leaf 5352)
  | 563 => some (.leaf 5353)
  | 564 => some (.leaf 5354)
  | 565 => some (.leaf 5355)
  | 566 => some (.leaf 5356)
  | 567 => some (.leaf 5357)
  | 568 => some (.heavy (![8165, 8166, 8167, 8168, 8169, 8170, 8210, 8226, 8227, 8228, 8237, 8238, 8239, 8240, 8241, 8242, 8243, 8244, 8245, 8246, 8247]))
  | 569 => some (.triangle 9 8105 8248)
  | 570 => some (.triangle 7 7918 8249)
  | 571 => some (.triangle 1 7180 8250)
  | 572 => some (.leaf 5358)
  | 573 => some (.leaf 5359)
  | 574 => some (.leaf 5360)
  | 575 => some (.triangle 13 8253 8254)
  | 576 => some (.triangle 3 8252 8255)
  | 577 => some (.leaf 5361)
  | 578 => some (.leaf 5362)
  | 579 => some (.triangle 13 8257 8258)
  | 580 => some (.triangle 12 8256 8259)
  | 581 => some (.leaf 5363)
  | 582 => some (.leaf 5364)
  | 583 => some (.leaf 5365)
  | 584 => some (.leaf 5366)
  | 585 => some (.leaf 5367)
  | 586 => some (.leaf 5368)
  | 587 => some (.leaf 5369)
  | 588 => some (.leaf 5370)
  | 589 => some (.leaf 5371)
  | 590 => some (.leaf 5372)
  | 591 => some (.triangle 12 8269 8270)
  | 592 => some (.leaf 5373)
  | 593 => some (.leaf 5374)
  | 594 => some (.triangle 12 8272 8273)
  | 595 => some (.leaf 5375)
  | 596 => some (.leaf 5376)
  | 597 => some (.leaf 5377)
  | 598 => some (.leaf 5378)
  | 599 => some (.leaf 5379)
  | 600 => some (.leaf 5380)
  | 601 => some (.leaf 5381)
  | 602 => some (.leaf 5382)
  | 603 => some (.leaf 5383)
  | 604 => some (.leaf 5384)
  | 605 => some (.heavy (![8260, 8261, 8262, 8263, 8264, 8265, 8266, 8267, 8268, 8271, 8274, 8275, 8276, 8277, 8278, 8279, 8280, 8281, 8282, 8283, 8284]))
  | 606 => some (.leaf 5385)
  | 607 => some (.leaf 5386)
  | 608 => some (.leaf 5387)
  | 609 => some (.leaf 5388)
  | 610 => some (.leaf 5389)
  | 611 => some (.leaf 5390)
  | 612 => some (.leaf 5391)
  | 613 => some (.leaf 5392)
  | 614 => some (.positive 1 (![8288, 8289, 8290, 8291, 8292, 8293]))
  | 615 => some (.triangle 16 1426 8294)
  | 616 => some (.leaf 5393)
  | 617 => some (.leaf 5394)
  | 618 => some (.leaf 5395)
  | 619 => some (.positive 0 (![8286, 8287, 8295, 8296, 8297, 8298]))
  | 620 => some (.triangle 13 1425 8299)
  | 621 => some (.triangle 3 8252 8300)
  | 622 => some (.leaf 5396)
  | 623 => some (.leaf 5397)
  | 624 => some (.leaf 5398)
  | 625 => some (.leaf 5399)
  | 626 => some (.leaf 5400)
  | 627 => some (.leaf 5401)
  | 628 => some (.positive 1 (![8302, 8303, 8304, 8305, 8306, 8307]))
  | 629 => some (.triangle 16 1426 8308)
  | 630 => some (.leaf 5402)
  | 631 => some (.leaf 5403)
  | 632 => some (.leaf 5404)
  | 633 => some (.leaf 5405)
  | 634 => some (.leaf 5406)
  | 635 => some (.positive 0 (![8309, 8310, 8311, 8312, 8313, 8314]))
  | 636 => some (.triangle 13 1425 8315)
  | 637 => some (.triangle 12 8301 8316)
  | 638 => some (.leaf 5407)
  | 639 => some (.leaf 5408)
  | 640 => some (.leaf 5409)
  | 641 => some (.leaf 5410)
  | 642 => some (.leaf 5411)
  | 643 => some (.leaf 5412)
  | 644 => some (.leaf 5413)
  | 645 => some (.leaf 5414)
  | 646 => some (.leaf 5415)
  | 647 => some (.triangle 12 8325 8326)
  | 648 => some (.leaf 5416)
  | 649 => some (.leaf 5417)
  | 650 => some (.triangle 12 8328 8329)
  | 651 => some (.leaf 5418)
  | 652 => some (.leaf 5419)
  | 653 => some (.triangle 12 8331 8332)
  | 654 => some (.leaf 5420)
  | 655 => some (.leaf 5421)
  | 656 => some (.leaf 5422)
  | 657 => some (.leaf 5423)
  | 658 => some (.leaf 5424)
  | 659 => some (.leaf 5425)
  | 660 => some (.leaf 5426)
  | 661 => some (.leaf 5427)
  | 662 => some (.leaf 5428)
  | 663 => some (.leaf 5429)
  | 664 => some (.heavy (![8317, 8318, 8319, 8320, 8321, 8322, 8323, 8324, 8327, 8330, 8333, 8334, 8335, 8336, 8337, 8338, 8339, 8340, 8341, 8342, 8343]))
  | 665 => some (.triangle 7 8285 8344)
  | 666 => some (.leaf 5430)
  | 667 => some (.leaf 5431)
  | 668 => some (.leaf 5432)
  | 669 => some (.leaf 5433)
  | 670 => some (.leaf 5434)
  | 671 => some (.leaf 5435)
  | 672 => some (.leaf 5436)
  | 673 => some (.leaf 5437)
  | 674 => some (.leaf 5438)
  | 675 => some (.leaf 5439)
  | 676 => some (.positive 1 (![8351, 8352, 8353, 8354, 8292, 8355]))
  | 677 => some (.triangle 16 8350 8356)
  | 678 => some (.leaf 5440)
  | 679 => some (.leaf 5441)
  | 680 => some (.positive 0 (![8347, 8348, 8349, 8357, 8358, 8359]))
  | 681 => some (.triangle 3 8346 8360)
  | 682 => some (.triangle 15 8361 7150)
  | 683 => some (.leaf 5442)
  | 684 => some (.leaf 5443)
  | 685 => some (.leaf 5444)
  | 686 => some (.leaf 5445)
  | 687 => some (.leaf 5446)
  | 688 => some (.leaf 5447)
  | 689 => some (.positive 1 (![8363, 8364, 8365, 8366, 8367, 8368]))
  | 690 => some (.triangle 16 8350 8369)
  | 691 => some (.leaf 5448)
  | 692 => some (.leaf 5449)
  | 693 => some (.leaf 5450)
  | 694 => some (.leaf 5451)
  | 695 => some (.leaf 5452)
  | 696 => some (.positive 0 (![8370, 8371, 8372, 8373, 8374, 8375]))
  | 697 => some (.triangle 12 8362 8376)
  | 698 => some (.triangle 11 8377 6780)
  | 699 => some (.leaf 5453)
  | 700 => some (.leaf 5454)
  | 701 => some (.leaf 5455)
  | 702 => some (.leaf 5456)
  | 703 => some (.leaf 5457)
  | 704 => some (.leaf 5458)
  | 705 => some (.leaf 5459)
  | 706 => some (.leaf 5460)
  | 707 => some (.leaf 5461)
  | 708 => some (.leaf 5462)
  | 709 => some (.triangle 12 8387 8388)
  | 710 => some (.triangle 11 8389 6780)
  | 711 => some (.leaf 5463)
  | 712 => some (.leaf 5464)
  | 713 => some (.triangle 12 8391 8392)
  | 714 => some (.triangle 11 8393 6780)
  | 715 => some (.leaf 5465)
  | 716 => some (.leaf 5466)
  | 717 => some (.leaf 5467)
  | 718 => some (.leaf 5468)
  | 719 => some (.leaf 5469)
  | 720 => some (.leaf 5470)
  | 721 => some (.leaf 5471)
  | 722 => some (.leaf 5472)
  | 723 => some (.leaf 5473)
  | 724 => some (.leaf 5474)
  | 725 => some (.heavy (![8378, 8379, 8380, 8381, 8382, 8383, 8384, 8385, 8386, 8390, 8394, 8395, 8396, 8397, 8398, 8399, 8400, 8401, 8402, 8403, 8404]))
  | 726 => some (.triangle 2 8345 8405)
  | 727 => some (.leaf 5475)
  | 728 => some (.leaf 5476)
  | 729 => some (.leaf 5477)
  | 730 => some (.leaf 5478)
  | 731 => some (.leaf 5479)
  | 732 => some (.leaf 5480)
  | 733 => some (.triangle 16 8411 8412)
  | 734 => some (.leaf 5481)
  | 735 => some (.leaf 5482)
  | 736 => some (.positive 0 (![8408, 8409, 8410, 8413, 8414, 8415]))
  | 737 => some (.triangle 3 8407 8416)
  | 738 => some (.leaf 5483)
  | 739 => some (.leaf 5484)
  | 740 => some (.leaf 5485)
  | 741 => some (.leaf 5486)
  | 742 => some (.leaf 5487)
  | 743 => some (.positive 0 (![8418, 8419, 7817, 8420, 8421, 8422]))
  | 744 => some (.triangle 14 8417 8423)
  | 745 => some (.leaf 5488)
  | 746 => some (.leaf 5489)
  | 747 => some (.leaf 5490)
  | 748 => some (.leaf 5491)
  | 749 => some (.leaf 5492)
  | 750 => some (.positive 0 (![8413, 8425, 8426, 8427, 8428, 8429]))
  | 751 => some (.triangle 12 8424 8430)
  | 752 => some (.triangle 10 8431 7184)
  | 753 => some (.leaf 5493)
  | 754 => some (.leaf 5494)
  | 755 => some (.leaf 5495)
  | 756 => some (.leaf 5496)
  | 757 => some (.leaf 5497)
  | 758 => some (.leaf 5498)
  | 759 => some (.leaf 5499)
  | 760 => some (.leaf 5500)
  | 761 => some (.leaf 5501)
  | 762 => some (.leaf 5502)
  | 763 => some (.triangle 12 8441 8442)
  | 764 => some (.triangle 10 8443 7184)
  | 765 => some (.leaf 5503)
  | 766 => some (.leaf 5504)
  | 767 => some (.triangle 12 8445 8446)
  | 768 => some (.triangle 10 8447 7184)
  | 769 => some (.leaf 5505)
  | 770 => some (.leaf 5506)
  | 771 => some (.leaf 5507)
  | 772 => some (.leaf 5508)
  | 773 => some (.leaf 5509)
  | 774 => some (.leaf 5510)
  | 775 => some (.leaf 5511)
  | 776 => some (.leaf 5512)
  | 777 => some (.leaf 5513)
  | 778 => some (.leaf 5514)
  | 779 => some (.heavy (![8432, 8433, 8434, 8435, 8436, 8437, 8438, 8439, 8440, 8444, 8448, 8449, 8450, 8451, 8452, 8453, 8454, 8455, 8456, 8457, 8458]))
  | 780 => some (.leaf 5515)
  | 781 => some (.leaf 5516)
  | 782 => some (.leaf 5517)
  | 783 => some (.leaf 5518)
  | 784 => some (.leaf 5519)
  | 785 => some (.leaf 5520)
  | 786 => some (.leaf 5521)
  | 787 => some (.triangle 16 8465 8466)
  | 788 => some (.leaf 5522)
  | 789 => some (.positive 0 (![8461, 8462, 8463, 8464, 8467, 8468]))
  | 790 => some (.triangle 3 8460 8469)
  | 791 => some (.leaf 5523)
  | 792 => some (.leaf 5524)
  | 793 => some (.leaf 5525)
  | 794 => some (.leaf 5526)
  | 795 => some (.leaf 5527)
  | 796 => some (.positive 0 (![8471, 8472, 8473, 7720, 8474, 8475]))
  | 797 => some (.triangle 15 8470 8476)
  | 798 => some (.leaf 5528)
  | 799 => some (.leaf 5529)
  | 800 => some (.leaf 5530)
  | 801 => some (.leaf 5531)
  | 802 => some (.leaf 5532)
  | 803 => some (.positive 0 (![8478, 8479, 7876, 8480, 8481, 8482]))
  | 804 => some (.triangle 14 8477 8483)
  | 805 => some (.triangle 13 8484 5358)
  | 806 => some (.leaf 5533)
  | 807 => some (.leaf 5534)
  | 808 => some (.leaf 5535)
  | 809 => some (.leaf 5536)
  | 810 => some (.leaf 5537)
  | 811 => some (.positive 0 (![8467, 8486, 8487, 8488, 8489, 8490]))
  | 812 => some (.triangle 13 8491 5358)
  | 813 => some (.triangle 12 8485 8492)
  | 814 => some (.triangle 11 8493 6780)
  | 815 => some (.triangle 10 8494 7184)
  | 816 => some (.leaf 5538)
  | 817 => some (.leaf 5539)
  | 818 => some (.leaf 5540)
  | 819 => some (.leaf 5541)
  | 820 => some (.leaf 5542)
  | 821 => some (.leaf 5543)
  | 822 => some (.leaf 5544)
  | 823 => some (.leaf 5545)
  | 824 => some (.leaf 5546)
  | 825 => some (.leaf 5547)
  | 826 => some (.leaf 5548)
  | 827 => some (.triangle 12 8505 8506)
  | 828 => some (.leaf 5549)
  | 829 => some (.triangle 11 8507 8508)
  | 830 => some (.leaf 5550)
  | 831 => some (.triangle 10 8509 8510)
  | 832 => some (.leaf 5551)
  | 833 => some (.leaf 5552)
  | 834 => some (.leaf 5553)
  | 835 => some (.leaf 5554)
  | 836 => some (.leaf 5555)
  | 837 => some (.leaf 5556)
  | 838 => some (.leaf 5557)
  | 839 => some (.leaf 5558)
  | 840 => some (.leaf 5559)
  | 841 => some (.leaf 5560)
  | 842 => some (.heavy (![8495, 8496, 8497, 8498, 8499, 8500, 8501, 8502, 8503, 8504, 8511, 8512, 8513, 8514, 8515, 8516, 8517, 8518, 8519, 8520, 8521]))
  | 843 => some (.triangle 2 8459 8522)
  | 844 => some (.leaf 5561)
  | 845 => some (.leaf 5562)
  | 846 => some (.leaf 5563)
  | 847 => some (.leaf 5564)
  | 848 => some (.positive 1 (![8288, 8525, 8290, 8526, 8292, 8527]))
  | 849 => some (.triangle 16 1426 8528)
  | 850 => some (.leaf 5565)
  | 851 => some (.positive 0 (![8461, 8025, 8463, 8464, 8529, 8530]))
  | 852 => some (.triangle 3 8524 8531)
  | 853 => some (.leaf 5566)
  | 854 => some (.positive 0 (![8471, 8126, 8473, 8128, 8474, 8533]))
  | 855 => some (.triangle 15 8532 8534)
  | 856 => some (.triangle 2 5796 8535)
  | 857 => some (.leaf 5567)
  | 858 => some (.triangle 14 8536 8537)
  | 859 => some (.leaf 5568)
  | 860 => some (.leaf 5569)
  | 861 => some (.leaf 5570)
  | 862 => some (.leaf 5571)
  | 863 => some (.leaf 5572)
  | 864 => some (.leaf 5573)
  | 865 => some (.positive 0 (![8540, 8541, 8542, 8043, 8543, 8544]))
  | 866 => some (.triangle 14 8539 8545)
  | 867 => some (.leaf 5574)
  | 868 => some (.leaf 5575)
  | 869 => some (.leaf 5576)
  | 870 => some (.leaf 5577)
  | 871 => some (.leaf 5578)
  | 872 => some (.positive 0 (![8547, 8548, 8156, 8549, 8550, 8551]))
  | 873 => some (.triangle 15 8546 8552)
  | 874 => some (.triangle 13 8538 8553)
  | 875 => some (.leaf 5579)
  | 876 => some (.leaf 5580)
  | 877 => some (.leaf 5581)
  | 878 => some (.leaf 5582)
  | 879 => some (.leaf 5583)
  | 880 => some (.leaf 5584)
  | 881 => some (.leaf 5585)
  | 882 => some (.positive 1 (![8556, 8557, 8558, 8559, 8560, 8561]))
  | 883 => some (.triangle 16 1426 8562)
  | 884 => some (.leaf 5586)
  | 885 => some (.leaf 5587)
  | 886 => some (.leaf 5588)
  | 887 => some (.leaf 5589)
  | 888 => some (.leaf 5590)
  | 889 => some (.positive 0 (![8563, 8564, 8565, 8566, 8567, 8568]))
  | 890 => some (.triangle 13 8555 8569)
  | 891 => some (.triangle 12 8554 8570)
  | 892 => some (.triangle 11 8571 6780)
  | 893 => some (.triangle 10 8572 7184)
  | 894 => some (.leaf 5591)
  | 895 => some (.leaf 5592)
  | 896 => some (.leaf 5593)
  | 897 => some (.leaf 5594)
  | 898 => some (.leaf 5595)
  | 899 => some (.leaf 5596)
  | 900 => some (.leaf 5597)
  | 901 => some (.leaf 5598)
  | 902 => some (.leaf 5599)
  | 903 => some (.leaf 5600)
  | 904 => some (.leaf 5601)
  | 905 => some (.triangle 12 8583 8584)
  | 906 => some (.leaf 5602)
  | 907 => some (.triangle 11 8585 8586)
  | 908 => some (.leaf 5603)
  | 909 => some (.triangle 10 8587 8588)
  | 910 => some (.leaf 5604)
  | 911 => some (.leaf 5605)
  | 912 => some (.leaf 5606)
  | 913 => some (.leaf 5607)
  | 914 => some (.leaf 5608)
  | 915 => some (.leaf 5609)
  | 916 => some (.leaf 5610)
  | 917 => some (.leaf 5611)
  | 918 => some (.leaf 5612)
  | 919 => some (.leaf 5613)
  | 920 => some (.heavy (![8573, 8574, 8575, 8576, 8577, 8578, 8579, 8580, 8581, 8582, 8589, 8590, 8591, 8592, 8593, 8594, 8595, 8596, 8597, 8598, 8599]))
  | 921 => some (.triangle 7 8523 8600)
  | 922 => some (.triangle 1 8406 8601)
  | 923 => some (.triangle 6 8251 8602)
  | 924 => some (.leaf 5614)
  | 925 => some (.leaf 5615)
  | 926 => some (.leaf 5616)
  | 927 => some (.triangle 14 8605 8606)
  | 928 => some (.triangle 2 8604 8607)
  | 929 => some (.leaf 5617)
  | 930 => some (.leaf 5618)
  | 931 => some (.triangle 14 8609 8610)
  | 932 => some (.triangle 11 8608 8611)
  | 933 => some (.leaf 5619)
  | 934 => some (.leaf 5620)
  | 935 => some (.leaf 5621)
  | 936 => some (.leaf 5622)
  | 937 => some (.leaf 5623)
  | 938 => some (.leaf 5624)
  | 939 => some (.leaf 5625)
  | 940 => some (.leaf 5626)
  | 941 => some (.leaf 5627)
  | 942 => some (.leaf 5628)
  | 943 => some (.triangle 11 8621 8622)
  | 944 => some (.leaf 5629)
  | 945 => some (.leaf 5630)
  | 946 => some (.triangle 11 8624 8625)
  | 947 => some (.leaf 5631)
  | 948 => some (.leaf 5632)
  | 949 => some (.leaf 5633)
  | 950 => some (.leaf 5634)
  | 951 => some (.leaf 5635)
  | 952 => some (.leaf 5636)
  | 953 => some (.leaf 5637)
  | 954 => some (.leaf 5638)
  | 955 => some (.leaf 5639)
  | 956 => some (.leaf 5640)
  | 957 => some (.heavy (![8612, 8613, 8614, 8615, 8616, 8617, 8618, 8619, 8620, 8623, 8626, 8627, 8628, 8629, 8630, 8631, 8632, 8633, 8634, 8635, 8636]))
  | 958 => some (.leaf 5641)
  | 959 => some (.leaf 5642)
  | 960 => some (.leaf 5643)
  | 961 => some (.leaf 5644)
  | 962 => some (.leaf 5645)
  | 963 => some (.leaf 5646)
  | 964 => some (.leaf 5647)
  | 965 => some (.leaf 5648)
  | 966 => some (.positive 1 (![8640, 8641, 8642, 8643, 8644, 8645]))
  | 967 => some (.triangle 17 1381 8646)
  | 968 => some (.leaf 5649)
  | 969 => some (.leaf 5650)
  | 970 => some (.leaf 5651)
  | 971 => some (.positive 0 (![8638, 8639, 8647, 8648, 8649, 8650]))
  | 972 => some (.triangle 14 1345 8651)
  | 973 => some (.triangle 2 8604 8652)
  | 974 => some (.leaf 5652)
  | 975 => some (.leaf 5653)
  | 976 => some (.leaf 5654)
  | 977 => some (.leaf 5655)
  | 978 => some (.leaf 5656)
  | 979 => some (.leaf 5657)
  | 980 => some (.positive 1 (![8654, 8655, 8656, 8657, 8658, 8659]))
  | 981 => some (.triangle 17 1381 8660)
  | 982 => some (.leaf 5658)
  | 983 => some (.leaf 5659)
  | 984 => some (.leaf 5660)
  | 985 => some (.leaf 5661)
  | 986 => some (.leaf 5662)
  | 987 => some (.positive 0 (![8661, 8662, 8663, 8664, 8665, 8666]))
  | 988 => some (.triangle 14 1345 8667)
  | 989 => some (.triangle 11 8653 8668)
  | 990 => some (.leaf 5663)
  | 991 => some (.leaf 5664)
  | 992 => some (.leaf 5665)
  | 993 => some (.leaf 5666)
  | 994 => some (.leaf 5667)
  | 995 => some (.leaf 5668)
  | 996 => some (.leaf 5669)
  | 997 => some (.leaf 5670)
  | 998 => some (.leaf 5671)
  | 999 => some (.triangle 11 8677 8678)
  | 1000 => some (.leaf 5672)
  | 1001 => some (.leaf 5673)
  | 1002 => some (.triangle 11 8680 8681)
  | 1003 => some (.leaf 5674)
  | 1004 => some (.leaf 5675)
  | 1005 => some (.triangle 11 8683 8684)
  | 1006 => some (.leaf 5676)
  | 1007 => some (.leaf 5677)
  | 1008 => some (.leaf 5678)
  | 1009 => some (.leaf 5679)
  | 1010 => some (.leaf 5680)
  | 1011 => some (.leaf 5681)
  | 1012 => some (.leaf 5682)
  | 1013 => some (.leaf 5683)
  | 1014 => some (.leaf 5684)
  | 1015 => some (.leaf 5685)
  | 1016 => some (.heavy (![8669, 8670, 8671, 8672, 8673, 8674, 8675, 8676, 8679, 8682, 8685, 8686, 8687, 8688, 8689, 8690, 8691, 8692, 8693, 8694, 8695]))
  | 1017 => some (.triangle 8 8637 8696)
  | 1018 => some (.leaf 5686)
  | 1019 => some (.leaf 5687)
  | 1020 => some (.leaf 5688)
  | 1021 => some (.leaf 5689)
  | 1022 => some (.leaf 5690)
  | 1023 => some (.leaf 5691)
  | 1024 => some (.leaf 5692)
  | 1025 => some (.leaf 5693)
  | 1026 => some (.leaf 5694)
  | 1027 => some (.positive 1 (![8701, 8702, 8703, 8704, 8705, 8706]))
  | 1028 => some (.triangle 17 8700 8707)
  | 1029 => some (.leaf 5695)
  | 1030 => some (.leaf 5696)
  | 1031 => some (.positive 0 (![8698, 8699, 6971, 8708, 8709, 8710]))
  | 1032 => some (.leaf 5697)
  | 1033 => some (.triangle 15 8711 8712)
  | 1034 => some (.leaf 5698)
  | 1035 => some (.triangle 12 8713 8714)
  | 1036 => some (.leaf 5699)
  | 1037 => some (.leaf 5700)
  | 1038 => some (.leaf 5701)
  | 1039 => some (.leaf 5702)
  | 1040 => some (.leaf 5703)
  | 1041 => some (.leaf 5704)
  | 1042 => some (.positive 1 (![8716, 8717, 8718, 8719, 8720, 8721]))
  | 1043 => some (.triangle 17 8700 8722)
  | 1044 => some (.leaf 5705)
  | 1045 => some (.leaf 5706)
  | 1046 => some (.leaf 5707)
  | 1047 => some (.leaf 5708)
  | 1048 => some (.leaf 5709)
  | 1049 => some (.positive 0 (![8723, 8724, 8725, 8726, 8727, 8728]))
  | 1050 => some (.triangle 12 8729 6528)
  | 1051 => some (.leaf 5710)
  | 1052 => some (.triangle 15 8730 8731)
  | 1053 => some (.triangle 11 8715 8732)
  | 1054 => some (.leaf 5711)
  | 1055 => some (.leaf 5712)
  | 1056 => some (.leaf 5713)
  | 1057 => some (.leaf 5714)
  | 1058 => some (.leaf 5715)
  | 1059 => some (.leaf 5716)
  | 1060 => some (.leaf 5717)
  | 1061 => some (.leaf 5718)
  | 1062 => some (.leaf 5719)
  | 1063 => some (.leaf 5720)
  | 1064 => some (.triangle 11 8742 8743)
  | 1065 => some (.leaf 5721)
  | 1066 => some (.leaf 5722)
  | 1067 => some (.triangle 11 8745 8746)
  | 1068 => some (.leaf 5723)
  | 1069 => some (.leaf 5724)
  | 1070 => some (.leaf 5725)
  | 1071 => some (.leaf 5726)
  | 1072 => some (.leaf 5727)
  | 1073 => some (.leaf 5728)
  | 1074 => some (.leaf 5729)
  | 1075 => some (.leaf 5730)
  | 1076 => some (.leaf 5731)
  | 1077 => some (.leaf 5732)
  | 1078 => some (.heavy (![8733, 8734, 8735, 8736, 8737, 8738, 8739, 8740, 8741, 8744, 8747, 8748, 8749, 8750, 8751, 8752, 8753, 8754, 8755, 8756, 8757]))
  | 1079 => some (.triangle 3 8697 8758)
  | 1080 => some (.leaf 5733)
  | 1081 => some (.leaf 5734)
  | 1082 => some (.leaf 5735)
  | 1083 => some (.leaf 5736)
  | 1084 => some (.leaf 5737)
  | 1085 => some (.leaf 5738)
  | 1086 => some (.triangle 17 8764 8765)
  | 1087 => some (.leaf 5739)
  | 1088 => some (.leaf 5740)
  | 1089 => some (.positive 0 (![8761, 8762, 8763, 8766, 8767, 8768]))
  | 1090 => some (.triangle 2 8760 8769)
  | 1091 => some (.leaf 5741)
  | 1092 => some (.leaf 5742)
  | 1093 => some (.leaf 5743)
  | 1094 => some (.leaf 5744)
  | 1095 => some (.leaf 5745)
  | 1096 => some (.leaf 5746)
  | 1097 => some (.positive 0 (![8771, 8772, 8773, 8774, 8775, 8776]))
  | 1098 => some (.triangle 13 8770 8777)
  | 1099 => some (.leaf 5747)
  | 1100 => some (.leaf 5748)
  | 1101 => some (.leaf 5749)
  | 1102 => some (.leaf 5750)
  | 1103 => some (.leaf 5751)
  | 1104 => some (.positive 0 (![8766, 8779, 8780, 8781, 8782, 8783]))
  | 1105 => some (.triangle 11 8778 8784)
  | 1106 => some (.triangle 10 8785 7184)
  | 1107 => some (.leaf 5752)
  | 1108 => some (.leaf 5753)
  | 1109 => some (.leaf 5754)
  | 1110 => some (.leaf 5755)
  | 1111 => some (.leaf 5756)
  | 1112 => some (.leaf 5757)
  | 1113 => some (.leaf 5758)
  | 1114 => some (.leaf 5759)
  | 1115 => some (.leaf 5760)
  | 1116 => some (.leaf 5761)
  | 1117 => some (.triangle 11 8795 8796)
  | 1118 => some (.triangle 10 8797 7184)
  | 1119 => some (.leaf 5762)
  | 1120 => some (.leaf 5763)
  | 1121 => some (.triangle 11 8799 8800)
  | 1122 => some (.triangle 10 8801 7184)
  | 1123 => some (.leaf 5764)
  | 1124 => some (.leaf 5765)
  | 1125 => some (.leaf 5766)
  | 1126 => some (.leaf 5767)
  | 1127 => some (.leaf 5768)
  | 1128 => some (.leaf 5769)
  | 1129 => some (.leaf 5770)
  | 1130 => some (.leaf 5771)
  | 1131 => some (.leaf 5772)
  | 1132 => some (.leaf 5773)
  | 1133 => some (.heavy (![8786, 8787, 8788, 8789, 8790, 8791, 8792, 8793, 8794, 8798, 8802, 8803, 8804, 8805, 8806, 8807, 8808, 8809, 8810, 8811, 8812]))
  | 1134 => some (.leaf 5774)
  | 1135 => some (.leaf 5775)
  | 1136 => some (.leaf 5776)
  | 1137 => some (.leaf 5777)
  | 1138 => some (.leaf 5778)
  | 1139 => some (.triangle 17 8817 8818)
  | 1140 => some (.leaf 5779)
  | 1141 => some (.positive 0 (![8814, 8815, 8816, 7568, 8819, 8820]))
  | 1142 => some (.leaf 5780)
  | 1143 => some (.triangle 15 8821 8822)
  | 1144 => some (.leaf 5781)
  | 1145 => some (.triangle 14 8823 8824)
  | 1146 => some (.leaf 5782)
  | 1147 => some (.leaf 5783)
  | 1148 => some (.leaf 5784)
  | 1149 => some (.leaf 5785)
  | 1150 => some (.leaf 5786)
  | 1151 => some (.positive 0 (![8826, 8827, 7981, 8828, 8829, 8830]))
  | 1152 => some (.triangle 14 8831 5170)
  | 1153 => some (.triangle 15 8832 8822)
  | 1154 => some (.triangle 13 8825 8833)
  | 1155 => some (.triangle 12 8834 8714)
  | 1156 => some (.leaf 5787)
  | 1157 => some (.leaf 5788)
  | 1158 => some (.leaf 5789)
  | 1159 => some (.leaf 5790)
  | 1160 => some (.leaf 5791)
  | 1161 => some (.positive 0 (![8819, 8836, 8837, 8838, 8839, 8840]))
  | 1162 => some (.triangle 14 8841 5170)
  | 1163 => some (.triangle 12 8842 6528)
  | 1164 => some (.leaf 5792)
  | 1165 => some (.triangle 15 8843 8844)
  | 1166 => some (.triangle 11 8835 8845)
  | 1167 => some (.triangle 10 8846 7184)
  | 1168 => some (.leaf 5793)
  | 1169 => some (.leaf 5794)
  | 1170 => some (.leaf 5795)
  | 1171 => some (.leaf 5796)
  | 1172 => some (.leaf 5797)
  | 1173 => some (.leaf 5798)
  | 1174 => some (.leaf 5799)
  | 1175 => some (.leaf 5800)
  | 1176 => some (.leaf 5801)
  | 1177 => some (.leaf 5802)
  | 1178 => some (.leaf 5803)
  | 1179 => some (.triangle 11 8857 8858)
  | 1180 => some (.leaf 5804)
  | 1181 => some (.triangle 10 8859 8860)
  | 1182 => some (.leaf 5805)
  | 1183 => some (.leaf 5806)
  | 1184 => some (.leaf 5807)
  | 1185 => some (.leaf 5808)
  | 1186 => some (.leaf 5809)
  | 1187 => some (.leaf 5810)
  | 1188 => some (.leaf 5811)
  | 1189 => some (.leaf 5812)
  | 1190 => some (.leaf 5813)
  | 1191 => some (.leaf 5814)
  | 1192 => some (.heavy (![8847, 8848, 8849, 8850, 8851, 8852, 8853, 8854, 8855, 8856, 8861, 8862, 8863, 8864, 8865, 8866, 8867, 8868, 8869, 8870, 8871]))
  | 1193 => some (.triangle 3 8813 8872)
  | 1194 => some (.leaf 5815)
  | 1195 => some (.leaf 5816)
  | 1196 => some (.leaf 5817)
  | 1197 => some (.leaf 5818)
  | 1198 => some (.leaf 5819)
  | 1199 => some (.positive 1 (![8640, 8875, 8642, 8876, 8877, 8878]))
  | 1200 => some (.triangle 17 1381 8879)
  | 1201 => some (.leaf 5820)
  | 1202 => some (.positive 0 (![8814, 8874, 8816, 8027, 8880, 8881]))
  | 1203 => some (.triangle 3 8023 8882)
  | 1204 => some (.leaf 5821)
  | 1205 => some (.triangle 15 8883 8884)
  | 1206 => some (.triangle 2 8760 8885)
  | 1207 => some (.leaf 5822)
  | 1208 => some (.triangle 14 8886 8887)
  | 1209 => some (.leaf 5823)
  | 1210 => some (.leaf 5824)
  | 1211 => some (.leaf 5825)
  | 1212 => some (.leaf 5826)
  | 1213 => some (.leaf 5827)
  | 1214 => some (.positive 0 (![8890, 8891, 8042, 8043, 8892, 8893]))
  | 1215 => some (.triangle 14 8889 8894)
  | 1216 => some (.leaf 5828)
  | 1217 => some (.triangle 15 8895 8896)
  | 1218 => some (.triangle 13 8888 8897)
  | 1219 => some (.triangle 12 8898 8714)
  | 1220 => some (.leaf 5829)
  | 1221 => some (.leaf 5830)
  | 1222 => some (.leaf 5831)
  | 1223 => some (.leaf 5832)
  | 1224 => some (.leaf 5833)
  | 1225 => some (.leaf 5834)
  | 1226 => some (.leaf 5835)
  | 1227 => some (.positive 1 (![8901, 8902, 8903, 8904, 8905, 8906]))
  | 1228 => some (.triangle 17 1381 8907)
  | 1229 => some (.leaf 5836)
  | 1230 => some (.leaf 5837)
  | 1231 => some (.leaf 5838)
  | 1232 => some (.leaf 5839)
  | 1233 => some (.leaf 5840)
  | 1234 => some (.positive 0 (![8908, 8909, 8910, 8911, 8912, 8913]))
  | 1235 => some (.triangle 14 8900 8914)
  | 1236 => some (.triangle 12 8915 6528)
  | 1237 => some (.leaf 5841)
  | 1238 => some (.triangle 15 8916 8917)
  | 1239 => some (.triangle 11 8899 8918)
  | 1240 => some (.triangle 10 8919 7184)
  | 1241 => some (.leaf 5842)
  | 1242 => some (.leaf 5843)
  | 1243 => some (.leaf 5844)
  | 1244 => some (.leaf 5845)
  | 1245 => some (.leaf 5846)
  | 1246 => some (.leaf 5847)
  | 1247 => some (.leaf 5848)
  | 1248 => some (.leaf 5849)
  | 1249 => some (.leaf 5850)
  | 1250 => some (.leaf 5851)
  | 1251 => some (.leaf 5852)
  | 1252 => some (.triangle 11 8930 8931)
  | 1253 => some (.leaf 5853)
  | 1254 => some (.triangle 10 8932 8933)
  | 1255 => some (.leaf 5854)
  | 1256 => some (.leaf 5855)
  | 1257 => some (.leaf 5856)
  | 1258 => some (.leaf 5857)
  | 1259 => some (.leaf 5858)
  | 1260 => some (.leaf 5859)
  | 1261 => some (.leaf 5860)
  | 1262 => some (.leaf 5861)
  | 1263 => some (.leaf 5862)
  | 1264 => some (.leaf 5863)
  | 1265 => some (.heavy (![8920, 8921, 8922, 8923, 8924, 8925, 8926, 8927, 8928, 8929, 8934, 8935, 8936, 8937, 8938, 8939, 8940, 8941, 8942, 8943, 8944]))
  | 1266 => some (.triangle 8 8873 8945)
  | 1267 => some (.triangle 1 8759 8946)
  | 1268 => some (.leaf 5864)
  | 1269 => some (.leaf 5865)
  | 1270 => some (.leaf 5866)
  | 1271 => some (.leaf 5867)
  | 1272 => some (.leaf 5868)
  | 1273 => some (.leaf 5869)
  | 1274 => some (.leaf 5870)
  | 1275 => some (.leaf 5871)
  | 1276 => some (.leaf 5872)
  | 1277 => some (.positive 1 (![8951, 8952, 8953, 8954, 8955, 8956]))
  | 1278 => some (.leaf 5873)
  | 1279 => some (.triangle 18 8957 8958)
  | 1280 => some (.leaf 5874)
  | 1281 => some (.leaf 5875)
  | 1282 => some (.positive 0 (![8948, 8949, 8950, 8959, 8960, 8961]))
  | 1283 => some (.triangle 3 8252 8962)
  | 1284 => some (.leaf 5876)
  | 1285 => some (.triangle 15 8963 8964)
  | 1286 => some (.triangle 2 8604 8965)
  | 1287 => some (.leaf 5877)
  | 1288 => some (.triangle 12 8966 8967)
  | 1289 => some (.leaf 5878)
  | 1290 => some (.leaf 5879)
  | 1291 => some (.leaf 5880)
  | 1292 => some (.leaf 5881)
  | 1293 => some (.leaf 5882)
  | 1294 => some (.leaf 5883)
  | 1295 => some (.leaf 5884)
  | 1296 => some (.positive 1 (![8970, 8971, 8972, 8973, 8974, 8975]))
  | 1297 => some (.leaf 5885)
  | 1298 => some (.triangle 18 8976 8977)
  | 1299 => some (.leaf 5886)
  | 1300 => some (.leaf 5887)
  | 1301 => some (.leaf 5888)
  | 1302 => some (.leaf 5889)
  | 1303 => some (.leaf 5890)
  | 1304 => some (.positive 0 (![8978, 8979, 8980, 8981, 8982, 8983]))
  | 1305 => some (.triangle 12 8969 8984)
  | 1306 => some (.leaf 5891)
  | 1307 => some (.triangle 15 8985 8986)
  | 1308 => some (.triangle 11 8968 8987)
  | 1309 => some (.leaf 5892)
  | 1310 => some (.leaf 5893)
  | 1311 => some (.leaf 5894)
  | 1312 => some (.leaf 5895)
  | 1313 => some (.leaf 5896)
  | 1314 => some (.leaf 5897)
  | 1315 => some (.leaf 5898)
  | 1316 => some (.leaf 5899)
  | 1317 => some (.leaf 5900)
  | 1318 => some (.leaf 5901)
  | 1319 => some (.triangle 11 8997 8998)
  | 1320 => some (.leaf 5902)
  | 1321 => some (.leaf 5903)
  | 1322 => some (.triangle 11 9000 9001)
  | 1323 => some (.leaf 5904)
  | 1324 => some (.leaf 5905)
  | 1325 => some (.leaf 5906)
  | 1326 => some (.leaf 5907)
  | 1327 => some (.leaf 5908)
  | 1328 => some (.leaf 5909)
  | 1329 => some (.leaf 5910)
  | 1330 => some (.leaf 5911)
  | 1331 => some (.leaf 5912)
  | 1332 => some (.leaf 5913)
  | 1333 => some (.heavy (![8988, 8989, 8990, 8991, 8992, 8993, 8994, 8995, 8996, 8999, 9002, 9003, 9004, 9005, 9006, 9007, 9008, 9009, 9010, 9011, 9012]))
  | 1334 => some (.leaf 5914)
  | 1335 => some (.leaf 5915)
  | 1336 => some (.leaf 5916)
  | 1337 => some (.positive 1 (![8951, 9014, 8953, 8954, 9015, 9016]))
  | 1338 => some (.leaf 5917)
  | 1339 => some (.triangle 18 9017 9018)
  | 1340 => some (.leaf 5918)
  | 1341 => some (.positive 0 (![8814, 8462, 8463, 8464, 9019, 9020]))
  | 1342 => some (.triangle 3 8524 9021)
  | 1343 => some (.leaf 5919)
  | 1344 => some (.triangle 15 9022 9023)
  | 1345 => some (.triangle 2 8760 9024)
  | 1346 => some (.triangle 14 9025 8887)
  | 1347 => some (.leaf 5920)
  | 1348 => some (.leaf 5921)
  | 1349 => some (.positive 0 (![8890, 8541, 8542, 9027, 8892, 9028]))
  | 1350 => some (.triangle 14 8539 9029)
  | 1351 => some (.leaf 5922)
  | 1352 => some (.triangle 15 9030 9031)
  | 1353 => some (.triangle 13 9026 9032)
  | 1354 => some (.leaf 5923)
  | 1355 => some (.triangle 12 9033 9034)
  | 1356 => some (.leaf 5924)
  | 1357 => some (.leaf 5925)
  | 1358 => some (.leaf 5926)
  | 1359 => some (.leaf 5927)
  | 1360 => some (.leaf 5928)
  | 1361 => some (.leaf 5929)
  | 1362 => some (.positive 1 (![9036, 9037, 9038, 9039, 9040, 9041]))
  | 1363 => some (.leaf 5930)
  | 1364 => some (.triangle 18 9042 9043)
  | 1365 => some (.leaf 5931)
  | 1366 => some (.leaf 5932)
  | 1367 => some (.leaf 5933)
  | 1368 => some (.leaf 5934)
  | 1369 => some (.leaf 5935)
  | 1370 => some (.positive 0 (![9044, 9045, 9046, 9047, 9048, 9049]))
  | 1371 => some (.triangle 12 8969 9050)
  | 1372 => some (.leaf 5936)
  | 1373 => some (.triangle 15 9051 9052)
  | 1374 => some (.triangle 11 9035 9053)
  | 1375 => some (.triangle 10 9054 7184)
  | 1376 => some (.leaf 5937)
  | 1377 => some (.leaf 5938)
  | 1378 => some (.leaf 5939)
  | 1379 => some (.leaf 5940)
  | 1380 => some (.leaf 5941)
  | 1381 => some (.leaf 5942)
  | 1382 => some (.leaf 5943)
  | 1383 => some (.leaf 5944)
  | 1384 => some (.leaf 5945)
  | 1385 => some (.leaf 5946)
  | 1386 => some (.leaf 5947)
  | 1387 => some (.triangle 11 9065 9066)
  | 1388 => some (.leaf 5948)
  | 1389 => some (.triangle 10 9067 9068)
  | 1390 => some (.leaf 5949)
  | 1391 => some (.leaf 5950)
  | 1392 => some (.leaf 5951)
  | 1393 => some (.leaf 5952)
  | 1394 => some (.leaf 5953)
  | 1395 => some (.leaf 5954)
  | 1396 => some (.leaf 5955)
  | 1397 => some (.leaf 5956)
  | 1398 => some (.heavy (![9055, 9056, 9057, 9058, 9059, 9060, 9061, 9062, 9063, 9064, 9069, 9070, 9071, 9072, 9073, 9063, 9064, 9074, 9075, 9076, 9077]))
  | 1399 => some (.triangle 1 9013 9078)
  | 1400 => some (.triangle 6 8947 9079)
  | 1401 => some (.leaf 5957)
  | 1402 => some (.leaf 5958)
  | 1403 => some (.leaf 5959)
  | 1404 => some (.leaf 5960)
  | 1405 => some (.triangle 18 9083 9084)
  | 1406 => some (.leaf 5961)
  | 1407 => some (.leaf 5962)
  | 1408 => some (.positive 0 (![9082, 7116, 7117, 9085, 9086, 9087]))
  | 1409 => some (.triangle 3 9081 9088)
  | 1410 => some (.leaf 5963)
  | 1411 => some (.triangle 15 9089 9090)
  | 1412 => some (.triangle 2 8604 9091)
  | 1413 => some (.triangle 12 9092 8967)
  | 1414 => some (.leaf 5964)
  | 1415 => some (.leaf 5965)
  | 1416 => some (.leaf 5966)
  | 1417 => some (.leaf 5967)
  | 1418 => some (.leaf 5968)
  | 1419 => some (.positive 0 (![9094, 9095, 9096, 8726, 9097, 9098]))
  | 1420 => some (.triangle 3 9081 9099)
  | 1421 => some (.leaf 5969)
  | 1422 => some (.leaf 5970)
  | 1423 => some (.leaf 5971)
  | 1424 => some (.leaf 5972)
  | 1425 => some (.positive 0 (![9101, 9102, 8980, 8981, 9103, 9104]))
  | 1426 => some (.triangle 12 9100 9105)
  | 1427 => some (.leaf 5973)
  | 1428 => some (.triangle 15 9106 9107)
  | 1429 => some (.triangle 11 9093 9108)
  | 1430 => some (.leaf 5974)
  | 1431 => some (.leaf 5975)
  | 1432 => some (.leaf 5976)
  | 1433 => some (.leaf 5977)
  | 1434 => some (.leaf 5978)
  | 1435 => some (.leaf 5979)
  | 1436 => some (.leaf 5980)
  | 1437 => some (.leaf 5981)
  | 1438 => some (.leaf 5982)
  | 1439 => some (.leaf 5983)
  | 1440 => some (.leaf 5984)
  | 1441 => some (.triangle 11 9119 9120)
  | 1442 => some (.leaf 5985)
  | 1443 => some (.leaf 5986)
  | 1444 => some (.leaf 5987)
  | 1445 => some (.leaf 5988)
  | 1446 => some (.leaf 5989)
  | 1447 => some (.leaf 5990)
  | 1448 => some (.leaf 5991)
  | 1449 => some (.leaf 5992)
  | 1450 => some (.heavy (![9109, 9110, 9111, 9112, 9113, 9114, 9115, 9116, 9117, 9118, 9121, 9122, 9123, 9124, 9125, 9126, 9127, 9116, 9128, 9117, 9129]))
  | 1451 => some (.leaf 5993)
  | 1452 => some (.leaf 5994)
  | 1453 => some (.leaf 5995)
  | 1454 => some (.leaf 5996)
  | 1455 => some (.leaf 5997)
  | 1456 => some (.leaf 5998)
  | 1457 => some (.triangle 18 9135 9136)
  | 1458 => some (.leaf 5999)
  | 1459 => some (.positive 0 (![8814, 9132, 9133, 9134, 9137, 9138]))
  | 1460 => some (.triangle 3 9131 9139)
  | 1461 => some (.leaf 6000)
  | 1462 => some (.triangle 15 9140 9141)
  | 1463 => some (.triangle 2 8760 9142)
  | 1464 => some (.triangle 14 9143 8887)
  | 1465 => some (.leaf 6001)
  | 1466 => some (.triangle 15 9145 9141)
  | 1467 => some (.triangle 13 9144 9146)
  | 1468 => some (.triangle 12 9147 9034)
  | 1469 => some (.leaf 6002)
  | 1470 => some (.leaf 6003)
  | 1471 => some (.leaf 6004)
  | 1472 => some (.leaf 6005)
  | 1473 => some (.leaf 6006)
  | 1474 => some (.leaf 6007)
  | 1475 => some (.leaf 6008)
  | 1476 => some (.positive 0 (![9150, 9151, 9152, 9153, 9154, 9155]))
  | 1477 => some (.triangle 3 9149 9156)
  | 1478 => some (.leaf 6009)
  | 1479 => some (.leaf 6010)
  | 1480 => some (.leaf 6011)
  | 1481 => some (.leaf 6012)
  | 1482 => some (.leaf 6013)
  | 1483 => some (.positive 0 (![9158, 9159, 9160, 8911, 9161, 9162]))
  | 1484 => some (.triangle 14 9157 9163)
  | 1485 => some (.leaf 6014)
  | 1486 => some (.leaf 6015)
  | 1487 => some (.leaf 6016)
  | 1488 => some (.positive 0 (![9165, 9166, 9046, 9047, 9048, 9167]))
  | 1489 => some (.triangle 12 9164 9168)
  | 1490 => some (.leaf 6017)
  | 1491 => some (.leaf 6018)
  | 1492 => some (.triangle 18 9170 9171)
  | 1493 => some (.leaf 6019)
  | 1494 => some (.leaf 6020)
  | 1495 => some (.leaf 6021)
  | 1496 => some (.leaf 6022)
  | 1497 => some (.leaf 6023)
  | 1498 => some (.positive 0 (![9172, 9173, 9174, 9175, 9176, 9177]))
  | 1499 => some (.triangle 15 9169 9178)
  | 1500 => some (.triangle 11 9148 9179)
  | 1501 => some (.triangle 10 9180 7184)
  | 1502 => some (.leaf 6024)
  | 1503 => some (.leaf 6025)
  | 1504 => some (.leaf 6026)
  | 1505 => some (.leaf 6027)
  | 1506 => some (.leaf 6028)
  | 1507 => some (.leaf 6029)
  | 1508 => some (.leaf 6030)
  | 1509 => some (.leaf 6031)
  | 1510 => some (.leaf 6032)
  | 1511 => some (.leaf 6033)
  | 1512 => some (.leaf 6034)
  | 1513 => some (.triangle 11 9191 9192)
  | 1514 => some (.leaf 6035)
  | 1515 => some (.triangle 10 9193 9194)
  | 1516 => some (.leaf 6036)
  | 1517 => some (.leaf 6037)
  | 1518 => some (.leaf 6038)
  | 1519 => some (.leaf 6039)
  | 1520 => some (.leaf 6040)
  | 1521 => some (.leaf 6041)
  | 1522 => some (.leaf 6042)
  | 1523 => some (.leaf 6043)
  | 1524 => some (.heavy (![9181, 9182, 9183, 9184, 9185, 9186, 9187, 9188, 9189, 9190, 9195, 9196, 9197, 9198, 9199, 9200, 9188, 9188, 9201, 9202, 9203]))
  | 1525 => some (.triangle 1 9130 9204)
  | 1526 => some (.triangle 9 9080 9205)
  | 1527 => some (.triangle 5 8603 9206)
  | 1528 => some (.leaf 6044)
  | 1529 => some (.leaf 6045)
  | 1530 => some (.leaf 6046)
  | 1531 => some (.triangle 15 9209 9210)
  | 1532 => some (.triangle 1 9208 9211)
  | 1533 => some (.triangle 10 9212 9211)
  | 1534 => some (.leaf 6047)
  | 1535 => some (.leaf 6048)
  | _ => none

end Jsp404.SevenLowerBranchShard05
