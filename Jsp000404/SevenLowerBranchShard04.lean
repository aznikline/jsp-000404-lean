import Jsp000404.SevenLowerReplay

/-! SOURCE_ONLY literal certificate data; no kernel PASS is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerBranchShard04
open SevenLowerReplay
def cycle0000 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 4, 5, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 9 1, .triangle 2 1]

def cycle0001 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 1 (![2, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 9 1, .triangle 2 1]

def cycle0002 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 0, 4, 5, 3]), .triangle 15 1, .triangle 2 0]

def cycle0003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 4, 5, 3]), .triangle 1 2, .gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 3 1]

def cycle0004 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 5, 4, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 9 1, .triangle 2 1]

def cycle0005 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 1 (![2, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 9 1, .triangle 2 1]

def cycle0006 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 18 0, .triangle 5 0]

def cycle0007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (0), (-2), (-1), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 8 1, .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0008 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (0), (-2), (0), (0), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, true, false, true, true] }
  origin := ![.gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 8 1, .gapLower 5 0 (![3, 0, 4, 1, 2]), .thetaOrder 4, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-2), (-1), (4), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, true] }
  origin := ![.gapLower 0 4 (![2, 1, 4, 5, 3]), .gapLower 5 1 (![3, 0, 4, 1, 2]), .corridorLower 3 5, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 10 2, .triangle 1 2]

def cycle0010 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (0), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 0, .gapLower 5 2 (![3, 0, 4, 1, 2]), .triangle 6 1]

def cycle0011 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (0), (-2), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 5 3 (![3, 0, 4, 1, 2]), .triangle 9 0, .triangle 2 1]

def cycle0012 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![3, 0, 4, 1, 2]), .gapLower 1 2 (![2, 0, 5, 4, 3])]

def cycle0013 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![3, 0, 4, 1, 2]), .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0014 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .triangle 18 1, .triangle 9 0, .gapLower 0 2 (![2, 1, 4, 5, 3])]

def cycle0015 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2]), .gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 9 1, .triangle 2 1]

def cycle0016 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![2, 0, 5, 4, 3])]

def cycle0017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0018 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 2 (![2, 1, 4, 5, 3])]

def cycle0019 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0020 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 18 0, .triangle 9 0, .triangle 2 1]

def cycle0021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 2, .gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 6 1]

def cycle0022 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 0, 5, 4, 3]), .triangle 15 1, .triangle 9 0, .triangle 2 1]

def cycle0023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 5, 3]), .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 0, 5, 4, 3]), .triangle 2 0]

def cycle0024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 5, 4, 3]), .triangle 1 2, .gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 3 1]

def cycle0025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 4, 5, 3]), .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![2, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0027 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 4, 5, 3]), .triangle 1 0]

def cycle0028 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 4, 5, 3]), .gapLower 0 5 (![2, 1, 4, 5, 3]), .triangle 7 0, .triangle 16 0, .triangle 4 0]

def cycle0029 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (0), (-2), (-1), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .gapLower 0 5 (![2, 1, 4, 5, 3]), .gapLower 3 2 (![4, 5, 0, 1, 2]), .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![2, 0, 5, 4, 3])]

def cycle0030 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (2), (-2), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 1, 4, 5, 3]), .gapLower 0 5 (![2, 1, 4, 5, 3]), .gapLower 3 2 (![4, 5, 0, 1, 2]), .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0031 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .distance 0 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .gapLower 0 5 (![2, 1, 4, 5, 3]), .triangle 7 0, .triangle 19 0, .triangle 9 0, .gapLower 0 2 (![2, 1, 4, 5, 3])]

def cycle0032 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 2 1]

def cycle0033 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 5, 4, 3]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![2, 1, 4, 5, 3])]

def cycle0034 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 5, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![2, 1, 4, 5, 3])]

def cycle0035 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 5, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 1, 4, 5, 3]), .triangle 2 1]

def cycle0036 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 5, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 9 1, .triangle 2 1]

def cycle0037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 5, 3]), .corridorLower 0 2, .gapLower 0 5 (![2, 1, 4, 5, 3]), .triangle 8 2, .triangle 9 1, .gapLower 0 2 (![2, 1, 4, 5, 3])]

def cycle0038 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 1, 4, 5, 3]), .gapLower 0 2 (![2, 1, 4, 5, 3])]

def cycle0039 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 9 1, .gapLower 0 2 (![2, 1, 4, 5, 3])]

def cycle0040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 4, 5, 3]), .triangle 8 2, .triangle 9 1, .gapLower 0 2 (![2, 1, 4, 5, 3])]

def cycle0041 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![2, 1, 4, 5, 3]), .gapLower 0 3 (![2, 1, 4, 5, 3]), .triangle 7 1, .corridorLower 3 4, .corridorUpper 1 3, .triangle 1 2]

def cycle0042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 4, 5, 3]), .triangle 8 2, .gapLower 0 3 (![2, 1, 4, 5, 3]), .triangle 2 1]

def cycle0043 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 4, 5, 3]), .gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 3 1]

def cycle0044 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 5 3 (![3, 4, 0, 1, 2]), .triangle 6 1]

def cycle0045 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![3, 4, 0, 1, 2]), .triangle 3 0]

def cycle0046 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![3, 4, 0, 1, 2]), .triangle 6 0]

def cycle0047 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 0 0, .triangle 12 2, .triangle 3 0]

def cycle0048 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(0), (-1), (-1), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 7 2, .triangle 9 0, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2])]

def cycle0049 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (0), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 2, .triangle 3 0]

def cycle0050 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 2, .triangle 13 2, .triangle 15 2, .triangle 3 0]

def cycle0051 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5]
    constant := ![(0), (-2), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, true, false] }
  origin := ![.triangle 8 1, .gapLower 3 0 (![5, 4, 0, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 5 3 (![4, 3, 0, 1, 2])]

def cycle0052 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![4, 3, 0, 1, 2]), .triangle 3 0]

def cycle0053 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![4, 3, 0, 1, 2]), .triangle 6 0]

def cycle0054 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-1), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 7 0, .triangle 19 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![5, 4, 0, 1, 2])]

def cycle0055 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![5, 4, 0, 1, 2]), .triangle 1 0]

def cycle0056 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (0), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![5, 4, 0, 1, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 2, .triangle 3 0]

def cycle0057 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1 (![1, 0, 5, 4, 3]), .gapLower 1 0 (![2, 0, 5, 4, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0058 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0060 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0061 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 0]

def cycle0062 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![2, 0, 5, 4, 3]), .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0063 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![2, 0, 5, 4, 3])]

def cycle0064 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 0, 5, 4, 3]), .triangle 3 0]

def cycle0065 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 0, 5, 4, 3]), .triangle 2 0]

def cycle0066 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 0, 5, 4, 3]), .triangle 1 0]

def cycle0067 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0068 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0069 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0070 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-3), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![2, 1, 5, 4, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0071 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 1, 5, 4, 3])]

def cycle0072 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0073 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 5, 4, 3]), .gapLower 1 5 (![2, 0, 5, 4, 3]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0074 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 1 (![2, 0, 5, 4, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 0, 5, 4, 3]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0075 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0076 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0077 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 5 3 (![3, 4, 0, 1, 2]), .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0078 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![3, 4, 0, 1, 2]), .triangle 3 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0079 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![3, 4, 0, 1, 2]), .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0080 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .gapLower 5 3 (![3, 4, 0, 2, 1]), .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0081 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0082 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0084 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 16 2, .triangle 18 2, .triangle 6 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0085 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 5 3 (![4, 3, 0, 1, 2]), .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0086 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![4, 3, 0, 1, 2]), .triangle 3 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0087 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![4, 3, 0, 1, 2]), .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0088 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 12 0, .gapLower 5 3 (![4, 3, 0, 2, 1]), .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0089 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![5, 4, 0, 1, 2]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0090 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![5, 4, 0, 1, 2]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0091 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![5, 4, 0, 1, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0092 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0093 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0094 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0095 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 0, 5, 4, 3]), .triangle 3 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0096 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 0, 5, 4, 3]), .triangle 2 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0097 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 5, 4, 3]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0098 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 5, 4, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0099 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![2, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0100 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0101 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(0), (-2), (0), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.triangle 7 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 9 1, .triangle 19 0, .corridorLower 3 4, .corridorUpper 1 3, .triangle 1 2]

def cycle0102 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![(-2), (0), (-2), (3), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true] }
  origin := ![.gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 8 1, .gapLower 3 0 (![5, 4, 0, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 2 2]

def cycle0103 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![5, 4, 0, 1, 2]), .triangle 7 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0104 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![5, 4, 0, 1, 2]), .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![2, 0, 5, 4, 3])]

def cycle0105 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 16 2, .triangle 5 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0106 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0107 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0108 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 2, .triangle 7 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 6 1]

def cycle0109 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 0, 5, 4, 3]), .triangle 3 0]

def cycle0110 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 0, 5, 4, 3]), .triangle 2 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0111 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 5, 4, 3]), .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0112 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![2, 1, 5, 4, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0113 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (2), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 5, 4, 3]), .thetaOrder 0, .gapLower 0 5 (![2, 1, 5, 4, 3]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0114 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (2), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 1 (![2, 0, 5, 4, 3]), .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 5, 4, 3]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0115 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .gapLower 0 5 (![2, 1, 5, 4, 3]), .triangle 7 0, .triangle 16 0, .triangle 4 0]

def cycle0116 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (0), (-1), (-1), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .gapLower 0 5 (![2, 1, 5, 4, 3]), .triangle 7 2, .triangle 9 0, .triangle 19 0, .corridorLower 3 4, .corridorUpper 1 3, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![2, 0, 5, 4, 3])]

def cycle0117 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .gapLower 0 5 (![2, 1, 5, 4, 3]), .triangle 7 0, .triangle 19 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![2, 0, 5, 4, 3])]

def cycle0118 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0119 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 0, 5, 4, 3]), .triangle 2 0]

def cycle0120 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 5, 4, 3]), .triangle 1 0]

def cycle0121 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0122 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0123 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 1, 5, 4, 3]), .triangle 2 1]

def cycle0124 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 4, 3]), .corridorLower 0 2, .gapLower 0 5 (![2, 1, 5, 4, 3]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0125 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0126 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 1, 5, 4, 3]), .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0127 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 5, 4, 3]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 1, 5, 4, 3])]

def cycle0128 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 1, 5, 4, 3]), .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0129 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 5, 4, 3]), .triangle 7 2, .gapLower 0 3 (![2, 1, 5, 4, 3]), .triangle 3 1]

def cycle0130 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 5, 4, 3]), .gapLower 0 4 (![2, 1, 5, 4, 3]), .triangle 2 1]

def cycle0131 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0132 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0133 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 0 1, .triangle 12 0, .triangle 6 0]

def cycle0134 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![2, 5, 1, 3, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0135 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0136 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![2, 5, 1, 3, 4])]

def cycle0137 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 5, 1, 3, 4]), .triangle 1 1]

def cycle0138 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![2, 5, 1, 3, 4]), .triangle 2 1]

def cycle0139 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![2, 5, 1, 3, 4]), .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0140 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 3, 4]), .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0141 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![2, 5, 1, 3, 4])]

def cycle0142 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 1 0 (![2, 5, 0, 3, 4]), .gapLower 1 5 (![2, 5, 0, 3, 4]), .triangle 2 2, .gapLower 0 4 (![2, 5, 1, 3, 4]), .triangle 1 1]

def cycle0143 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![2, 5, 0, 3, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0144 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 5, 0, 3, 4]), .triangle 12 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .triangle 2 2, .gapLower 0 4 (![2, 5, 1, 3, 4]), .triangle 1 1]

def cycle0145 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 3 (![2, 5, 0, 3, 4])]

def cycle0146 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .gapLower 1 4 (![2, 5, 0, 3, 4]), .triangle 1 0]

def cycle0147 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 12 1, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 0, 3, 4]), .triangle 2 2, .gapLower 0 4 (![2, 5, 1, 3, 4]), .triangle 1 1]

def cycle0148 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![2, 5, 1, 3, 4]), .triangle 1 1]

def cycle0149 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 1 0 (![2, 5, 0, 3, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0150 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2 (![2, 5, 0, 3, 4]), .triangle 12 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0151 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 0, 3, 4]), .triangle 2 0]

def cycle0152 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 1 0 (![2, 5, 0, 4, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .gapLower 0 3 (![2, 5, 1, 3, 4])]

def cycle0153 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![2, 5, 0, 4, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 13 0, .triangle 7 0, .gapLower 0 3 (![2, 5, 1, 3, 4])]

def cycle0154 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2 (![2, 5, 0, 4, 3]), .triangle 12 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0155 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 16 0, .triangle 4 0]

def cycle0156 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 16 0, .triangle 7 0, .triangle 1 1]

def cycle0157 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 0 (![1, 0, 4, 5, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0158 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 1 (![1, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0159 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 2 (![1, 0, 4, 5, 3])]

def cycle0160 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![1, 0, 4, 5, 3]), .triangle 5 0]

def cycle0161 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 4, 5, 3]), .triangle 6 0]

def cycle0162 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 16 0, .triangle 7 0, .triangle 1 1]

def cycle0163 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0164 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0165 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0166 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0167 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 0, .triangle 7 0, .triangle 1 1]

def cycle0168 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 5, 0, 4, 3]), .triangle 2 0]

def cycle0169 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 13 0, .triangle 7 0, .gapLower 0 3 (![2, 5, 1, 3, 4])]

def cycle0170 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 3, 4]), .gapLower 0 1 (![2, 5, 1, 3, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0171 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![2, 5, 1, 3, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![2, 5, 1, 3, 4])]

def cycle0172 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![2, 5, 1, 3, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 5, 1, 3, 4]), .triangle 1 1]

def cycle0173 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![2, 5, 1, 3, 4]), .corridorLower 0 2, .gapLower 0 5 (![2, 5, 1, 3, 4]), .triangle 7 1, .triangle 1 1]

def cycle0174 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 3, 4]), .triangle 6 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![2, 5, 1, 3, 4])]

def cycle0175 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 3, 4]), .triangle 6 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 5, 1, 3, 4]), .triangle 1 1]

def cycle0176 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 3, 4]), .corridorLower 0 5, .gapLower 0 5 (![2, 5, 1, 3, 4]), .triangle 7 1, .triangle 1 1]

def cycle0177 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 5, 1, 3, 4]), .gapLower 0 3 (![2, 5, 1, 3, 4])]

def cycle0178 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 1, 3, 4]), .triangle 7 1, .gapLower 0 3 (![2, 5, 1, 3, 4])]

def cycle0179 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![2, 5, 1, 3, 4]), .gapLower 0 4 (![2, 5, 1, 3, 4]), .triangle 1 1]

def cycle0180 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 5 0]

def cycle0181 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (0), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 1 0 (![2, 5, 0, 4, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 19 2, .triangle 8 0, .triangle 1 1]

def cycle0182 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![(0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 16 2, .triangle 18 0, .triangle 19 0, .gapLower 3 0 (![4, 5, 0, 1, 2]), .corridorUpper 2 3]

def cycle0183 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (3), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 0]

def cycle0184 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 14 0, .triangle 1 0]

def cycle0185 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 2 0]

def cycle0186 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (3), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 0]

def cycle0187 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2]), .triangle 1 1]

def cycle0188 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .gapLower 2 5 (![1, 0, 5, 4, 3]), .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 1 0]

def cycle0189 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 4 0]

def cycle0190 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 10 2, .triangle 13 2, .triangle 2 0]

def cycle0191 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 1 0]

def cycle0192 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (3), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 3 0 (![5, 4, 0, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .triangle 1 0]

def cycle0193 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .gapLower 2 5 (![1, 0, 5, 4, 3]), .gapLower 3 4 (![5, 4, 0, 1, 2]), .triangle 1 0]

def cycle0194 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![5, 4, 0, 1, 2]), .triangle 4 0]

def cycle0195 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .gapLower 1 0 (![2, 5, 0, 4, 3]), .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 0]

def cycle0196 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0197 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0198 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0199 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 0]

def cycle0200 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![2, 5, 0, 4, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 0]

def cycle0201 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 1 2 (![2, 5, 0, 4, 3]), .triangle 12 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0202 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 19 2, .triangle 8 0, .triangle 1 1]

def cycle0203 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (3), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 2 (![2, 5, 0, 4, 3]), .triangle 14 1, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 0]

def cycle0204 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2]), .triangle 1 1]

def cycle0205 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 1 0]

def cycle0206 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (3), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 1 2 (![2, 5, 0, 4, 3]), .triangle 15 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 0]

def cycle0207 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![5, 4, 0, 1, 2]), .triangle 1 0]

def cycle0208 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0209 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 5, 0, 4, 3]), .triangle 2 0]

def cycle0210 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 0]

def cycle0211 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![2, 5, 1, 4, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0212 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 4, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0213 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0214 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0215 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 1 1]

def cycle0216 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![2, 5, 1, 4, 3]), .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0217 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 4, 3]), .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0218 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 1 0 (![2, 5, 0, 4, 3]), .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0219 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![2, 5, 0, 4, 3]), .gapLower 1 1 (![2, 5, 0, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0220 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![2, 5, 0, 4, 3]), .corridorLower 1 5, .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0221 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 5 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0222 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0223 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0224 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0225 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0226 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 14 0, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0227 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0228 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2]), .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0229 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0230 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0231 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 10 0, .triangle 16 2, .triangle 5 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0232 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 2 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0233 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0234 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![5, 4, 0, 1, 2]), .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0235 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![5, 4, 0, 1, 2]), .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0236 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![5, 4, 0, 1, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0237 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0238 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0239 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0240 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 5, 0, 4, 3]), .triangle 2 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0241 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0242 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 1 0 (![2, 5, 0, 4, 3]), .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0243 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![2, 5, 0, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0244 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 5, 0, 4, 3]), .triangle 12 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0245 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 4 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0246 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 0 (![1, 0, 4, 5, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0247 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 2 (![1, 0, 4, 5, 3])]

def cycle0248 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![1, 0, 4, 5, 3]), .triangle 5 0]

def cycle0249 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 4, 5, 3]), .triangle 6 0]

def cycle0250 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 4 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0251 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0252 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0253 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0254 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2]), .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0255 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0256 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 10 0, .gapLower 3 3 (![4, 5, 0, 2, 1]), .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0257 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 7 1, .triangle 19 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0258 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0259 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0260 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 5, 0, 4, 3]), .triangle 2 0]

def cycle0261 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 12 1, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0262 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .distance 0 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 7 0, .triangle 13 0, .gapLower 1 3 (![2, 5, 0, 3, 4])]

def cycle0263 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 1 0 (![2, 5, 0, 4, 3]), .thetaOrder 0, .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 1 1]

def cycle0264 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![2, 5, 0, 4, 3]), .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 1 1]

def cycle0265 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 5, 0, 4, 3]), .triangle 12 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 1 1]

def cycle0266 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 7 0, .triangle 16 0, .triangle 4 0]

def cycle0267 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .gapLower 2 0 (![1, 0, 4, 3, 5]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0268 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 1 (![1, 0, 4, 3, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0269 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 16 2, .gapLower 2 2 (![1, 0, 4, 3, 5])]

def cycle0270 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .gapLower 2 3 (![1, 0, 4, 3, 5]), .triangle 5 0]

def cycle0271 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 2, .gapLower 2 4 (![1, 0, 4, 3, 5]), .triangle 4 0]

def cycle0272 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .gapLower 3 3 (![4, 0, 1, 2, 5]), .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0273 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 2 3, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 17 0, .triangle 8 0]

def cycle0274 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0275 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (0), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .triangle 10 0, .triangle 17 2, .triangle 18 1, .triangle 5 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0276 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 7 0, .triangle 19 0, .triangle 18 0, .gapLower 2 2 (![1, 0, 4, 5, 3])]

def cycle0277 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (2), (-1), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 8 0, .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0278 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (2), (-2), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 1, 4, 3]), .gapLower 0 5 (![2, 5, 1, 4, 3]), .gapLower 3 2 (![4, 5, 0, 1, 2]), .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0279 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 1, 4, 3]), .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 7 0, .triangle 19 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 5, 0, 4, 3])]

def cycle0280 : Cycle where
  length := 6
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .distance 2 3]
    constant := ![(0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 16 2, .triangle 18 0, .triangle 19 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 5 (![1, 0, 5, 4, 3])]

def cycle0281 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 12 1, .corridorLower 1 2, .gapLower 1 5 (![2, 5, 0, 4, 3]), .triangle 1 0]

def cycle0282 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 4, 3]), .gapLower 0 1 (![2, 5, 1, 4, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0283 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![2, 5, 1, 4, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0284 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![2, 5, 1, 4, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0285 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![2, 5, 1, 4, 3]), .corridorLower 0 2, .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 1 1]

def cycle0286 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 4, 3]), .triangle 6 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0287 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 4, 3]), .triangle 6 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0288 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 2 (![2, 5, 1, 4, 3]), .corridorLower 0 5, .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 1 1]

def cycle0289 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 1, 4, 3]), .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0290 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 1, 4, 3]), .triangle 7 2, .gapLower 0 3 (![2, 5, 1, 4, 3])]

def cycle0291 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![2, 5, 1, 4, 3]), .gapLower 0 4 (![2, 5, 1, 4, 3]), .triangle 2 1]

def cycle0292 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0293 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0294 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 0 1, .triangle 11 0, .triangle 5 0]

def cycle0295 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![2, 4, 1, 3, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0296 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0297 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![2, 4, 1, 3, 5])]

def cycle0298 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 4, 1, 3, 5]), .triangle 1 1]

def cycle0299 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![2, 4, 1, 3, 5]), .triangle 8 1, .triangle 1 1]

def cycle0300 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![2, 4, 1, 3, 5]), .gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0301 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 3, 5]), .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0302 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![2, 4, 1, 3, 5])]

def cycle0303 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 1 0 (![2, 4, 0, 3, 5]), .gapLower 1 5 (![2, 4, 0, 3, 5]), .triangle 3 2, .gapLower 0 4 (![2, 4, 1, 3, 5]), .triangle 1 1]

def cycle0304 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1 (![2, 4, 0, 3, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0305 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 4, 0, 3, 5]), .triangle 11 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 2, .triangle 3 2, .gapLower 0 4 (![2, 4, 1, 3, 5]), .triangle 1 1]

def cycle0306 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 3 (![2, 4, 0, 3, 5])]

def cycle0307 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 2, .gapLower 1 4 (![2, 4, 0, 3, 5]), .triangle 1 0]

def cycle0308 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 0, 3, 5]), .triangle 3 2, .gapLower 0 4 (![2, 4, 1, 3, 5]), .triangle 1 1]

def cycle0309 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![2, 4, 1, 3, 5]), .triangle 1 1]

def cycle0310 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 1 0 (![2, 4, 0, 3, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0311 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2 (![2, 4, 0, 3, 5]), .triangle 11 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0312 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 0, 3, 5]), .triangle 3 0]

def cycle0313 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 1 0 (![2, 4, 0, 5, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0314 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1 (![2, 4, 0, 5, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 14 0, .triangle 8 0, .gapLower 0 3 (![2, 4, 1, 3, 5])]

def cycle0315 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2 (![2, 4, 0, 5, 3]), .triangle 11 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0316 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 0, .triangle 17 0, .triangle 4 0]

def cycle0317 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 0, .triangle 1 1]

def cycle0318 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 2 0 (![1, 0, 4, 5, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0319 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 2 1 (![1, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0320 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 2 (![1, 0, 4, 5, 3])]

def cycle0321 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![1, 0, 4, 5, 3]), .triangle 5 0]

def cycle0322 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 4, 5, 3]), .triangle 6 0]

def cycle0323 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 17 0, .triangle 8 0, .triangle 1 1]

def cycle0324 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0325 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0326 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0327 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0328 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 5 1]

def cycle0329 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 3, 5]), .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 0, 5, 3]), .triangle 3 0]

def cycle0330 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 14 0, .triangle 8 0, .gapLower 0 3 (![2, 4, 1, 3, 5])]

def cycle0331 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 3, 5]), .gapLower 0 1 (![2, 4, 1, 3, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0332 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![2, 4, 1, 3, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![2, 4, 1, 3, 5])]

def cycle0333 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![2, 4, 1, 3, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 4, 1, 3, 5]), .triangle 1 1]

def cycle0334 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![2, 4, 1, 3, 5]), .corridorLower 0 2, .gapLower 0 5 (![2, 4, 1, 3, 5]), .triangle 3 1]

def cycle0335 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 3, 5]), .triangle 5 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![2, 4, 1, 3, 5])]

def cycle0336 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 3, 5]), .triangle 5 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 4, 1, 3, 5]), .triangle 1 1]

def cycle0337 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 3, 5]), .corridorLower 0 4, .gapLower 0 5 (![2, 4, 1, 3, 5]), .triangle 8 1, .triangle 1 1]

def cycle0338 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 4, 1, 3, 5]), .gapLower 0 3 (![2, 4, 1, 3, 5])]

def cycle0339 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 1, 3, 5]), .triangle 8 1, .gapLower 0 3 (![2, 4, 1, 3, 5])]

def cycle0340 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![2, 4, 1, 3, 5]), .gapLower 0 4 (![2, 4, 1, 3, 5]), .triangle 1 1]

def cycle0341 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0342 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 5 0]

def cycle0343 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 5 1]

def cycle0344 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1 (![2, 4, 0, 5, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 1 0]

def cycle0345 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0346 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 5, 3]), .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 0, 5, 3]), .triangle 3 0]

def cycle0347 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 1 0]

def cycle0348 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![2, 4, 1, 5, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0349 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 5, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0350 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0351 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 8 1, .corridorLower 3 5, .corridorUpper 1 3, .triangle 1 2]

def cycle0352 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 4, 1, 5, 3])]

def cycle0353 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![2, 4, 1, 5, 3]), .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0354 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 5, 3]), .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0355 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 1 0 (![2, 4, 0, 5, 3]), .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0356 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![2, 4, 0, 5, 3]), .gapLower 1 1 (![2, 4, 0, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0357 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![2, 4, 0, 5, 3]), .corridorLower 1 4, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0358 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 2, .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0359 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 2 0 (![1, 0, 4, 5, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0360 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 2 1 (![1, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0361 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 2 (![1, 0, 4, 5, 3])]

def cycle0362 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![1, 0, 4, 5, 3]), .triangle 5 0]

def cycle0363 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 4, 5, 3]), .triangle 6 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0364 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 4 2, .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0365 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 9 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0366 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 0, 5, 3]), .triangle 3 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0367 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0368 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 1 0 (![2, 4, 0, 5, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 3 1]

def cycle0369 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 4, 0, 5, 3]), .gapLower 1 1 (![2, 4, 0, 5, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 1 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 3 1]

def cycle0370 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 4, 0, 5, 3]), .triangle 11 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 3 1]

def cycle0371 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 9 1, .triangle 5 1]

def cycle0372 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 2 0 (![1, 0, 4, 5, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 3 1]

def cycle0373 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 4, 5, 3]), .triangle 6 0]

def cycle0374 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 4 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 6 1]

def cycle0375 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 3 1]

def cycle0376 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (0), (-2), (-1), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 8 1, .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0377 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .gapLower 5 3 (![3, 0, 1, 4, 2]), .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0378 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 2 0, .triangle 15 2, .triangle 3 0]

def cycle0379 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2]), .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 9 1, .triangle 5 1]

def cycle0380 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0381 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0382 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 10 0, .gapLower 3 3 (![4, 5, 0, 2, 1]), .gapLower 0 4 (![2, 4, 1, 5, 3]), .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0383 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 19 0, .triangle 9 0, .gapLower 0 1 (![2, 4, 1, 5, 3])]

def cycle0384 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0385 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0386 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 6 1]

def cycle0387 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 0, 5, 3]), .triangle 3 0]

def cycle0388 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 1 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 3 1]

def cycle0389 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .gapLower 0 5 (![2, 4, 1, 5, 3]), .triangle 8 0, .triangle 14 0, .gapLower 1 3 (![2, 4, 0, 3, 5])]

def cycle0390 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, true, true] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 1 0 (![2, 4, 0, 5, 3]), .thetaOrder 0, .gapLower 0 5 (![2, 4, 1, 5, 3]), .triangle 8 2, .triangle 3 1]

def cycle0391 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 1 (![2, 4, 0, 5, 3]), .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 1, 5, 3]), .triangle 1 1]

def cycle0392 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 4, 0, 5, 3]), .triangle 11 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 1, 5, 3]), .triangle 1 1]

def cycle0393 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .gapLower 0 5 (![2, 4, 1, 5, 3]), .triangle 8 0, .triangle 17 0, .triangle 4 0]

def cycle0394 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .gapLower 2 0 (![1, 0, 5, 3, 4]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0395 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 2 1 (![1, 0, 5, 3, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0396 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 2, .gapLower 2 2 (![1, 0, 5, 3, 4])]

def cycle0397 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 3 (![1, 0, 5, 3, 4]), .triangle 6 0]

def cycle0398 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![1, 0, 5, 3, 4]), .triangle 4 0]

def cycle0399 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 3 3 (![5, 0, 1, 2, 4]), .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0400 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 10 2, .triangle 14 2, .triangle 3 0]

def cycle0401 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .gapLower 0 5 (![2, 4, 1, 5, 3]), .triangle 8 0, .triangle 17 0, .gapLower 2 3 (![1, 0, 4, 3, 5]), .gapLower 2 2 (![1, 0, 4, 3, 5])]

def cycle0402 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0403 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 1 2]
    constant := ![(-1), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.triangle 10 0, .triangle 17 2, .triangle 18 1, .triangle 11 0]

def cycle0404 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 3 4, .distance 4 5, .distance 2 4]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 16 1, .triangle 19 0, .triangle 18 0]

def cycle0405 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (0), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 4, 1, 5, 3]), .gapLower 0 5 (![2, 4, 1, 5, 3]), .gapLower 3 2 (![4, 5, 0, 1, 2]), .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 14 2, .gapLower 1 3 (![2, 4, 0, 5, 3])]

def cycle0406 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (2), (-2), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .gapLower 0 5 (![2, 4, 1, 5, 3]), .gapLower 3 2 (![4, 5, 0, 1, 2]), .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0407 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 9 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0408 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (2), (-1), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .gapLower 0 5 (![2, 4, 1, 5, 3]), .triangle 8 0, .triangle 19 1, .triangle 9 0, .gapLower 0 1 (![2, 4, 1, 5, 3])]

def cycle0409 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 1, 5, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 5 1]

def cycle0410 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 0, 5, 3]), .triangle 14 2, .triangle 3 0]

def cycle0411 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 5, 3]), .gapLower 0 1 (![2, 4, 1, 5, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0412 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![2, 4, 1, 5, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0413 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![2, 4, 1, 5, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 3 1]

def cycle0414 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![2, 4, 1, 5, 3]), .corridorLower 0 2, .gapLower 0 5 (![2, 4, 1, 5, 3]), .triangle 8 2, .triangle 3 1]

def cycle0415 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 5, 3]), .triangle 5 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0416 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 5, 3]), .triangle 5 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 3 1]

def cycle0417 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 2 (![2, 4, 1, 5, 3]), .corridorLower 0 4, .gapLower 0 5 (![2, 4, 1, 5, 3]), .triangle 1 1]

def cycle0418 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 1, 5, 3]), .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0419 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 1, 5, 3]), .triangle 8 2, .gapLower 0 3 (![2, 4, 1, 5, 3])]

def cycle0420 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 1, 5, 3]), .gapLower 0 4 (![2, 4, 1, 5, 3]), .triangle 3 1]

def cycle0421 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0422 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 5 0]

def cycle0423 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 5 1]

def cycle0424 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 1 (![2, 4, 5, 0, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0425 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 2 (![2, 4, 5, 0, 3]), .corridorLower 1 4, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0426 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0427 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0428 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![2, 4, 5, 1, 3]), .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0429 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 0, .triangle 6 0, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0430 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 1 (![2, 4, 5, 1, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0431 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![2, 4, 5, 1, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0432 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 4, 5, 1, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0433 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0434 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 1 1]

def cycle0435 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 1 (![2, 4, 5, 1, 3]), .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0436 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![2, 4, 5, 1, 3]), .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0437 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 4, 5, 1, 3]), .triangle 6 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0438 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (4), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .gapLower 1 0 (![2, 4, 5, 0, 3]), .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0439 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![2, 4, 5, 0, 3]), .triangle 15 1, .gapLower 1 1 (![2, 4, 5, 0, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0440 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![2, 4, 5, 0, 3]), .gapLower 1 2 (![2, 4, 5, 0, 3]), .triangle 11 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0441 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![2, 4, 5, 0, 3]), .corridorLower 1 5, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0442 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0443 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 4 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0444 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .gapLower 2 0 (![1, 0, 4, 5, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0445 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 2 1 (![1, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0446 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 2 (![1, 0, 4, 5, 3])]

def cycle0447 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![1, 0, 4, 5, 3]), .triangle 5 0]

def cycle0448 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 4, 5, 3]), .triangle 6 0]

def cycle0449 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 4 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0450 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0451 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0452 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 19 2, .triangle 8 0]

def cycle0453 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0454 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 14 0, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0455 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0456 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2]), .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0457 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0458 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0459 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2]
    constant := ![(-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 15 0, .triangle 11 1]

def cycle0460 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0461 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0462 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0463 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0464 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .gapLower 1 0 (![2, 4, 5, 0, 3]), .thetaOrder 0, .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 1 1]

def cycle0465 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 1 (![2, 4, 5, 0, 3]), .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 1 1]

def cycle0466 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 2 (![2, 4, 5, 0, 3]), .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 1 1]

def cycle0467 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.gapLower 1 3 (![2, 4, 5, 0, 3]), .triangle 15 1, .triangle 11 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 1 1]

def cycle0468 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .gapLower 2 0 (![1, 0, 3, 4, 5]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0469 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 2 1 (![1, 0, 3, 4, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0470 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![1, 0, 3, 4, 5])]

def cycle0471 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 3 (![1, 0, 3, 4, 5]), .triangle 4 0]

def cycle0472 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 2, .gapLower 2 4 (![1, 0, 3, 4, 5]), .triangle 5 0]

def cycle0473 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 2, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0474 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .triangle 10 2, .triangle 1 0]

def cycle0475 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .gapLower 2 0 (![1, 0, 3, 5, 4]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0476 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 2 1 (![1, 0, 3, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0477 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![1, 0, 3, 5, 4])]

def cycle0478 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 18 2, .gapLower 2 3 (![1, 0, 3, 5, 4]), .triangle 4 0]

def cycle0479 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![1, 0, 3, 5, 4]), .triangle 6 0]

def cycle0480 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 3, 5, 4]), .triangle 18 0, .triangle 9 0, .triangle 5 1]

def cycle0481 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .gapLower 2 0 (![1, 0, 5, 3, 4]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0482 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 2 1 (![1, 0, 5, 3, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0483 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 2, .gapLower 2 2 (![1, 0, 5, 3, 4])]

def cycle0484 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 3 (![1, 0, 5, 3, 4]), .triangle 6 0]

def cycle0485 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![1, 0, 5, 3, 4]), .triangle 4 0]

def cycle0486 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 0, .triangle 1 1]

def cycle0487 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 3 3 (![5, 0, 1, 2, 4]), .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0488 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .gapLower 2 0 (![1, 0, 4, 3, 5]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0489 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 2 1 (![1, 0, 4, 3, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0490 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 16 2, .gapLower 2 2 (![1, 0, 4, 3, 5])]

def cycle0491 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .gapLower 2 3 (![1, 0, 4, 3, 5]), .triangle 5 0]

def cycle0492 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 2, .gapLower 2 4 (![1, 0, 4, 3, 5]), .triangle 4 0]

def cycle0493 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 16 0, .triangle 7 0, .triangle 1 1]

def cycle0494 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .gapLower 3 3 (![4, 0, 1, 2, 5]), .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0495 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .gapLower 2 0 (![1, 0, 4, 5, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0496 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 2 1 (![1, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0497 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 16 0, .triangle 7 0, .triangle 1 1]

def cycle0498 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 10 2, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0499 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 7 0, .triangle 19 0, .triangle 9 0, .gapLower 0 1 (![2, 4, 5, 1, 3])]

def cycle0500 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0501 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0502 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (2), (-1), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 8 0, .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0503 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (2), (-2), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .gapLower 0 5 (![2, 4, 5, 1, 3]), .gapLower 3 2 (![4, 5, 0, 1, 2]), .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0504 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![4, 5, 0, 1, 2]), .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0505 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 4, 5, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 5 1]

def cycle0506 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0507 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![2, 4, 5, 1, 3]), .gapLower 0 0 (![2, 4, 5, 1, 3]), .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 1 1]

def cycle0508 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 0, .triangle 6 0, .gapLower 0 0 (![2, 4, 5, 1, 3]), .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 1 1]

def cycle0509 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![2, 4, 5, 1, 3]), .gapLower 0 1 (![2, 4, 5, 1, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0510 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 4, 5, 1, 3]), .triangle 9 1, .gapLower 0 1 (![2, 4, 5, 1, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0511 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 1 (![2, 4, 5, 1, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0512 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 1 (![2, 4, 5, 1, 3]), .corridorLower 0 2, .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 1 1]

def cycle0513 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 4, 5, 1, 3]), .gapLower 0 2 (![2, 4, 5, 1, 3]), .triangle 5 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0514 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![2, 4, 5, 1, 3]), .triangle 5 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0515 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![2, 4, 5, 1, 3]), .corridorLower 0 4, .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 1 1]

def cycle0516 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![2, 4, 5, 1, 3]), .triangle 9 1, .triangle 5 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0517 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 3 (![2, 4, 5, 1, 3]), .corridorLower 0 5, .gapLower 0 5 (![2, 4, 5, 1, 3]), .triangle 1 1]

def cycle0518 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 4, 5, 1, 3]), .gapLower 0 4 (![2, 4, 5, 1, 3])]

def cycle0519 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .triangle 11 1, .gapLower 1 0 (![2, 4, 5, 0, 3]), .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0520 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 5, 0, 3]), .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0521 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![2, 4, 5, 0, 3]), .corridorLower 1 4, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0522 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0523 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 5, 0, 3]), .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0524 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 1 1]

def cycle0525 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 19 0, .corridorLower 3 4, .corridorUpper 1 3, .triangle 1 0]

def cycle0526 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 3 (![2, 4, 5, 0, 3]), .gapLower 5 0 (![1, 4, 3, 0, 2]), .thetaOrder 4, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 0]

def cycle0527 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 3 4, .distance 4 5, .distance 1 5, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 19 0, .gapLower 5 1 (![1, 4, 3, 0, 2]), .corridorLower 1 5, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0528 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 3 4, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (-1), (0), (0), (3), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 19 2, .gapLower 5 2 (![1, 4, 3, 0, 2]), .triangle 15 0, .gapLower 1 1 (![2, 4, 5, 0, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 0]

def cycle0529 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (4), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 5 3 (![1, 4, 3, 0, 2]), .gapLower 3 0 (![5, 4, 0, 1, 2]), .gapLower 3 5 (![5, 4, 0, 1, 2]), .triangle 10 2, .triangle 1 0]

def cycle0530 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 5]
    constant := ![(0), (-2), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, true, false] }
  origin := ![.triangle 8 1, .gapLower 3 0 (![5, 4, 0, 1, 2]), .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![1, 4, 3, 0, 2])]

def cycle0531 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![1, 4, 3, 0, 2]), .triangle 6 0]

def cycle0532 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 3 4, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (3), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 3 1 (![5, 4, 0, 1, 2]), .corridorLower 3 5, .corridorUpper 2 3, .triangle 10 2, .triangle 1 0]

def cycle0533 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-1), (-1), (0), (-1), (0), (0), (0), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 3 2 (![5, 4, 0, 1, 2]), .triangle 19 0, .triangle 15 0, .gapLower 1 1 (![2, 4, 5, 0, 3]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0534 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![5, 4, 0, 1, 2]), .triangle 1 0]

def cycle0535 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![5, 4, 0, 1, 2]), .triangle 4 0]

def cycle0536 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 2]
    constant := ![(-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 10 0, .triangle 16 0, .triangle 19 0, .gapLower 4 1 (![1, 5, 3, 0, 2]), .triangle 11 1]

def cycle0537 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0538 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0539 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0540 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 4 0]

def cycle0541 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 4, 5, 0, 3])]

def cycle0542 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .triangle 11 1, .corridorLower 1 2, .gapLower 1 5 (![2, 4, 5, 0, 3]), .triangle 1 0]

def cycle0543 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0544 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 0, .triangle 6 0, .gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0545 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 1, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0546 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![2, 5, 4, 1, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0547 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![2, 5, 4, 1, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0548 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 4, 1, 3])]

def cycle0549 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![2, 5, 4, 1, 3]), .triangle 1 1]

def cycle0550 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 1, 3]), .gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0551 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![2, 5, 4, 1, 3]), .triangle 6 1, .gapLower 0 0 (![2, 5, 4, 1, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0552 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![2, 5, 4, 1, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0553 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 4, 1, 3])]

def cycle0554 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .triangle 11 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 4, 1, 3]), .triangle 1 1]

def cycle0555 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 11 1, .triangle 12 0, .triangle 6 0, .gapLower 0 0 (![2, 5, 4, 1, 3]), .gapLower 0 5 (![2, 5, 4, 1, 3]), .triangle 1 1]

def cycle0556 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![2, 5, 4, 1, 3]), .gapLower 0 1 (![2, 5, 4, 1, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0557 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 5, 4, 1, 3]), .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 1, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0558 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 1, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 4, 1, 3])]

def cycle0559 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 1 (![2, 5, 4, 1, 3]), .corridorLower 0 2, .gapLower 0 5 (![2, 5, 4, 1, 3]), .triangle 1 1]

def cycle0560 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 0 3 (![2, 5, 4, 1, 3]), .gapLower 0 2 (![2, 5, 4, 1, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0561 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![2, 5, 4, 1, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 4, 1, 3])]

def cycle0562 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![2, 5, 4, 1, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0563 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3 (![2, 5, 4, 1, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![2, 5, 4, 1, 3])]

def cycle0564 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 4, 1, 3]), .gapLower 0 4 (![2, 5, 4, 1, 3])]

def cycle0565 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0566 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0567 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 0 1, .triangle 10 0, .triangle 4 0]

def cycle0568 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![2, 3, 1, 4, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0569 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 4, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0570 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![2, 3, 1, 4, 5])]

def cycle0571 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 1, 4, 5]), .triangle 2 1]

def cycle0572 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 1, 4, 5]), .triangle 9 1, .triangle 2 1]

def cycle0573 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![2, 3, 1, 4, 5]), .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0574 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 4, 5]), .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0575 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![2, 3, 1, 4, 5])]

def cycle0576 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 1 0 (![2, 3, 0, 4, 5]), .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 2, .triangle 3 2, .gapLower 0 4 (![2, 3, 1, 4, 5]), .triangle 2 1]

def cycle0577 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 3, 0, 4, 5]), .gapLower 1 1 (![2, 3, 0, 4, 5]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 2, .triangle 3 2, .gapLower 0 4 (![2, 3, 1, 4, 5]), .triangle 2 1]

def cycle0578 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 3, 0, 4, 5]), .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 2, .triangle 3 2, .gapLower 0 4 (![2, 3, 1, 4, 5]), .triangle 2 1]

def cycle0579 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 3 (![2, 3, 0, 4, 5])]

def cycle0580 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 2, .gapLower 1 4 (![2, 3, 0, 4, 5]), .triangle 2 0]

def cycle0581 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 1 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 0, 4, 5]), .triangle 3 2, .gapLower 0 4 (![2, 3, 1, 4, 5]), .triangle 2 1]

def cycle0582 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![2, 3, 1, 4, 5]), .triangle 7 1, .triangle 4 1]

def cycle0583 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 1 0 (![2, 3, 0, 4, 5]), .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0584 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1 (![2, 3, 0, 4, 5]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0585 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2 (![2, 3, 0, 4, 5]), .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0586 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 0, 4, 5]), .triangle 15 1, .triangle 2 0]

def cycle0587 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 1 0 (![2, 3, 0, 5, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0588 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1 (![2, 3, 0, 5, 4]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![2, 3, 1, 4, 5])]

def cycle0589 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2 (![2, 3, 0, 5, 4]), .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0590 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 0, .triangle 18 0, .triangle 16 1, .triangle 4 0]

def cycle0591 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 5, 4]), .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 3 (![2, 3, 0, 5, 4])]

def cycle0592 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 2 1 (![1, 0, 3, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 3 (![2, 3, 0, 5, 4])]

def cycle0593 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![1, 0, 3, 5, 4])]

def cycle0594 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 18 2, .gapLower 2 3 (![1, 0, 3, 5, 4]), .triangle 4 0]

def cycle0595 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![1, 0, 3, 5, 4]), .triangle 6 0]

def cycle0596 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 3, 5, 4]), .triangle 18 0, .triangle 9 0, .triangle 2 1]

def cycle0597 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 0, .triangle 4 1]

def cycle0598 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 0, .triangle 18 0, .triangle 5 0]

def cycle0599 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 3 (![2, 3, 0, 5, 4])]

def cycle0600 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 3 (![2, 3, 0, 5, 4])]

def cycle0601 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 19 0, .triangle 7 0, .triangle 4 1]

def cycle0602 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 19 0, .triangle 9 0, .triangle 2 1]

def cycle0603 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0604 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 18 0, .triangle 9 0, .triangle 2 1]

def cycle0605 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 2 1]

def cycle0606 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 0, 5, 4]), .triangle 15 1, .triangle 9 0, .triangle 2 1]

def cycle0607 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 0, 5, 4]), .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![2, 3, 1, 4, 5])]

def cycle0608 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 4, 5]), .gapLower 0 1 (![2, 3, 1, 4, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0609 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![2, 3, 1, 4, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![2, 3, 1, 4, 5])]

def cycle0610 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![2, 3, 1, 4, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 1, 4, 5]), .triangle 2 1]

def cycle0611 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![2, 3, 1, 4, 5]), .corridorLower 0 2, .gapLower 0 5 (![2, 3, 1, 4, 5]), .triangle 9 1, .triangle 2 1]

def cycle0612 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 4, 5]), .triangle 4 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![2, 3, 1, 4, 5])]

def cycle0613 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 4, 5]), .triangle 4 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 1, 4, 5]), .triangle 2 1]

def cycle0614 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 4, 5]), .corridorLower 0 3, .gapLower 0 5 (![2, 3, 1, 4, 5]), .triangle 9 1, .triangle 2 1]

def cycle0615 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 1, 4, 5]), .gapLower 0 3 (![2, 3, 1, 4, 5])]

def cycle0616 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 1, 4, 5]), .triangle 9 1, .gapLower 0 3 (![2, 3, 1, 4, 5])]

def cycle0617 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 1, 4, 5]), .gapLower 0 4 (![2, 3, 1, 4, 5]), .triangle 2 1]

def cycle0618 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0619 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0620 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1 (![2, 3, 0, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0621 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 3 (![2, 3, 0, 5, 4])]

def cycle0622 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 5, 4]), .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 0, 5, 4]), .triangle 3 0]

def cycle0623 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 5, 4]), .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 0, 5, 4]), .triangle 2 0]

def cycle0624 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![2, 3, 1, 5, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0625 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 5, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0626 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0627 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .distance 1 4, .distance 0 4]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![2, 3, 1, 5, 4]), .triangle 9 1, .corridorLower 4 5, .corridorUpper 1 4, .triangle 2 2]

def cycle0628 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4]
    constant := ![(-1), (-1), (0), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 3, 1, 5, 4])]

def cycle0629 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![2, 3, 1, 5, 4]), .gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0630 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 5, 4]), .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0631 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 1 0 (![2, 3, 0, 5, 4]), .gapLower 1 5 (![2, 3, 0, 5, 4]), .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0632 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![2, 3, 0, 5, 4]), .gapLower 1 1 (![2, 3, 0, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0633 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![2, 3, 0, 5, 4]), .corridorLower 1 3, .gapLower 1 5 (![2, 3, 0, 5, 4]), .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0634 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 2, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 5, 4]), .gapLower 2 5 (![1, 0, 3, 5, 4]), .triangle 18 2, .triangle 6 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0635 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 2 1 (![1, 0, 3, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0636 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![1, 0, 3, 5, 4])]

def cycle0637 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 18 2, .gapLower 2 3 (![1, 0, 3, 5, 4]), .triangle 4 0]

def cycle0638 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![1, 0, 3, 5, 4]), .triangle 6 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0639 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 3, 5, 4]), .triangle 5 2, .triangle 9 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0640 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0641 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 2, .triangle 9 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0642 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 0, 5, 4]), .triangle 3 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0643 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 0, 5, 4]), .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0644 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 1 0 (![2, 3, 0, 5, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 1, 5, 4]), .triangle 3 1]

def cycle0645 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 3, 0, 5, 4]), .gapLower 1 1 (![2, 3, 0, 5, 4]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 1, 5, 4]), .triangle 3 1]

def cycle0646 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 3, 0, 5, 4]), .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 1, 5, 4]), .triangle 3 1]

def cycle0647 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 5, 4]), .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 1, 5, 4]), .triangle 3 1]

def cycle0648 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![1, 0, 3, 5, 4]), .triangle 6 0]

def cycle0649 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 3, 5, 4]), .triangle 5 2, .gapLower 0 4 (![2, 3, 1, 5, 4]), .triangle 6 1]

def cycle0650 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 0, .triangle 4 1]

def cycle0651 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 2, .gapLower 0 4 (![2, 3, 1, 5, 4]), .triangle 8 1, .triangle 4 1]

def cycle0652 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 0, 5, 4]), .triangle 3 0]

def cycle0653 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 1 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 0, 5, 4]), .triangle 2 2, .gapLower 0 4 (![2, 3, 1, 5, 4]), .triangle 3 1]

def cycle0654 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 1 0 (![2, 3, 0, 5, 4]), .thetaOrder 0, .gapLower 0 5 (![2, 3, 1, 5, 4]), .triangle 2 1]

def cycle0655 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 1 (![2, 3, 0, 5, 4]), .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 1, 5, 4]), .triangle 2 1]

def cycle0656 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.gapLower 1 2 (![2, 3, 0, 5, 4]), .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 1, 5, 4]), .triangle 2 1]

def cycle0657 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .gapLower 0 5 (![2, 3, 1, 5, 4]), .triangle 9 0, .triangle 18 0, .gapLower 2 3 (![1, 0, 3, 4, 5]), .triangle 4 0]

def cycle0658 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .gapLower 0 5 (![2, 3, 1, 5, 4]), .triangle 9 0, .triangle 19 0, .gapLower 3 3 (![1, 0, 2, 4, 5]), .triangle 4 0]

def cycle0659 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 3 0 (![1, 0, 2, 5, 4]), .thetaOrder 2, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 3 (![2, 3, 0, 5, 4])]

def cycle0660 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 3 1 (![1, 0, 2, 5, 4]), .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 3 (![2, 3, 0, 5, 4])]

def cycle0661 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 3 2 (![1, 0, 2, 5, 4]), .triangle 4 1]

def cycle0662 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 3 3 (![1, 0, 2, 5, 4]), .triangle 4 0]

def cycle0663 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![1, 0, 2, 5, 4]), .triangle 17 0, .triangle 4 0]

def cycle0664 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![1, 0, 2, 5, 4]), .triangle 16 0, .triangle 4 0]

def cycle0665 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 4, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .gapLower 0 5 (![2, 3, 1, 5, 4]), .triangle 9 0, .triangle 18 0, .triangle 5 0]

def cycle0666 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 3 0 (![1, 0, 5, 4, 2]), .thetaOrder 2, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 3 (![2, 3, 0, 5, 4])]

def cycle0667 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 3 1 (![1, 0, 5, 4, 2]), .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 3 (![2, 3, 0, 5, 4])]

def cycle0668 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 19 2, .gapLower 3 2 (![1, 0, 5, 4, 2]), .triangle 4 1]

def cycle0669 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .gapLower 3 3 (![1, 0, 5, 4, 2]), .triangle 8 0, .gapLower 0 1 (![2, 3, 1, 5, 4])]

def cycle0670 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![1, 0, 5, 4, 2]), .triangle 7 0, .triangle 4 1]

def cycle0671 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![1, 0, 5, 4, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0672 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0673 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0674 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 1, 5, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0675 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 0, 5, 4]), .triangle 2 0]

def cycle0676 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 5, 4]), .gapLower 0 1 (![2, 3, 1, 5, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0677 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![2, 3, 1, 5, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0678 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![2, 3, 1, 5, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 1, 5, 4]), .triangle 3 1]

def cycle0679 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![2, 3, 1, 5, 4]), .corridorLower 0 2, .gapLower 0 5 (![2, 3, 1, 5, 4]), .triangle 2 1]

def cycle0680 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 5, 4]), .triangle 4 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0681 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 5, 4]), .triangle 4 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 1, 5, 4]), .triangle 3 1]

def cycle0682 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 2 (![2, 3, 1, 5, 4]), .corridorLower 0 3, .gapLower 0 5 (![2, 3, 1, 5, 4]), .triangle 2 1]

def cycle0683 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 1, 5, 4]), .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0684 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 1, 5, 4]), .triangle 9 2, .gapLower 0 3 (![2, 3, 1, 5, 4])]

def cycle0685 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 1, 5, 4]), .gapLower 0 4 (![2, 3, 1, 5, 4]), .triangle 3 1]

def cycle0686 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0687 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0688 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 1 1 (![2, 3, 5, 0, 4]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0689 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 2 (![2, 3, 5, 0, 4]), .corridorLower 1 3, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0690 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0691 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0692 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 1 (![2, 3, 5, 1, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0693 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![2, 3, 5, 1, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0694 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 3, 5, 1, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0695 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0696 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![2, 3, 5, 1, 4]), .triangle 2 1]

def cycle0697 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 1 (![2, 3, 5, 1, 4]), .gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0698 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![2, 3, 5, 1, 4]), .triangle 4 1, .gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0699 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 3, 5, 1, 4]), .triangle 6 1, .gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0700 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (4), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 1 0 (![2, 3, 5, 0, 4]), .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0701 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![2, 3, 5, 0, 4]), .triangle 14 1, .gapLower 1 1 (![2, 3, 5, 0, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0702 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![2, 3, 5, 0, 4]), .gapLower 1 2 (![2, 3, 5, 0, 4]), .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0703 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![2, 3, 5, 0, 4]), .corridorLower 1 5, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0704 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 5 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0705 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 5, 4]), .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0706 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .gapLower 2 1 (![1, 0, 3, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0707 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![1, 0, 3, 5, 4])]

def cycle0708 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 18 2, .gapLower 2 3 (![1, 0, 3, 5, 4]), .triangle 4 0]

def cycle0709 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![1, 0, 3, 5, 4]), .triangle 6 0]

def cycle0710 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 3, 5, 4]), .triangle 5 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0711 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 0, .triangle 4 1]

def cycle0712 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0713 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0714 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 1 0 (![2, 3, 5, 0, 4]), .thetaOrder 0, .gapLower 0 5 (![2, 3, 5, 1, 4]), .triangle 2 1]

def cycle0715 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 1 1 (![2, 3, 5, 0, 4]), .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 5, 1, 4]), .triangle 2 1]

def cycle0716 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 2 (![2, 3, 5, 0, 4]), .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![2, 3, 5, 1, 4]), .triangle 2 1]

def cycle0717 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.gapLower 1 3 (![2, 3, 5, 0, 4]), .triangle 14 1, .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 5, 1, 4]), .triangle 2 1]

def cycle0718 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 4, 5]), .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0719 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .gapLower 2 1 (![1, 0, 3, 4, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0720 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![1, 0, 3, 4, 5])]

def cycle0721 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 3 (![1, 0, 3, 4, 5]), .triangle 4 0]

def cycle0722 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 2, .gapLower 2 4 (![1, 0, 3, 4, 5]), .triangle 5 0]

def cycle0723 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 16 0, .triangle 4 0]

def cycle0724 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 18 0, .triangle 16 1, .triangle 4 0]

def cycle0725 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 5, 4]), .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0726 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .gapLower 2 1 (![1, 0, 3, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0727 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 3 4, .distance 2 4]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 18 0, .triangle 19 0, .triangle 16 2]

def cycle0728 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 3 0 (![1, 0, 2, 5, 4]), .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0729 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 3 1 (![1, 0, 2, 5, 4]), .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0730 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 3 2 (![1, 0, 2, 5, 4]), .triangle 4 1]

def cycle0731 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 3 3 (![1, 0, 2, 5, 4]), .triangle 4 0]

def cycle0732 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![1, 0, 2, 5, 4]), .triangle 17 0, .triangle 4 0]

def cycle0733 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![1, 0, 2, 5, 4]), .triangle 16 0, .triangle 4 0]

def cycle0734 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0735 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 4, 5, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0736 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .gapLower 2 1 (![1, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0737 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 2 (![1, 0, 4, 5, 3])]

def cycle0738 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![1, 0, 4, 5, 3]), .triangle 5 0]

def cycle0739 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 4, 5, 3]), .triangle 6 0]

def cycle0740 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0741 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0742 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0743 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 19 0, .triangle 7 0, .triangle 4 1]

def cycle0744 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 3 0 (![1, 0, 5, 4, 2]), .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0745 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 3 1 (![1, 0, 5, 4, 2]), .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0746 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 19 2, .gapLower 3 2 (![1, 0, 5, 4, 2]), .triangle 4 1]

def cycle0747 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .gapLower 3 3 (![1, 0, 5, 4, 2]), .triangle 8 0, .gapLower 0 1 (![2, 3, 5, 1, 4])]

def cycle0748 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![1, 0, 5, 4, 2]), .triangle 7 0, .triangle 4 1]

def cycle0749 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![1, 0, 5, 4, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0750 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0751 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0752 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 1, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0753 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0754 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![2, 3, 5, 1, 4]), .gapLower 0 1 (![2, 3, 5, 1, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0755 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 3, 5, 1, 4]), .triangle 8 1, .gapLower 0 1 (![2, 3, 5, 1, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0756 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 1 (![2, 3, 5, 1, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0757 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 1 (![2, 3, 5, 1, 4]), .corridorLower 0 2, .gapLower 0 5 (![2, 3, 5, 1, 4]), .triangle 2 1]

def cycle0758 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 3, 5, 1, 4]), .gapLower 0 2 (![2, 3, 5, 1, 4]), .triangle 4 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0759 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![2, 3, 5, 1, 4]), .triangle 4 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0760 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![2, 3, 5, 1, 4]), .corridorLower 0 3, .gapLower 0 5 (![2, 3, 5, 1, 4]), .triangle 2 1]

def cycle0761 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![2, 3, 5, 1, 4]), .triangle 8 1, .triangle 4 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0762 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 3 (![2, 3, 5, 1, 4]), .corridorLower 0 5, .gapLower 0 5 (![2, 3, 5, 1, 4]), .triangle 2 1]

def cycle0763 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 5, 1, 4]), .gapLower 0 4 (![2, 3, 5, 1, 4])]

def cycle0764 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0765 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0766 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 0, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0767 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2 (![2, 3, 4, 0, 5]), .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0768 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0769 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 3, 4, 1, 5]), .triangle 7 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 4, 0, 5]), .triangle 3 0]

def cycle0770 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![2, 3, 4, 1, 5])]

def cycle0771 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![2, 3, 4, 1, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0772 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 3, 4, 1, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0773 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0774 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 1, 5]), .triangle 3 1]

def cycle0775 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![2, 3, 4, 1, 5])]

def cycle0776 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![2, 3, 4, 1, 5]), .triangle 4 1, .gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0777 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 3, 4, 1, 5]), .triangle 5 1, .gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0778 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (4), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .gapLower 1 0 (![2, 3, 4, 0, 5]), .gapLower 1 5 (![2, 3, 4, 0, 5]), .triangle 3 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0779 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![2, 3, 4, 0, 5]), .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 0, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0780 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![2, 3, 4, 0, 5]), .gapLower 1 2 (![2, 3, 4, 0, 5]), .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0781 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![2, 3, 4, 0, 5]), .corridorLower 1 4, .gapLower 1 5 (![2, 3, 4, 0, 5]), .triangle 3 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0782 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 4, 5]), .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0783 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 2 1 (![1, 0, 3, 4, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0784 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![1, 0, 3, 4, 5])]

def cycle0785 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 3 (![1, 0, 3, 4, 5]), .triangle 4 0]

def cycle0786 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 2, .gapLower 2 4 (![1, 0, 3, 4, 5]), .triangle 5 0]

def cycle0787 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 3, 4, 5]), .triangle 6 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0788 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 18 0, .triangle 9 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0789 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0790 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0791 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .triangle 8 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0792 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 9 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0793 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 0, 5]), .triangle 3 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0794 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .gapLower 1 0 (![2, 3, 4, 0, 5]), .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 1, 5]), .triangle 3 1]

def cycle0795 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 0, 5]), .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 1, 5]), .triangle 3 1]

def cycle0796 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 2 (![2, 3, 4, 0, 5]), .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 1, 5]), .triangle 3 1]

def cycle0797 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.gapLower 1 3 (![2, 3, 4, 0, 5]), .triangle 13 1, .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 1, 5]), .triangle 3 1]

def cycle0798 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 4, 5]), .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0799 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 2 1 (![1, 0, 3, 4, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0800 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 16 0, .triangle 4 0]

def cycle0801 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 18 0, .triangle 16 1, .triangle 4 0]

def cycle0802 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 5, 4]), .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0803 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 2 1 (![1, 0, 3, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0804 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![1, 0, 3, 5, 4])]

def cycle0805 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 18 2, .gapLower 2 3 (![1, 0, 3, 5, 4]), .triangle 4 0]

def cycle0806 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![1, 0, 3, 5, 4]), .triangle 6 0]

def cycle0807 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 3, 5, 4]), .triangle 18 0, .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0808 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 0, .triangle 4 1]

def cycle0809 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 4, 5, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0810 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 2 1 (![1, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0811 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 2 (![1, 0, 4, 5, 3])]

def cycle0812 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![1, 0, 4, 5, 3]), .triangle 5 0]

def cycle0813 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 4, 5, 3]), .triangle 6 0]

def cycle0814 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0815 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0816 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0817 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 19 0, .triangle 7 0, .triangle 4 1]

def cycle0818 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 19 0, .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0819 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0820 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 18 0, .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0821 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 1, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0822 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 0, 5]), .triangle 3 0]

def cycle0823 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![2, 3, 4, 1, 5]), .gapLower 0 1 (![2, 3, 4, 1, 5])]

def cycle0824 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 3, 4, 1, 5]), .triangle 7 1, .gapLower 0 1 (![2, 3, 4, 1, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0825 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 1 (![2, 3, 4, 1, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0826 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 2, .gapLower 0 5 (![2, 3, 4, 1, 5]), .triangle 9 1, .triangle 7 1, .gapLower 0 1 (![2, 3, 4, 1, 5])]

def cycle0827 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 3, 4, 1, 5]), .gapLower 0 2 (![2, 3, 4, 1, 5]), .triangle 4 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 0]

def cycle0828 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![2, 3, 4, 1, 5]), .triangle 4 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0829 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![2, 3, 4, 1, 5]), .corridorLower 0 3, .gapLower 0 5 (![2, 3, 4, 1, 5]), .triangle 3 1]

def cycle0830 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![2, 3, 4, 1, 5]), .triangle 7 1, .triangle 4 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0831 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 3 (![2, 3, 4, 1, 5]), .corridorLower 0 4, .gapLower 0 5 (![2, 3, 4, 1, 5]), .triangle 3 1]

def cycle0832 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 1, 5]), .gapLower 0 4 (![2, 3, 4, 1, 5])]

def cycle0833 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0834 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0835 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0836 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0837 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0838 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![2, 3, 4, 5, 1])]

def cycle0839 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![2, 3, 4, 5, 1])]

def cycle0840 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 7 1, .triangle 4 1, .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0841 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-3), (0), (0), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 9 1, .triangle 7 1, .triangle 4 1, .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0842 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0843 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![2, 3, 4, 5, 1])]

def cycle0844 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![2, 3, 4, 5, 1]), .triangle 4 1]

def cycle0845 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 2 1, .triangle 11 1, .gapLower 1 0 (![2, 3, 4, 5, 0]), .corridorUpper 0 1]

def cycle0846 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 2 1, .gapLower 1 2 (![2, 3, 4, 5, 0]), .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0847 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 1 4, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 2 1, .triangle 11 1, .gapLower 2 0 (![1, 0, 3, 4, 5]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0848 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 5 1, .gapLower 2 1 (![1, 0, 3, 4, 5]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0849 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![1, 0, 3, 4, 5])]

def cycle0850 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 3 (![1, 0, 3, 4, 5]), .triangle 4 0]

def cycle0851 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 2, .gapLower 2 4 (![1, 0, 3, 4, 5]), .triangle 5 0]

def cycle0852 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 3, 4, 5]), .triangle 6 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 7 1, .triangle 4 1]

def cycle0853 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 18 0, .gapLower 5 2 (![1, 0, 4, 2, 3]), .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 7 1, .triangle 4 1]

def cycle0854 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 7 1, .triangle 4 1]

def cycle0855 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0856 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .gapLower 5 2 (![1, 0, 3, 2, 4]), .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 7 1, .triangle 4 1]

def cycle0857 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 9 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 7 1, .triangle 4 1]

def cycle0858 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 7 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0859 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![(0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 2 1, .triangle 15 0, .triangle 9 2, .gapLower 0 3 (![2, 3, 4, 5, 1])]

def cycle0860 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4]
    constant := ![(0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 2 1, .triangle 13 1, .triangle 14 0, .triangle 8 2, .gapLower 0 3 (![2, 3, 4, 5, 1])]

def cycle0861 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 4]
    constant := ![(0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 2 1, .triangle 11 1, .triangle 12 0, .triangle 6 2, .gapLower 0 3 (![2, 3, 4, 5, 1])]

def cycle0862 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 3 1, .triangle 12 1, .gapLower 1 0 (![2, 3, 4, 5, 0]), .corridorUpper 0 1]

def cycle0863 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 2 (![2, 3, 4, 5, 0]), .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0864 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 3 (![2, 3, 4, 5, 0]), .triangle 13 1, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0865 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 3 1, .triangle 12 1, .gapLower 2 0 (![1, 0, 3, 4, 5]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0866 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 6 1, .gapLower 2 1 (![1, 0, 3, 4, 5]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0867 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 16 0, .triangle 4 0]

def cycle0868 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 18 0, .triangle 16 1, .triangle 4 0]

def cycle0869 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 3 1, .triangle 12 1, .gapLower 2 0 (![1, 0, 3, 5, 4]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0870 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 6 1, .gapLower 2 1 (![1, 0, 3, 5, 4]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0871 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![1, 0, 3, 5, 4])]

def cycle0872 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 18 2, .gapLower 2 3 (![1, 0, 3, 5, 4]), .triangle 4 0]

def cycle0873 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![1, 0, 3, 5, 4]), .triangle 6 0]

def cycle0874 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 3, 5, 4]), .triangle 18 0, .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0875 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 0, .triangle 4 1]

def cycle0876 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 3 1, .triangle 12 1, .gapLower 2 0 (![1, 0, 4, 5, 3]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0877 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 6 1, .gapLower 2 1 (![1, 0, 4, 5, 3]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0878 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 2 (![1, 0, 4, 5, 3])]

def cycle0879 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![1, 0, 4, 5, 3]), .triangle 5 0]

def cycle0880 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 4, 5, 3]), .triangle 6 0]

def cycle0881 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 4, 5, 3]), .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0882 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 3 1, .triangle 12 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0883 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 6 1, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0884 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 19 0, .triangle 7 0, .triangle 4 1]

def cycle0885 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 19 0, .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0886 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0887 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 18 0, .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0888 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0889 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 9 1, .triangle 7 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0890 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-2), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .triangle 10 1, .gapLower 1 0 (![2, 3, 4, 5, 0]), .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0891 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0892 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 2 (![2, 3, 4, 5, 0]), .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0893 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 3 0, .gapLower 1 3 (![2, 3, 4, 5, 0]), .triangle 13 1, .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0894 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.gapLower 1 4 (![2, 3, 4, 5, 0]), .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0895 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-2), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 4, 5]), .thetaOrder 1, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0896 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 1 (![1, 0, 3, 4, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0897 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-2), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 5, 4]), .thetaOrder 1, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0898 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 1 (![1, 0, 3, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0899 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 3, 5, 4]), .triangle 18 0, .triangle 9 0, .gapLower 0 2 (![2, 3, 4, 5, 1]), .triangle 4 1]

def cycle0900 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-2), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 4, 5, 3]), .thetaOrder 1, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0901 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 2 1 (![1, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0902 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-2), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0903 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 2 (![2, 3, 4, 5, 1]), .triangle 4 1]

def cycle0904 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 4, 5, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 2 (![2, 3, 4, 5, 1]), .gapLower 0 1 (![2, 3, 4, 5, 1])]

def cycle0905 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![2, 3, 4, 5, 1]), .triangle 4 1, .gapLower 0 0 (![2, 3, 4, 5, 1]), .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0906 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![2, 3, 4, 5, 1]), .gapLower 0 0 (![2, 3, 4, 5, 1]), .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0907 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .triangle 6 0, .gapLower 0 0 (![2, 3, 4, 5, 1]), .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0908 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .triangle 5 0, .gapLower 0 0 (![2, 3, 4, 5, 1]), .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0909 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .gapLower 0 0 (![2, 3, 4, 5, 1]), .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0910 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![2, 3, 4, 5, 1]), .gapLower 0 1 (![2, 3, 4, 5, 1])]

def cycle0911 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 7 1, .gapLower 0 1 (![2, 3, 4, 5, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0912 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 8 1, .gapLower 0 1 (![2, 3, 4, 5, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0913 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 1 (![2, 3, 4, 5, 1]), .corridorLower 0 2, .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0914 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .gapLower 0 2 (![2, 3, 4, 5, 1]), .triangle 4 1, .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0915 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .triangle 9 1, .gapLower 0 2 (![2, 3, 4, 5, 1]), .triangle 4 1, .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0916 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 2 (![2, 3, 4, 5, 1]), .corridorLower 0 3, .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0917 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .gapLower 0 3 (![2, 3, 4, 5, 1]), .triangle 5 1, .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0918 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 1]
    strict := ![true, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 3 (![2, 3, 4, 5, 1]), .corridorLower 0 4, .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0919 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(-2), (-1), (2)]
    coefficient := ![0, 0, 1]
    strict := ![false, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 4, 5, 1]), .corridorLower 0 5, .gapLower 0 5 (![2, 3, 4, 5, 1])]

def cycle0920 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle0921 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .triangle 10 1, .gapLower 1 0 (![2, 3, 4, 5, 0]), .corridorUpper 0 1]

def cycle0922 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0923 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0924 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .corridorUpper 0 1]

def cycle0925 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0926 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0927 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0928 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0929 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 15 2, .gapLower 1 2 (![2, 3, 5, 4, 0]), .corridorLower 1 3, .corridorUpper 0 1]

def cycle0930 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 3 (![2, 3, 5, 4, 0]), .corridorLower 1 5, .corridorUpper 0 1]

def cycle0931 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 4 (![2, 3, 5, 4, 0]), .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0932 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 2 0, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0933 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![2, 3, 5, 4, 1])]

def cycle0934 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 4 1, .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0935 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .distance 2 4, .distance 0 4]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 3 (![2, 3, 5, 4, 1]), .triangle 9 1, .corridorLower 4 5, .corridorUpper 2 4, .triangle 5 2]

def cycle0936 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 3, 5, 4, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0937 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (0), (1)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 5, 4, 1])]

def cycle0938 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![2, 3, 5, 4, 1])]

def cycle0939 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 1 1, .triangle 10 1, .gapLower 1 0 (![2, 3, 4, 5, 0]), .corridorUpper 0 1]

def cycle0940 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 1 3, .distance 1 2, .theta 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 1 1, .triangle 10 1, .gapLower 2 0 (![1, 0, 3, 5, 4]), .thetaOrder 1, .corridorUpper 0 1]

def cycle0941 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 4 1, .gapLower 2 1 (![1, 0, 3, 5, 4]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0942 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![1, 0, 3, 5, 4])]

def cycle0943 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 18 2, .gapLower 2 3 (![1, 0, 3, 5, 4]), .triangle 4 0]

def cycle0944 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![1, 0, 3, 5, 4]), .gapLower 5 3 (![1, 4, 0, 2, 3]), .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 4 1]

def cycle0945 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 3, 5, 4]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 4 1]

def cycle0946 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .gapLower 5 3 (![1, 4, 0, 3, 2]), .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 4 1]

def cycle0947 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .gapLower 4 3 (![1, 5, 0, 3, 2]), .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 4 1]

def cycle0948 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 4 1, .gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle0949 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, true, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 1 1, .triangle 10 1, .gapLower 1 0 (![2, 3, 5, 4, 0]), .corridorUpper 0 1]

def cycle0950 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 1 1, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0951 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 4 1, .gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0952 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![(0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.triangle 1 1, .triangle 14 0, .gapLower 5 2 (![4, 0, 3, 1, 2]), .gapLower 0 2 (![2, 3, 5, 4, 1])]

def cycle0953 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false] }
  origin := ![.triangle 1 1, .triangle 13 0, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1])]

def cycle0954 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 3]
    constant := ![(0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 1 1, .triangle 10 1, .triangle 12 0, .triangle 6 2, .gapLower 0 2 (![2, 3, 5, 4, 1])]

def cycle0955 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(0), (0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, true, false] }
  origin := ![.triangle 1 1, .triangle 10 1, .triangle 11 0, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1])]

def cycle0956 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 3, 5, 4, 1]), .triangle 9 1, .triangle 15 0, .triangle 13 1, .triangle 10 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0957 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 3, 5, 4, 1]), .triangle 8 1, .triangle 1 1, .triangle 10 1, .gapLower 1 0 (![2, 3, 5, 4, 0]), .corridorUpper 0 1]

def cycle0958 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 3, 5, 4, 1]), .triangle 8 1, .triangle 1 1, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .corridorUpper 0 1]

def cycle0959 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 3, 5, 4, 1]), .triangle 8 1, .triangle 4 1, .gapLower 0 0 (![2, 3, 5, 4, 1]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 5, 4, 0])]

def cycle0960 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(0), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 1 1, .triangle 10 1, .triangle 11 0, .triangle 5 2, .gapLower 0 3 (![2, 3, 5, 4, 1]), .triangle 8 1]

def cycle0961 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 3, 5, 4, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def cycle0962 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 3, 5, 4, 1])]

def cycle0963 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.triangle 2 0, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 3, 5, 4, 1])]

def cycle0964 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![2, 3, 5, 4, 1]), .gapLower 0 0 (![2, 3, 5, 4, 1]), .gapLower 0 5 (![2, 3, 5, 4, 1])]

def cycle0965 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 12 0, .triangle 6 0, .gapLower 0 0 (![2, 3, 5, 4, 1]), .gapLower 0 5 (![2, 3, 5, 4, 1])]

def cycle0966 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .triangle 11 0, .triangle 5 0, .gapLower 0 0 (![2, 3, 5, 4, 1]), .gapLower 0 5 (![2, 3, 5, 4, 1])]

def cycle0967 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 4 0, .gapLower 0 0 (![2, 3, 5, 4, 1]), .gapLower 0 5 (![2, 3, 5, 4, 1])]

def cycle0968 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .gapLower 0 1 (![2, 3, 5, 4, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0969 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 3, 5, 4, 1]), .triangle 8 1, .gapLower 0 1 (![2, 3, 5, 4, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0970 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 5, 4, 1]), .triangle 7 1, .gapLower 0 1 (![2, 3, 5, 4, 1]), .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0971 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 1 (![2, 3, 5, 4, 1]), .corridorLower 0 2, .gapLower 0 5 (![2, 3, 5, 4, 1])]

def cycle0972 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 3, 5, 4, 1]), .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 4 1, .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0973 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 5, 4, 1]), .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .triangle 4 1, .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0974 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 2 (![2, 3, 5, 4, 1]), .corridorLower 0 3, .gapLower 0 5 (![2, 3, 5, 4, 1])]

def cycle0975 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false] }
  origin := ![.gapLower 0 4 (![2, 3, 5, 4, 1]), .gapLower 0 3 (![2, 3, 5, 4, 1]), .triangle 6 1, .triangle 0 1, .corridorLower 1 2, .corridorUpper 0 1]

def cycle0976 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .distance 0 1]
    constant := ![(0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 1]
    strict := ![true, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 3 (![2, 3, 5, 4, 1]), .corridorLower 0 5, .gapLower 0 5 (![2, 3, 5, 4, 1])]

def cycle0977 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 4 (![2, 3, 5, 4, 1]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 3, 5, 4, 1])]

def cycle0978 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 0, .triangle 10 1, .gapLower 1 0 (![2, 3, 5, 0, 4]), .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0979 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 5, 0, 4]), .corridorLower 1 2, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0980 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 2, .gapLower 1 2 (![2, 3, 5, 0, 4]), .corridorLower 1 3, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0981 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle0982 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 3, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 1, 4])]

def cycle0983 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 5, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 3, 5, 0, 4])]

def cycle0984 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 0 0 (![2, 5, 3, 1, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![2, 3, 5, 0, 4]), .triangle 2 0]

def cycle0985 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 5, 3, 1, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 8 2, .triangle 6 1]

def cycle0986 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 14 2, .gapLower 1 1 (![2, 5, 3, 0, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0987 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 5, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 2 (![2, 5, 3, 0, 4]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0988 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (3), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3 (![2, 5, 3, 0, 4]), .triangle 14 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 0 (![2, 5, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0989 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 0 0 (![2, 5, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .gapLower 1 4 (![2, 5, 3, 0, 4])]

def cycle0990 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.triangle 1 0, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![2, 5, 3, 0, 4]), .triangle 2 0]

def cycle0991 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 1, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0992 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![2, 5, 3, 1, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0993 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 5, 3, 1, 4]), .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0994 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 5, 3, 1, 4])]

def cycle0995 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, true] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 5, 3, 1, 4]), .triangle 7 1]

def cycle0996 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 1, 4]), .gapLower 0 0 (![2, 5, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0997 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![2, 5, 3, 1, 4]), .triangle 6 1, .gapLower 0 0 (![2, 5, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0998 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 5, 3, 1, 4]), .triangle 4 1, .gapLower 0 0 (![2, 5, 3, 1, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle0999 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 5, 3, 1, 4])]

def cycle1000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 14 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 5, 3, 1, 4])]

def cycle1001 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 3, 1, 4]), .triangle 7 1]

def cycle1002 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, true, false, true] }
  origin := ![.triangle 1 0, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 5, 3, 1, 4]), .triangle 2 1]

def cycle1003 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![2, 5, 3, 1, 4]), .gapLower 0 1 (![2, 5, 3, 1, 4])]

def cycle1004 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 5, 3, 1, 4]), .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 1, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1005 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 1, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 5, 3, 1, 4])]

def cycle1006 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 1, 4]), .corridorLower 0 2, .gapLower 0 5 (![2, 5, 3, 1, 4]), .triangle 2 1]

def cycle1007 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 5, 3, 1, 4]), .gapLower 0 2 (![2, 5, 3, 1, 4]), .triangle 6 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1008 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![2, 5, 3, 1, 4]), .triangle 6 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 5, 3, 1, 4])]

def cycle1009 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![2, 5, 3, 1, 4]), .corridorLower 0 5, .gapLower 0 5 (![2, 5, 3, 1, 4]), .triangle 2 1]

def cycle1010 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![2, 5, 3, 1, 4]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 5, 3, 1, 4])]

def cycle1011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 5, 3, 1, 4]), .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 0]

def cycle1012 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 5, 3, 1, 4]), .gapLower 0 4 (![2, 5, 3, 1, 4])]

def cycle1013 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .triangle 14 2, .gapLower 1 4 (![2, 3, 4, 0, 5])]

def cycle1014 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (-2), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .triangle 10 1, .gapLower 1 0 (![2, 3, 4, 5, 0]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle1015 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 4, 5, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle1016 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 2 (![2, 3, 4, 5, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle1017 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .gapLower 1 3 (![2, 3, 4, 5, 0]), .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle1018 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 5, 3, 4, 1]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 4 0]

def cycle1019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![2, 5, 3, 4, 1]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0, .triangle 8 2, .gapLower 0 1 (![2, 5, 3, 4, 1])]

def cycle1020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .triangle 14 0, .triangle 10 1, .corridorLower 1 2, .gapLower 1 5 (![2, 3, 4, 5, 0])]

def cycle1021 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (-2), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .triangle 10 1, .gapLower 1 0 (![2, 3, 5, 4, 0]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle1022 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 0, .gapLower 1 1 (![2, 3, 5, 4, 0]), .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle1023 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 14 2, .gapLower 1 2 (![2, 3, 5, 4, 0]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

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
  | 0 => some (.leaf 3977)
  | 1 => some (.triangle 14 6143 6144)
  | 2 => some (.leaf 3978)
  | 3 => some (.triangle 13 6145 6146)
  | 4 => some (.leaf 3979)
  | 5 => some (.positive 0 (![6066, 6067, 6128, 6129, 6140, 6148]))
  | 6 => some (.triangle 15 1161 6149)
  | 7 => some (.triangle 14 6150 6144)
  | 8 => some (.leaf 3980)
  | 9 => some (.leaf 3981)
  | 10 => some (.leaf 3982)
  | 11 => some (.leaf 3983)
  | 12 => some (.leaf 3984)
  | 13 => some (.leaf 3985)
  | 14 => some (.leaf 3986)
  | 15 => some (.leaf 3987)
  | 16 => some (.leaf 3988)
  | 17 => some (.positive 2 (![1265, 6156, 6157, 6158, 6159, 6160]))
  | 18 => some (.leaf 3989)
  | 19 => some (.triangle 10 6161 6162)
  | 20 => some (.triangle 19 1264 6163)
  | 21 => some (.leaf 3990)
  | 22 => some (.leaf 3991)
  | 23 => some (.leaf 3992)
  | 24 => some (.positive 1 (![6088, 6089, 6164, 6165, 6166, 6167]))
  | 25 => some (.triangle 18 6155 6168)
  | 26 => some (.triangle 16 6154 6169)
  | 27 => some (.leaf 3993)
  | 28 => some (.leaf 3994)
  | 29 => some (.leaf 3995)
  | 30 => some (.positive 0 (![6152, 6153, 6170, 6171, 6172, 6173]))
  | 31 => some (.triangle 15 1161 6174)
  | 32 => some (.triangle 13 6151 6175)
  | 33 => some (.leaf 3996)
  | 34 => some (.leaf 3997)
  | 35 => some (.leaf 3998)
  | 36 => some (.leaf 3999)
  | 37 => some (.leaf 4000)
  | 38 => some (.leaf 4001)
  | 39 => some (.leaf 4002)
  | 40 => some (.leaf 4003)
  | 41 => some (.leaf 4004)
  | 42 => some (.leaf 4005)
  | 43 => some (.heavy (![6118, 6119, 6120, 6121, 6122, 6123, 6124, 6125, 6137, 6147, 6176, 6177, 6178, 6179, 6180, 6181, 6182, 6183, 6184, 6185, 6186]))
  | 44 => some (.triangle 9 6115 6187)
  | 45 => some (.leaf 4006)
  | 46 => some (.leaf 4007)
  | 47 => some (.triangle 13 6189 6190)
  | 48 => some (.leaf 4008)
  | 49 => some (.leaf 4009)
  | 50 => some (.leaf 4010)
  | 51 => some (.leaf 4011)
  | 52 => some (.leaf 4012)
  | 53 => some (.leaf 4013)
  | 54 => some (.leaf 4014)
  | 55 => some (.leaf 4015)
  | 56 => some (.leaf 4016)
  | 57 => some (.leaf 4017)
  | 58 => some (.leaf 4018)
  | 59 => some (.leaf 4019)
  | 60 => some (.leaf 4020)
  | 61 => some (.leaf 4021)
  | 62 => some (.positive 0 (![6200, 6201, 6202, 6203, 6204, 6205]))
  | 63 => some (.triangle 14 1345 6206)
  | 64 => some (.leaf 4022)
  | 65 => some (.triangle 13 6207 6208)
  | 66 => some (.leaf 4023)
  | 67 => some (.leaf 4024)
  | 68 => some (.leaf 4025)
  | 69 => some (.positive 0 (![6210, 6211, 6202, 6203, 6204, 6212]))
  | 70 => some (.triangle 14 1345 6213)
  | 71 => some (.leaf 4026)
  | 72 => some (.triangle 13 6214 6215)
  | 73 => some (.leaf 4027)
  | 74 => some (.leaf 4028)
  | 75 => some (.leaf 4029)
  | 76 => some (.leaf 4030)
  | 77 => some (.leaf 4031)
  | 78 => some (.leaf 4032)
  | 79 => some (.leaf 4033)
  | 80 => some (.leaf 4034)
  | 81 => some (.leaf 4035)
  | 82 => some (.leaf 4036)
  | 83 => some (.heavy (![6191, 6192, 6193, 6194, 6195, 6196, 6197, 6198, 6199, 6209, 6216, 6217, 6218, 6219, 6220, 6221, 6222, 6223, 6224, 6225, 6226]))
  | 84 => some (.triangle 8 6188 6227)
  | 85 => some (.leaf 4037)
  | 86 => some (.leaf 4038)
  | 87 => some (.triangle 15 6229 6230)
  | 88 => some (.triangle 13 1425 6231)
  | 89 => some (.leaf 4039)
  | 90 => some (.leaf 4040)
  | 91 => some (.leaf 4041)
  | 92 => some (.leaf 4042)
  | 93 => some (.leaf 4043)
  | 94 => some (.leaf 4044)
  | 95 => some (.leaf 4045)
  | 96 => some (.leaf 4046)
  | 97 => some (.leaf 4047)
  | 98 => some (.leaf 4048)
  | 99 => some (.leaf 4049)
  | 100 => some (.leaf 4050)
  | 101 => some (.leaf 4051)
  | 102 => some (.leaf 4052)
  | 103 => some (.positive 0 (![6241, 6242, 6243, 6244, 6245, 6246]))
  | 104 => some (.leaf 4053)
  | 105 => some (.triangle 14 6247 6248)
  | 106 => some (.leaf 4054)
  | 107 => some (.triangle 15 6249 6250)
  | 108 => some (.triangle 13 1425 6251)
  | 109 => some (.leaf 4055)
  | 110 => some (.leaf 4056)
  | 111 => some (.leaf 4057)
  | 112 => some (.positive 0 (![6253, 6254, 6243, 6244, 6245, 6255]))
  | 113 => some (.leaf 4058)
  | 114 => some (.triangle 14 6256 6257)
  | 115 => some (.leaf 4059)
  | 116 => some (.leaf 4060)
  | 117 => some (.leaf 4061)
  | 118 => some (.leaf 4062)
  | 119 => some (.triangle 14 6262 1463)
  | 120 => some (.leaf 4063)
  | 121 => some (.triangle 10 6263 6264)
  | 122 => some (.leaf 4064)
  | 123 => some (.leaf 4065)
  | 124 => some (.leaf 4066)
  | 125 => some (.positive 1 (![6088, 6089, 6265, 6266, 6267, 6268]))
  | 126 => some (.triangle 18 6261 6269)
  | 127 => some (.triangle 16 1426 6270)
  | 128 => some (.leaf 4067)
  | 129 => some (.leaf 4068)
  | 130 => some (.leaf 4069)
  | 131 => some (.positive 0 (![6259, 6260, 6271, 6272, 6273, 6274]))
  | 132 => some (.triangle 15 6258 6275)
  | 133 => some (.triangle 13 1425 6276)
  | 134 => some (.leaf 4070)
  | 135 => some (.leaf 4071)
  | 136 => some (.leaf 4072)
  | 137 => some (.leaf 4073)
  | 138 => some (.leaf 4074)
  | 139 => some (.leaf 4075)
  | 140 => some (.leaf 4076)
  | 141 => some (.leaf 4077)
  | 142 => some (.leaf 4078)
  | 143 => some (.leaf 4079)
  | 144 => some (.heavy (![6232, 6233, 6234, 6235, 6236, 6237, 6238, 6239, 6240, 6252, 6277, 6278, 6279, 6280, 6281, 6282, 6283, 6284, 6285, 6286, 6287]))
  | 145 => some (.leaf 4080)
  | 146 => some (.leaf 4081)
  | 147 => some (.triangle 15 6289 6290)
  | 148 => some (.triangle 13 1425 6291)
  | 149 => some (.leaf 4082)
  | 150 => some (.leaf 4083)
  | 151 => some (.leaf 4084)
  | 152 => some (.leaf 4085)
  | 153 => some (.leaf 4086)
  | 154 => some (.leaf 4087)
  | 155 => some (.leaf 4088)
  | 156 => some (.leaf 4089)
  | 157 => some (.leaf 4090)
  | 158 => some (.leaf 4091)
  | 159 => some (.leaf 4092)
  | 160 => some (.leaf 4093)
  | 161 => some (.leaf 4094)
  | 162 => some (.positive 0 (![6300, 6301, 6302, 6303, 6304, 6305]))
  | 163 => some (.triangle 14 1345 6306)
  | 164 => some (.leaf 4095)
  | 165 => some (.triangle 15 6307 6308)
  | 166 => some (.triangle 13 1425 6309)
  | 167 => some (.leaf 4096)
  | 168 => some (.leaf 4097)
  | 169 => some (.leaf 4098)
  | 170 => some (.leaf 4099)
  | 171 => some (.positive 0 (![6311, 6312, 6302, 6303, 6313, 6314]))
  | 172 => some (.triangle 14 1345 6315)
  | 173 => some (.leaf 4100)
  | 174 => some (.leaf 4101)
  | 175 => some (.leaf 4102)
  | 176 => some (.leaf 4103)
  | 177 => some (.leaf 4104)
  | 178 => some (.leaf 4105)
  | 179 => some (.leaf 4106)
  | 180 => some (.leaf 4107)
  | 181 => some (.leaf 4108)
  | 182 => some (.leaf 4109)
  | 183 => some (.positive 3 (![6321, 6322, 6323, 6324, 6325, 6326]))
  | 184 => some (.leaf 4110)
  | 185 => some (.triangle 12 6327 6328)
  | 186 => some (.leaf 4111)
  | 187 => some (.leaf 4112)
  | 188 => some (.leaf 4113)
  | 189 => some (.positive 2 (![1566, 6320, 6329, 6330, 6331, 6332]))
  | 190 => some (.leaf 4114)
  | 191 => some (.triangle 10 6333 6334)
  | 192 => some (.triangle 19 6335 1579)
  | 193 => some (.leaf 4115)
  | 194 => some (.leaf 4116)
  | 195 => some (.leaf 4117)
  | 196 => some (.positive 1 (![6088, 6089, 6336, 6337, 6338, 6339]))
  | 197 => some (.triangle 18 6319 6340)
  | 198 => some (.triangle 16 1426 6341)
  | 199 => some (.leaf 4118)
  | 200 => some (.leaf 4119)
  | 201 => some (.leaf 4120)
  | 202 => some (.positive 0 (![6317, 6318, 6342, 6343, 6344, 6345]))
  | 203 => some (.triangle 15 6316 6346)
  | 204 => some (.triangle 13 1425 6347)
  | 205 => some (.leaf 4121)
  | 206 => some (.leaf 4122)
  | 207 => some (.leaf 4123)
  | 208 => some (.positive 0 (![6349, 6350, 6302, 6303, 6313, 6351]))
  | 209 => some (.triangle 14 1345 6352)
  | 210 => some (.leaf 4124)
  | 211 => some (.leaf 4125)
  | 212 => some (.leaf 4126)
  | 213 => some (.positive 2 (![1566, 6355, 6356, 1611, 6331, 6332]))
  | 214 => some (.triangle 10 6357 6334)
  | 215 => some (.leaf 4127)
  | 216 => some (.triangle 19 6358 6359)
  | 217 => some (.leaf 4128)
  | 218 => some (.positive 1 (![6088, 6089, 6360, 6337, 6338, 6361]))
  | 219 => some (.triangle 18 6319 6362)
  | 220 => some (.triangle 16 6354 6363)
  | 221 => some (.leaf 4129)
  | 222 => some (.positive 0 (![6259, 6260, 6364, 6343, 6344, 6365]))
  | 223 => some (.triangle 15 6353 6366)
  | 224 => some (.triangle 13 1425 6367)
  | 225 => some (.leaf 4130)
  | 226 => some (.leaf 4131)
  | 227 => some (.leaf 4132)
  | 228 => some (.leaf 4133)
  | 229 => some (.leaf 4134)
  | 230 => some (.leaf 4135)
  | 231 => some (.leaf 4136)
  | 232 => some (.leaf 4137)
  | 233 => some (.leaf 4138)
  | 234 => some (.leaf 4139)
  | 235 => some (.heavy (![6292, 6293, 6294, 6295, 6296, 6297, 6298, 6299, 6310, 6348, 6368, 6369, 6370, 6371, 6372, 6373, 6374, 6375, 6376, 6377, 6378]))
  | 236 => some (.triangle 8 6288 6379)
  | 237 => some (.leaf 4140)
  | 238 => some (.leaf 4141)
  | 239 => some (.leaf 4142)
  | 240 => some (.positive 3 (![1680, 1681, 1682, 6381, 6382, 6383]))
  | 241 => some (.leaf 4143)
  | 242 => some (.triangle 12 6384 6385)
  | 243 => some (.leaf 4144)
  | 244 => some (.leaf 4145)
  | 245 => some (.positive 2 (![1678, 1679, 6386, 6387, 1688, 6388]))
  | 246 => some (.leaf 4146)
  | 247 => some (.triangle 10 6389 6390)
  | 248 => some (.triangle 8 1677 6391)
  | 249 => some (.leaf 4147)
  | 250 => some (.leaf 4148)
  | 251 => some (.leaf 4149)
  | 252 => some (.positive 3 (![1693, 1694, 1695, 6393, 6394, 6395]))
  | 253 => some (.triangle 12 6396 6385)
  | 254 => some (.triangle 8 1692 6397)
  | 255 => some (.leaf 4150)
  | 256 => some (.leaf 4151)
  | 257 => some (.leaf 4152)
  | 258 => some (.positive 2 (![6398, 1701, 1702, 6399, 6400, 6401]))
  | 259 => some (.triangle 10 6402 6390)
  | 260 => some (.triangle 19 6392 6403)
  | 261 => some (.leaf 4153)
  | 262 => some (.leaf 4154)
  | 263 => some (.leaf 4155)
  | 264 => some (.leaf 4156)
  | 265 => some (.leaf 4157)
  | 266 => some (.positive 1 (![6404, 6405, 6406, 6407, 6408, 6409]))
  | 267 => some (.triangle 18 1165 6410)
  | 268 => some (.triangle 16 1426 6411)
  | 269 => some (.leaf 4158)
  | 270 => some (.positive 1 (![6413, 6404, 6406, 6407, 6408, 6409]))
  | 271 => some (.triangle 18 1165 6414)
  | 272 => some (.triangle 16 1426 6415)
  | 273 => some (.leaf 4159)
  | 274 => some (.leaf 4160)
  | 275 => some (.leaf 4161)
  | 276 => some (.leaf 4162)
  | 277 => some (.positive 0 (![6412, 6416, 6417, 6418, 6419, 6420]))
  | 278 => some (.triangle 15 1161 6421)
  | 279 => some (.triangle 13 1425 6422)
  | 280 => some (.leaf 4163)
  | 281 => some (.leaf 4164)
  | 282 => some (.leaf 4165)
  | 283 => some (.leaf 4166)
  | 284 => some (.leaf 4167)
  | 285 => some (.leaf 4168)
  | 286 => some (.leaf 4169)
  | 287 => some (.leaf 4170)
  | 288 => some (.leaf 4171)
  | 289 => some (.leaf 4172)
  | 290 => some (.leaf 4173)
  | 291 => some (.leaf 4174)
  | 292 => some (.leaf 4175)
  | 293 => some (.positive 3 (![1680, 1681, 1682, 6434, 6435, 6436]))
  | 294 => some (.leaf 4176)
  | 295 => some (.triangle 12 6437 6438)
  | 296 => some (.leaf 4177)
  | 297 => some (.leaf 4178)
  | 298 => some (.leaf 4179)
  | 299 => some (.positive 2 (![1678, 1679, 6439, 6440, 6441, 6442]))
  | 300 => some (.leaf 4180)
  | 301 => some (.triangle 10 6443 6444)
  | 302 => some (.triangle 8 1677 6445)
  | 303 => some (.leaf 4181)
  | 304 => some (.leaf 4182)
  | 305 => some (.leaf 4183)
  | 306 => some (.positive 3 (![1693, 1694, 1695, 6447, 6448, 6449]))
  | 307 => some (.leaf 4184)
  | 308 => some (.triangle 12 6450 6451)
  | 309 => some (.triangle 8 1692 6452)
  | 310 => some (.leaf 4185)
  | 311 => some (.leaf 4186)
  | 312 => some (.leaf 4187)
  | 313 => some (.positive 2 (![6453, 1701, 1702, 6454, 6455, 6456]))
  | 314 => some (.triangle 10 6457 6444)
  | 315 => some (.triangle 19 6446 6458)
  | 316 => some (.leaf 4188)
  | 317 => some (.leaf 4189)
  | 318 => some (.leaf 4190)
  | 319 => some (.positive 1 (![6432, 6433, 6459, 6460, 6461, 6462]))
  | 320 => some (.triangle 18 1165 6463)
  | 321 => some (.triangle 16 1426 6464)
  | 322 => some (.leaf 4191)
  | 323 => some (.leaf 4192)
  | 324 => some (.leaf 4193)
  | 325 => some (.positive 0 (![6430, 6431, 6465, 6466, 6467, 6468]))
  | 326 => some (.triangle 15 1161 6469)
  | 327 => some (.triangle 13 1425 6470)
  | 328 => some (.leaf 4194)
  | 329 => some (.leaf 4195)
  | 330 => some (.leaf 4196)
  | 331 => some (.leaf 4197)
  | 332 => some (.leaf 4198)
  | 333 => some (.triangle 8 1692 6476)
  | 334 => some (.leaf 4199)
  | 335 => some (.leaf 4200)
  | 336 => some (.positive 2 (![6477, 1701, 1702, 6478, 6479, 6456]))
  | 337 => some (.leaf 4201)
  | 338 => some (.triangle 10 6480 6481)
  | 339 => some (.triangle 19 6475 6482)
  | 340 => some (.leaf 4202)
  | 341 => some (.leaf 4203)
  | 342 => some (.leaf 4204)
  | 343 => some (.positive 1 (![6474, 6089, 6483, 6484, 6485, 6486]))
  | 344 => some (.triangle 18 1165 6487)
  | 345 => some (.triangle 16 1426 6488)
  | 346 => some (.leaf 4205)
  | 347 => some (.leaf 4206)
  | 348 => some (.leaf 4207)
  | 349 => some (.positive 0 (![6472, 6473, 6489, 6490, 6491, 6492]))
  | 350 => some (.triangle 15 1161 6493)
  | 351 => some (.triangle 13 1425 6494)
  | 352 => some (.leaf 4208)
  | 353 => some (.leaf 4209)
  | 354 => some (.leaf 4210)
  | 355 => some (.leaf 4211)
  | 356 => some (.leaf 4212)
  | 357 => some (.leaf 4213)
  | 358 => some (.triangle 19 6500 6501)
  | 359 => some (.leaf 4214)
  | 360 => some (.positive 1 (![6088, 6089, 6502, 6484, 6503, 6502]))
  | 361 => some (.triangle 18 1165 6504)
  | 362 => some (.triangle 16 6499 6505)
  | 363 => some (.leaf 4215)
  | 364 => some (.leaf 4216)
  | 365 => some (.positive 0 (![6497, 6498, 6506, 6490, 6507, 6508]))
  | 366 => some (.triangle 15 1161 6509)
  | 367 => some (.triangle 13 1425 6510)
  | 368 => some (.leaf 4217)
  | 369 => some (.leaf 4218)
  | 370 => some (.leaf 4219)
  | 371 => some (.leaf 4220)
  | 372 => some (.leaf 4221)
  | 373 => some (.leaf 4222)
  | 374 => some (.leaf 4223)
  | 375 => some (.leaf 4224)
  | 376 => some (.leaf 4225)
  | 377 => some (.leaf 4226)
  | 378 => some (.heavy (![6423, 6424, 6425, 6426, 6427, 6428, 6429, 6471, 6495, 6496, 6511, 6512, 6513, 6514, 6515, 6516, 6517, 6518, 6519, 6520, 6521]))
  | 379 => some (.triangle 9 6380 6522)
  | 380 => some (.triangle 7 6228 6523)
  | 381 => some (.leaf 4227)
  | 382 => some (.leaf 4228)
  | 383 => some (.triangle 13 6525 6526)
  | 384 => some (.leaf 4229)
  | 385 => some (.triangle 12 6527 6528)
  | 386 => some (.leaf 4230)
  | 387 => some (.leaf 4231)
  | 388 => some (.leaf 4232)
  | 389 => some (.leaf 4233)
  | 390 => some (.leaf 4234)
  | 391 => some (.leaf 4235)
  | 392 => some (.leaf 4236)
  | 393 => some (.leaf 4237)
  | 394 => some (.leaf 4238)
  | 395 => some (.leaf 4239)
  | 396 => some (.leaf 4240)
  | 397 => some (.leaf 4241)
  | 398 => some (.leaf 4242)
  | 399 => some (.leaf 4243)
  | 400 => some (.positive 0 (![6538, 6539, 6540, 6541, 6542, 6543]))
  | 401 => some (.leaf 4244)
  | 402 => some (.triangle 13 6544 6545)
  | 403 => some (.triangle 12 6546 6528)
  | 404 => some (.leaf 4245)
  | 405 => some (.leaf 4246)
  | 406 => some (.leaf 4247)
  | 407 => some (.positive 0 (![6548, 6539, 6549, 6541, 6542, 6550]))
  | 408 => some (.leaf 4248)
  | 409 => some (.leaf 4249)
  | 410 => some (.leaf 4250)
  | 411 => some (.leaf 4251)
  | 412 => some (.leaf 4252)
  | 413 => some (.leaf 4253)
  | 414 => some (.leaf 4254)
  | 415 => some (.leaf 4255)
  | 416 => some (.leaf 4256)
  | 417 => some (.leaf 4257)
  | 418 => some (.leaf 4258)
  | 419 => some (.positive 1 (![6557, 6558, 6559, 6560, 6561, 6562]))
  | 420 => some (.triangle 17 6556 6563)
  | 421 => some (.leaf 4259)
  | 422 => some (.leaf 4260)
  | 423 => some (.triangle 8 3758 6215)
  | 424 => some (.leaf 4261)
  | 425 => some (.leaf 4262)
  | 426 => some (.leaf 4263)
  | 427 => some (.positive 1 (![6565, 6566, 6567, 6568, 6569, 6570]))
  | 428 => some (.triangle 18 6564 6571)
  | 429 => some (.triangle 16 6555 6572)
  | 430 => some (.leaf 4264)
  | 431 => some (.leaf 4265)
  | 432 => some (.positive 0 (![6552, 6553, 6554, 6573, 6574, 6575]))
  | 433 => some (.triangle 13 6551 6576)
  | 434 => some (.triangle 12 6577 6528)
  | 435 => some (.leaf 4266)
  | 436 => some (.leaf 4267)
  | 437 => some (.leaf 4268)
  | 438 => some (.leaf 4269)
  | 439 => some (.leaf 4270)
  | 440 => some (.leaf 4271)
  | 441 => some (.leaf 4272)
  | 442 => some (.leaf 4273)
  | 443 => some (.leaf 4274)
  | 444 => some (.leaf 4275)
  | 445 => some (.heavy (![6529, 6530, 6531, 6532, 6533, 6534, 6535, 6536, 6537, 6547, 6578, 6579, 6580, 6581, 6582, 6583, 6584, 6585, 6586, 6587, 6588]))
  | 446 => some (.leaf 4276)
  | 447 => some (.leaf 4277)
  | 448 => some (.leaf 4278)
  | 449 => some (.leaf 4279)
  | 450 => some (.leaf 4280)
  | 451 => some (.leaf 4281)
  | 452 => some (.leaf 4282)
  | 453 => some (.triangle 15 6595 6596)
  | 454 => some (.triangle 14 6594 6597)
  | 455 => some (.leaf 4283)
  | 456 => some (.leaf 4284)
  | 457 => some (.leaf 4285)
  | 458 => some (.positive 2 (![6592, 6593, 6598, 6599, 6600, 6601]))
  | 459 => some (.leaf 4286)
  | 460 => some (.triangle 10 6602 6603)
  | 461 => some (.triangle 8 6591 6604)
  | 462 => some (.leaf 4287)
  | 463 => some (.leaf 4288)
  | 464 => some (.triangle 14 6606 6607)
  | 465 => some (.triangle 15 6595 6608)
  | 466 => some (.leaf 4289)
  | 467 => some (.leaf 4290)
  | 468 => some (.positive 2 (![6609, 1701, 1702, 6399, 6610, 6611]))
  | 469 => some (.triangle 10 6612 6603)
  | 470 => some (.triangle 19 6605 6613)
  | 471 => some (.leaf 4291)
  | 472 => some (.leaf 4292)
  | 473 => some (.leaf 4293)
  | 474 => some (.leaf 4294)
  | 475 => some (.leaf 4295)
  | 476 => some (.positive 1 (![6614, 6615, 6616, 6617, 6618, 6619]))
  | 477 => some (.triangle 18 6590 6620)
  | 478 => some (.triangle 16 1426 6621)
  | 479 => some (.leaf 4296)
  | 480 => some (.leaf 4297)
  | 481 => some (.leaf 4298)
  | 482 => some (.leaf 4299)
  | 483 => some (.triangle 14 6594 6626)
  | 484 => some (.leaf 4300)
  | 485 => some (.leaf 4301)
  | 486 => some (.positive 2 (![6592, 6593, 6627, 6628, 6629, 6601]))
  | 487 => some (.triangle 10 6630 6603)
  | 488 => some (.triangle 8 6625 6631)
  | 489 => some (.leaf 4302)
  | 490 => some (.triangle 15 6595 6633)
  | 491 => some (.leaf 4303)
  | 492 => some (.positive 2 (![6634, 1701, 1702, 6399, 6635, 6611]))
  | 493 => some (.triangle 10 6636 6603)
  | 494 => some (.triangle 19 6632 6637)
  | 495 => some (.positive 1 (![6624, 6638, 6616, 6617, 6618, 6619]))
  | 496 => some (.triangle 18 6590 6639)
  | 497 => some (.triangle 16 1426 6640)
  | 498 => some (.leaf 4304)
  | 499 => some (.leaf 4305)
  | 500 => some (.leaf 4306)
  | 501 => some (.positive 0 (![6622, 6623, 6641, 6642, 6643, 6644]))
  | 502 => some (.triangle 13 1425 6645)
  | 503 => some (.triangle 12 6646 6528)
  | 504 => some (.leaf 4307)
  | 505 => some (.leaf 4308)
  | 506 => some (.leaf 4309)
  | 507 => some (.leaf 4310)
  | 508 => some (.leaf 4311)
  | 509 => some (.leaf 4312)
  | 510 => some (.leaf 4313)
  | 511 => some (.leaf 4314)
  | 512 => some (.leaf 4315)
  | 513 => some (.leaf 4316)
  | 514 => some (.leaf 4317)
  | 515 => some (.leaf 4318)
  | 516 => some (.leaf 4319)
  | 517 => some (.leaf 4320)
  | 518 => some (.leaf 4321)
  | 519 => some (.leaf 4322)
  | 520 => some (.leaf 4323)
  | 521 => some (.triangle 14 6663 6664)
  | 522 => some (.leaf 4324)
  | 523 => some (.leaf 4325)
  | 524 => some (.leaf 4326)
  | 525 => some (.positive 2 (![6592, 6662, 6665, 6666, 6667, 6668]))
  | 526 => some (.leaf 4327)
  | 527 => some (.triangle 10 6669 6670)
  | 528 => some (.triangle 8 6661 6671)
  | 529 => some (.leaf 4328)
  | 530 => some (.leaf 4329)
  | 531 => some (.triangle 15 6673 6674)
  | 532 => some (.leaf 4330)
  | 533 => some (.leaf 4331)
  | 534 => some (.leaf 4332)
  | 535 => some (.positive 2 (![6675, 1701, 1702, 6676, 6677, 6678]))
  | 536 => some (.triangle 10 6679 6670)
  | 537 => some (.triangle 19 6672 6680)
  | 538 => some (.leaf 4333)
  | 539 => some (.leaf 4334)
  | 540 => some (.leaf 4335)
  | 541 => some (.positive 1 (![6659, 6660, 6681, 6682, 6683, 6684]))
  | 542 => some (.triangle 18 6658 6685)
  | 543 => some (.triangle 16 1426 6686)
  | 544 => some (.leaf 4336)
  | 545 => some (.leaf 4337)
  | 546 => some (.positive 0 (![6655, 6656, 6657, 6687, 6688, 6689]))
  | 547 => some (.triangle 13 1425 6690)
  | 548 => some (.triangle 12 6691 6528)
  | 549 => some (.leaf 4338)
  | 550 => some (.leaf 4339)
  | 551 => some (.leaf 4340)
  | 552 => some (.leaf 4341)
  | 553 => some (.leaf 4342)
  | 554 => some (.leaf 4343)
  | 555 => some (.leaf 4344)
  | 556 => some (.leaf 4345)
  | 557 => some (.leaf 4346)
  | 558 => some (.positive 1 (![6697, 6558, 6698, 6699, 6700, 6701]))
  | 559 => some (.triangle 17 6696 6702)
  | 560 => some (.leaf 4347)
  | 561 => some (.leaf 4348)
  | 562 => some (.leaf 4349)
  | 563 => some (.triangle 14 6594 6706)
  | 564 => some (.leaf 4350)
  | 565 => some (.leaf 4351)
  | 566 => some (.positive 2 (![6592, 6705, 6707, 6708, 6709, 6668]))
  | 567 => some (.leaf 4352)
  | 568 => some (.triangle 10 6710 6711)
  | 569 => some (.triangle 8 6661 6712)
  | 570 => some (.leaf 4353)
  | 571 => some (.triangle 19 6713 6714)
  | 572 => some (.leaf 4354)
  | 573 => some (.leaf 4355)
  | 574 => some (.positive 1 (![6704, 6566, 6715, 6682, 6716, 6717]))
  | 575 => some (.triangle 18 6703 6718)
  | 576 => some (.triangle 16 1426 6719)
  | 577 => some (.leaf 4356)
  | 578 => some (.leaf 4357)
  | 579 => some (.positive 0 (![6693, 6694, 6695, 6720, 6721, 6722]))
  | 580 => some (.triangle 13 1425 6723)
  | 581 => some (.triangle 12 6724 6528)
  | 582 => some (.leaf 4358)
  | 583 => some (.leaf 4359)
  | 584 => some (.leaf 4360)
  | 585 => some (.leaf 4361)
  | 586 => some (.leaf 4362)
  | 587 => some (.leaf 4363)
  | 588 => some (.leaf 4364)
  | 589 => some (.leaf 4365)
  | 590 => some (.leaf 4366)
  | 591 => some (.leaf 4367)
  | 592 => some (.leaf 4368)
  | 593 => some (.triangle 10 6736 6603)
  | 594 => some (.positive 1 (![6731, 6732, 6733, 6734, 6735, 6737]))
  | 595 => some (.leaf 4369)
  | 596 => some (.leaf 4370)
  | 597 => some (.leaf 4371)
  | 598 => some (.triangle 10 6740 6741)
  | 599 => some (.triangle 8 6739 6742)
  | 600 => some (.leaf 4372)
  | 601 => some (.triangle 19 6743 6744)
  | 602 => some (.positive 1 (![6557, 6558, 6698, 6699, 6700, 6745]))
  | 603 => some (.triangle 17 6738 6746)
  | 604 => some (.leaf 4373)
  | 605 => some (.leaf 4374)
  | 606 => some (.positive 2 (![6592, 6748, 6749, 1611, 6709, 6668]))
  | 607 => some (.triangle 10 6750 6603)
  | 608 => some (.triangle 8 6661 6751)
  | 609 => some (.leaf 4375)
  | 610 => some (.triangle 19 6752 6753)
  | 611 => some (.leaf 4376)
  | 612 => some (.triangle 19 6755 6753)
  | 613 => some (.positive 1 (![6565, 6566, 6754, 6682, 6716, 6756]))
  | 614 => some (.triangle 18 6747 6757)
  | 615 => some (.triangle 16 6730 6758)
  | 616 => some (.leaf 4377)
  | 617 => some (.positive 0 (![6727, 6728, 6729, 6759, 6721, 6760]))
  | 618 => some (.triangle 13 6726 6761)
  | 619 => some (.triangle 12 6762 6528)
  | 620 => some (.leaf 4378)
  | 621 => some (.leaf 4379)
  | 622 => some (.leaf 4380)
  | 623 => some (.leaf 4381)
  | 624 => some (.leaf 4382)
  | 625 => some (.leaf 4383)
  | 626 => some (.leaf 4384)
  | 627 => some (.leaf 4385)
  | 628 => some (.leaf 4386)
  | 629 => some (.leaf 4387)
  | 630 => some (.heavy (![6647, 6648, 6649, 6650, 6651, 6652, 6653, 6654, 6692, 6725, 6763, 6764, 6765, 6766, 6767, 6768, 6769, 6770, 6771, 6772, 6773]))
  | 631 => some (.triangle 7 6589 6774)
  | 632 => some (.triangle 3 6524 6775)
  | 633 => some (.leaf 4388)
  | 634 => some (.leaf 4389)
  | 635 => some (.triangle 14 6777 6778)
  | 636 => some (.leaf 4390)
  | 637 => some (.triangle 11 6779 6780)
  | 638 => some (.leaf 4391)
  | 639 => some (.leaf 4392)
  | 640 => some (.leaf 4393)
  | 641 => some (.leaf 4394)
  | 642 => some (.leaf 4395)
  | 643 => some (.leaf 4396)
  | 644 => some (.leaf 4397)
  | 645 => some (.leaf 4398)
  | 646 => some (.leaf 4399)
  | 647 => some (.leaf 4400)
  | 648 => some (.leaf 4401)
  | 649 => some (.leaf 4402)
  | 650 => some (.leaf 4403)
  | 651 => some (.leaf 4404)
  | 652 => some (.positive 0 (![6790, 6791, 6792, 6793, 6794, 6795]))
  | 653 => some (.leaf 4405)
  | 654 => some (.triangle 14 6796 6797)
  | 655 => some (.triangle 11 6798 6780)
  | 656 => some (.leaf 4406)
  | 657 => some (.leaf 4407)
  | 658 => some (.leaf 4408)
  | 659 => some (.positive 0 (![6800, 6791, 6801, 6793, 6794, 6802]))
  | 660 => some (.leaf 4409)
  | 661 => some (.leaf 4410)
  | 662 => some (.leaf 4411)
  | 663 => some (.leaf 4412)
  | 664 => some (.leaf 4413)
  | 665 => some (.triangle 17 6807 6808)
  | 666 => some (.leaf 4414)
  | 667 => some (.leaf 4415)
  | 668 => some (.leaf 4416)
  | 669 => some (.leaf 4417)
  | 670 => some (.leaf 4418)
  | 671 => some (.leaf 4419)
  | 672 => some (.positive 1 (![6810, 6811, 6812, 6813, 6814, 6815]))
  | 673 => some (.triangle 17 6807 6816)
  | 674 => some (.leaf 4420)
  | 675 => some (.leaf 4421)
  | 676 => some (.triangle 7 4227 6257)
  | 677 => some (.leaf 4422)
  | 678 => some (.leaf 4423)
  | 679 => some (.leaf 4424)
  | 680 => some (.positive 1 (![6818, 6819, 6820, 6821, 6822, 6823]))
  | 681 => some (.triangle 18 6817 6824)
  | 682 => some (.triangle 16 6809 6825)
  | 683 => some (.leaf 4425)
  | 684 => some (.leaf 4426)
  | 685 => some (.positive 0 (![6804, 6805, 6806, 6826, 6827, 6828]))
  | 686 => some (.triangle 14 6803 6829)
  | 687 => some (.triangle 11 6830 6780)
  | 688 => some (.leaf 4427)
  | 689 => some (.leaf 4428)
  | 690 => some (.leaf 4429)
  | 691 => some (.leaf 4430)
  | 692 => some (.leaf 4431)
  | 693 => some (.leaf 4432)
  | 694 => some (.leaf 4433)
  | 695 => some (.leaf 4434)
  | 696 => some (.leaf 4435)
  | 697 => some (.leaf 4436)
  | 698 => some (.heavy (![6781, 6782, 6783, 6784, 6785, 6786, 6787, 6788, 6789, 6799, 6831, 6832, 6833, 6834, 6835, 6836, 6837, 6838, 6839, 6840, 6841]))
  | 699 => some (.leaf 4437)
  | 700 => some (.leaf 4438)
  | 701 => some (.leaf 4439)
  | 702 => some (.triangle 18 6844 6845)
  | 703 => some (.triangle 16 6843 6846)
  | 704 => some (.leaf 4440)
  | 705 => some (.leaf 4441)
  | 706 => some (.leaf 4442)
  | 707 => some (.leaf 4443)
  | 708 => some (.positive 0 (![6847, 6848, 6847, 6849, 6850, 6851]))
  | 709 => some (.triangle 14 1345 6852)
  | 710 => some (.triangle 11 6853 6780)
  | 711 => some (.leaf 4444)
  | 712 => some (.leaf 4445)
  | 713 => some (.leaf 4446)
  | 714 => some (.leaf 4447)
  | 715 => some (.leaf 4448)
  | 716 => some (.leaf 4449)
  | 717 => some (.leaf 4450)
  | 718 => some (.leaf 4451)
  | 719 => some (.leaf 4452)
  | 720 => some (.leaf 4453)
  | 721 => some (.leaf 4454)
  | 722 => some (.leaf 4455)
  | 723 => some (.leaf 4456)
  | 724 => some (.leaf 4457)
  | 725 => some (.leaf 4458)
  | 726 => some (.leaf 4459)
  | 727 => some (.leaf 4460)
  | 728 => some (.positive 1 (![6866, 6867, 6868, 6869, 6870, 6871]))
  | 729 => some (.triangle 17 1381 6872)
  | 730 => some (.leaf 4461)
  | 731 => some (.triangle 18 6873 6874)
  | 732 => some (.triangle 16 6865 6875)
  | 733 => some (.leaf 4462)
  | 734 => some (.leaf 4463)
  | 735 => some (.positive 0 (![6862, 6863, 6864, 6876, 6877, 6878]))
  | 736 => some (.triangle 14 1345 6879)
  | 737 => some (.triangle 11 6880 6780)
  | 738 => some (.leaf 4464)
  | 739 => some (.leaf 4465)
  | 740 => some (.leaf 4466)
  | 741 => some (.leaf 4467)
  | 742 => some (.leaf 4468)
  | 743 => some (.leaf 4469)
  | 744 => some (.leaf 4470)
  | 745 => some (.positive 1 (![6886, 6811, 6868, 6869, 6887, 6888]))
  | 746 => some (.triangle 17 1381 6889)
  | 747 => some (.leaf 4471)
  | 748 => some (.leaf 4472)
  | 749 => some (.leaf 4473)
  | 750 => some (.leaf 4474)
  | 751 => some (.triangle 15 6893 6894)
  | 752 => some (.leaf 4475)
  | 753 => some (.leaf 4476)
  | 754 => some (.leaf 4477)
  | 755 => some (.positive 2 (![6592, 6892, 6895, 6896, 6897, 6898]))
  | 756 => some (.leaf 4478)
  | 757 => some (.triangle 10 6899 6900)
  | 758 => some (.leaf 4479)
  | 759 => some (.triangle 19 6901 6902)
  | 760 => some (.leaf 4480)
  | 761 => some (.leaf 4481)
  | 762 => some (.leaf 4482)
  | 763 => some (.positive 1 (![6891, 6819, 6903, 6904, 6905, 6906]))
  | 764 => some (.triangle 18 6890 6907)
  | 765 => some (.triangle 16 6885 6908)
  | 766 => some (.leaf 4483)
  | 767 => some (.leaf 4484)
  | 768 => some (.positive 0 (![6882, 6883, 6884, 6909, 6910, 6911]))
  | 769 => some (.triangle 14 1345 6912)
  | 770 => some (.triangle 11 6913 6780)
  | 771 => some (.leaf 4485)
  | 772 => some (.leaf 4486)
  | 773 => some (.leaf 4487)
  | 774 => some (.leaf 4488)
  | 775 => some (.leaf 4489)
  | 776 => some (.leaf 4490)
  | 777 => some (.leaf 4491)
  | 778 => some (.leaf 4492)
  | 779 => some (.leaf 4493)
  | 780 => some (.leaf 4494)
  | 781 => some (.leaf 4495)
  | 782 => some (.leaf 4496)
  | 783 => some (.triangle 10 6925 6926)
  | 784 => some (.positive 1 (![6920, 6921, 6922, 6923, 6924, 6927]))
  | 785 => some (.triangle 17 6919 6928)
  | 786 => some (.leaf 4497)
  | 787 => some (.leaf 4498)
  | 788 => some (.leaf 4499)
  | 789 => some (.triangle 10 6931 6932)
  | 790 => some (.leaf 4500)
  | 791 => some (.triangle 19 6933 6934)
  | 792 => some (.positive 1 (![6810, 6811, 6868, 6869, 6887, 6935]))
  | 793 => some (.triangle 17 6930 6936)
  | 794 => some (.leaf 4501)
  | 795 => some (.leaf 4502)
  | 796 => some (.positive 2 (![6592, 6938, 6939, 1611, 6897, 6898]))
  | 797 => some (.leaf 4503)
  | 798 => some (.triangle 10 6940 6941)
  | 799 => some (.leaf 4504)
  | 800 => some (.triangle 19 6942 6943)
  | 801 => some (.leaf 4505)
  | 802 => some (.positive 1 (![6818, 6819, 6944, 6904, 6905, 6945]))
  | 803 => some (.triangle 18 6937 6946)
  | 804 => some (.triangle 16 6929 6947)
  | 805 => some (.leaf 4506)
  | 806 => some (.positive 0 (![6916, 6917, 6918, 6948, 6910, 6949]))
  | 807 => some (.triangle 14 6915 6950)
  | 808 => some (.triangle 11 6951 6780)
  | 809 => some (.leaf 4507)
  | 810 => some (.leaf 4508)
  | 811 => some (.leaf 4509)
  | 812 => some (.leaf 4510)
  | 813 => some (.leaf 4511)
  | 814 => some (.leaf 4512)
  | 815 => some (.leaf 4513)
  | 816 => some (.leaf 4514)
  | 817 => some (.leaf 4515)
  | 818 => some (.leaf 4516)
  | 819 => some (.heavy (![6854, 6855, 6856, 6857, 6858, 6859, 6860, 6861, 6881, 6914, 6952, 6953, 6954, 6955, 6956, 6957, 6958, 6959, 6960, 6961, 6962]))
  | 820 => some (.triangle 8 6842 6963)
  | 821 => some (.leaf 4517)
  | 822 => some (.leaf 4518)
  | 823 => some (.leaf 4519)
  | 824 => some (.triangle 18 6966 6967)
  | 825 => some (.triangle 16 6965 6968)
  | 826 => some (.leaf 4520)
  | 827 => some (.leaf 4521)
  | 828 => some (.leaf 4522)
  | 829 => some (.leaf 4523)
  | 830 => some (.positive 0 (![6969, 6970, 6971, 6969, 6972, 6973]))
  | 831 => some (.leaf 4524)
  | 832 => some (.triangle 15 6974 6975)
  | 833 => some (.leaf 4525)
  | 834 => some (.triangle 12 6976 6977)
  | 835 => some (.triangle 11 6978 6780)
  | 836 => some (.leaf 4526)
  | 837 => some (.leaf 4527)
  | 838 => some (.leaf 4528)
  | 839 => some (.leaf 4529)
  | 840 => some (.leaf 4530)
  | 841 => some (.leaf 4531)
  | 842 => some (.leaf 4532)
  | 843 => some (.leaf 4533)
  | 844 => some (.leaf 4534)
  | 845 => some (.leaf 4535)
  | 846 => some (.leaf 4536)
  | 847 => some (.leaf 4537)
  | 848 => some (.leaf 4538)
  | 849 => some (.leaf 4539)
  | 850 => some (.leaf 4540)
  | 851 => some (.leaf 4541)
  | 852 => some (.leaf 4542)
  | 853 => some (.leaf 4543)
  | 854 => some (.leaf 4544)
  | 855 => some (.leaf 4545)
  | 856 => some (.positive 1 (![6994, 6995, 6996, 6997, 6998, 6999]))
  | 857 => some (.triangle 17 6993 7000)
  | 858 => some (.leaf 4546)
  | 859 => some (.leaf 4547)
  | 860 => some (.leaf 4548)
  | 861 => some (.leaf 4549)
  | 862 => some (.leaf 4550)
  | 863 => some (.leaf 4551)
  | 864 => some (.triangle 14 7006 7007)
  | 865 => some (.leaf 4552)
  | 866 => some (.leaf 4553)
  | 867 => some (.leaf 4554)
  | 868 => some (.positive 2 (![6592, 7005, 7008, 7009, 7010, 7011]))
  | 869 => some (.leaf 4555)
  | 870 => some (.triangle 10 7012 7013)
  | 871 => some (.triangle 8 7004 7014)
  | 872 => some (.triangle 19 7015 1579)
  | 873 => some (.triangle 7 4476 7016)
  | 874 => some (.leaf 4556)
  | 875 => some (.leaf 4557)
  | 876 => some (.leaf 4558)
  | 877 => some (.positive 1 (![7002, 7003, 7017, 7018, 7019, 7020]))
  | 878 => some (.triangle 18 7001 7021)
  | 879 => some (.triangle 16 6992 7022)
  | 880 => some (.leaf 4559)
  | 881 => some (.positive 0 (![6988, 6989, 6990, 6991, 7023, 7024]))
  | 882 => some (.triangle 15 7025 4448)
  | 883 => some (.triangle 12 7026 6528)
  | 884 => some (.triangle 11 7027 6780)
  | 885 => some (.leaf 4560)
  | 886 => some (.leaf 4561)
  | 887 => some (.leaf 4562)
  | 888 => some (.leaf 4563)
  | 889 => some (.leaf 4564)
  | 890 => some (.leaf 4565)
  | 891 => some (.leaf 4566)
  | 892 => some (.leaf 4567)
  | 893 => some (.leaf 4568)
  | 894 => some (.leaf 4569)
  | 895 => some (.leaf 4570)
  | 896 => some (.triangle 10 7038 7039)
  | 897 => some (.positive 1 (![7033, 7034, 7035, 7036, 7037, 7040]))
  | 898 => some (.leaf 4571)
  | 899 => some (.leaf 4572)
  | 900 => some (.leaf 4573)
  | 901 => some (.leaf 4574)
  | 902 => some (.leaf 4575)
  | 903 => some (.leaf 4576)
  | 904 => some (.positive 1 (![7042, 7043, 7044, 7045, 7046, 7047]))
  | 905 => some (.triangle 18 7041 7048)
  | 906 => some (.leaf 4577)
  | 907 => some (.leaf 4578)
  | 908 => some (.leaf 4579)
  | 909 => some (.leaf 4580)
  | 910 => some (.leaf 4581)
  | 911 => some (.leaf 4582)
  | 912 => some (.leaf 4583)
  | 913 => some (.triangle 10 7056 7039)
  | 914 => some (.triangle 8 7055 7057)
  | 915 => some (.positive 1 (![7050, 7051, 7052, 7053, 7054, 7058]))
  | 916 => some (.triangle 17 7049 7059)
  | 917 => some (.leaf 4584)
  | 918 => some (.leaf 4585)
  | 919 => some (.leaf 4586)
  | 920 => some (.leaf 4587)
  | 921 => some (.leaf 4588)
  | 922 => some (.leaf 4589)
  | 923 => some (.leaf 4590)
  | 924 => some (.triangle 10 7067 7039)
  | 925 => some (.triangle 7 7066 7068)
  | 926 => some (.positive 1 (![7061, 7062, 7063, 7064, 7065, 7069]))
  | 927 => some (.leaf 4591)
  | 928 => some (.leaf 4592)
  | 929 => some (.leaf 4593)
  | 930 => some (.leaf 4594)
  | 931 => some (.triangle 10 7074 6932)
  | 932 => some (.triangle 8 6739 7075)
  | 933 => some (.leaf 4595)
  | 934 => some (.triangle 19 7076 7077)
  | 935 => some (.triangle 7 7073 7078)
  | 936 => some (.positive 1 (![7071, 7072, 6996, 6997, 6998, 7079]))
  | 937 => some (.triangle 17 7070 7080)
  | 938 => some (.leaf 4596)
  | 939 => some (.leaf 4597)
  | 940 => some (.leaf 4598)
  | 941 => some (.leaf 4599)
  | 942 => some (.leaf 4600)
  | 943 => some (.positive 2 (![6592, 7084, 7085, 1611, 7086, 7011]))
  | 944 => some (.triangle 10 7087 7013)
  | 945 => some (.triangle 8 7004 7088)
  | 946 => some (.triangle 19 7089 1579)
  | 947 => some (.triangle 7 4476 7090)
  | 948 => some (.leaf 4601)
  | 949 => some (.positive 1 (![7082, 7083, 7091, 7018, 7019, 7092]))
  | 950 => some (.triangle 18 7081 7093)
  | 951 => some (.triangle 16 7060 7094)
  | 952 => some (.leaf 4602)
  | 953 => some (.positive 0 (![7029, 7030, 7031, 7032, 7095, 7096]))
  | 954 => some (.leaf 4603)
  | 955 => some (.triangle 15 7097 7098)
  | 956 => some (.leaf 4604)
  | 957 => some (.triangle 12 7099 7100)
  | 958 => some (.triangle 11 7101 6780)
  | 959 => some (.leaf 4605)
  | 960 => some (.leaf 4606)
  | 961 => some (.leaf 4607)
  | 962 => some (.leaf 4608)
  | 963 => some (.leaf 4609)
  | 964 => some (.leaf 4610)
  | 965 => some (.leaf 4611)
  | 966 => some (.leaf 4612)
  | 967 => some (.leaf 4613)
  | 968 => some (.leaf 4614)
  | 969 => some (.heavy (![6979, 6980, 6981, 6982, 6983, 6984, 6985, 6986, 6987, 7028, 7102, 7103, 7104, 7105, 7106, 7107, 7108, 7109, 7110, 7111, 7112]))
  | 970 => some (.triangle 3 6964 7113)
  | 971 => some (.leaf 4615)
  | 972 => some (.leaf 4616)
  | 973 => some (.leaf 4617)
  | 974 => some (.leaf 4618)
  | 975 => some (.leaf 4619)
  | 976 => some (.leaf 4620)
  | 977 => some (.leaf 4621)
  | 978 => some (.leaf 4622)
  | 979 => some (.leaf 4623)
  | 980 => some (.leaf 4624)
  | 981 => some (.leaf 4625)
  | 982 => some (.leaf 4626)
  | 983 => some (.leaf 4627)
  | 984 => some (.positive 3 (![7122, 7123, 7124, 7125, 7126, 7127]))
  | 985 => some (.triangle 8 1692 7128)
  | 986 => some (.leaf 4628)
  | 987 => some (.leaf 4629)
  | 988 => some (.leaf 4630)
  | 989 => some (.leaf 4631)
  | 990 => some (.positive 2 (![7129, 7130, 7131, 6399, 7132, 7133]))
  | 991 => some (.leaf 4632)
  | 992 => some (.triangle 10 7134 7135)
  | 993 => some (.triangle 19 7121 7136)
  | 994 => some (.triangle 7 7120 7137)
  | 995 => some (.leaf 4633)
  | 996 => some (.leaf 4634)
  | 997 => some (.leaf 4635)
  | 998 => some (.leaf 4636)
  | 999 => some (.positive 1 (![7119, 7138, 7139, 7140, 7141, 7142]))
  | 1000 => some (.triangle 18 1165 7143)
  | 1001 => some (.triangle 16 7118 7144)
  | 1002 => some (.leaf 4637)
  | 1003 => some (.leaf 4638)
  | 1004 => some (.positive 0 (![7115, 7116, 7117, 7145, 7146, 7147]))
  | 1005 => some (.triangle 3 4640 7148)
  | 1006 => some (.leaf 4639)
  | 1007 => some (.triangle 15 7149 7150)
  | 1008 => some (.leaf 4640)
  | 1009 => some (.triangle 12 7151 7152)
  | 1010 => some (.triangle 11 7153 6780)
  | 1011 => some (.leaf 4641)
  | 1012 => some (.leaf 4642)
  | 1013 => some (.leaf 4643)
  | 1014 => some (.leaf 4644)
  | 1015 => some (.leaf 4645)
  | 1016 => some (.leaf 4646)
  | 1017 => some (.leaf 4647)
  | 1018 => some (.leaf 4648)
  | 1019 => some (.leaf 4649)
  | 1020 => some (.leaf 4650)
  | 1021 => some (.triangle 15 7164 7150)
  | 1022 => some (.leaf 4651)
  | 1023 => some (.triangle 12 7165 7166)
  | 1024 => some (.triangle 11 7167 6780)
  | 1025 => some (.leaf 4652)
  | 1026 => some (.leaf 4653)
  | 1027 => some (.leaf 4654)
  | 1028 => some (.leaf 4655)
  | 1029 => some (.leaf 4656)
  | 1030 => some (.leaf 4657)
  | 1031 => some (.leaf 4658)
  | 1032 => some (.leaf 4659)
  | 1033 => some (.leaf 4660)
  | 1034 => some (.heavy (![7154, 7155, 7156, 7157, 7158, 7159, 7160, 7161, 7162, 7163, 7168, 7169, 7170, 7171, 7172, 7173, 7174, 7175, 7176, 7162, 7177]))
  | 1035 => some (.triangle 9 7114 7178)
  | 1036 => some (.triangle 2 6776 7179)
  | 1037 => some (.leaf 4661)
  | 1038 => some (.leaf 4662)
  | 1039 => some (.triangle 15 7181 7182)
  | 1040 => some (.leaf 4663)
  | 1041 => some (.triangle 10 7183 7184)
  | 1042 => some (.leaf 4664)
  | 1043 => some (.leaf 4665)
  | 1044 => some (.leaf 4666)
  | 1045 => some (.leaf 4667)
  | 1046 => some (.leaf 4668)
  | 1047 => some (.leaf 4669)
  | 1048 => some (.leaf 4670)
  | 1049 => some (.leaf 4671)
  | 1050 => some (.leaf 4672)
  | 1051 => some (.leaf 4673)
  | 1052 => some (.leaf 4674)
  | 1053 => some (.leaf 4675)
  | 1054 => some (.leaf 4676)
  | 1055 => some (.leaf 4677)
  | 1056 => some (.positive 0 (![7194, 7195, 7196, 7197, 7198, 7199]))
  | 1057 => some (.leaf 4678)
  | 1058 => some (.triangle 15 7200 7201)
  | 1059 => some (.triangle 10 7202 7184)
  | 1060 => some (.leaf 4679)
  | 1061 => some (.leaf 4680)
  | 1062 => some (.leaf 4681)
  | 1063 => some (.leaf 4682)
  | 1064 => some (.positive 0 (![7204, 7205, 7206, 7197, 7198, 7207]))
  | 1065 => some (.leaf 4683)
  | 1066 => some (.leaf 4684)
  | 1067 => some (.leaf 4685)
  | 1068 => some (.leaf 4686)
  | 1069 => some (.leaf 4687)
  | 1070 => some (.leaf 4688)
  | 1071 => some (.leaf 4689)
  | 1072 => some (.leaf 4690)
  | 1073 => some (.leaf 4691)
  | 1074 => some (.leaf 4692)
  | 1075 => some (.positive 1 (![7213, 7214, 7215, 7216, 7217, 7218]))
  | 1076 => some (.triangle 18 7212 7219)
  | 1077 => some (.leaf 4693)
  | 1078 => some (.triangle 17 7220 7221)
  | 1079 => some (.leaf 4694)
  | 1080 => some (.leaf 4695)
  | 1081 => some (.leaf 4696)
  | 1082 => some (.leaf 4697)
  | 1083 => some (.leaf 4698)
  | 1084 => some (.triangle 19 7226 7227)
  | 1085 => some (.leaf 4699)
  | 1086 => some (.leaf 4700)
  | 1087 => some (.leaf 4701)
  | 1088 => some (.positive 1 (![7224, 7225, 7228, 7229, 7230, 7231]))
  | 1089 => some (.triangle 18 7223 7232)
  | 1090 => some (.triangle 16 7222 7233)
  | 1091 => some (.leaf 4702)
  | 1092 => some (.leaf 4703)
  | 1093 => some (.positive 0 (![7209, 7210, 7211, 7234, 7235, 7236]))
  | 1094 => some (.triangle 15 7208 7237)
  | 1095 => some (.triangle 10 7238 7184)
  | 1096 => some (.leaf 4704)
  | 1097 => some (.leaf 4705)
  | 1098 => some (.leaf 4706)
  | 1099 => some (.leaf 4707)
  | 1100 => some (.leaf 4708)
  | 1101 => some (.leaf 4709)
  | 1102 => some (.leaf 4710)
  | 1103 => some (.leaf 4711)
  | 1104 => some (.leaf 4712)
  | 1105 => some (.leaf 4713)
  | 1106 => some (.heavy (![7185, 7186, 7187, 7188, 7189, 7190, 7191, 7192, 7193, 7203, 7239, 7240, 7241, 7242, 7243, 7244, 7245, 7246, 7247, 7248, 7249]))
  | 1107 => some (.leaf 4714)
  | 1108 => some (.leaf 4715)
  | 1109 => some (.triangle 16 7251 7252)
  | 1110 => some (.leaf 4716)
  | 1111 => some (.leaf 4717)
  | 1112 => some (.leaf 4718)
  | 1113 => some (.leaf 4719)
  | 1114 => some (.positive 0 (![7253, 7254, 7253, 7255, 7256, 7257]))
  | 1115 => some (.triangle 15 1161 7258)
  | 1116 => some (.triangle 10 7259 7184)
  | 1117 => some (.leaf 4720)
  | 1118 => some (.leaf 4721)
  | 1119 => some (.leaf 4722)
  | 1120 => some (.leaf 4723)
  | 1121 => some (.leaf 4724)
  | 1122 => some (.leaf 4725)
  | 1123 => some (.leaf 4726)
  | 1124 => some (.leaf 4727)
  | 1125 => some (.leaf 4728)
  | 1126 => some (.leaf 4729)
  | 1127 => some (.leaf 4730)
  | 1128 => some (.leaf 4731)
  | 1129 => some (.leaf 4732)
  | 1130 => some (.leaf 4733)
  | 1131 => some (.leaf 4734)
  | 1132 => some (.leaf 4735)
  | 1133 => some (.positive 1 (![7271, 7272, 7273, 7274, 7275, 7276]))
  | 1134 => some (.triangle 18 1165 7277)
  | 1135 => some (.leaf 4736)
  | 1136 => some (.triangle 17 7278 7279)
  | 1137 => some (.leaf 4737)
  | 1138 => some (.triangle 16 7280 7281)
  | 1139 => some (.leaf 4738)
  | 1140 => some (.leaf 4739)
  | 1141 => some (.positive 0 (![7268, 7269, 7270, 7282, 7283, 7284]))
  | 1142 => some (.triangle 15 1161 7285)
  | 1143 => some (.triangle 10 7286 7184)
  | 1144 => some (.leaf 4740)
  | 1145 => some (.leaf 4741)
  | 1146 => some (.leaf 4742)
  | 1147 => some (.leaf 4743)
  | 1148 => some (.leaf 4744)
  | 1149 => some (.leaf 4745)
  | 1150 => some (.positive 1 (![7291, 7214, 7273, 7274, 7292, 7293]))
  | 1151 => some (.triangle 18 1165 7294)
  | 1152 => some (.leaf 4746)
  | 1153 => some (.triangle 17 7295 7296)
  | 1154 => some (.leaf 4747)
  | 1155 => some (.triangle 16 7297 7298)
  | 1156 => some (.leaf 4748)
  | 1157 => some (.leaf 4749)
  | 1158 => some (.positive 0 (![7288, 7289, 7290, 7299, 7300, 7301]))
  | 1159 => some (.triangle 15 1161 7302)
  | 1160 => some (.triangle 10 7303 7184)
  | 1161 => some (.leaf 4750)
  | 1162 => some (.leaf 4751)
  | 1163 => some (.leaf 4752)
  | 1164 => some (.leaf 4753)
  | 1165 => some (.leaf 4754)
  | 1166 => some (.leaf 4755)
  | 1167 => some (.leaf 4756)
  | 1168 => some (.leaf 4757)
  | 1169 => some (.leaf 4758)
  | 1170 => some (.leaf 4759)
  | 1171 => some (.leaf 4760)
  | 1172 => some (.positive 2 (![7310, 7311, 7312, 7313, 7314, 7315]))
  | 1173 => some (.triangle 19 7309 7316)
  | 1174 => some (.positive 1 (![7213, 7214, 7273, 7274, 7292, 7317]))
  | 1175 => some (.triangle 18 7308 7318)
  | 1176 => some (.triangle 17 7319 7296)
  | 1177 => some (.leaf 4761)
  | 1178 => some (.leaf 4762)
  | 1179 => some (.leaf 4763)
  | 1180 => some (.leaf 4764)
  | 1181 => some (.leaf 4765)
  | 1182 => some (.leaf 4766)
  | 1183 => some (.leaf 4767)
  | 1184 => some (.positive 2 (![7322, 7323, 7324, 7325, 7326, 7327]))
  | 1185 => some (.triangle 19 1264 7328)
  | 1186 => some (.leaf 4768)
  | 1187 => some (.leaf 4769)
  | 1188 => some (.leaf 4770)
  | 1189 => some (.positive 1 (![7224, 7225, 7329, 7330, 7331, 7332]))
  | 1190 => some (.triangle 18 7321 7333)
  | 1191 => some (.triangle 16 7320 7334)
  | 1192 => some (.leaf 4771)
  | 1193 => some (.positive 0 (![7305, 7306, 7307, 7335, 7300, 7336]))
  | 1194 => some (.triangle 15 1161 7337)
  | 1195 => some (.triangle 10 7338 7184)
  | 1196 => some (.leaf 4772)
  | 1197 => some (.leaf 4773)
  | 1198 => some (.leaf 4774)
  | 1199 => some (.leaf 4775)
  | 1200 => some (.leaf 4776)
  | 1201 => some (.leaf 4777)
  | 1202 => some (.leaf 4778)
  | 1203 => some (.leaf 4779)
  | 1204 => some (.leaf 4780)
  | 1205 => some (.leaf 4781)
  | 1206 => some (.heavy (![7260, 7261, 7262, 7263, 7264, 7265, 7266, 7267, 7287, 7304, 7339, 7340, 7341, 7342, 7343, 7344, 7345, 7346, 7347, 7348, 7349]))
  | 1207 => some (.triangle 9 7250 7350)
  | 1208 => some (.leaf 4782)
  | 1209 => some (.leaf 4783)
  | 1210 => some (.triangle 16 7352 7353)
  | 1211 => some (.leaf 4784)
  | 1212 => some (.leaf 4785)
  | 1213 => some (.leaf 4786)
  | 1214 => some (.leaf 4787)
  | 1215 => some (.positive 0 (![7354, 7355, 7356, 7354, 7357, 7358]))
  | 1216 => some (.triangle 14 7359 5170)
  | 1217 => some (.triangle 12 7360 6528)
  | 1218 => some (.triangle 10 7361 7184)
  | 1219 => some (.leaf 4788)
  | 1220 => some (.leaf 4789)
  | 1221 => some (.leaf 4790)
  | 1222 => some (.leaf 4791)
  | 1223 => some (.leaf 4792)
  | 1224 => some (.leaf 4793)
  | 1225 => some (.leaf 4794)
  | 1226 => some (.leaf 4795)
  | 1227 => some (.leaf 4796)
  | 1228 => some (.leaf 4797)
  | 1229 => some (.leaf 4798)
  | 1230 => some (.leaf 4799)
  | 1231 => some (.leaf 4800)
  | 1232 => some (.leaf 4801)
  | 1233 => some (.leaf 4802)
  | 1234 => some (.leaf 4803)
  | 1235 => some (.leaf 4804)
  | 1236 => some (.leaf 4805)
  | 1237 => some (.leaf 4806)
  | 1238 => some (.positive 1 (![7376, 7377, 7378, 7379, 7380, 7381]))
  | 1239 => some (.triangle 18 7375 7382)
  | 1240 => some (.leaf 4807)
  | 1241 => some (.triangle 17 7383 7384)
  | 1242 => some (.leaf 4808)
  | 1243 => some (.triangle 16 7385 7386)
  | 1244 => some (.leaf 4809)
  | 1245 => some (.positive 0 (![7371, 7372, 7373, 7374, 7387, 7388]))
  | 1246 => some (.triangle 14 7389 5170)
  | 1247 => some (.triangle 12 7390 6528)
  | 1248 => some (.triangle 10 7391 7184)
  | 1249 => some (.leaf 4810)
  | 1250 => some (.leaf 4811)
  | 1251 => some (.leaf 4812)
  | 1252 => some (.leaf 4813)
  | 1253 => some (.leaf 4814)
  | 1254 => some (.leaf 4815)
  | 1255 => some (.leaf 4816)
  | 1256 => some (.leaf 4817)
  | 1257 => some (.leaf 4818)
  | 1258 => some (.leaf 4819)
  | 1259 => some (.leaf 4820)
  | 1260 => some (.triangle 19 7402 7403)
  | 1261 => some (.positive 1 (![7397, 7398, 7399, 7400, 7401, 7404]))
  | 1262 => some (.leaf 4821)
  | 1263 => some (.leaf 4822)
  | 1264 => some (.leaf 4823)
  | 1265 => some (.leaf 4824)
  | 1266 => some (.leaf 4825)
  | 1267 => some (.leaf 4826)
  | 1268 => some (.leaf 4827)
  | 1269 => some (.leaf 4828)
  | 1270 => some (.leaf 4829)
  | 1271 => some (.positive 2 (![7409, 7410, 7411, 7412, 7413, 7414]))
  | 1272 => some (.triangle 19 7408 7415)
  | 1273 => some (.positive 1 (![7406, 7407, 7378, 7379, 7380, 7416]))
  | 1274 => some (.triangle 18 7405 7417)
  | 1275 => some (.triangle 17 7418 7384)
  | 1276 => some (.leaf 4830)
  | 1277 => some (.leaf 4831)
  | 1278 => some (.leaf 4832)
  | 1279 => some (.leaf 4833)
  | 1280 => some (.leaf 4834)
  | 1281 => some (.leaf 4835)
  | 1282 => some (.leaf 4836)
  | 1283 => some (.positive 1 (![7421, 7422, 7423, 7424, 7425, 7426]))
  | 1284 => some (.triangle 17 7420 7427)
  | 1285 => some (.leaf 4837)
  | 1286 => some (.leaf 4838)
  | 1287 => some (.leaf 4839)
  | 1288 => some (.leaf 4840)
  | 1289 => some (.leaf 4841)
  | 1290 => some (.leaf 4842)
  | 1291 => some (.leaf 4843)
  | 1292 => some (.leaf 4844)
  | 1293 => some (.leaf 4845)
  | 1294 => some (.positive 2 (![7432, 7433, 7434, 7435, 7436, 7437]))
  | 1295 => some (.triangle 19 7431 7438)
  | 1296 => some (.leaf 4846)
  | 1297 => some (.leaf 4847)
  | 1298 => some (.leaf 4848)
  | 1299 => some (.positive 1 (![7429, 7430, 7439, 7440, 7441, 7442]))
  | 1300 => some (.triangle 18 7428 7443)
  | 1301 => some (.triangle 16 7419 7444)
  | 1302 => some (.leaf 4849)
  | 1303 => some (.positive 0 (![7393, 7394, 7395, 7396, 7445, 7446]))
  | 1304 => some (.triangle 14 7447 5170)
  | 1305 => some (.triangle 12 7448 6528)
  | 1306 => some (.triangle 10 7449 7184)
  | 1307 => some (.leaf 4850)
  | 1308 => some (.leaf 4851)
  | 1309 => some (.leaf 4852)
  | 1310 => some (.leaf 4853)
  | 1311 => some (.leaf 4854)
  | 1312 => some (.leaf 4855)
  | 1313 => some (.leaf 4856)
  | 1314 => some (.leaf 4857)
  | 1315 => some (.leaf 4858)
  | 1316 => some (.leaf 4859)
  | 1317 => some (.heavy (![7362, 7363, 7364, 7365, 7366, 7367, 7368, 7369, 7370, 7392, 7450, 7451, 7452, 7453, 7454, 7455, 7456, 7457, 7458, 7459, 7460]))
  | 1318 => some (.triangle 3 7351 7461)
  | 1319 => some (.leaf 4860)
  | 1320 => some (.leaf 4861)
  | 1321 => some (.triangle 16 7463 7464)
  | 1322 => some (.leaf 4862)
  | 1323 => some (.leaf 4863)
  | 1324 => some (.leaf 4864)
  | 1325 => some (.leaf 4865)
  | 1326 => some (.positive 0 (![7465, 7466, 7467, 7465, 7468, 7469]))
  | 1327 => some (.triangle 13 7470 5358)
  | 1328 => some (.triangle 11 7471 6780)
  | 1329 => some (.triangle 10 7472 7184)
  | 1330 => some (.leaf 4866)
  | 1331 => some (.leaf 4867)
  | 1332 => some (.leaf 4868)
  | 1333 => some (.leaf 4869)
  | 1334 => some (.leaf 4870)
  | 1335 => some (.leaf 4871)
  | 1336 => some (.leaf 4872)
  | 1337 => some (.leaf 4873)
  | 1338 => some (.leaf 4874)
  | 1339 => some (.leaf 4875)
  | 1340 => some (.leaf 4876)
  | 1341 => some (.leaf 4877)
  | 1342 => some (.leaf 4878)
  | 1343 => some (.leaf 4879)
  | 1344 => some (.leaf 4880)
  | 1345 => some (.leaf 4881)
  | 1346 => some (.leaf 4882)
  | 1347 => some (.leaf 4883)
  | 1348 => some (.positive 1 (![7486, 7487, 7488, 7489, 7490, 7491]))
  | 1349 => some (.leaf 4884)
  | 1350 => some (.triangle 18 7492 7493)
  | 1351 => some (.leaf 4885)
  | 1352 => some (.triangle 17 7494 7495)
  | 1353 => some (.leaf 4886)
  | 1354 => some (.leaf 4887)
  | 1355 => some (.triangle 17 7497 7498)
  | 1356 => some (.leaf 4888)
  | 1357 => some (.triangle 18 7499 7500)
  | 1358 => some (.triangle 16 7496 7501)
  | 1359 => some (.leaf 4889)
  | 1360 => some (.positive 0 (![7482, 7483, 7484, 7485, 7502, 7503]))
  | 1361 => some (.triangle 13 7504 5358)
  | 1362 => some (.triangle 11 7505 6780)
  | 1363 => some (.triangle 10 7506 7184)
  | 1364 => some (.leaf 4890)
  | 1365 => some (.leaf 4891)
  | 1366 => some (.leaf 4892)
  | 1367 => some (.leaf 4893)
  | 1368 => some (.leaf 4894)
  | 1369 => some (.leaf 4895)
  | 1370 => some (.leaf 4896)
  | 1371 => some (.leaf 4897)
  | 1372 => some (.triangle 19 7514 7515)
  | 1373 => some (.positive 1 (![7512, 7513, 7488, 7489, 7490, 7516]))
  | 1374 => some (.leaf 4898)
  | 1375 => some (.leaf 4899)
  | 1376 => some (.leaf 4900)
  | 1377 => some (.leaf 4901)
  | 1378 => some (.leaf 4902)
  | 1379 => some (.leaf 4903)
  | 1380 => some (.positive 1 (![7518, 7519, 7520, 7521, 7522, 7523]))
  | 1381 => some (.triangle 18 7517 7524)
  | 1382 => some (.leaf 4904)
  | 1383 => some (.triangle 17 7525 7526)
  | 1384 => some (.leaf 4905)
  | 1385 => some (.leaf 4906)
  | 1386 => some (.leaf 4907)
  | 1387 => some (.leaf 4908)
  | 1388 => some (.leaf 4909)
  | 1389 => some (.leaf 4910)
  | 1390 => some (.positive 1 (![7528, 7529, 7530, 7531, 7532, 7533]))
  | 1391 => some (.triangle 17 7497 7534)
  | 1392 => some (.leaf 4911)
  | 1393 => some (.leaf 4912)
  | 1394 => some (.leaf 4913)
  | 1395 => some (.leaf 4914)
  | 1396 => some (.triangle 19 7538 7539)
  | 1397 => some (.leaf 4915)
  | 1398 => some (.leaf 4916)
  | 1399 => some (.leaf 4917)
  | 1400 => some (.positive 1 (![7536, 7537, 7540, 7541, 7542, 7543]))
  | 1401 => some (.triangle 18 7535 7544)
  | 1402 => some (.triangle 16 7527 7545)
  | 1403 => some (.leaf 4918)
  | 1404 => some (.positive 0 (![7508, 7509, 7510, 7511, 7546, 7547]))
  | 1405 => some (.triangle 13 7548 5358)
  | 1406 => some (.triangle 11 7549 6780)
  | 1407 => some (.triangle 10 7550 7184)
  | 1408 => some (.leaf 4919)
  | 1409 => some (.leaf 4920)
  | 1410 => some (.leaf 4921)
  | 1411 => some (.leaf 4922)
  | 1412 => some (.leaf 4923)
  | 1413 => some (.leaf 4924)
  | 1414 => some (.leaf 4925)
  | 1415 => some (.leaf 4926)
  | 1416 => some (.leaf 4927)
  | 1417 => some (.leaf 4928)
  | 1418 => some (.heavy (![7473, 7474, 7475, 7476, 7477, 7478, 7479, 7480, 7481, 7507, 7551, 7552, 7553, 7554, 7555, 7556, 7557, 7558, 7559, 7560, 7561]))
  | 1419 => some (.leaf 4929)
  | 1420 => some (.leaf 4930)
  | 1421 => some (.triangle 16 7563 7564)
  | 1422 => some (.leaf 4931)
  | 1423 => some (.leaf 4932)
  | 1424 => some (.leaf 4933)
  | 1425 => some (.positive 0 (![7565, 7566, 7567, 7568, 7565, 7565]))
  | 1426 => some (.triangle 15 7569 4448)
  | 1427 => some (.triangle 14 7570 5170)
  | 1428 => some (.triangle 13 7571 5358)
  | 1429 => some (.triangle 12 7572 6528)
  | 1430 => some (.triangle 11 7573 6780)
  | 1431 => some (.triangle 10 7574 7184)
  | 1432 => some (.leaf 4934)
  | 1433 => some (.leaf 4935)
  | 1434 => some (.leaf 4936)
  | 1435 => some (.leaf 4937)
  | 1436 => some (.leaf 4938)
  | 1437 => some (.leaf 4939)
  | 1438 => some (.leaf 4940)
  | 1439 => some (.leaf 4941)
  | 1440 => some (.leaf 4942)
  | 1441 => some (.leaf 4943)
  | 1442 => some (.leaf 4944)
  | 1443 => some (.leaf 4945)
  | 1444 => some (.leaf 4946)
  | 1445 => some (.leaf 4947)
  | 1446 => some (.leaf 4948)
  | 1447 => some (.positive 1 (![7585, 7586, 7587, 7588, 7589, 7590]))
  | 1448 => some (.leaf 4949)
  | 1449 => some (.triangle 18 7591 7592)
  | 1450 => some (.leaf 4950)
  | 1451 => some (.triangle 17 7593 7594)
  | 1452 => some (.leaf 4951)
  | 1453 => some (.leaf 4952)
  | 1454 => some (.triangle 17 7596 7597)
  | 1455 => some (.leaf 4953)
  | 1456 => some (.triangle 18 7598 7599)
  | 1457 => some (.triangle 16 7595 7600)
  | 1458 => some (.leaf 4954)
  | 1459 => some (.positive 0 (![7583, 7566, 7584, 7568, 7601, 7602]))
  | 1460 => some (.leaf 4955)
  | 1461 => some (.triangle 15 7603 7604)
  | 1462 => some (.leaf 4956)
  | 1463 => some (.triangle 14 7605 7606)
  | 1464 => some (.triangle 13 7607 5358)
  | 1465 => some (.leaf 4957)
  | 1466 => some (.triangle 12 7608 7609)
  | 1467 => some (.triangle 11 7610 6780)
  | 1468 => some (.triangle 10 7611 7184)
  | 1469 => some (.leaf 4958)
  | 1470 => some (.leaf 4959)
  | 1471 => some (.leaf 4960)
  | 1472 => some (.leaf 4961)
  | 1473 => some (.leaf 4962)
  | 1474 => some (.leaf 4963)
  | 1475 => some (.leaf 4964)
  | 1476 => some (.triangle 19 7618 7619)
  | 1477 => some (.positive 1 (![7616, 7617, 7587, 7588, 7589, 7620]))
  | 1478 => some (.leaf 4965)
  | 1479 => some (.leaf 4966)
  | 1480 => some (.leaf 4967)
  | 1481 => some (.leaf 4968)
  | 1482 => some (.leaf 4969)
  | 1483 => some (.leaf 4970)
  | 1484 => some (.positive 1 (![7622, 7623, 7624, 7625, 7626, 7627]))
  | 1485 => some (.triangle 18 7621 7628)
  | 1486 => some (.leaf 4971)
  | 1487 => some (.triangle 17 7629 7630)
  | 1488 => some (.leaf 4972)
  | 1489 => some (.leaf 4973)
  | 1490 => some (.leaf 4974)
  | 1491 => some (.leaf 4975)
  | 1492 => some (.leaf 4976)
  | 1493 => some (.leaf 4977)
  | 1494 => some (.positive 1 (![7632, 7633, 7634, 7635, 7636, 7637]))
  | 1495 => some (.triangle 17 7596 7638)
  | 1496 => some (.leaf 4978)
  | 1497 => some (.leaf 4979)
  | 1498 => some (.leaf 4980)
  | 1499 => some (.leaf 4981)
  | 1500 => some (.triangle 19 7642 7643)
  | 1501 => some (.leaf 4982)
  | 1502 => some (.leaf 4983)
  | 1503 => some (.leaf 4984)
  | 1504 => some (.positive 1 (![7640, 7641, 7644, 7645, 7646, 7647]))
  | 1505 => some (.triangle 18 7639 7648)
  | 1506 => some (.triangle 16 7631 7649)
  | 1507 => some (.leaf 4985)
  | 1508 => some (.positive 0 (![7613, 7566, 7614, 7615, 7650, 7651]))
  | 1509 => some (.triangle 15 7652 4448)
  | 1510 => some (.triangle 14 7653 5170)
  | 1511 => some (.triangle 13 7654 5358)
  | 1512 => some (.triangle 12 7655 6528)
  | 1513 => some (.triangle 11 7656 6780)
  | 1514 => some (.triangle 10 7657 7184)
  | 1515 => some (.leaf 4986)
  | 1516 => some (.leaf 4987)
  | 1517 => some (.leaf 4988)
  | 1518 => some (.leaf 4989)
  | 1519 => some (.leaf 4990)
  | 1520 => some (.leaf 4991)
  | 1521 => some (.leaf 4992)
  | 1522 => some (.positive 1 (![7664, 7665, 7587, 7588, 7589, 7620]))
  | 1523 => some (.leaf 4993)
  | 1524 => some (.leaf 4994)
  | 1525 => some (.leaf 4995)
  | 1526 => some (.positive 1 (![7667, 7668, 7624, 7625, 7626, 7669]))
  | 1527 => some (.triangle 18 7666 7670)
  | 1528 => some (.triangle 17 7671 7630)
  | 1529 => some (.leaf 4996)
  | 1530 => some (.leaf 4997)
  | 1531 => some (.positive 1 (![7673, 7674, 7634, 7635, 7636, 7637]))
  | 1532 => some (.triangle 17 7596 7675)
  | 1533 => some (.leaf 4998)
  | 1534 => some (.leaf 4999)
  | 1535 => some (.leaf 5000)
  | _ => none

end Jsp404.SevenLowerBranchShard04
