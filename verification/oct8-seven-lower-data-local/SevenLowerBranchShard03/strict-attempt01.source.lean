import Jsp000404.SevenLowerReplay

/-! SOURCE_ONLY literal certificate data; no kernel PASS is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerBranchShard03
open SevenLowerReplay
def cycle0000 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1 (![3, 0, 2, 5, 4]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![3, 1, 2, 5, 4]), .triangle 0 1]

def cycle0001 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 2 (![3, 0, 2, 5, 4])]

def cycle0002 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 2, .gapLower 1 3 (![3, 0, 2, 5, 4]), .triangle 0 0]

def cycle0003 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![3, 0, 2, 5, 4]), .triangle 3 2, .gapLower 0 3 (![3, 1, 2, 5, 4]), .triangle 0 1]

def cycle0004 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 2, 5, 4]), .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![3, 1, 2, 5, 4]), .triangle 0 1]

def cycle0005 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .triangle 6 2, .gapLower 0 3 (![3, 1, 2, 5, 4]), .triangle 0 1]

def cycle0006 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 2, .triangle 9 2, .gapLower 0 3 (![3, 1, 2, 5, 4]), .triangle 0 1]

def cycle0007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 2, 5, 4]), .gapLower 1 5 (![3, 0, 2, 5, 4]), .triangle 2 2, .gapLower 0 4 (![3, 1, 2, 5, 4]), .triangle 3 1]

def cycle0008 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 1 (![3, 0, 2, 5, 4]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![3, 1, 2, 5, 4]), .triangle 6 1, .triangle 0 1]

def cycle0009 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![3, 0, 2, 5, 4]), .triangle 12 1, .triangle 0 0]

def cycle0010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 0, 2, 5, 4]), .triangle 2 2, .gapLower 0 4 (![3, 1, 2, 5, 4]), .triangle 8 1]

def cycle0011 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0012 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![3, 1, 2, 5, 4]), .triangle 3 1]

def cycle0013 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .gapLower 0 5 (![3, 1, 2, 5, 4]), .triangle 9 0, .triangle 15 0, .gapLower 1 3 (![3, 0, 2, 4, 5]), .triangle 0 0]

def cycle0014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 2, 5, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0015 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 2, 5, 4]), .triangle 2 0]

def cycle0016 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 5, 4, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0017 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1 (![3, 0, 5, 4, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0018 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 0, 5, 4, 2]), .triangle 3 0]

def cycle0019 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 5, 4]), .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 0, 5, 4, 2]), .triangle 2 0]

def cycle0020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 11 0, .triangle 5 0, .gapLower 0 2 (![3, 1, 2, 5, 4])]

def cycle0021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 5, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 2 (![3, 1, 2, 5, 4])]

def cycle0022 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 5, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![3, 1, 2, 5, 4]), .triangle 0 1]

def cycle0023 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 5, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 1, 2, 5, 4]), .triangle 6 1, .triangle 0 1]

def cycle0024 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 5, 4]), .corridorLower 0 3, .gapLower 0 5 (![3, 1, 2, 5, 4]), .triangle 5 1, .triangle 0 1]

def cycle0025 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![3, 1, 2, 5, 4]), .gapLower 0 2 (![3, 1, 2, 5, 4])]

def cycle0026 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 1, 2, 5, 4]), .triangle 6 1, .gapLower 0 2 (![3, 1, 2, 5, 4])]

def cycle0027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 2, 5, 4]), .triangle 5 1, .gapLower 0 2 (![3, 1, 2, 5, 4])]

def cycle0028 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 1, 2, 5, 4]), .gapLower 0 3 (![3, 1, 2, 5, 4]), .triangle 0 1]

def cycle0029 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 2, 5, 4]), .triangle 9 2, .gapLower 0 3 (![3, 1, 2, 5, 4]), .triangle 0 1]

def cycle0030 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 2, 5, 4]), .gapLower 0 4 (![3, 1, 2, 5, 4]), .triangle 3 1]

def cycle0031 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0032 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .gapLower 0 0 (![3, 1, 5, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0]

def cycle0033 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 2, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 6 2, .gapLower 0 2 (![3, 1, 5, 2, 4])]

def cycle0034 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 6 2, .gapLower 0 2 (![3, 1, 5, 2, 4])]

def cycle0035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 1, 5, 2, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0036 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 1, 5, 2, 4]), .triangle 0 1]

def cycle0037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![3, 1, 5, 2, 4]), .triangle 5 1]

def cycle0038 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 2, 4]), .gapLower 0 0 (![3, 1, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 6 2, .gapLower 0 2 (![3, 1, 5, 2, 4])]

def cycle0039 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 6 2, .gapLower 0 2 (![3, 1, 5, 2, 4])]

def cycle0040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 1, 5, 2, 4]), .triangle 8 1, .gapLower 0 0 (![3, 1, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0041 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 5, 2, 4]), .gapLower 1 5 (![3, 0, 5, 2, 4]), .triangle 2 2, .gapLower 0 4 (![3, 1, 5, 2, 4]), .triangle 0 1]

def cycle0042 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![3, 0, 5, 2, 4]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![3, 1, 5, 2, 4]), .triangle 0 1]

def cycle0043 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 2, .gapLower 1 2 (![3, 0, 5, 2, 4])]

def cycle0044 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 2, 4]), .gapLower 0 0 (![3, 1, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 3 (![3, 0, 5, 2, 4]), .triangle 3 0]

def cycle0045 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![3, 0, 5, 2, 4]), .triangle 0 0]

def cycle0046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 5, 2, 4]), .triangle 2 2, .gapLower 0 4 (![3, 1, 5, 2, 4]), .triangle 0 1]

def cycle0047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .corridorUpper 1 2, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![3, 1, 5, 2, 4])]

def cycle0048 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 5, 2, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 2, .triangle 3 0]

def cycle0049 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1 (![3, 0, 5, 2, 4]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 2, .triangle 3 0]

def cycle0050 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 5, 2, 4]), .triangle 2 0]

def cycle0051 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 2, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 6 2, .gapLower 0 2 (![3, 1, 5, 2, 4])]

def cycle0052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 2, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![3, 1, 5, 2, 4]), .triangle 3 1]

def cycle0053 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 2, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 1, 5, 2, 4]), .triangle 0 1]

def cycle0054 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 2, 4]), .corridorLower 0 3, .gapLower 0 5 (![3, 1, 5, 2, 4]), .triangle 5 1, .triangle 6 2, .gapLower 0 2 (![3, 1, 5, 2, 4])]

def cycle0055 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![3, 1, 5, 2, 4]), .gapLower 0 2 (![3, 1, 5, 2, 4])]

def cycle0056 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 1, 5, 2, 4]), .triangle 6 2, .gapLower 0 2 (![3, 1, 5, 2, 4])]

def cycle0057 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 5, 2, 4]), .triangle 5 1, .triangle 6 2, .gapLower 0 2 (![3, 1, 5, 2, 4])]

def cycle0058 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 1, 5, 2, 4]), .gapLower 0 3 (![3, 1, 5, 2, 4]), .triangle 3 1]

def cycle0059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 5, 2, 4]), .triangle 5 1, .gapLower 0 3 (![3, 1, 5, 2, 4]), .triangle 3 1]

def cycle0060 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 5, 2, 4]), .gapLower 0 4 (![3, 1, 5, 2, 4]), .triangle 0 1]

def cycle0061 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0062 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0063 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 2, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0064 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![3, 1, 4, 2, 5])]

def cycle0065 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 1, 4, 2, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0066 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 1, 4, 2, 5]), .triangle 0 1]

def cycle0067 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 4, 2, 5]), .triangle 6 1, .triangle 0 1]

def cycle0068 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 2, 5]), .gapLower 0 0 (![3, 1, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0069 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .triangle 5 2, .gapLower 0 2 (![3, 1, 4, 2, 5])]

def cycle0070 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 1, 4, 2, 5]), .triangle 7 1, .gapLower 0 0 (![3, 1, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0071 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 4, 2, 5]), .gapLower 1 5 (![3, 0, 4, 2, 5]), .triangle 3 2, .gapLower 0 4 (![3, 1, 4, 2, 5]), .triangle 0 1]

def cycle0072 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![3, 0, 4, 2, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![3, 1, 4, 2, 5]), .triangle 0 1]

def cycle0073 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 11 2, .gapLower 1 2 (![3, 0, 4, 2, 5])]

def cycle0074 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 2, 5]), .gapLower 0 0 (![3, 1, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .gapLower 1 3 (![3, 0, 4, 2, 5]), .triangle 2 0]

def cycle0075 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![3, 0, 4, 2, 5]), .triangle 0 0]

def cycle0076 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 4, 2, 5]), .triangle 3 2, .gapLower 0 4 (![3, 1, 4, 2, 5]), .triangle 0 1]

def cycle0077 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![3, 1, 4, 2, 5])]

def cycle0078 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![3, 1, 4, 2, 5])]

def cycle0079 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 4, 2, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 0 0]

def cycle0080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![3, 0, 4, 2, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 0 0]

def cycle0081 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 4, 2, 5]), .triangle 3 0]

def cycle0082 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 12 0, .triangle 6 0]

def cycle0083 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 5, 4, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0084 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 1 (![3, 0, 5, 4, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0085 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0086 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (-1), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 7 0, .gapLower 0 0 (![3, 1, 4, 2, 5]), .gapLower 0 5 (![3, 1, 4, 2, 5]), .triangle 6 1]

def cycle0087 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 0, 5, 4, 2]), .triangle 15 1, .triangle 9 0, .triangle 2 1]

def cycle0088 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 2, 5]), .gapLower 0 0 (![3, 1, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 0, 5, 4, 2]), .triangle 2 0]

def cycle0089 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![3, 1, 4, 2, 5])]

def cycle0090 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 2, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![3, 1, 4, 2, 5])]

def cycle0091 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 2, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![3, 1, 4, 2, 5]), .triangle 2 1]

def cycle0092 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 2, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 1, 4, 2, 5]), .triangle 0 1]

def cycle0093 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 2, 5]), .corridorLower 0 3, .gapLower 0 5 (![3, 1, 4, 2, 5]), .triangle 6 1, .triangle 0 1]

def cycle0094 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![3, 1, 4, 2, 5]), .gapLower 0 2 (![3, 1, 4, 2, 5])]

def cycle0095 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 1, 4, 2, 5]), .triangle 5 2, .gapLower 0 2 (![3, 1, 4, 2, 5])]

def cycle0096 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 4, 2, 5]), .triangle 6 1, .triangle 5 2, .gapLower 0 2 (![3, 1, 4, 2, 5])]

def cycle0097 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 1, 4, 2, 5]), .gapLower 0 3 (![3, 1, 4, 2, 5]), .triangle 2 1]

def cycle0098 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 4, 2, 5]), .triangle 6 1, .gapLower 0 3 (![3, 1, 4, 2, 5]), .triangle 2 1]

def cycle0099 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 4, 2, 5]), .gapLower 0 4 (![3, 1, 4, 2, 5]), .triangle 0 1]

def cycle0100 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0101 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0102 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 5, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0103 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![3, 1, 4, 5, 2])]

def cycle0104 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 3 (![3, 1, 4, 5, 2]), .triangle 5 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def cycle0105 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 6 1, .corridorLower 2 5, .corridorUpper 1 2, .triangle 0 2]

def cycle0106 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 4, 5, 2]), .triangle 6 2, .triangle 9 1, .gapLower 0 2 (![3, 1, 4, 5, 2])]

def cycle0107 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 5, 2]), .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0108 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![3, 1, 4, 5, 2])]

def cycle0109 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 4, 5, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 1, 4, 5, 2]), .triangle 2 1]

def cycle0110 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![3, 0, 4, 5, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 1, 4, 5, 2]), .triangle 2 1]

def cycle0111 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![3, 0, 4, 5, 2])]

def cycle0112 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![3, 0, 4, 5, 2]), .triangle 2 0]

def cycle0113 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 0, 4, 5, 2]), .triangle 3 2, .gapLower 0 3 (![3, 1, 4, 5, 2]), .triangle 2 1]

def cycle0114 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 4, 5, 2]), .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 1, 4, 5, 2]), .triangle 2 1]

def cycle0115 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 3 (![3, 1, 4, 5, 2]), .triangle 2 1]

def cycle0116 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 4, 5, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 9 1, .triangle 2 1]

def cycle0117 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 1 (![3, 0, 4, 5, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 9 1, .triangle 2 1]

def cycle0118 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 0, 4, 5, 2]), .triangle 15 1, .triangle 2 0]

def cycle0119 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 4, 5, 2]), .triangle 0 2, .gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 3 1]

def cycle0120 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 5, 4, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 9 1, .triangle 2 1]

def cycle0121 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 1 (![3, 0, 5, 4, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 9 1, .triangle 2 1]

def cycle0122 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 6 1, .triangle 17 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0123 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0124 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2]
    constant := ![(0), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false] }
  origin := ![.triangle 11 2, .triangle 15 0, .triangle 18 0, .triangle 16 1, .triangle 10 0]

def cycle0125 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![3, 0, 5, 4, 2])]

def cycle0126 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 9 1, .triangle 2 1]

def cycle0127 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![3, 0, 5, 4, 2])]

def cycle0128 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, true] }
  origin := ![.triangle 5 1, .triangle 16 1, .triangle 17 0, .triangle 8 2, .triangle 9 1]

def cycle0129 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (0), (-1), (-2), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 9 1, .triangle 5 1, .triangle 16 1, .triangle 7 0, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0130 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 0, 5, 4, 2]), .triangle 15 1, .triangle 9 0, .triangle 2 1]

def cycle0131 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 5, 2]), .gapLower 0 0 (![3, 1, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 0, 5, 4, 2]), .triangle 2 0]

def cycle0132 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 0 2, .gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 3 1]

def cycle0133 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .gapLower 0 5 (![3, 1, 4, 5, 2]), .triangle 5 0, .triangle 11 0, .triangle 0 0]

def cycle0134 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .gapLower 0 5 (![3, 1, 4, 5, 2]), .triangle 6 0, .triangle 12 0, .gapLower 1 3 (![3, 0, 4, 2, 5]), .gapLower 1 2 (![3, 0, 4, 2, 5])]

def cycle0135 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 4, 5, 2]), .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0136 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![3, 0, 4, 5, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0137 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 4, 5, 2]), .triangle 12 2, .triangle 15 1, .triangle 2 0]

def cycle0138 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 5, 4, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![3, 1, 4, 5, 2])]

def cycle0139 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (0), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .gapLower 0 5 (![3, 1, 4, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![3, 0, 5, 4, 2])]

def cycle0140 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (-2), (0), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, true, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .gapLower 0 5 (![3, 1, 4, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![3, 0, 5, 4, 2])]

def cycle0141 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 4, 5, 2]), .gapLower 0 5 (![3, 1, 4, 5, 2]), .triangle 5 0, .triangle 18 0, .triangle 9 0, .gapLower 0 2 (![3, 1, 4, 5, 2])]

def cycle0142 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 2 3 (![5, 3, 4, 0, 1]), .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 1, 4, 5, 2]), .gapLower 0 5 (![3, 1, 4, 5, 2])]

def cycle0143 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 7 0, .gapLower 0 0 (![3, 1, 4, 5, 2]), .gapLower 0 5 (![3, 1, 4, 5, 2])]

def cycle0144 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![3, 1, 4, 5, 2])]

def cycle0145 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 5, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![3, 1, 4, 5, 2])]

def cycle0146 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 5, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 1, 4, 5, 2]), .triangle 2 1]

def cycle0147 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 5, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 9 1, .triangle 2 1]

def cycle0148 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![3, 1, 4, 5, 2]), .corridorLower 0 3, .gapLower 0 5 (![3, 1, 4, 5, 2]), .triangle 6 2, .triangle 9 1, .gapLower 0 2 (![3, 1, 4, 5, 2])]

def cycle0149 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 1, 4, 5, 2]), .gapLower 0 2 (![3, 1, 4, 5, 2])]

def cycle0150 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 9 1, .gapLower 0 2 (![3, 1, 4, 5, 2])]

def cycle0151 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 4, 5, 2]), .triangle 6 2, .triangle 9 1, .gapLower 0 2 (![3, 1, 4, 5, 2])]

def cycle0152 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![3, 1, 4, 5, 2]), .gapLower 0 3 (![3, 1, 4, 5, 2]), .triangle 5 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def cycle0153 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 4, 5, 2]), .triangle 6 2, .gapLower 0 3 (![3, 1, 4, 5, 2]), .triangle 2 1]

def cycle0154 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 4, 5, 2]), .gapLower 0 4 (![3, 1, 4, 5, 2]), .triangle 3 1]

def cycle0155 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 18 0, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0156 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (-2), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 18 0, .gapLower 2 1 (![3, 4, 5, 0, 1]), .gapLower 3 0 (![2, 1, 0, 5, 4]), .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0157 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .gapLower 3 1 (![2, 1, 0, 5, 4]), .corridorLower 2 3, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 11 2, .triangle 15 2, .triangle 3 0]

def cycle0158 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (-2), (4), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 3 2 (![2, 1, 0, 5, 4]), .gapLower 1 0 (![3, 0, 5, 4, 2]), .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 11 2, .triangle 15 2, .triangle 3 0]

def cycle0159 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 3 3 (![2, 1, 0, 5, 4])]

def cycle0160 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![2, 1, 0, 5, 4]), .triangle 8 0]

def cycle0161 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 3, .distance 3 4, .distance 0 3]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![2, 1, 0, 5, 4]), .triangle 7 0]

def cycle0162 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 18 0, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1])]

def cycle0163 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 11 2, .triangle 15 2, .triangle 3 0]

def cycle0164 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .distance 1 2]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 11 0, .triangle 16 1, .triangle 10 0]

def cycle0165 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 2 0 (![3, 5, 4, 0, 1]), .corridorUpper 1 2, .triangle 0 0]

def cycle0166 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.triangle 5 0, .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 5, 4, 0, 1])]

def cycle0167 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 11 2, .triangle 15 2, .triangle 3 0]

def cycle0168 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 2 3 (![5, 3, 4, 0, 1]), .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 1, 5, 4, 2]), .gapLower 0 5 (![3, 1, 5, 4, 2])]

def cycle0169 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 7 0, .gapLower 0 0 (![3, 1, 5, 4, 2]), .gapLower 0 5 (![3, 1, 5, 4, 2])]

def cycle0170 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 1 (![3, 0, 5, 4, 2]), .triangle 10 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def cycle0171 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 1 (![3, 0, 5, 4, 2]), .triangle 10 1, .gapLower 2 0 (![3, 5, 4, 0, 1]), .corridorUpper 1 2, .triangle 0 0]

def cycle0172 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![3, 0, 5, 4, 2])]

def cycle0173 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 4, 2]), .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 0, 5, 4, 2]), .triangle 3 0]

def cycle0174 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 4, 2]), .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 0, 5, 4, 2]), .triangle 2 0]

def cycle0175 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 11 2, .triangle 15 2, .triangle 3 0]

def cycle0176 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 4, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0177 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0178 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 1, 5, 4, 2]), .triangle 3 1]

def cycle0179 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 4 (![3, 1, 5, 4, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0180 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 5, 4, 2]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0181 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 4, 2]), .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0182 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 5, 4, 2]), .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0183 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 1 (![3, 0, 5, 4, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0184 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0185 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0186 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0187 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 2 0 (![3, 5, 4, 0, 1]), .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0188 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 5, 4, 0, 1]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0189 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0190 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 16 1, .triangle 17 0, .triangle 8 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0191 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 16 1, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0192 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 0, 5, 4, 2]), .triangle 3 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0193 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 0, 5, 4, 2]), .triangle 2 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0194 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0195 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 5, 4, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 1, 5, 4, 2]), .triangle 3 1]

def cycle0196 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![3, 0, 5, 4, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 1, 5, 4, 2]), .triangle 3 1]

def cycle0197 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false, true] }
  origin := ![.triangle 5 2, .gapLower 0 3 (![3, 1, 5, 4, 2]), .triangle 9 1, .triangle 18 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0198 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 10 1, .gapLower 2 0 (![3, 5, 4, 0, 1]), .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![3, 0, 5, 4, 2])]

def cycle0199 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 5, 4, 0, 1]), .triangle 5 2, .gapLower 0 3 (![3, 1, 5, 4, 2]), .triangle 3 1]

def cycle0200 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![3, 0, 5, 4, 2])]

def cycle0201 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 1, 5, 4, 2]), .gapLower 0 5 (![3, 1, 5, 4, 2])]

def cycle0202 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 16 1, .triangle 7 2, .gapLower 0 3 (![3, 1, 5, 4, 2]), .triangle 3 1]

def cycle0203 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 0, 5, 4, 2]), .triangle 3 0]

def cycle0204 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 0, 5, 4, 2]), .triangle 2 2, .gapLower 0 3 (![3, 1, 5, 4, 2]), .triangle 3 1]

def cycle0205 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 1, 5, 4, 2]), .triangle 3 1]

def cycle0206 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 4 (![3, 1, 5, 4, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0207 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .gapLower 0 5 (![3, 1, 5, 4, 2]), .triangle 5 0, .triangle 11 0, .triangle 0 0]

def cycle0208 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (2), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 5, 4, 2]), .thetaOrder 0, .gapLower 0 5 (![3, 1, 5, 4, 2]), .triangle 5 2, .triangle 9 2, .triangle 3 1]

def cycle0209 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (2), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 1 (![3, 0, 5, 4, 2]), .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 5, 4, 2]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0210 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (0), (-1), (-1), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .gapLower 0 5 (![3, 1, 5, 4, 2]), .triangle 5 2, .triangle 9 0, .triangle 18 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![3, 0, 5, 4, 2])]

def cycle0211 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .gapLower 0 5 (![3, 1, 5, 4, 2]), .triangle 5 0, .triangle 18 0, .corridorLower 4 5, .corridorUpper 1 4, .triangle 15 2, .gapLower 1 2 (![3, 0, 5, 4, 2])]

def cycle0212 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 2 3 (![5, 3, 4, 0, 1]), .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 1, 5, 4, 2]), .gapLower 0 5 (![3, 1, 5, 4, 2])]

def cycle0213 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 7 0, .gapLower 0 0 (![3, 1, 5, 4, 2]), .gapLower 0 5 (![3, 1, 5, 4, 2])]

def cycle0214 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 0, 5, 4, 2]), .triangle 2 0]

def cycle0215 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 11 2, .triangle 15 2, .triangle 3 0]

def cycle0216 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 4, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0217 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 4, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 1, 5, 4, 2]), .triangle 3 1]

def cycle0218 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 4, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 1, 5, 4, 2]), .triangle 2 1]

def cycle0219 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![3, 1, 5, 4, 2]), .corridorLower 0 3, .gapLower 0 5 (![3, 1, 5, 4, 2]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0220 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 1, 5, 4, 2]), .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0221 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 1, 5, 4, 2]), .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0222 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 5, 4, 2]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![3, 1, 5, 4, 2])]

def cycle0223 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 1, 5, 4, 2]), .gapLower 0 3 (![3, 1, 5, 4, 2]), .triangle 3 1]

def cycle0224 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 5, 4, 2]), .triangle 5 2, .gapLower 0 3 (![3, 1, 5, 4, 2]), .triangle 3 1]

def cycle0225 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 5, 4, 2]), .gapLower 0 4 (![3, 1, 5, 4, 2]), .triangle 2 1]

def cycle0226 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0227 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0228 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 1, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0229 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![3, 5, 1, 2, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0230 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 2, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0231 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![3, 5, 1, 2, 4])]

def cycle0232 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 5, 1, 2, 4]), .triangle 0 1]

def cycle0233 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 5, 1, 2, 4]), .triangle 2 1]

def cycle0234 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![3, 5, 1, 2, 4]), .gapLower 0 0 (![3, 5, 1, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0235 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 2, 4]), .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0236 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![3, 5, 1, 2, 4])]

def cycle0237 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 1 0 (![3, 5, 0, 2, 4]), .gapLower 1 5 (![3, 5, 0, 2, 4]), .triangle 2 2, .gapLower 0 4 (![3, 5, 1, 2, 4]), .triangle 0 1]

def cycle0238 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![3, 5, 0, 2, 4]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0239 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2 (![3, 5, 0, 2, 4]), .triangle 14 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![3, 5, 1, 2, 4]), .triangle 0 1]

def cycle0240 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 3 (![3, 5, 0, 2, 4])]

def cycle0241 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![3, 5, 0, 2, 4]), .triangle 0 0]

def cycle0242 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 14 1, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 0, 2, 4]), .triangle 2 2, .gapLower 0 4 (![3, 5, 1, 2, 4]), .triangle 0 1]

def cycle0243 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![3, 5, 1, 2, 4]), .triangle 0 1]

def cycle0244 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 3 5, .distance 0 3]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 1 1, .triangle 14 0, .triangle 8 0]

def cycle0245 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 1 0 (![3, 5, 0, 2, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0246 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2 (![3, 5, 0, 2, 4]), .triangle 14 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0247 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 0, 2, 4]), .triangle 2 0]

def cycle0248 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 1 0 (![3, 5, 0, 4, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0, .gapLower 0 3 (![3, 5, 1, 2, 4])]

def cycle0249 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![3, 5, 0, 4, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 11 0, .triangle 5 0, .gapLower 0 3 (![3, 5, 1, 2, 4])]

def cycle0250 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2 (![3, 5, 0, 4, 2]), .triangle 14 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0251 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0), (0)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, true] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 4 1, .triangle 0 1]

def cycle0252 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 5, 0, 4, 2]), .triangle 2 0]

def cycle0253 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 11 0, .triangle 5 0, .gapLower 0 3 (![3, 5, 1, 2, 4])]

def cycle0254 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 1, 2, 4]), .gapLower 0 5 (![3, 5, 1, 2, 4]), .triangle 2 1]

def cycle0255 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 2, 4]), .gapLower 0 1 (![3, 5, 1, 2, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0256 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![3, 5, 1, 2, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![3, 5, 1, 2, 4])]

def cycle0257 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![3, 5, 1, 2, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 5, 1, 2, 4]), .triangle 0 1]

def cycle0258 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![3, 5, 1, 2, 4]), .corridorLower 0 3, .gapLower 0 5 (![3, 5, 1, 2, 4]), .triangle 5 1, .triangle 0 1]

def cycle0259 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 2, 4]), .triangle 8 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![3, 5, 1, 2, 4])]

def cycle0260 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 2, 4]), .triangle 8 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 5, 1, 2, 4]), .triangle 0 1]

def cycle0261 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 2, 4]), .corridorLower 0 5, .gapLower 0 5 (![3, 5, 1, 2, 4]), .triangle 5 1, .triangle 0 1]

def cycle0262 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 5, 1, 2, 4]), .gapLower 0 3 (![3, 5, 1, 2, 4])]

def cycle0263 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 5, 1, 2, 4]), .triangle 5 1, .gapLower 0 3 (![3, 5, 1, 2, 4])]

def cycle0264 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 5, 1, 2, 4]), .gapLower 0 4 (![3, 5, 1, 2, 4]), .triangle 0 1]

def cycle0265 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 0]

def cycle0266 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 7 0]

def cycle0267 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 3 0 (![2, 1, 0, 5, 4]), .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0268 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 3 1 (![2, 1, 0, 5, 4]), .corridorLower 2 3, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 0]

def cycle0269 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 3 2 (![2, 1, 0, 5, 4]), .gapLower 1 0 (![3, 5, 0, 4, 2]), .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 0]

def cycle0270 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 3 3 (![2, 1, 0, 5, 4])]

def cycle0271 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![2, 1, 0, 5, 4]), .triangle 8 0]

def cycle0272 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 3, .distance 3 4, .distance 0 3]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![2, 1, 0, 5, 4]), .triangle 7 0]

def cycle0273 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 1 0 (![3, 5, 0, 4, 2]), .gapLower 1 5 (![3, 5, 0, 4, 2]), .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 0 1]

def cycle0274 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 0]

def cycle0275 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 2 0 (![3, 5, 4, 0, 1]), .corridorUpper 1 2, .triangle 0 0]

def cycle0276 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 0]

def cycle0277 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 2 3 (![5, 3, 4, 0, 1]), .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2])]

def cycle0278 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 7 0, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2])]

def cycle0279 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![3, 5, 0, 4, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 0]

def cycle0280 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 2 (![3, 5, 0, 4, 2]), .triangle 14 1, .triangle 10 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 0]

def cycle0281 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 2 (![3, 5, 0, 4, 2]), .triangle 14 1, .triangle 10 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def cycle0282 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 0 1]

def cycle0283 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 2 (![3, 5, 0, 4, 2]), .triangle 14 1, .triangle 10 1, .gapLower 2 0 (![3, 5, 4, 0, 1]), .corridorUpper 1 2, .triangle 0 0]

def cycle0284 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0285 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 5, 0, 4, 2]), .triangle 2 0]

def cycle0286 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 0]

def cycle0287 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0288 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![3, 5, 1, 4, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0289 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 4, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0290 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0291 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 5, 1, 4, 2]), .triangle 2 1]

def cycle0292 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 0 1]

def cycle0293 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![3, 5, 1, 4, 2]), .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0294 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 4, 2]), .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0295 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 1 0 (![3, 5, 0, 4, 2]), .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0296 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![3, 5, 0, 4, 2]), .gapLower 1 1 (![3, 5, 0, 4, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0297 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![3, 5, 0, 4, 2]), .corridorLower 1 5, .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0298 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0299 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 17 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0300 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0301 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0302 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0303 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0304 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0305 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .gapLower 2 0 (![3, 5, 4, 0, 1]), .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0306 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 5, 4, 0, 1]), .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0307 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0308 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2])]

def cycle0309 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 16 1, .triangle 7 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0310 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 5, 0, 4, 2]), .triangle 2 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0311 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0312 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 1 0 (![3, 5, 0, 4, 2]), .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 2, .gapLower 0 4 (![3, 5, 1, 4, 2]), .triangle 2 1]

def cycle0313 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![3, 5, 0, 4, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0314 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 2 (![3, 5, 0, 4, 2]), .triangle 14 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 5, 1, 4, 2]), .triangle 2 1]

def cycle0315 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 17 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 5, 1, 4, 2]), .triangle 2 1]

def cycle0316 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0317 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0318 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .triangle 10 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0319 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .gapLower 0 4 (![3, 5, 1, 4, 2]), .triangle 2 1]

def cycle0320 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 11 2, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0321 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.gapLower 0 4 (![3, 5, 1, 4, 2]), .triangle 5 1, .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0322 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (-2), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0323 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (-1), (-2), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 4 (![3, 5, 1, 4, 2]), .triangle 5 1, .triangle 16 1, .triangle 7 0, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0324 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 5, 0, 4, 2]), .triangle 2 0]

def cycle0325 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 14 1, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 2, .gapLower 0 4 (![3, 5, 1, 4, 2]), .triangle 2 1]

def cycle0326 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .distance 0 2, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 5 0, .triangle 11 0, .gapLower 1 3 (![3, 5, 0, 2, 4])]

def cycle0327 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 14 1, .gapLower 1 0 (![3, 5, 0, 4, 2]), .thetaOrder 0, .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 0 1]

def cycle0328 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![3, 5, 0, 4, 2]), .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 0 1]

def cycle0329 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.gapLower 1 2 (![3, 5, 0, 4, 2]), .triangle 14 1, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 0 1]

def cycle0330 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (0), (0), (-2), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, true, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 6 0, .triangle 18 1, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0331 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (0), (-2), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 6 0, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0332 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (-2), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 6 0, .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0333 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-2), (0), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, true, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0334 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (-1), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 5 0, .triangle 18 0, .corridorLower 4 5, .corridorUpper 1 4, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0335 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 2 3 (![5, 3, 4, 0, 1]), .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2])]

def cycle0336 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 7 0, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2])]

def cycle0337 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 14 1, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 0]

def cycle0338 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.triangle 1 0, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 1, 4, 2]), .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 5 2, .triangle 2 1]

def cycle0339 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 4, 2]), .gapLower 0 1 (![3, 5, 1, 4, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0340 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![3, 5, 1, 4, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0341 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![3, 5, 1, 4, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 5, 1, 4, 2]), .triangle 2 1]

def cycle0342 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![3, 5, 1, 4, 2]), .corridorLower 0 3, .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 0 1]

def cycle0343 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 4, 2]), .triangle 8 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0344 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 4, 2]), .triangle 8 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 5, 1, 4, 2]), .triangle 2 1]

def cycle0345 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 2 (![3, 5, 1, 4, 2]), .corridorLower 0 5, .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 0 1]

def cycle0346 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 5, 1, 4, 2]), .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0347 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 5, 1, 4, 2]), .triangle 5 2, .gapLower 0 3 (![3, 5, 1, 4, 2])]

def cycle0348 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![3, 5, 1, 4, 2]), .gapLower 0 4 (![3, 5, 1, 4, 2]), .triangle 2 1]

def cycle0349 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 0 0]

def cycle0350 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0351 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 1, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0352 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![3, 4, 1, 2, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0353 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 2, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0354 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![3, 4, 1, 2, 5])]

def cycle0355 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 4, 1, 2, 5]), .triangle 0 1]

def cycle0356 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 1, 2, 5]), .triangle 6 1, .triangle 0 1]

def cycle0357 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![3, 4, 1, 2, 5]), .gapLower 0 0 (![3, 4, 1, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0358 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 2, 5]), .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0359 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![3, 4, 1, 2, 5])]

def cycle0360 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 0 (![3, 4, 0, 2, 5]), .gapLower 1 5 (![3, 4, 0, 2, 5]), .triangle 3 2, .gapLower 0 4 (![3, 4, 1, 2, 5]), .triangle 0 1]

def cycle0361 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1 (![3, 4, 0, 2, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 0 0]

def cycle0362 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2 (![3, 4, 0, 2, 5]), .triangle 13 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![3, 4, 1, 2, 5]), .triangle 0 1]

def cycle0363 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .gapLower 1 3 (![3, 4, 0, 2, 5])]

def cycle0364 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![3, 4, 0, 2, 5]), .triangle 0 0]

def cycle0365 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 2, 5]), .triangle 3 2, .gapLower 0 4 (![3, 4, 1, 2, 5]), .triangle 0 1]

def cycle0366 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![3, 4, 1, 2, 5]), .triangle 0 1]

def cycle0367 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 1 1, .triangle 13 0, .triangle 7 0]

def cycle0368 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 0 (![3, 4, 0, 2, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 0 0]

def cycle0369 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2 (![3, 4, 0, 2, 5]), .triangle 13 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 0 0]

def cycle0370 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 2, 5]), .triangle 3 0]

def cycle0371 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 0 (![3, 4, 0, 5, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0372 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1 (![3, 4, 0, 5, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 12 0, .triangle 6 0, .gapLower 0 3 (![3, 4, 1, 2, 5])]

def cycle0373 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2 (![3, 4, 0, 5, 2]), .triangle 13 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0374 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0), (0)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, true] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0375 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 2, 5]), .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 0, 5, 2]), .triangle 3 0]

def cycle0376 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 12 0, .triangle 6 0, .gapLower 0 3 (![3, 4, 1, 2, 5])]

def cycle0377 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 1, 2, 5]), .gapLower 0 5 (![3, 4, 1, 2, 5]), .triangle 3 1]

def cycle0378 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 2, 5]), .gapLower 0 1 (![3, 4, 1, 2, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0379 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![3, 4, 1, 2, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![3, 4, 1, 2, 5])]

def cycle0380 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![3, 4, 1, 2, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 4, 1, 2, 5]), .triangle 0 1]

def cycle0381 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![3, 4, 1, 2, 5]), .corridorLower 0 3, .gapLower 0 5 (![3, 4, 1, 2, 5]), .triangle 3 1]

def cycle0382 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 2, 5]), .triangle 7 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![3, 4, 1, 2, 5])]

def cycle0383 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 2, 5]), .triangle 7 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 4, 1, 2, 5]), .triangle 0 1]

def cycle0384 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 2, 5]), .corridorLower 0 4, .gapLower 0 5 (![3, 4, 1, 2, 5]), .triangle 6 1, .triangle 0 1]

def cycle0385 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 4, 1, 2, 5]), .gapLower 0 3 (![3, 4, 1, 2, 5])]

def cycle0386 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 1, 2, 5]), .triangle 6 1, .gapLower 0 3 (![3, 4, 1, 2, 5])]

def cycle0387 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 1, 2, 5]), .gapLower 0 4 (![3, 4, 1, 2, 5]), .triangle 0 1]

def cycle0388 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 3, .distance 1 2]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 12 0, .triangle 17 1, .triangle 10 0]

def cycle0389 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 0]

def cycle0390 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 7 0]

def cycle0391 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 9 0, .triangle 7 1]

def cycle0392 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 0 (![3, 4, 0, 5, 2]), .gapLower 1 5 (![3, 4, 0, 5, 2]), .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 0 1]

def cycle0393 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 0]

def cycle0394 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (-3), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 18 1, .triangle 9 0, .gapLower 0 1 (![3, 4, 1, 5, 2]), .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0395 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 0]

def cycle0396 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 7 0]

def cycle0397 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1 (![3, 4, 0, 5, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 0 0]

def cycle0398 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 2 (![3, 4, 0, 5, 2]), .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 0]

def cycle0399 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 2 (![3, 4, 0, 5, 2]), .triangle 13 1, .triangle 10 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def cycle0400 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 0 1]

def cycle0401 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![3, 4, 0, 5, 2])]

def cycle0402 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 5, 2]), .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 0, 5, 2]), .triangle 3 0]

def cycle0403 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 0 0]

def cycle0404 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0405 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![3, 4, 1, 5, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0406 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 5, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0407 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0408 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 6 1, .corridorLower 2 5, .corridorUpper 1 2, .triangle 0 2]

def cycle0409 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 1, 5, 2]), .triangle 0 1]

def cycle0410 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![3, 4, 1, 5, 2]), .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0411 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 5, 2]), .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0412 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 0 (![3, 4, 0, 5, 2]), .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0413 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![3, 4, 0, 5, 2]), .gapLower 1 1 (![3, 4, 0, 5, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0414 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![3, 4, 0, 5, 2]), .corridorLower 1 4, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0415 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0416 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0417 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0418 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0419 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 4 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 18 1, .triangle 9 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0420 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0421 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (-2), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 17 1, .triangle 16 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0422 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 3 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 17 1, .triangle 8 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0423 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 0, 5, 2]), .triangle 3 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0424 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0425 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 0 (![3, 4, 0, 5, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 3 1]

def cycle0426 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 2 (![3, 4, 0, 5, 2]), .gapLower 1 1 (![3, 4, 0, 5, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 0 2, .gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 3 1]

def cycle0427 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 2 (![3, 4, 0, 5, 2]), .triangle 13 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 3 1]

def cycle0428 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 6 1, .triangle 17 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0429 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 10 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![3, 4, 0, 5, 2])]

def cycle0430 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (-2), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1])]

def cycle0431 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 12 2, .gapLower 1 3 (![3, 4, 0, 5, 2])]

def cycle0432 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (-1), (0), (-2), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 6 1, .triangle 18 1, .triangle 9 0, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0433 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 8 0]

def cycle0434 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (0), (-1), (-2), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 6 1, .triangle 18 1, .triangle 16 1, .triangle 7 0, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0435 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 0, 5, 2]), .triangle 3 0]

def cycle0436 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 0 2, .gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 3 1]

def cycle0437 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .gapLower 0 5 (![3, 4, 1, 5, 2]), .triangle 6 0, .triangle 12 0, .gapLower 1 3 (![3, 4, 0, 2, 5])]

def cycle0438 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, true, true] }
  origin := ![.triangle 2 0, .triangle 13 1, .gapLower 1 0 (![3, 4, 0, 5, 2]), .thetaOrder 0, .gapLower 0 5 (![3, 4, 1, 5, 2]), .triangle 6 2, .triangle 3 1]

def cycle0439 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 1 (![3, 4, 0, 5, 2]), .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 1, 5, 2]), .triangle 0 1]

def cycle0440 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.gapLower 1 2 (![3, 4, 0, 5, 2]), .triangle 13 1, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 1, 5, 2]), .triangle 0 1]

def cycle0441 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (0), (0), (-2), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, true, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .gapLower 0 5 (![3, 4, 1, 5, 2]), .triangle 6 0, .triangle 18 1, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![3, 4, 0, 5, 2])]

def cycle0442 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (0), (0), (-2), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .gapLower 0 5 (![3, 4, 1, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![3, 4, 0, 5, 2])]

def cycle0443 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (0), (-2), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .gapLower 0 5 (![3, 4, 1, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![3, 4, 0, 5, 2])]

def cycle0444 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-2), (0), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, true, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 4, 1, 5, 2]), .gapLower 0 5 (![3, 4, 1, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![3, 4, 0, 5, 2])]

def cycle0445 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .triangle 9 0, .gapLower 0 1 (![3, 4, 1, 5, 2]), .gapLower 0 0 (![3, 4, 1, 5, 2]), .gapLower 0 5 (![3, 4, 1, 5, 2])]

def cycle0446 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 6 0, .triangle 17 1, .triangle 8 0, .gapLower 0 0 (![3, 4, 1, 5, 2]), .gapLower 0 5 (![3, 4, 1, 5, 2])]

def cycle0447 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (0), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .gapLower 4 3 (![1, 0, 3, 2, 5]), .triangle 7 0, .gapLower 0 0 (![3, 4, 1, 5, 2]), .gapLower 0 5 (![3, 4, 1, 5, 2])]

def cycle0448 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 12 2, .triangle 3 0]

def cycle0449 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 1, 5, 2]), .gapLower 0 5 (![3, 4, 1, 5, 2]), .triangle 6 2, .triangle 3 1]

def cycle0450 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 5, 2]), .gapLower 0 1 (![3, 4, 1, 5, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0451 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![3, 4, 1, 5, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0452 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![3, 4, 1, 5, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 3 1]

def cycle0453 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![3, 4, 1, 5, 2]), .corridorLower 0 3, .gapLower 0 5 (![3, 4, 1, 5, 2]), .triangle 6 2, .triangle 3 1]

def cycle0454 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 5, 2]), .triangle 7 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0455 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 5, 2]), .triangle 7 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 3 1]

def cycle0456 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 2 (![3, 4, 1, 5, 2]), .corridorLower 0 4, .gapLower 0 5 (![3, 4, 1, 5, 2]), .triangle 0 1]

def cycle0457 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 1, 5, 2]), .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0458 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 1, 5, 2]), .triangle 6 2, .gapLower 0 3 (![3, 4, 1, 5, 2])]

def cycle0459 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 1, 5, 2]), .gapLower 0 4 (![3, 4, 1, 5, 2]), .triangle 3 1]

def cycle0460 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, true, true] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0461 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .triangle 16 1, .triangle 10 0, .triangle 0 0]

def cycle0462 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-2), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .triangle 10 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 0]

def cycle0463 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 7 0]

def cycle0464 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 9 0, .triangle 7 1]

def cycle0465 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (4), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .gapLower 1 0 (![3, 4, 5, 0, 2]), .gapLower 1 5 (![3, 4, 5, 0, 2]), .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 0 1]

def cycle0466 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 0]

def cycle0467 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0468 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 2 (![3, 4, 5, 0, 2]), .corridorLower 1 4, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0469 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (-2), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 3 (![3, 4, 5, 0, 2]), .triangle 14 1, .triangle 10 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 0]

def cycle0470 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 3 (![3, 4, 5, 0, 2]), .triangle 14 1, .triangle 10 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def cycle0471 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 0 1]

def cycle0472 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0473 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0474 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![3, 4, 5, 1, 2]), .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0475 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0476 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0477 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 1 (![3, 4, 5, 1, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0478 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![3, 4, 5, 1, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0479 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 5, 1, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0480 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0481 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 0 1]

def cycle0482 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 1 (![3, 4, 5, 1, 2]), .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0483 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![3, 4, 5, 1, 2]), .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0484 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 5, 1, 2]), .triangle 8 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0485 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (4), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .gapLower 1 0 (![3, 4, 5, 0, 2]), .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0486 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![3, 4, 5, 0, 2]), .triangle 15 1, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0487 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![3, 4, 5, 0, 2]), .gapLower 1 2 (![3, 4, 5, 0, 2]), .triangle 13 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0488 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 1 3 (![3, 4, 5, 0, 2]), .corridorLower 1 5, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0489 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0490 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0491 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0), (0), (-2), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, true, true, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0492 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0493 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0494 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .triangle 16 1, .triangle 10 0, .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0495 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .triangle 10 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0496 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (3), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0497 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0498 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0499 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (-2), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .gapLower 1 0 (![3, 4, 5, 0, 2]), .thetaOrder 0, .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 0 1]

def cycle0500 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 0 1]

def cycle0501 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 2 (![3, 4, 5, 0, 2]), .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 0 1]

def cycle0502 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.gapLower 1 3 (![3, 4, 5, 0, 2]), .triangle 15 1, .triangle 13 1, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 0 1]

def cycle0503 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (2), (-1), (0), (0), (-2), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 6 0, .triangle 18 1, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0504 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (2), (-1), (0), (-2), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 6 0, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0505 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (2), (-1), (-2), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 6 0, .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0506 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (2), (-2), (0), (0), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .gapLower 0 5 (![3, 4, 5, 1, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0507 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .gapLower 0 0 (![3, 4, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0508 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 17 0, .triangle 8 0, .gapLower 0 0 (![3, 4, 5, 1, 2]), .gapLower 0 5 (![3, 4, 5, 1, 2])]

def cycle0509 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 16 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 5, 1, 2]), .gapLower 0 5 (![3, 4, 5, 1, 2])]

def cycle0510 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0511 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![3, 4, 5, 1, 2]), .gapLower 0 0 (![3, 4, 5, 1, 2]), .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 0 1]

def cycle0512 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 4, 5, 1, 2]), .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 0 1]

def cycle0513 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 4, 5, 1, 2]), .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 0 1]

def cycle0514 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![3, 4, 5, 1, 2]), .gapLower 0 1 (![3, 4, 5, 1, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0515 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 5, 1, 2]), .triangle 9 1, .gapLower 0 1 (![3, 4, 5, 1, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0516 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 1 (![3, 4, 5, 1, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0517 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 1 (![3, 4, 5, 1, 2]), .corridorLower 0 3, .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 0 1]

def cycle0518 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 4, 5, 1, 2]), .gapLower 0 2 (![3, 4, 5, 1, 2]), .triangle 7 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0519 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![3, 4, 5, 1, 2]), .triangle 7 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0520 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![3, 4, 5, 1, 2]), .corridorLower 0 4, .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 0 1]

def cycle0521 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![3, 4, 5, 1, 2]), .triangle 9 1, .triangle 7 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0522 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 3 (![3, 4, 5, 1, 2]), .corridorLower 0 5, .gapLower 0 5 (![3, 4, 5, 1, 2]), .triangle 0 1]

def cycle0523 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 4, 5, 1, 2]), .gapLower 0 4 (![3, 4, 5, 1, 2])]

def cycle0524 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .gapLower 1 0 (![3, 4, 5, 0, 2]), .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0525 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0526 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![3, 4, 5, 0, 2]), .corridorLower 1 4, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0527 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 16 1, .triangle 10 0, .triangle 0 0]

def cycle0528 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 18 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 0, 2]), .triangle 10 1, .gapLower 2 0 (![3, 5, 4, 0, 1]), .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 0]

def cycle0529 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (-1), (0), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true] }
  origin := ![.gapLower 2 3 (![3, 5, 4, 0, 1]), .triangle 18 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0530 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (-1), (4), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 18 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .gapLower 2 4 (![3, 5, 4, 0, 1])]

def cycle0531 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 5, 4, 1, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 0]

def cycle0532 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 0 (![3, 5, 4, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0533 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0534 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 4, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0535 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 5, 4, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0536 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 1, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0537 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![3, 5, 4, 1, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0538 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 3 (![3, 5, 4, 1, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0539 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 5, 4, 1, 2])]

def cycle0540 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 5, 4, 1, 2]), .triangle 0 1]

def cycle0541 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 1, 2]), .gapLower 0 0 (![3, 5, 4, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0542 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![3, 5, 4, 1, 2]), .triangle 8 1, .gapLower 0 0 (![3, 5, 4, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0543 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 3 (![3, 5, 4, 1, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0544 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 5, 4, 1, 2])]

def cycle0545 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 5, 4, 1, 2]), .triangle 0 1]

def cycle0546 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 14 0, .triangle 8 0, .gapLower 0 0 (![3, 5, 4, 1, 2]), .gapLower 0 5 (![3, 5, 4, 1, 2]), .triangle 0 1]

def cycle0547 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .gapLower 0 0 (![3, 5, 4, 1, 2]), .gapLower 0 5 (![3, 5, 4, 1, 2]), .triangle 0 1]

def cycle0548 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![3, 5, 4, 1, 2]), .gapLower 0 1 (![3, 5, 4, 1, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0549 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 5, 4, 1, 2]), .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 1, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0550 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 1, 2]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 5, 4, 1, 2])]

def cycle0551 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 1 (![3, 5, 4, 1, 2]), .corridorLower 0 3, .gapLower 0 5 (![3, 5, 4, 1, 2]), .triangle 0 1]

def cycle0552 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![3, 5, 4, 1, 2]), .gapLower 0 2 (![3, 5, 4, 1, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0553 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![3, 5, 4, 1, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 5, 4, 1, 2])]

def cycle0554 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![3, 5, 4, 1, 2]), .corridorLower 0 5, .gapLower 0 5 (![3, 5, 4, 1, 2]), .triangle 0 1]

def cycle0555 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.gapLower 0 3 (![3, 5, 4, 1, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![3, 5, 4, 1, 2])]

def cycle0556 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 5, 4, 1, 2]), .gapLower 0 4 (![3, 5, 4, 1, 2])]

def cycle0557 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 2, .triangle 3 0]

def cycle0558 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 0 (![5, 3, 1, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0559 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 0 (![5, 3, 1, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0560 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0561 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![5, 3, 1, 2, 4]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0562 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 1, 2, 4]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0563 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![5, 3, 1, 2, 4])]

def cycle0564 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 3, 1, 2, 4]), .triangle 0 1]

def cycle0565 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![5, 3, 1, 2, 4]), .triangle 2 1]

def cycle0566 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![5, 3, 1, 2, 4]), .gapLower 0 0 (![5, 3, 1, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0567 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 1, 2, 4]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0568 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 0 (![5, 3, 1, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![5, 3, 1, 2, 4])]

def cycle0569 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 3, 1, 2, 4]), .triangle 0 1]

def cycle0570 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 8 0, .triangle 14 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![5, 3, 1, 2, 4]), .triangle 7 1]

def cycle0571 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 1, 2, 4]), .gapLower 0 1 (![5, 3, 1, 2, 4]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0572 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![5, 3, 1, 2, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![5, 3, 1, 2, 4])]

def cycle0573 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![5, 3, 1, 2, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 3, 1, 2, 4]), .triangle 0 1]

def cycle0574 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![5, 3, 1, 2, 4]), .corridorLower 0 5, .gapLower 0 5 (![5, 3, 1, 2, 4]), .triangle 2 1]

def cycle0575 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 1, 2, 4]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaLower 2, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![5, 3, 1, 2, 4])]

def cycle0576 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 3, 1, 2, 4]), .gapLower 0 3 (![5, 3, 1, 2, 4])]

def cycle0577 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![5, 3, 1, 2, 4]), .triangle 5 1, .gapLower 0 3 (![5, 3, 1, 2, 4])]

def cycle0578 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![5, 3, 1, 2, 4]), .gapLower 0 4 (![5, 3, 1, 2, 4]), .triangle 0 1]

def cycle0579 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 0, .gapLower 1 0 (![3, 5, 0, 4, 2]), .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 0]

def cycle0580 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 2, .gapLower 1 1 (![3, 5, 0, 4, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 0]

def cycle0581 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (3), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .triangle 2 0]

def cycle0582 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 4 0]

def cycle0583 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 3 5, .distance 1 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 17 0, .triangle 14 0, .gapLower 3 0 (![1, 5, 2, 0, 4]), .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0584 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 3 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 17 0, .gapLower 3 1 (![1, 5, 2, 0, 4]), .corridorLower 1 3, .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 0]

def cycle0585 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 3 2 (![1, 5, 2, 0, 4]), .triangle 14 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0586 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 2 5, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (4), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 3 3 (![1, 5, 2, 0, 4]), .triangle 17 2, .gapLower 2 0 (![5, 3, 4, 0, 1]), .gapLower 2 5 (![5, 3, 4, 0, 1]), .triangle 11 2, .triangle 2 0]

def cycle0587 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 8 2, .gapLower 0 0 (![5, 3, 1, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![1, 5, 2, 0, 4])]

def cycle0588 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .zero, .theta 3, .distance 3 4, .distance 0 3]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 8 2, .gapLower 0 0 (![5, 3, 1, 4, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![1, 5, 2, 0, 4]), .triangle 7 0]

def cycle0589 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 2 5, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 5 0, .triangle 16 1, .gapLower 2 1 (![5, 3, 4, 0, 1]), .corridorLower 2 5, .corridorUpper 1 2, .triangle 0 2]

def cycle0590 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.triangle 5 0, .gapLower 2 2 (![5, 3, 4, 0, 1]), .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0591 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (-1), (0), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 2 3 (![5, 3, 4, 0, 1]), .triangle 16 1, .triangle 17 0, .triangle 14 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0592 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 0 (![5, 3, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 3, 4, 0, 1]), .triangle 0 0]

def cycle0593 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 5, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 7 0, .triangle 8 2, .gapLower 0 0 (![5, 3, 1, 4, 2]), .gapLower 0 5 (![5, 3, 1, 4, 2])]

def cycle0594 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 0 (![5, 3, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 5, 0, 4, 2])]

def cycle0595 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 3, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 5, 0, 4, 2]), .triangle 2 0]

def cycle0596 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .gapLower 1 5 (![3, 5, 0, 4, 2]), .triangle 0 0]

def cycle0597 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![5, 3, 1, 4, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0598 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 1, 4, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0599 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![5, 3, 1, 4, 2])]

def cycle0600 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 3, 1, 4, 2]), .triangle 2 1]

def cycle0601 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, true, false, true] }
  origin := ![.triangle 1 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 1, 4, 2]), .triangle 0 1]

def cycle0602 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![5, 3, 1, 4, 2]), .gapLower 0 0 (![5, 3, 1, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0603 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 1, 4, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0604 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![5, 3, 1, 4, 2])]

def cycle0605 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 3, 1, 4, 2]), .triangle 2 1]

def cycle0606 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![5, 3, 1, 4, 2]), .triangle 0 1]

def cycle0607 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 3, 1, 4, 2]), .gapLower 0 1 (![5, 3, 1, 4, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0608 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![5, 3, 1, 4, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![5, 3, 1, 4, 2])]

def cycle0609 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.gapLower 0 4 (![5, 3, 1, 4, 2]), .triangle 7 1, .gapLower 0 1 (![5, 3, 1, 4, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0610 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![5, 3, 1, 4, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0611 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 2 (![5, 3, 1, 4, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![5, 3, 1, 4, 2])]

def cycle0612 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 2 (![5, 3, 1, 4, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 3, 1, 4, 2]), .triangle 2 1]

def cycle0613 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 3, 1, 4, 2]), .gapLower 0 3 (![5, 3, 1, 4, 2])]

def cycle0614 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![5, 3, 1, 4, 2]), .triangle 5 2, .gapLower 0 3 (![5, 3, 1, 4, 2])]

def cycle0615 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![5, 3, 1, 4, 2]), .gapLower 0 4 (![5, 3, 1, 4, 2]), .triangle 2 1]

def cycle0616 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .triangle 14 2, .triangle 3 0]

def cycle0617 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .triangle 14 0, .gapLower 1 0 (![3, 4, 5, 0, 2]), .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0618 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0619 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .triangle 14 2, .gapLower 1 2 (![3, 4, 5, 0, 2]), .corridorLower 1 4, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0620 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def cycle0621 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .triangle 17 0, .triangle 14 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0622 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 1 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-2), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 16 1, .triangle 17 0, .triangle 14 0, .gapLower 3 0 (![1, 5, 2, 0, 4]), .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0623 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 16 1, .triangle 17 0, .gapLower 3 1 (![1, 5, 2, 0, 4]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0624 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 16 1, .gapLower 3 2 (![1, 5, 2, 0, 4]), .triangle 14 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0625 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 2 3, .distance 2 5, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 3 3 (![1, 5, 2, 0, 4]), .triangle 17 2, .gapLower 2 0 (![5, 3, 4, 0, 1]), .gapLower 2 5 (![5, 3, 4, 0, 1]), .triangle 0 0]

def cycle0626 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 8 2, .gapLower 0 0 (![5, 3, 4, 1, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![1, 5, 2, 0, 4])]

def cycle0627 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .zero, .theta 3, .distance 3 4, .distance 0 3]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 8 2, .gapLower 0 0 (![5, 3, 4, 1, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![1, 5, 2, 0, 4]), .triangle 7 0]

def cycle0628 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 2, .gapLower 0 0 (![5, 3, 4, 1, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 3, 4, 0, 1]), .triangle 0 0]

def cycle0629 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 2, .gapLower 0 0 (![5, 3, 4, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0630 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0631 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 13 1, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0632 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .triangle 8 2, .gapLower 0 0 (![5, 3, 4, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0633 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 1 (![5, 3, 4, 1, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0634 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![5, 3, 4, 1, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0635 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![5, 3, 4, 1, 2]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0636 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 3, 4, 1, 2])]

def cycle0637 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, true, false, true] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 3, 4, 1, 2]), .triangle 0 1]

def cycle0638 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 1 (![5, 3, 4, 1, 2]), .gapLower 0 0 (![5, 3, 4, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0639 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![5, 3, 4, 1, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0640 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![5, 3, 4, 1, 2]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0641 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 3, 4, 1, 2])]

def cycle0642 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 8 0, .triangle 14 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![5, 3, 4, 1, 2]), .triangle 0 1]

def cycle0643 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .triangle 13 0, .triangle 7 0, .triangle 8 2, .gapLower 0 0 (![5, 3, 4, 1, 2]), .gapLower 0 5 (![5, 3, 4, 1, 2]), .triangle 0 1]

def cycle0644 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![5, 3, 4, 1, 2]), .gapLower 0 1 (![5, 3, 4, 1, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0645 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 0 3 (![5, 3, 4, 1, 2]), .triangle 7 1, .gapLower 0 1 (![5, 3, 4, 1, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0646 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 1 (![5, 3, 4, 1, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 3, 4, 1, 2])]

def cycle0647 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 7 1, .gapLower 0 1 (![5, 3, 4, 1, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0648 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![5, 3, 4, 1, 2]), .gapLower 0 2 (![5, 3, 4, 1, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0649 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 2 (![5, 3, 4, 1, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 3, 4, 1, 2])]

def cycle0650 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3 (![5, 3, 4, 1, 2]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 3, 4, 1, 2])]

def cycle0651 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![5, 3, 4, 1, 2]), .gapLower 0 4 (![5, 3, 4, 1, 2])]

def cycle0652 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 2, .triangle 2 0]

def cycle0653 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 0 (![4, 3, 1, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 0 0]

def cycle0654 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 0 (![4, 3, 1, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0655 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 13 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0656 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![4, 3, 1, 2, 5]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0657 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 1, 2, 5]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0658 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![4, 3, 1, 2, 5])]

def cycle0659 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 3, 1, 2, 5]), .triangle 0 1]

def cycle0660 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![4, 3, 1, 2, 5]), .triangle 3 1]

def cycle0661 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![4, 3, 1, 2, 5]), .gapLower 0 0 (![4, 3, 1, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0662 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 1, 2, 5]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0663 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 0 (![4, 3, 1, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![4, 3, 1, 2, 5])]

def cycle0664 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 3, 1, 2, 5]), .triangle 0 1]

def cycle0665 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, true, true] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![4, 3, 1, 2, 5]), .triangle 6 1, .triangle 0 1]

def cycle0666 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 1, 2, 5]), .gapLower 0 1 (![4, 3, 1, 2, 5]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0667 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![4, 3, 1, 2, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![4, 3, 1, 2, 5])]

def cycle0668 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![4, 3, 1, 2, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 3, 1, 2, 5]), .triangle 0 1]

def cycle0669 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![4, 3, 1, 2, 5]), .corridorLower 0 4, .gapLower 0 5 (![4, 3, 1, 2, 5]), .triangle 3 1]

def cycle0670 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 1, 2, 5]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaLower 2, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![4, 3, 1, 2, 5])]

def cycle0671 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 3, 1, 2, 5]), .gapLower 0 3 (![4, 3, 1, 2, 5])]

def cycle0672 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![4, 3, 1, 2, 5]), .triangle 6 1, .gapLower 0 3 (![4, 3, 1, 2, 5])]

def cycle0673 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![4, 3, 1, 2, 5]), .gapLower 0 4 (![4, 3, 1, 2, 5]), .triangle 0 1]

def cycle0674 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 4, 0, 5, 2]), .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 0 0]

def cycle0675 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 2, .gapLower 1 1 (![3, 4, 0, 5, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 0 0]

def cycle0676 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (3), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 12 2, .triangle 3 0]

def cycle0677 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 6 0, .triangle 17 1, .triangle 4 0]

def cycle0678 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 3 4, .distance 1 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 16 0, .triangle 13 0, .gapLower 3 0 (![1, 4, 2, 0, 5]), .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0679 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 16 0, .gapLower 3 1 (![1, 4, 2, 0, 5]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 0 0]

def cycle0680 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 3 2 (![1, 4, 2, 0, 5]), .triangle 13 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0681 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (4), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 3 3 (![1, 4, 2, 0, 5]), .triangle 16 2, .gapLower 2 0 (![4, 3, 5, 0, 1]), .gapLower 2 5 (![4, 3, 5, 0, 1]), .triangle 12 2, .triangle 3 0]

def cycle0682 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 7 2, .gapLower 0 0 (![4, 3, 1, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .gapLower 3 4 (![1, 4, 2, 0, 5])]

def cycle0683 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .theta 0, .zero, .theta 3, .distance 3 5, .distance 0 3]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 7 2, .gapLower 0 0 (![4, 3, 1, 5, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![1, 4, 2, 0, 5]), .triangle 8 0]

def cycle0684 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 17 1, .gapLower 2 1 (![4, 3, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def cycle0685 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.triangle 6 0, .gapLower 2 2 (![4, 3, 5, 0, 1]), .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0686 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (-1), (0), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 2 3 (![4, 3, 5, 0, 1]), .triangle 17 1, .triangle 16 0, .triangle 13 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0687 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 17 1, .triangle 16 0, .triangle 13 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 3, 5, 0, 1])]

def cycle0688 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 0 (![4, 3, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 3, 5, 0, 1]), .triangle 0 0]

def cycle0689 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (-3), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 17 1, .triangle 8 0, .gapLower 0 1 (![4, 3, 1, 5, 2]), .gapLower 0 0 (![4, 3, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0690 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .triangle 9 0, .gapLower 0 0 (![4, 3, 1, 5, 2]), .gapLower 0 5 (![4, 3, 1, 5, 2])]

def cycle0691 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 0 (![4, 3, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![3, 4, 0, 5, 2])]

def cycle0692 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 1, 5, 2]), .triangle 7 2, .gapLower 0 0 (![4, 3, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 0, 5, 2]), .triangle 3 0]

def cycle0693 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 0, 5, 2]), .triangle 0 0]

def cycle0694 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![4, 3, 1, 5, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0695 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 1, 5, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0696 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![4, 3, 1, 5, 2])]

def cycle0697 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![4, 3, 1, 5, 2]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0698 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, true, false, true] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 1, 5, 2]), .triangle 0 1]

def cycle0699 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![4, 3, 1, 5, 2]), .gapLower 0 0 (![4, 3, 1, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0700 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 1, 5, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0701 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![4, 3, 1, 5, 2])]

def cycle0702 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![4, 3, 1, 5, 2]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0703 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![4, 3, 1, 5, 2]), .triangle 0 1]

def cycle0704 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 0 2 (![4, 3, 1, 5, 2]), .gapLower 0 1 (![4, 3, 1, 5, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0705 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![4, 3, 1, 5, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![4, 3, 1, 5, 2])]

def cycle0706 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.gapLower 0 4 (![4, 3, 1, 5, 2]), .triangle 8 1, .gapLower 0 1 (![4, 3, 1, 5, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0707 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1 (![4, 3, 1, 5, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0708 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 2 (![4, 3, 1, 5, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![4, 3, 1, 5, 2])]

def cycle0709 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 2 (![4, 3, 1, 5, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 3, 1, 5, 2]), .triangle 3 1]

def cycle0710 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 3, 1, 5, 2]), .gapLower 0 3 (![4, 3, 1, 5, 2])]

def cycle0711 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![4, 3, 1, 5, 2]), .triangle 6 2, .gapLower 0 3 (![4, 3, 1, 5, 2])]

def cycle0712 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![4, 3, 1, 5, 2]), .gapLower 0 4 (![4, 3, 1, 5, 2]), .triangle 3 1]

def cycle0713 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 4, 5, 0, 2]), .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0714 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .triangle 13 2, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0715 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 16 0, .triangle 13 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0716 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-2), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 17 1, .triangle 16 0, .triangle 13 0, .gapLower 3 0 (![1, 4, 2, 0, 5]), .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0717 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 17 1, .triangle 16 0, .gapLower 3 1 (![1, 4, 2, 0, 5]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0718 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 17 1, .gapLower 3 2 (![1, 4, 2, 0, 5]), .triangle 13 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0719 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 3 3 (![1, 4, 2, 0, 5]), .triangle 16 2, .gapLower 2 0 (![4, 3, 5, 0, 1]), .gapLower 2 5 (![4, 3, 5, 0, 1]), .triangle 0 0]

def cycle0720 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 7 2, .gapLower 0 0 (![4, 3, 5, 1, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .gapLower 3 4 (![1, 4, 2, 0, 5])]

def cycle0721 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .theta 0, .zero, .theta 3, .distance 3 5, .distance 0 3]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 7 2, .gapLower 0 0 (![4, 3, 5, 1, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![1, 4, 2, 0, 5]), .triangle 8 0]

def cycle0722 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 2, .gapLower 0 0 (![4, 3, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 3, 5, 0, 1]), .triangle 0 0]

def cycle0723 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 3]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.gapLower 3 3 (![1, 4, 2, 0, 5]), .triangle 16 2, .triangle 18 0, .triangle 9 2, .gapLower 0 2 (![4, 3, 5, 1, 2])]

def cycle0724 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 2, .gapLower 0 0 (![4, 3, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0725 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0726 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.triangle 7 0, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 2 (![4, 3, 5, 1, 2])]

def cycle0727 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 13 0, .triangle 14 0, .triangle 8 0]

def cycle0728 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 1 (![4, 3, 5, 1, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0729 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![4, 3, 5, 1, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0730 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 5, 1, 2]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0731 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 3, 5, 1, 2])]

def cycle0732 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, true, false, true] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 3, 5, 1, 2]), .triangle 0 1]

def cycle0733 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 1 (![4, 3, 5, 1, 2]), .gapLower 0 0 (![4, 3, 5, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0734 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![4, 3, 5, 1, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0735 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 5, 1, 2]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0736 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 3, 5, 1, 2])]

def cycle0737 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![4, 3, 5, 1, 2]), .triangle 0 1]

def cycle0738 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![4, 3, 5, 1, 2]), .gapLower 0 1 (![4, 3, 5, 1, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0739 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 5, 1, 2]), .triangle 8 1, .gapLower 0 1 (![4, 3, 5, 1, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0740 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 1 (![4, 3, 5, 1, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 3, 5, 1, 2])]

def cycle0741 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .gapLower 0 1 (![4, 3, 5, 1, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0742 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![4, 3, 5, 1, 2]), .gapLower 0 2 (![4, 3, 5, 1, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0743 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 2 (![4, 3, 5, 1, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 3, 5, 1, 2])]

def cycle0744 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 3, 5, 1, 2]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 3, 5, 1, 2])]

def cycle0745 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![4, 3, 5, 1, 2]), .gapLower 0 4 (![4, 3, 5, 1, 2])]

def cycle0746 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .gapLower 1 0 (![3, 4, 5, 0, 2]), .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0747 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0748 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 14 2, .gapLower 1 2 (![3, 4, 5, 0, 2]), .corridorLower 1 4, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0749 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def cycle0750 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 8 0, .triangle 17 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0751 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1), (-2), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 17 0, .triangle 19 1, .triangle 13 0, .gapLower 3 0 (![1, 4, 5, 2, 0]), .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0752 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 17 0, .triangle 19 1, .gapLower 3 1 (![1, 4, 5, 2, 0]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0753 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-2), (-1), (0), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 17 0, .gapLower 3 2 (![1, 4, 5, 2, 0]), .triangle 13 0, .gapLower 1 0 (![3, 4, 5, 0, 2]), .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0754 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 3 3 (![1, 4, 5, 2, 0]), .triangle 14 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0755 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 4 (![1, 4, 5, 2, 0]), .triangle 17 2, .triangle 18 1, .gapLower 2 0 (![4, 5, 3, 0, 1]), .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 0]

def cycle0756 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 4 0, .triangle 17 2, .triangle 6 0]

def cycle0757 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 3 (![3, 4, 5, 0, 2]), .gapLower 5 0 (![1, 3, 2, 0, 4]), .thetaOrder 4, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0758 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 3, .distance 0 3]
    constant := ![(0), (-1), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 4 1, .triangle 17 0, .gapLower 5 1 (![1, 3, 2, 0, 4]), .triangle 14 1, .gapLower 3 0 (![1, 4, 5, 2, 0]), .gapLower 3 5 (![1, 4, 5, 2, 0])]

def cycle0759 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 2 5, .distance 3 5, .theta 3, .distance 0 3]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 4 1, .triangle 17 2, .gapLower 5 2 (![1, 3, 2, 0, 4]), .corridorLower 3 5, .gapLower 3 5 (![1, 4, 5, 2, 0])]

def cycle0760 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 5 3 (![1, 3, 2, 0, 4]), .triangle 18 1, .gapLower 2 0 (![4, 5, 3, 0, 1]), .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 0]

def cycle0761 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![(-3), (0), (0), (3), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![4, 5, 3, 1, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .gapLower 5 4 (![1, 3, 2, 0, 4]), .triangle 9 1]

def cycle0762 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![4, 5, 3, 1, 2]), .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![1, 3, 2, 0, 4]), .triangle 9 0]

def cycle0763 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 3 (![4, 5, 3, 0, 1]), .gapLower 3 3 (![1, 5, 4, 2, 0]), .triangle 19 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 3, 1, 2]), .gapLower 0 5 (![4, 5, 3, 1, 2])]

def cycle0764 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 17 2, .gapLower 2 1 (![4, 5, 3, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def cycle0765 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 2 5, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 2 2 (![4, 5, 3, 0, 1]), .corridorLower 2 5, .corridorUpper 1 2, .triangle 0 0]

def cycle0766 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (-1), (0), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 2 3 (![4, 5, 3, 0, 1]), .triangle 16 0, .triangle 13 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0767 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 3, 1, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 0]

def cycle0768 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 2 3 (![5, 4, 3, 0, 1]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 3, 1, 2]), .gapLower 0 5 (![4, 5, 3, 1, 2])]

def cycle0769 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 3, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0770 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0771 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (0), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 3, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0772 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .triangle 14 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0773 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 1, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0774 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![4, 5, 3, 1, 2]), .triangle 9 1, .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0775 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![4, 5, 3, 1, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0776 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 5, 3, 1, 2])]

def cycle0777 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, true, false, true] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 5, 3, 1, 2]), .triangle 0 1]

def cycle0778 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 1, 2]), .gapLower 0 0 (![4, 5, 3, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0779 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![4, 5, 3, 1, 2]), .triangle 9 1, .gapLower 0 0 (![4, 5, 3, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0780 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![4, 5, 3, 1, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0781 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 5, 3, 1, 2])]

def cycle0782 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![4, 5, 3, 1, 2]), .triangle 0 1]

def cycle0783 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![4, 5, 3, 1, 2]), .gapLower 0 1 (![4, 5, 3, 1, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0784 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 0 3 (![4, 5, 3, 1, 2]), .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 1, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0785 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 1, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 5, 3, 1, 2])]

def cycle0786 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 8 2, .gapLower 0 1 (![4, 5, 3, 1, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0787 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 0 3 (![4, 5, 3, 1, 2]), .gapLower 0 2 (![4, 5, 3, 1, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0788 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![4, 5, 3, 1, 2]), .triangle 9 1, .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0789 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3 (![4, 5, 3, 1, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 5, 3, 1, 2])]

def cycle0790 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![4, 5, 3, 1, 2]), .gapLower 0 4 (![4, 5, 3, 1, 2])]

def cycle0791 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .triangle 3 0]

def cycle0792 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 0, 2]), .gapLower 1 0 (![3, 4, 5, 0, 2]), .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0793 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0794 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 2, .gapLower 1 2 (![3, 4, 5, 0, 2]), .corridorLower 1 4, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0795 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 18 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def cycle0796 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 16 2, .triangle 18 0, .triangle 19 0, .triangle 13 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0797 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 16 0, .triangle 19 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0798 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (0), (-1), (0), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, true, false, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 16 2, .gapLower 2 1 (![5, 4, 3, 0, 1]), .triangle 18 1, .triangle 15 0, .triangle 13 1, .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0799 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 4 1, .gapLower 2 2 (![5, 4, 3, 0, 1]), .triangle 18 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0800 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (-1), (0), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 2 3 (![5, 4, 3, 0, 1]), .triangle 16 2, .triangle 18 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0801 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 3, 1, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 4, 3, 0, 1]), .triangle 0 0]

def cycle0802 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-3), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 3, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 4, 5, 0, 2])]

def cycle0803 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .triangle 15 0, .gapLower 1 1 (![3, 4, 5, 0, 2]), .corridorLower 1 3, .gapLower 1 5 (![3, 4, 5, 0, 2]), .triangle 0 0]

def cycle0804 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 2, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0805 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, true, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 1, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0806 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![5, 4, 3, 1, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0807 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 0 3 (![5, 4, 3, 1, 2]), .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0808 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, true, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 4, 3, 1, 2])]

def cycle0809 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, true, false, true] }
  origin := ![.triangle 1 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![5, 4, 3, 1, 2]), .triangle 0 1]

def cycle0810 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 1, 2]), .gapLower 0 0 (![5, 4, 3, 1, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0811 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![5, 4, 3, 1, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0812 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 0 3 (![5, 4, 3, 1, 2]), .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0813 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, true, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 4, 3, 1, 2])]

def cycle0814 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 7 0, .triangle 13 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![5, 4, 3, 1, 2]), .triangle 0 1]

def cycle0815 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![5, 4, 3, 1, 2]), .gapLower 0 1 (![5, 4, 3, 1, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0816 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![5, 4, 3, 1, 2]), .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 1, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0817 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, true, true, false, true, false] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 1, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 4, 3, 1, 2])]

def cycle0818 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 1 2, .triangle 7 2, .gapLower 0 1 (![5, 4, 3, 1, 2]), .corridorLower 0 5, .gapLower 0 5 (![5, 4, 3, 1, 2]), .triangle 0 1]

def cycle0819 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 3 (![5, 4, 3, 1, 2]), .gapLower 0 2 (![5, 4, 3, 1, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0820 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, true, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2 (![5, 4, 3, 1, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 4, 3, 1, 2])]

def cycle0821 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3 (![5, 4, 3, 1, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 4, 3, 1, 2])]

def cycle0822 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![5, 4, 3, 1, 2]), .gapLower 0 4 (![5, 4, 3, 1, 2])]

def cycle0823 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0824 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0825 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 4, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0826 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![2, 1, 3, 4, 5])]

def cycle0827 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![2, 1, 3, 4, 5])]

def cycle0828 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 1, 3, 4, 5]), .triangle 2 1]

def cycle0829 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 3, 4, 5]), .triangle 9 1, .triangle 7 1, .triangle 1 1]

def cycle0830 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 4, 5]), .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0831 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![2, 1, 3, 4, 5])]

def cycle0832 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![2, 1, 3, 4, 5]), .triangle 4 1]

def cycle0833 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 3, 4, 5]), .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 2, .triangle 3 2, .gapLower 0 4 (![2, 1, 3, 4, 5]), .triangle 7 1, .triangle 1 1]

def cycle0834 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 1 (![2, 0, 3, 4, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 2, .triangle 3 2, .gapLower 0 4 (![2, 1, 3, 4, 5]), .triangle 7 1, .triangle 1 1]

def cycle0835 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![2, 0, 3, 4, 5])]

def cycle0836 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 4, 5]), .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 3 (![2, 0, 3, 4, 5]), .triangle 1 0]

def cycle0837 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 2, .gapLower 1 4 (![2, 0, 3, 4, 5]), .triangle 13 1, .triangle 1 0]

def cycle0838 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 3, 4, 5]), .triangle 3 2, .gapLower 0 4 (![2, 1, 3, 4, 5]), .triangle 2 1]

def cycle0839 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![2, 1, 3, 4, 5]), .triangle 7 1, .triangle 1 1]

def cycle0840 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![2, 1, 3, 4, 5]), .triangle 7 1, .triangle 1 1]

def cycle0841 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0842 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![2, 1, 3, 4, 5]), .triangle 7 1, .triangle 1 1]

def cycle0843 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![2, 1, 3, 4, 5]), .triangle 7 1, .triangle 1 1]

def cycle0844 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 3, 4, 5]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0845 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![2, 0, 3, 4, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0846 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 3, 4, 5]), .triangle 15 1, .triangle 13 1, .triangle 1 0]

def cycle0847 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 3, 5, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0848 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![2, 0, 3, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0849 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![2, 0, 3, 5, 4])]

def cycle0850 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .triangle 15 2, .gapLower 1 3 (![2, 0, 3, 5, 4]), .triangle 1 0]

def cycle0851 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .gapLower 1 4 (![2, 0, 3, 5, 4]), .triangle 14 1, .triangle 1 0]

def cycle0852 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 3, 5, 4]), .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![2, 1, 3, 4, 5]), .triangle 1 1]

def cycle0853 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0854 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 4, 5, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0855 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1 (![2, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0856 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![2, 0, 4, 5, 3])]

def cycle0857 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 2, .gapLower 1 3 (![2, 0, 4, 5, 3]), .triangle 13 1, .triangle 7 0, .triangle 1 1]

def cycle0858 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 0, 4, 5, 3]), .triangle 15 1, .triangle 13 1, .triangle 7 0, .triangle 1 1]

def cycle0859 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 4, 5, 3]), .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![2, 1, 3, 4, 5])]

def cycle0860 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 5, 4, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![2, 1, 3, 4, 5]), .triangle 1 1]

def cycle0861 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 1 (![2, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![2, 1, 3, 4, 5]), .triangle 1 1]

def cycle0862 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 16 0, .triangle 4 0]

def cycle0863 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 18 0, .triangle 5 0]

def cycle0864 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 0 (![1, 0, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![2, 0, 5, 4, 3])]

def cycle0865 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 1 (![1, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![2, 0, 5, 4, 3])]

def cycle0866 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 19 0, .triangle 7 0, .triangle 1 1]

def cycle0867 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 19 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0868 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0869 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 18 0, .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0870 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0871 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 0, 5, 4, 3]), .triangle 15 1, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0872 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 4, 5]), .gapLower 0 0 (![2, 1, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 0, 5, 4, 3]), .triangle 2 0]

def cycle0873 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 5, 4, 3]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![2, 1, 3, 4, 5]), .gapLower 0 2 (![2, 1, 3, 4, 5])]

def cycle0874 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 4, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![2, 1, 3, 4, 5])]

def cycle0875 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 4, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![2, 1, 3, 4, 5]), .triangle 1 1]

def cycle0876 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 4, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 1, 3, 4, 5]), .triangle 7 1, .triangle 1 1]

def cycle0877 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 4, 5]), .corridorLower 0 2, .gapLower 0 5 (![2, 1, 3, 4, 5]), .triangle 9 1, .triangle 7 1, .triangle 1 1]

def cycle0878 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![2, 1, 3, 4, 5]), .gapLower 0 2 (![2, 1, 3, 4, 5])]

def cycle0879 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 1, 3, 4, 5]), .triangle 7 1, .gapLower 0 2 (![2, 1, 3, 4, 5])]

def cycle0880 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 3, 4, 5]), .triangle 9 1, .triangle 7 1, .gapLower 0 2 (![2, 1, 3, 4, 5])]

def cycle0881 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 1, 3, 4, 5]), .gapLower 0 3 (![2, 1, 3, 4, 5]), .triangle 1 1]

def cycle0882 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 3, 4, 5]), .triangle 9 1, .gapLower 0 3 (![2, 1, 3, 4, 5]), .triangle 1 1]

def cycle0883 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 3, 4, 5]), .gapLower 0 4 (![2, 1, 3, 4, 5]), .triangle 2 1]

def cycle0884 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0885 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0886 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 5, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0887 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![2, 1, 3, 5, 4])]

def cycle0888 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 1, 3, 5, 4]), .triangle 1 1]

def cycle0889 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .distance 1 4, .distance 0 4]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![2, 1, 3, 5, 4]), .triangle 9 1, .corridorLower 4 5, .corridorUpper 1 4, .triangle 2 2]

def cycle0890 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4]
    constant := ![(-1), (-1), (0), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 1, 3, 5, 4])]

def cycle0891 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 5, 4]), .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0892 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![2, 1, 3, 5, 4])]

def cycle0893 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 3, 5, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 1, 3, 5, 4]), .triangle 1 1]

def cycle0894 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1 (![2, 0, 3, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 1, 3, 5, 4]), .triangle 1 1]

def cycle0895 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![2, 0, 3, 5, 4])]

def cycle0896 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .triangle 15 2, .gapLower 1 3 (![2, 0, 3, 5, 4]), .triangle 1 0]

def cycle0897 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .gapLower 1 4 (![2, 0, 3, 5, 4]), .triangle 3 2, .gapLower 0 3 (![2, 1, 3, 5, 4]), .triangle 1 1]

def cycle0898 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 3, 5, 4]), .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 1, 3, 5, 4]), .triangle 1 1]

def cycle0899 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 2, .gapLower 0 3 (![2, 1, 3, 5, 4]), .triangle 1 1]

def cycle0900 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 2, .triangle 9 2, .gapLower 0 3 (![2, 1, 3, 5, 4]), .triangle 1 1]

def cycle0901 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 3, 5, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .triangle 2 2, .gapLower 0 4 (![2, 1, 3, 5, 4]), .triangle 8 1, .triangle 1 1]

def cycle0902 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 1 (![2, 0, 3, 5, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .triangle 2 2, .gapLower 0 4 (![2, 1, 3, 5, 4]), .triangle 8 1, .triangle 1 1]

def cycle0903 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .gapLower 1 4 (![2, 0, 3, 5, 4]), .triangle 14 1, .triangle 1 0]

def cycle0904 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 3, 5, 4]), .triangle 2 2, .gapLower 0 4 (![2, 1, 3, 5, 4]), .triangle 3 1]

def cycle0905 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0906 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![2, 1, 3, 5, 4]), .triangle 8 1, .triangle 1 1]

def cycle0907 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 3, 5, 4]), .triangle 13 1, .triangle 1 0]

def cycle0908 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 5, 4, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0909 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1 (![2, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0910 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 16 0, .triangle 4 0]

def cycle0911 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 4, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 5, 4]), .gapLower 0 5 (![2, 1, 3, 5, 4]), .triangle 9 0, .triangle 18 0, .triangle 5 0]

def cycle0912 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 19 2, .gapLower 3 1 (![0, 5, 4, 1, 2]), .triangle 4 1]

def cycle0913 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .gapLower 3 2 (![0, 5, 4, 1, 2]), .triangle 8 0, .gapLower 0 2 (![2, 1, 3, 5, 4])]

def cycle0914 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![0, 5, 4, 1, 2]), .triangle 7 0, .triangle 1 1]

def cycle0915 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![0, 5, 4, 1, 2]), .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![2, 0, 5, 4, 3])]

def cycle0916 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 5, 4, 1, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![1, 0, 5, 4, 3])]

def cycle0917 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 16 0, .triangle 19 2, .triangle 8 0, .gapLower 0 2 (![2, 1, 3, 5, 4])]

def cycle0918 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0919 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 5 0]

def cycle0920 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 0, .triangle 7 0, .triangle 1 1]

def cycle0921 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 0, 5, 4, 3]), .triangle 3 0]

def cycle0922 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 0, 5, 4, 3]), .triangle 13 1, .triangle 7 0, .triangle 1 1]

def cycle0923 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 5, 4, 3]), .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![2, 1, 3, 5, 4])]

def cycle0924 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 5, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![2, 1, 3, 5, 4])]

def cycle0925 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 5, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 1, 3, 5, 4]), .triangle 1 1]

def cycle0926 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 5, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 1, 3, 5, 4]), .triangle 8 1, .triangle 1 1]

def cycle0927 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 1 (![2, 1, 3, 5, 4]), .corridorLower 0 2, .gapLower 0 5 (![2, 1, 3, 5, 4]), .triangle 7 1, .triangle 1 1]

def cycle0928 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![2, 1, 3, 5, 4]), .gapLower 0 2 (![2, 1, 3, 5, 4])]

def cycle0929 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 1, 3, 5, 4]), .triangle 8 1, .gapLower 0 2 (![2, 1, 3, 5, 4])]

def cycle0930 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 3, 5, 4]), .triangle 7 1, .gapLower 0 2 (![2, 1, 3, 5, 4])]

def cycle0931 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 1, 3, 5, 4]), .gapLower 0 3 (![2, 1, 3, 5, 4]), .triangle 1 1]

def cycle0932 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 3, 5, 4]), .triangle 9 2, .gapLower 0 3 (![2, 1, 3, 5, 4]), .triangle 1 1]

def cycle0933 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 3, 5, 4]), .gapLower 0 4 (![2, 1, 3, 5, 4]), .triangle 3 1]

def cycle0934 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0935 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .triangle 8 2, .triangle 3 1]

def cycle0936 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 3, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 2 (![2, 1, 5, 3, 4])]

def cycle0937 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 2 (![2, 1, 5, 3, 4])]

def cycle0938 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 1, 5, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0939 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 1, 5, 3, 4])]

def cycle0940 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, true] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 1, 5, 3, 4]), .triangle 7 1]

def cycle0941 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 3, 4]), .gapLower 0 0 (![2, 1, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 2 (![2, 1, 5, 3, 4])]

def cycle0942 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 2 (![2, 1, 5, 3, 4])]

def cycle0943 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 1, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![2, 1, 5, 3, 4]), .triangle 6 1]

def cycle0944 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 5, 3, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .triangle 2 2, .gapLower 0 4 (![2, 1, 5, 3, 4]), .triangle 1 1]

def cycle0945 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![2, 0, 5, 3, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .triangle 2 2, .gapLower 0 4 (![2, 1, 5, 3, 4]), .triangle 1 1]

def cycle0946 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 2, .gapLower 1 2 (![2, 0, 5, 3, 4])]

def cycle0947 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 3, 4]), .gapLower 0 0 (![2, 1, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 3 (![2, 0, 5, 3, 4]), .triangle 3 0]

def cycle0948 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 2, .gapLower 1 4 (![2, 0, 5, 3, 4]), .triangle 1 0]

def cycle0949 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![2, 0, 5, 3, 4]), .triangle 2 2, .gapLower 0 4 (![2, 1, 5, 3, 4])]

def cycle0950 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .corridorUpper 1 3, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![2, 1, 5, 3, 4])]

def cycle0951 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 5, 3, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 2, .triangle 3 0]

def cycle0952 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1 (![2, 0, 5, 3, 4]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 2, .triangle 3 0]

def cycle0953 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 5, 3, 4]), .triangle 2 0]

def cycle0954 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0]

def cycle0955 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 3, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 2 (![2, 1, 5, 3, 4])]

def cycle0956 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 3, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![2, 1, 5, 3, 4]), .triangle 3 1]

def cycle0957 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 3, 4]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 1, 5, 3, 4]), .triangle 1 1]

def cycle0958 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![2, 1, 5, 3, 4]), .corridorLower 0 2, .gapLower 0 5 (![2, 1, 5, 3, 4]), .triangle 7 1, .triangle 8 2, .gapLower 0 2 (![2, 1, 5, 3, 4])]

def cycle0959 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![2, 1, 5, 3, 4]), .gapLower 0 2 (![2, 1, 5, 3, 4])]

def cycle0960 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 1, 5, 3, 4]), .triangle 8 2, .gapLower 0 2 (![2, 1, 5, 3, 4])]

def cycle0961 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 5, 3, 4]), .triangle 7 1, .triangle 8 2, .gapLower 0 2 (![2, 1, 5, 3, 4])]

def cycle0962 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![2, 1, 5, 3, 4]), .gapLower 0 3 (![2, 1, 5, 3, 4]), .triangle 3 1]

def cycle0963 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 5, 3, 4]), .triangle 7 1, .gapLower 0 3 (![2, 1, 5, 3, 4]), .triangle 3 1]

def cycle0964 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 1, 5, 3, 4]), .gapLower 0 4 (![2, 1, 5, 3, 4])]

def cycle0965 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0966 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0967 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 3, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0968 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![2, 1, 4, 3, 5])]

def cycle0969 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![2, 1, 4, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0970 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 1, 4, 3, 5])]

def cycle0971 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, true] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 1, 4, 3, 5]), .triangle 8 1]

def cycle0972 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 3, 5]), .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0973 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .triangle 7 2, .gapLower 0 2 (![2, 1, 4, 3, 5])]

def cycle0974 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![2, 1, 4, 3, 5]), .triangle 5 1]

def cycle0975 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 4, 3, 5]), .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 2, .triangle 3 2, .gapLower 0 4 (![2, 1, 4, 3, 5]), .triangle 1 1]

def cycle0976 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![2, 0, 4, 3, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 2, .triangle 3 2, .gapLower 0 4 (![2, 1, 4, 3, 5]), .triangle 1 1]

def cycle0977 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 2, .gapLower 1 2 (![2, 0, 4, 3, 5])]

def cycle0978 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 3, 5]), .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 3 (![2, 0, 4, 3, 5]), .triangle 2 0]

def cycle0979 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 2, .gapLower 1 4 (![2, 0, 4, 3, 5]), .triangle 1 0]

def cycle0980 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![2, 0, 4, 3, 5]), .triangle 3 2, .gapLower 0 4 (![2, 1, 4, 3, 5])]

def cycle0981 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .corridorUpper 1 3, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![2, 1, 4, 3, 5])]

def cycle0982 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![2, 1, 4, 3, 5])]

def cycle0983 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 4, 3, 5]), .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0984 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![2, 0, 4, 3, 5]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0985 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 4, 3, 5]), .triangle 14 1, .triangle 1 0]

def cycle0986 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .distance 1 3, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .corridorUpper 1 3, .triangle 14 0, .triangle 8 0]

def cycle0987 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 5, 4, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0988 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 1 (![2, 0, 5, 4, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0989 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 18 0, .triangle 5 0]

def cycle0990 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0991 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 2 (![2, 1, 4, 3, 5])]

def cycle0992 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![1, 0, 5, 4, 3]), .triangle 6 0]

def cycle0993 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![1, 0, 5, 4, 3]), .triangle 18 0, .triangle 9 0, .triangle 2 1]

def cycle0994 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![1, 0, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 2 1]

def cycle0995 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 3 (![2, 0, 5, 4, 3]), .triangle 15 1, .triangle 9 0, .triangle 2 1]

def cycle0996 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 3, 5]), .gapLower 0 0 (![2, 1, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 0, 5, 4, 3]), .triangle 2 0]

def cycle0997 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 5, 4, 3]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![2, 1, 4, 3, 5])]

def cycle0998 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 3, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![2, 1, 4, 3, 5])]

def cycle0999 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 3, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![2, 1, 4, 3, 5]), .triangle 2 1]

def cycle1000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 3, 5]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 1, 4, 3, 5]), .triangle 1 1]

def cycle1001 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 3, 5]), .corridorLower 0 2, .gapLower 0 5 (![2, 1, 4, 3, 5]), .triangle 8 1, .triangle 1 1]

def cycle1002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![2, 1, 4, 3, 5]), .gapLower 0 2 (![2, 1, 4, 3, 5])]

def cycle1003 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 1, 4, 3, 5]), .triangle 7 2, .gapLower 0 2 (![2, 1, 4, 3, 5])]

def cycle1004 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 4, 3, 5]), .triangle 8 1, .triangle 7 2, .gapLower 0 2 (![2, 1, 4, 3, 5])]

def cycle1005 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![2, 1, 4, 3, 5]), .gapLower 0 3 (![2, 1, 4, 3, 5]), .triangle 2 1]

def cycle1006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 4, 3, 5]), .triangle 8 1, .gapLower 0 3 (![2, 1, 4, 3, 5]), .triangle 2 1]

def cycle1007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![2, 1, 4, 3, 5]), .gapLower 0 4 (![2, 1, 4, 3, 5])]

def cycle1008 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle1009 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle1010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 5, 3]), .corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle1011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![2, 1, 4, 5, 3])]

def cycle1012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(0), (-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 8 2, .gapLower 0 3 (![2, 1, 4, 5, 3]), .triangle 7 1, .corridorLower 3 4, .corridorUpper 1 3, .triangle 1 2]

def cycle1013 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![2, 1, 4, 5, 3]), .triangle 8 1, .corridorLower 3 5, .corridorUpper 1 3, .triangle 1 2]

def cycle1014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 5 (![2, 1, 4, 5, 3]), .triangle 8 2, .triangle 9 1, .triangle 2 1]

def cycle1015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![2, 1, 4, 5, 3]), .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 0]

def cycle1016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![2, 1, 4, 5, 3])]

def cycle1017 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0 (![2, 0, 4, 5, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 1, 4, 5, 3]), .triangle 2 1]

def cycle1018 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![2, 0, 4, 5, 3]), .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 1, 4, 5, 3]), .triangle 2 1]

def cycle1019 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![2, 0, 4, 5, 3])]

def cycle1020 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 14 2, .gapLower 1 3 (![2, 0, 4, 5, 3]), .triangle 2 0]

def cycle1021 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .gapLower 1 4 (![2, 0, 4, 5, 3]), .triangle 3 2, .gapLower 0 3 (![2, 1, 4, 5, 3]), .triangle 2 1]

def cycle1022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 5 (![2, 0, 4, 5, 3]), .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![2, 1, 4, 5, 3]), .triangle 2 1]

def cycle1023 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 0 2, .gapLower 0 0 (![2, 1, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 3 (![2, 1, 4, 5, 3]), .triangle 2 1]

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
  | 0 => some (.leaf 2931)
  | 1 => some (.leaf 2932)
  | 2 => some (.leaf 2933)
  | 3 => some (.leaf 2934)
  | 4 => some (.leaf 2935)
  | 5 => some (.positive 1 (![4609, 4610, 4611, 4612, 2760, 4591]))
  | 6 => some (.triangle 6 4546 4613)
  | 7 => some (.leaf 2936)
  | 8 => some (.triangle 18 4614 4615)
  | 9 => some (.triangle 5 4545 4616)
  | 10 => some (.leaf 2937)
  | 11 => some (.triangle 17 4617 4618)
  | 12 => some (.leaf 2938)
  | 13 => some (.triangle 16 4619 4620)
  | 14 => some (.leaf 2939)
  | 15 => some (.positive 0 (![4606, 4607, 4608, 4621, 4600, 4622]))
  | 16 => some (.triangle 10 4605 4623)
  | 17 => some (.leaf 2940)
  | 18 => some (.triangle 15 4624 4625)
  | 19 => some (.leaf 2941)
  | 20 => some (.leaf 2942)
  | 21 => some (.leaf 2943)
  | 22 => some (.leaf 2944)
  | 23 => some (.leaf 2945)
  | 24 => some (.leaf 2946)
  | 25 => some (.leaf 2947)
  | 26 => some (.leaf 2948)
  | 27 => some (.leaf 2949)
  | 28 => some (.leaf 2950)
  | 29 => some (.heavy (![4534, 4535, 4536, 4537, 4538, 4539, 4540, 4541, 4581, 4604, 4626, 4627, 4628, 4629, 4630, 4631, 4632, 4633, 4634, 4635, 4636]))
  | 30 => some (.triangle 4 4475 4637)
  | 31 => some (.triangle 3 4425 4638)
  | 32 => some (.leaf 2951)
  | 33 => some (.leaf 2952)
  | 34 => some (.leaf 2953)
  | 35 => some (.triangle 10 4641 4642)
  | 36 => some (.triangle 3 4640 4643)
  | 37 => some (.leaf 2954)
  | 38 => some (.triangle 15 4644 4645)
  | 39 => some (.leaf 2955)
  | 40 => some (.leaf 2956)
  | 41 => some (.leaf 2957)
  | 42 => some (.leaf 2958)
  | 43 => some (.leaf 2959)
  | 44 => some (.leaf 2960)
  | 45 => some (.leaf 2961)
  | 46 => some (.leaf 2962)
  | 47 => some (.leaf 2963)
  | 48 => some (.leaf 2964)
  | 49 => some (.triangle 15 4656 4645)
  | 50 => some (.leaf 2965)
  | 51 => some (.leaf 2966)
  | 52 => some (.leaf 2967)
  | 53 => some (.leaf 2968)
  | 54 => some (.leaf 2969)
  | 55 => some (.leaf 2970)
  | 56 => some (.leaf 2971)
  | 57 => some (.leaf 2972)
  | 58 => some (.heavy (![4646, 4647, 4648, 4649, 4650, 4651, 4652, 4653, 4654, 4655, 4657, 4658, 4659, 4660, 4661, 4662, 4663, 4653, 4664, 4654, 4665]))
  | 59 => some (.leaf 2973)
  | 60 => some (.leaf 2974)
  | 61 => some (.leaf 2975)
  | 62 => some (.triangle 7 4227 3303)
  | 63 => some (.leaf 2976)
  | 64 => some (.leaf 2977)
  | 65 => some (.leaf 2978)
  | 66 => some (.leaf 2979)
  | 67 => some (.leaf 2980)
  | 68 => some (.positive 1 (![4670, 4671, 4672, 4673, 4674, 4675]))
  | 69 => some (.triangle 18 4669 4676)
  | 70 => some (.triangle 5 4021 4677)
  | 71 => some (.triangle 7 4227 4296)
  | 72 => some (.leaf 2981)
  | 73 => some (.positive 1 (![4679, 4298, 4299, 4300, 4301, 4680]))
  | 74 => some (.triangle 5 4294 4681)
  | 75 => some (.triangle 17 4678 4682)
  | 76 => some (.leaf 2982)
  | 77 => some (.triangle 19 3327 4684)
  | 78 => some (.leaf 2983)
  | 79 => some (.leaf 2984)
  | 80 => some (.leaf 2985)
  | 81 => some (.positive 1 (![4685, 4686, 3331, 4687, 3850, 4688]))
  | 82 => some (.triangle 18 4669 4689)
  | 83 => some (.triangle 16 4683 4690)
  | 84 => some (.leaf 2986)
  | 85 => some (.leaf 2987)
  | 86 => some (.leaf 2988)
  | 87 => some (.positive 0 (![4667, 4668, 4691, 4692, 4693, 4694]))
  | 88 => some (.triangle 10 2251 4695)
  | 89 => some (.triangle 3 4640 4696)
  | 90 => some (.triangle 15 4697 4645)
  | 91 => some (.leaf 2989)
  | 92 => some (.leaf 2990)
  | 93 => some (.leaf 2991)
  | 94 => some (.leaf 2992)
  | 95 => some (.leaf 2993)
  | 96 => some (.leaf 2994)
  | 97 => some (.leaf 2995)
  | 98 => some (.leaf 2996)
  | 99 => some (.leaf 2997)
  | 100 => some (.leaf 2998)
  | 101 => some (.triangle 15 4708 4645)
  | 102 => some (.leaf 2999)
  | 103 => some (.leaf 3000)
  | 104 => some (.leaf 3001)
  | 105 => some (.leaf 3002)
  | 106 => some (.leaf 3003)
  | 107 => some (.leaf 3004)
  | 108 => some (.leaf 3005)
  | 109 => some (.leaf 3006)
  | 110 => some (.leaf 3007)
  | 111 => some (.heavy (![4698, 4699, 4700, 4701, 4702, 4703, 4704, 4705, 4706, 4707, 4709, 4710, 4711, 4712, 4713, 4714, 4715, 4705, 4716, 4717, 4718]))
  | 112 => some (.triangle 4 4666 4719)
  | 113 => some (.triangle 9 4639 4720)
  | 114 => some (.triangle 2 3968 4721)
  | 115 => some (.leaf 3008)
  | 116 => some (.leaf 3009)
  | 117 => some (.triangle 11 4723 4724)
  | 118 => some (.leaf 3010)
  | 119 => some (.leaf 3011)
  | 120 => some (.leaf 3012)
  | 121 => some (.leaf 3013)
  | 122 => some (.leaf 3014)
  | 123 => some (.leaf 3015)
  | 124 => some (.leaf 3016)
  | 125 => some (.leaf 3017)
  | 126 => some (.leaf 3018)
  | 127 => some (.leaf 3019)
  | 128 => some (.leaf 3020)
  | 129 => some (.leaf 3021)
  | 130 => some (.leaf 3022)
  | 131 => some (.leaf 3023)
  | 132 => some (.positive 0 (![4734, 4735, 4736, 4737, 4738, 4739]))
  | 133 => some (.leaf 3024)
  | 134 => some (.triangle 15 4740 4741)
  | 135 => some (.leaf 3025)
  | 136 => some (.triangle 12 4742 4743)
  | 137 => some (.leaf 3026)
  | 138 => some (.leaf 3027)
  | 139 => some (.triangle 12 4745 4746)
  | 140 => some (.leaf 3028)
  | 141 => some (.triangle 15 4747 4748)
  | 142 => some (.triangle 11 4744 4749)
  | 143 => some (.leaf 3029)
  | 144 => some (.leaf 3030)
  | 145 => some (.leaf 3031)
  | 146 => some (.positive 0 (![4751, 4752, 4736, 4737, 4738, 4753]))
  | 147 => some (.leaf 3032)
  | 148 => some (.leaf 3033)
  | 149 => some (.leaf 3034)
  | 150 => some (.leaf 3035)
  | 151 => some (.leaf 3036)
  | 152 => some (.leaf 3037)
  | 153 => some (.positive 0 (![4755, 4756, 4757, 4758, 4759, 4760]))
  | 154 => some (.triangle 15 4754 4761)
  | 155 => some (.leaf 3038)
  | 156 => some (.triangle 12 4762 4763)
  | 157 => some (.leaf 3039)
  | 158 => some (.leaf 3040)
  | 159 => some (.leaf 3041)
  | 160 => some (.leaf 3042)
  | 161 => some (.leaf 3043)
  | 162 => some (.leaf 3044)
  | 163 => some (.positive 0 (![4765, 4766, 4767, 4768, 4769, 4770]))
  | 164 => some (.triangle 12 4745 4771)
  | 165 => some (.leaf 3045)
  | 166 => some (.leaf 3046)
  | 167 => some (.leaf 3047)
  | 168 => some (.leaf 3048)
  | 169 => some (.triangle 4 4775 4776)
  | 170 => some (.leaf 3049)
  | 171 => some (.leaf 3050)
  | 172 => some (.leaf 3051)
  | 173 => some (.positive 0 (![4773, 4774, 4777, 4778, 4779, 4780]))
  | 174 => some (.triangle 15 4772 4781)
  | 175 => some (.triangle 11 4764 4782)
  | 176 => some (.leaf 3052)
  | 177 => some (.leaf 3053)
  | 178 => some (.leaf 3054)
  | 179 => some (.leaf 3055)
  | 180 => some (.leaf 3056)
  | 181 => some (.leaf 3057)
  | 182 => some (.leaf 3058)
  | 183 => some (.leaf 3059)
  | 184 => some (.leaf 3060)
  | 185 => some (.leaf 3061)
  | 186 => some (.heavy (![4725, 4726, 4727, 4728, 4729, 4730, 4731, 4732, 4733, 4750, 4783, 4784, 4785, 4786, 4787, 4788, 4789, 4790, 4791, 4792, 4793]))
  | 187 => some (.leaf 3062)
  | 188 => some (.leaf 3063)
  | 189 => some (.triangle 11 4795 4796)
  | 190 => some (.leaf 3064)
  | 191 => some (.leaf 3065)
  | 192 => some (.leaf 3066)
  | 193 => some (.leaf 3067)
  | 194 => some (.leaf 3068)
  | 195 => some (.leaf 3069)
  | 196 => some (.leaf 3070)
  | 197 => some (.leaf 3071)
  | 198 => some (.leaf 3072)
  | 199 => some (.leaf 3073)
  | 200 => some (.leaf 3074)
  | 201 => some (.leaf 3075)
  | 202 => some (.leaf 3076)
  | 203 => some (.positive 0 (![4805, 4806, 4807, 4808, 4809, 4810]))
  | 204 => some (.triangle 15 1161 4811)
  | 205 => some (.leaf 3077)
  | 206 => some (.triangle 12 4812 4813)
  | 207 => some (.leaf 3078)
  | 208 => some (.triangle 11 4814 4815)
  | 209 => some (.leaf 3079)
  | 210 => some (.leaf 3080)
  | 211 => some (.leaf 3081)
  | 212 => some (.leaf 3082)
  | 213 => some (.positive 0 (![4817, 4818, 4807, 4808, 4819, 4820]))
  | 214 => some (.triangle 15 1161 4821)
  | 215 => some (.leaf 3083)
  | 216 => some (.triangle 12 4822 4823)
  | 217 => some (.leaf 3084)
  | 218 => some (.triangle 11 4824 4825)
  | 219 => some (.leaf 3085)
  | 220 => some (.leaf 3086)
  | 221 => some (.leaf 3087)
  | 222 => some (.positive 0 (![4828, 4756, 4807, 4808, 4819, 4829]))
  | 223 => some (.triangle 15 4827 4830)
  | 224 => some (.triangle 12 4831 4823)
  | 225 => some (.leaf 3088)
  | 226 => some (.leaf 3089)
  | 227 => some (.triangle 4 4775 2277)
  | 228 => some (.leaf 3090)
  | 229 => some (.leaf 3091)
  | 230 => some (.leaf 3092)
  | 231 => some (.positive 0 (![4833, 4834, 4835, 4836, 4837, 4838]))
  | 232 => some (.triangle 15 1161 4839)
  | 233 => some (.triangle 11 4832 4840)
  | 234 => some (.leaf 3093)
  | 235 => some (.leaf 3094)
  | 236 => some (.leaf 3095)
  | 237 => some (.leaf 3096)
  | 238 => some (.leaf 3097)
  | 239 => some (.leaf 3098)
  | 240 => some (.leaf 3099)
  | 241 => some (.leaf 3100)
  | 242 => some (.leaf 3101)
  | 243 => some (.leaf 3102)
  | 244 => some (.heavy (![4797, 4798, 4799, 4800, 4801, 4802, 4803, 4804, 4816, 4826, 4841, 4842, 4843, 4844, 4845, 4846, 4847, 4848, 4849, 4850, 4851]))
  | 245 => some (.triangle 9 4794 4852)
  | 246 => some (.leaf 3103)
  | 247 => some (.leaf 3104)
  | 248 => some (.triangle 11 4854 4855)
  | 249 => some (.leaf 3105)
  | 250 => some (.leaf 3106)
  | 251 => some (.leaf 3107)
  | 252 => some (.leaf 3108)
  | 253 => some (.leaf 3109)
  | 254 => some (.leaf 3110)
  | 255 => some (.leaf 3111)
  | 256 => some (.leaf 3112)
  | 257 => some (.leaf 3113)
  | 258 => some (.leaf 3114)
  | 259 => some (.leaf 3115)
  | 260 => some (.leaf 3116)
  | 261 => some (.leaf 3117)
  | 262 => some (.leaf 3118)
  | 263 => some (.positive 0 (![4865, 4866, 4867, 4868, 4869, 4870]))
  | 264 => some (.triangle 12 1879 4871)
  | 265 => some (.leaf 3119)
  | 266 => some (.triangle 11 4872 4873)
  | 267 => some (.leaf 3120)
  | 268 => some (.leaf 3121)
  | 269 => some (.leaf 3122)
  | 270 => some (.positive 0 (![4875, 4876, 4867, 4868, 4869, 4877]))
  | 271 => some (.triangle 12 1879 4878)
  | 272 => some (.triangle 11 4879 2482)
  | 273 => some (.leaf 3123)
  | 274 => some (.leaf 3124)
  | 275 => some (.leaf 3125)
  | 276 => some (.leaf 3126)
  | 277 => some (.leaf 3127)
  | 278 => some (.leaf 3128)
  | 279 => some (.leaf 3129)
  | 280 => some (.leaf 3130)
  | 281 => some (.leaf 3131)
  | 282 => some (.leaf 3132)
  | 283 => some (.heavy (![4856, 4857, 4858, 4859, 4860, 4861, 4862, 4863, 4864, 4874, 4880, 4881, 4882, 4883, 4884, 4885, 4886, 4887, 4888, 4889, 4890]))
  | 284 => some (.triangle 6 4853 4891)
  | 285 => some (.leaf 3133)
  | 286 => some (.leaf 3134)
  | 287 => some (.triangle 15 4893 4894)
  | 288 => some (.triangle 11 2017 4895)
  | 289 => some (.leaf 3135)
  | 290 => some (.leaf 3136)
  | 291 => some (.leaf 3137)
  | 292 => some (.leaf 3138)
  | 293 => some (.leaf 3139)
  | 294 => some (.leaf 3140)
  | 295 => some (.leaf 3141)
  | 296 => some (.leaf 3142)
  | 297 => some (.leaf 3143)
  | 298 => some (.leaf 3144)
  | 299 => some (.leaf 3145)
  | 300 => some (.leaf 3146)
  | 301 => some (.leaf 3147)
  | 302 => some (.leaf 3148)
  | 303 => some (.positive 0 (![4905, 4906, 4907, 4908, 4909, 4910]))
  | 304 => some (.leaf 3149)
  | 305 => some (.triangle 12 4911 4912)
  | 306 => some (.leaf 3150)
  | 307 => some (.triangle 15 4913 4914)
  | 308 => some (.triangle 11 2017 4915)
  | 309 => some (.leaf 3151)
  | 310 => some (.leaf 3152)
  | 311 => some (.leaf 3153)
  | 312 => some (.positive 0 (![4917, 4918, 4907, 4908, 4909, 4919]))
  | 313 => some (.leaf 3154)
  | 314 => some (.triangle 12 4920 4921)
  | 315 => some (.leaf 3155)
  | 316 => some (.leaf 3156)
  | 317 => some (.leaf 3157)
  | 318 => some (.triangle 12 4925 2574)
  | 319 => some (.leaf 3158)
  | 320 => some (.triangle 16 4926 4927)
  | 321 => some (.leaf 3159)
  | 322 => some (.leaf 3160)
  | 323 => some (.leaf 3161)
  | 324 => some (.positive 0 (![4923, 4924, 4928, 4929, 4930, 4931]))
  | 325 => some (.triangle 15 4922 4932)
  | 326 => some (.triangle 11 2017 4933)
  | 327 => some (.leaf 3162)
  | 328 => some (.leaf 3163)
  | 329 => some (.leaf 3164)
  | 330 => some (.leaf 3165)
  | 331 => some (.leaf 3166)
  | 332 => some (.leaf 3167)
  | 333 => some (.leaf 3168)
  | 334 => some (.leaf 3169)
  | 335 => some (.leaf 3170)
  | 336 => some (.leaf 3171)
  | 337 => some (.heavy (![4896, 4897, 4898, 4899, 4900, 4901, 4902, 4903, 4904, 4916, 4934, 4935, 4936, 4937, 4938, 4939, 4940, 4941, 4942, 4943, 4944]))
  | 338 => some (.leaf 3172)
  | 339 => some (.leaf 3173)
  | 340 => some (.triangle 15 4946 4947)
  | 341 => some (.triangle 11 2017 4948)
  | 342 => some (.leaf 3174)
  | 343 => some (.leaf 3175)
  | 344 => some (.leaf 3176)
  | 345 => some (.leaf 3177)
  | 346 => some (.leaf 3178)
  | 347 => some (.leaf 3179)
  | 348 => some (.leaf 3180)
  | 349 => some (.leaf 3181)
  | 350 => some (.leaf 3182)
  | 351 => some (.leaf 3183)
  | 352 => some (.leaf 3184)
  | 353 => some (.leaf 3185)
  | 354 => some (.leaf 3186)
  | 355 => some (.positive 0 (![4957, 4958, 4959, 4960, 4961, 4962]))
  | 356 => some (.triangle 12 1879 4963)
  | 357 => some (.leaf 3187)
  | 358 => some (.triangle 15 4964 4965)
  | 359 => some (.triangle 11 2017 4966)
  | 360 => some (.leaf 3188)
  | 361 => some (.leaf 3189)
  | 362 => some (.leaf 3190)
  | 363 => some (.leaf 3191)
  | 364 => some (.positive 0 (![4968, 4969, 4959, 4960, 4970, 4971]))
  | 365 => some (.triangle 12 1879 4972)
  | 366 => some (.leaf 3192)
  | 367 => some (.leaf 3193)
  | 368 => some (.leaf 3194)
  | 369 => some (.leaf 3195)
  | 370 => some (.leaf 3196)
  | 371 => some (.leaf 3197)
  | 372 => some (.triangle 10 4978 4979)
  | 373 => some (.leaf 3198)
  | 374 => some (.leaf 3199)
  | 375 => some (.positive 1 (![4976, 2679, 4977, 4980, 4981, 4982]))
  | 376 => some (.triangle 18 4983 2170)
  | 377 => some (.leaf 3200)
  | 378 => some (.triangle 17 4984 4985)
  | 379 => some (.leaf 3201)
  | 380 => some (.triangle 16 4986 4987)
  | 381 => some (.leaf 3202)
  | 382 => some (.leaf 3203)
  | 383 => some (.leaf 3204)
  | 384 => some (.positive 0 (![4974, 4975, 4988, 4989, 4990, 4991]))
  | 385 => some (.triangle 15 4973 4992)
  | 386 => some (.triangle 11 2017 4993)
  | 387 => some (.leaf 3205)
  | 388 => some (.leaf 3206)
  | 389 => some (.leaf 3207)
  | 390 => some (.leaf 3208)
  | 391 => some (.leaf 3209)
  | 392 => some (.positive 0 (![4997, 4998, 4959, 4960, 4970, 4999]))
  | 393 => some (.triangle 12 4996 5000)
  | 394 => some (.leaf 3210)
  | 395 => some (.leaf 3211)
  | 396 => some (.leaf 3212)
  | 397 => some (.positive 1 (![2782, 2679, 5003, 5004, 2760, 4982]))
  | 398 => some (.leaf 3213)
  | 399 => some (.triangle 18 5005 5006)
  | 400 => some (.leaf 3214)
  | 401 => some (.triangle 17 5007 5008)
  | 402 => some (.leaf 3215)
  | 403 => some (.triangle 16 5009 5010)
  | 404 => some (.leaf 3216)
  | 405 => some (.positive 0 (![5002, 4924, 5011, 4989, 4990, 5012]))
  | 406 => some (.triangle 15 5001 5013)
  | 407 => some (.triangle 11 4995 5014)
  | 408 => some (.leaf 3217)
  | 409 => some (.leaf 3218)
  | 410 => some (.leaf 3219)
  | 411 => some (.leaf 3220)
  | 412 => some (.leaf 3221)
  | 413 => some (.leaf 3222)
  | 414 => some (.leaf 3223)
  | 415 => some (.leaf 3224)
  | 416 => some (.leaf 3225)
  | 417 => some (.leaf 3226)
  | 418 => some (.heavy (![4949, 4950, 4951, 4952, 4953, 4954, 4955, 4956, 4967, 4994, 5015, 5016, 5017, 5018, 5019, 5020, 5021, 5022, 5023, 5024, 5025]))
  | 419 => some (.triangle 6 4945 5026)
  | 420 => some (.leaf 3227)
  | 421 => some (.leaf 3228)
  | 422 => some (.leaf 3229)
  | 423 => some (.leaf 3230)
  | 424 => some (.leaf 3231)
  | 425 => some (.leaf 3232)
  | 426 => some (.leaf 3233)
  | 427 => some (.positive 2 (![5029, 5030, 5031, 5032, 5033, 5034]))
  | 428 => some (.triangle 19 1264 5035)
  | 429 => some (.triangle 10 4978 5036)
  | 430 => some (.leaf 3234)
  | 431 => some (.leaf 3235)
  | 432 => some (.positive 1 (![5028, 2848, 2849, 5037, 5038, 5039]))
  | 433 => some (.triangle 6 2846 5040)
  | 434 => some (.leaf 3236)
  | 435 => some (.leaf 3237)
  | 436 => some (.triangle 10 5042 5043)
  | 437 => some (.leaf 3238)
  | 438 => some (.leaf 3239)
  | 439 => some (.positive 1 (![5044, 2863, 2864, 2865, 5045, 5046]))
  | 440 => some (.triangle 18 5041 5047)
  | 441 => some (.leaf 3240)
  | 442 => some (.triangle 17 5048 5049)
  | 443 => some (.leaf 3241)
  | 444 => some (.triangle 16 5050 5051)
  | 445 => some (.leaf 3242)
  | 446 => some (.triangle 10 4978 5053)
  | 447 => some (.positive 1 (![5028, 2848, 2849, 5054, 5038, 5039]))
  | 448 => some (.triangle 6 2846 5055)
  | 449 => some (.leaf 3243)
  | 450 => some (.triangle 10 5042 5057)
  | 451 => some (.positive 1 (![5058, 2863, 2864, 2865, 5045, 5046]))
  | 452 => some (.triangle 18 5056 5059)
  | 453 => some (.triangle 17 5060 5049)
  | 454 => some (.triangle 16 5061 5051)
  | 455 => some (.leaf 3244)
  | 456 => some (.leaf 3245)
  | 457 => some (.leaf 3246)
  | 458 => some (.leaf 3247)
  | 459 => some (.positive 0 (![5052, 5062, 5063, 5064, 5065, 5066]))
  | 460 => some (.triangle 15 1161 5067)
  | 461 => some (.triangle 11 2017 5068)
  | 462 => some (.leaf 3248)
  | 463 => some (.leaf 3249)
  | 464 => some (.leaf 3250)
  | 465 => some (.leaf 3251)
  | 466 => some (.leaf 3252)
  | 467 => some (.leaf 3253)
  | 468 => some (.leaf 3254)
  | 469 => some (.leaf 3255)
  | 470 => some (.leaf 3256)
  | 471 => some (.triangle 10 4978 5078)
  | 472 => some (.leaf 3257)
  | 473 => some (.leaf 3258)
  | 474 => some (.positive 1 (![5028, 2848, 2849, 5079, 5080, 5081]))
  | 475 => some (.triangle 6 2846 5082)
  | 476 => some (.leaf 3259)
  | 477 => some (.triangle 10 5042 5084)
  | 478 => some (.leaf 3260)
  | 479 => some (.leaf 3261)
  | 480 => some (.positive 1 (![5085, 2863, 2864, 2865, 5086, 5087]))
  | 481 => some (.triangle 18 5083 5088)
  | 482 => some (.leaf 3262)
  | 483 => some (.triangle 17 5089 5090)
  | 484 => some (.leaf 3263)
  | 485 => some (.triangle 16 5091 5092)
  | 486 => some (.leaf 3264)
  | 487 => some (.leaf 3265)
  | 488 => some (.leaf 3266)
  | 489 => some (.positive 0 (![5076, 5077, 5093, 5094, 5095, 5096]))
  | 490 => some (.triangle 15 1161 5097)
  | 491 => some (.triangle 11 2017 5098)
  | 492 => some (.leaf 3267)
  | 493 => some (.leaf 3268)
  | 494 => some (.leaf 3269)
  | 495 => some (.leaf 3270)
  | 496 => some (.triangle 10 5042 5103)
  | 497 => some (.leaf 3271)
  | 498 => some (.leaf 3272)
  | 499 => some (.positive 1 (![5104, 2863, 2864, 2865, 5105, 5106]))
  | 500 => some (.triangle 18 5102 5107)
  | 501 => some (.leaf 3273)
  | 502 => some (.triangle 17 5108 5109)
  | 503 => some (.leaf 3274)
  | 504 => some (.triangle 16 5110 5111)
  | 505 => some (.leaf 3275)
  | 506 => some (.leaf 3276)
  | 507 => some (.leaf 3277)
  | 508 => some (.positive 0 (![5100, 5101, 5112, 5113, 5114, 5115]))
  | 509 => some (.triangle 15 1161 5116)
  | 510 => some (.triangle 11 2017 5117)
  | 511 => some (.leaf 3278)
  | 512 => some (.leaf 3279)
  | 513 => some (.leaf 3280)
  | 514 => some (.leaf 3281)
  | 515 => some (.leaf 3282)
  | 516 => some (.leaf 3283)
  | 517 => some (.triangle 18 5123 5124)
  | 518 => some (.leaf 3284)
  | 519 => some (.triangle 17 5125 5126)
  | 520 => some (.leaf 3285)
  | 521 => some (.triangle 16 5127 5128)
  | 522 => some (.leaf 3286)
  | 523 => some (.leaf 3287)
  | 524 => some (.positive 0 (![5121, 5122, 5129, 5113, 5130, 5131]))
  | 525 => some (.triangle 15 1161 5132)
  | 526 => some (.triangle 11 5120 5133)
  | 527 => some (.leaf 3288)
  | 528 => some (.leaf 3289)
  | 529 => some (.leaf 3290)
  | 530 => some (.leaf 3291)
  | 531 => some (.leaf 3292)
  | 532 => some (.leaf 3293)
  | 533 => some (.leaf 3294)
  | 534 => some (.leaf 3295)
  | 535 => some (.leaf 3296)
  | 536 => some (.leaf 3297)
  | 537 => some (.heavy (![5069, 5070, 5071, 5072, 5073, 5074, 5075, 5099, 5118, 5119, 5134, 5135, 5136, 5137, 5138, 5139, 5140, 5141, 5142, 5143, 5144]))
  | 538 => some (.triangle 9 5027 5145)
  | 539 => some (.triangle 5 4892 5146)
  | 540 => some (.leaf 3298)
  | 541 => some (.leaf 3299)
  | 542 => some (.triangle 11 5148 5149)
  | 543 => some (.leaf 3300)
  | 544 => some (.triangle 14 5150 5151)
  | 545 => some (.leaf 3301)
  | 546 => some (.leaf 3302)
  | 547 => some (.leaf 3303)
  | 548 => some (.leaf 3304)
  | 549 => some (.leaf 3305)
  | 550 => some (.leaf 3306)
  | 551 => some (.leaf 3307)
  | 552 => some (.leaf 3308)
  | 553 => some (.leaf 3309)
  | 554 => some (.leaf 3310)
  | 555 => some (.leaf 3311)
  | 556 => some (.leaf 3312)
  | 557 => some (.leaf 3313)
  | 558 => some (.leaf 3314)
  | 559 => some (.positive 0 (![5161, 5162, 5163, 5164, 5165, 5166]))
  | 560 => some (.leaf 3315)
  | 561 => some (.triangle 11 5167 5168)
  | 562 => some (.leaf 3316)
  | 563 => some (.triangle 14 5169 5170)
  | 564 => some (.leaf 3317)
  | 565 => some (.leaf 3318)
  | 566 => some (.leaf 3319)
  | 567 => some (.positive 0 (![5172, 5162, 5173, 5164, 5165, 5174]))
  | 568 => some (.leaf 3320)
  | 569 => some (.leaf 3321)
  | 570 => some (.leaf 3322)
  | 571 => some (.leaf 3323)
  | 572 => some (.triangle 4 5179 2277)
  | 573 => some (.leaf 3324)
  | 574 => some (.leaf 3325)
  | 575 => some (.positive 0 (![5176, 5177, 5178, 5180, 5181, 5182]))
  | 576 => some (.triangle 11 5175 5183)
  | 577 => some (.leaf 3326)
  | 578 => some (.triangle 14 5184 5185)
  | 579 => some (.leaf 3327)
  | 580 => some (.leaf 3328)
  | 581 => some (.leaf 3329)
  | 582 => some (.leaf 3330)
  | 583 => some (.leaf 3331)
  | 584 => some (.leaf 3332)
  | 585 => some (.leaf 3333)
  | 586 => some (.leaf 3334)
  | 587 => some (.leaf 3335)
  | 588 => some (.leaf 3336)
  | 589 => some (.heavy (![5152, 5153, 5154, 5155, 5156, 5157, 5158, 5159, 5160, 5171, 5186, 5187, 5188, 5189, 5190, 5191, 5192, 5193, 5194, 5195, 5196]))
  | 590 => some (.leaf 3337)
  | 591 => some (.triangle 10 5042 5198)
  | 592 => some (.leaf 3338)
  | 593 => some (.leaf 3339)
  | 594 => some (.leaf 3340)
  | 595 => some (.leaf 3341)
  | 596 => some (.leaf 3342)
  | 597 => some (.leaf 3343)
  | 598 => some (.leaf 3344)
  | 599 => some (.positive 2 (![5201, 5202, 5203, 5204, 5205, 5206]))
  | 600 => some (.triangle 19 5200 5207)
  | 601 => some (.triangle 10 5042 5208)
  | 602 => some (.leaf 3345)
  | 603 => some (.leaf 3346)
  | 604 => some (.positive 1 (![5199, 4478, 3812, 5209, 5210, 5211]))
  | 605 => some (.triangle 6 3552 5212)
  | 606 => some (.leaf 3347)
  | 607 => some (.triangle 10 5042 5214)
  | 608 => some (.leaf 3348)
  | 609 => some (.positive 1 (![5215, 2863, 2864, 2865, 5045, 5216]))
  | 610 => some (.triangle 18 5213 5217)
  | 611 => some (.leaf 3349)
  | 612 => some (.triangle 17 5218 5219)
  | 613 => some (.leaf 3350)
  | 614 => some (.triangle 16 5220 5221)
  | 615 => some (.leaf 3351)
  | 616 => some (.leaf 3352)
  | 617 => some (.triangle 10 5042 5224)
  | 618 => some (.leaf 3353)
  | 619 => some (.triangle 10 5042 5226)
  | 620 => some (.leaf 3354)
  | 621 => some (.positive 1 (![5225, 4478, 3812, 5227, 5228, 5211]))
  | 622 => some (.triangle 6 3552 5229)
  | 623 => some (.leaf 3355)
  | 624 => some (.triangle 10 5042 5231)
  | 625 => some (.positive 1 (![5232, 2863, 2864, 2865, 5045, 5216]))
  | 626 => some (.triangle 18 5230 5233)
  | 627 => some (.triangle 17 5234 5219)
  | 628 => some (.triangle 16 5235 5221)
  | 629 => some (.leaf 3356)
  | 630 => some (.leaf 3357)
  | 631 => some (.leaf 3358)
  | 632 => some (.positive 0 (![5222, 5223, 5236, 5237, 5238, 5239]))
  | 633 => some (.triangle 11 2017 5240)
  | 634 => some (.leaf 3359)
  | 635 => some (.triangle 14 5241 5242)
  | 636 => some (.leaf 3360)
  | 637 => some (.leaf 3361)
  | 638 => some (.leaf 3362)
  | 639 => some (.leaf 3363)
  | 640 => some (.leaf 3364)
  | 641 => some (.leaf 3365)
  | 642 => some (.leaf 3366)
  | 643 => some (.leaf 3367)
  | 644 => some (.leaf 3368)
  | 645 => some (.leaf 3369)
  | 646 => some (.leaf 3370)
  | 647 => some (.leaf 3371)
  | 648 => some (.leaf 3372)
  | 649 => some (.leaf 3373)
  | 650 => some (.leaf 3374)
  | 651 => some (.triangle 10 5042 5258)
  | 652 => some (.leaf 3375)
  | 653 => some (.leaf 3376)
  | 654 => some (.positive 1 (![5255, 5256, 5257, 5259, 5260, 5261]))
  | 655 => some (.triangle 6 5254 5262)
  | 656 => some (.leaf 3377)
  | 657 => some (.triangle 10 5042 5264)
  | 658 => some (.leaf 3378)
  | 659 => some (.leaf 3379)
  | 660 => some (.positive 1 (![5265, 2863, 2864, 2865, 5266, 5267]))
  | 661 => some (.triangle 18 5263 5268)
  | 662 => some (.leaf 3380)
  | 663 => some (.triangle 17 5269 5270)
  | 664 => some (.leaf 3381)
  | 665 => some (.triangle 16 5271 5272)
  | 666 => some (.leaf 3382)
  | 667 => some (.leaf 3383)
  | 668 => some (.positive 0 (![5251, 5252, 5253, 5273, 5274, 5275]))
  | 669 => some (.triangle 11 2017 5276)
  | 670 => some (.triangle 14 5277 5170)
  | 671 => some (.leaf 3384)
  | 672 => some (.leaf 3385)
  | 673 => some (.leaf 3386)
  | 674 => some (.leaf 3387)
  | 675 => some (.leaf 3388)
  | 676 => some (.leaf 3389)
  | 677 => some (.leaf 3390)
  | 678 => some (.triangle 10 5042 5285)
  | 679 => some (.leaf 3391)
  | 680 => some (.leaf 3392)
  | 681 => some (.positive 1 (![5282, 5283, 5284, 5286, 5287, 5288]))
  | 682 => some (.triangle 6 5254 5289)
  | 683 => some (.leaf 3393)
  | 684 => some (.triangle 18 5290 5291)
  | 685 => some (.leaf 3394)
  | 686 => some (.triangle 17 5292 5293)
  | 687 => some (.leaf 3395)
  | 688 => some (.triangle 16 5294 5295)
  | 689 => some (.leaf 3396)
  | 690 => some (.leaf 3397)
  | 691 => some (.positive 0 (![5279, 5280, 5281, 5296, 5297, 5298]))
  | 692 => some (.triangle 11 2017 5299)
  | 693 => some (.triangle 14 5300 5170)
  | 694 => some (.leaf 3398)
  | 695 => some (.leaf 3399)
  | 696 => some (.leaf 3400)
  | 697 => some (.leaf 3401)
  | 698 => some (.leaf 3402)
  | 699 => some (.leaf 3403)
  | 700 => some (.leaf 3404)
  | 701 => some (.leaf 3405)
  | 702 => some (.positive 1 (![5306, 5307, 5308, 5309, 2760, 5288]))
  | 703 => some (.triangle 6 5254 5310)
  | 704 => some (.leaf 3406)
  | 705 => some (.triangle 18 5311 5312)
  | 706 => some (.leaf 3407)
  | 707 => some (.triangle 17 5313 5314)
  | 708 => some (.leaf 3408)
  | 709 => some (.triangle 16 5315 5316)
  | 710 => some (.leaf 3409)
  | 711 => some (.positive 0 (![5303, 5304, 5305, 5317, 5297, 5318]))
  | 712 => some (.triangle 11 5302 5319)
  | 713 => some (.leaf 3410)
  | 714 => some (.triangle 14 5320 5321)
  | 715 => some (.leaf 3411)
  | 716 => some (.leaf 3412)
  | 717 => some (.leaf 3413)
  | 718 => some (.leaf 3414)
  | 719 => some (.leaf 3415)
  | 720 => some (.leaf 3416)
  | 721 => some (.leaf 3417)
  | 722 => some (.leaf 3418)
  | 723 => some (.leaf 3419)
  | 724 => some (.leaf 3420)
  | 725 => some (.heavy (![5243, 5244, 5245, 5246, 5247, 5248, 5249, 5250, 5278, 5301, 5322, 5323, 5324, 5325, 5326, 5327, 5328, 5329, 5330, 5331, 5332]))
  | 726 => some (.triangle 5 5197 5333)
  | 727 => some (.triangle 3 5147 5334)
  | 728 => some (.leaf 3421)
  | 729 => some (.leaf 3422)
  | 730 => some (.triangle 12 5336 5337)
  | 731 => some (.leaf 3423)
  | 732 => some (.triangle 13 5338 5339)
  | 733 => some (.leaf 3424)
  | 734 => some (.leaf 3425)
  | 735 => some (.leaf 3426)
  | 736 => some (.leaf 3427)
  | 737 => some (.leaf 3428)
  | 738 => some (.leaf 3429)
  | 739 => some (.leaf 3430)
  | 740 => some (.leaf 3431)
  | 741 => some (.leaf 3432)
  | 742 => some (.leaf 3433)
  | 743 => some (.leaf 3434)
  | 744 => some (.leaf 3435)
  | 745 => some (.leaf 3436)
  | 746 => some (.leaf 3437)
  | 747 => some (.positive 0 (![5349, 5350, 5351, 5352, 5353, 5354]))
  | 748 => some (.leaf 3438)
  | 749 => some (.triangle 12 5355 5356)
  | 750 => some (.leaf 3439)
  | 751 => some (.triangle 13 5357 5358)
  | 752 => some (.leaf 3440)
  | 753 => some (.leaf 3441)
  | 754 => some (.leaf 3442)
  | 755 => some (.positive 0 (![5360, 5350, 5361, 5352, 5353, 5362]))
  | 756 => some (.leaf 3443)
  | 757 => some (.leaf 3444)
  | 758 => some (.leaf 3445)
  | 759 => some (.leaf 3446)
  | 760 => some (.triangle 4 5367 2571)
  | 761 => some (.leaf 3447)
  | 762 => some (.leaf 3448)
  | 763 => some (.positive 0 (![5364, 5365, 5366, 5368, 5369, 5370]))
  | 764 => some (.triangle 12 5363 5371)
  | 765 => some (.leaf 3449)
  | 766 => some (.triangle 13 5372 5373)
  | 767 => some (.leaf 3450)
  | 768 => some (.leaf 3451)
  | 769 => some (.leaf 3452)
  | 770 => some (.leaf 3453)
  | 771 => some (.leaf 3454)
  | 772 => some (.leaf 3455)
  | 773 => some (.leaf 3456)
  | 774 => some (.leaf 3457)
  | 775 => some (.leaf 3458)
  | 776 => some (.leaf 3459)
  | 777 => some (.heavy (![5340, 5341, 5342, 5343, 5344, 5345, 5346, 5347, 5348, 5359, 5374, 5375, 5376, 5377, 5378, 5379, 5380, 5381, 5382, 5383, 5384]))
  | 778 => some (.leaf 3460)
  | 779 => some (.leaf 3461)
  | 780 => some (.triangle 10 5386 5387)
  | 781 => some (.leaf 3462)
  | 782 => some (.leaf 3463)
  | 783 => some (.triangle 19 5389 5390)
  | 784 => some (.triangle 10 5386 5391)
  | 785 => some (.leaf 3464)
  | 786 => some (.leaf 3465)
  | 787 => some (.positive 1 (![5388, 2665, 2633, 5392, 5393, 5394]))
  | 788 => some (.leaf 3466)
  | 789 => some (.triangle 18 5395 5396)
  | 790 => some (.leaf 3467)
  | 791 => some (.triangle 17 5397 5398)
  | 792 => some (.leaf 3468)
  | 793 => some (.triangle 16 5399 5400)
  | 794 => some (.leaf 3469)
  | 795 => some (.leaf 3470)
  | 796 => some (.triangle 10 5386 5403)
  | 797 => some (.leaf 3471)
  | 798 => some (.triangle 10 5386 5405)
  | 799 => some (.leaf 3472)
  | 800 => some (.positive 1 (![5404, 2665, 2633, 5406, 5407, 5394]))
  | 801 => some (.triangle 18 5408 5396)
  | 802 => some (.triangle 17 5409 5398)
  | 803 => some (.triangle 16 5410 5400)
  | 804 => some (.leaf 3473)
  | 805 => some (.leaf 3474)
  | 806 => some (.leaf 3475)
  | 807 => some (.positive 0 (![5401, 5402, 5411, 5412, 5413, 5414]))
  | 808 => some (.triangle 12 1879 5415)
  | 809 => some (.leaf 3476)
  | 810 => some (.triangle 13 5416 5417)
  | 811 => some (.leaf 3477)
  | 812 => some (.leaf 3478)
  | 813 => some (.leaf 3479)
  | 814 => some (.leaf 3480)
  | 815 => some (.leaf 3481)
  | 816 => some (.leaf 3482)
  | 817 => some (.leaf 3483)
  | 818 => some (.leaf 3484)
  | 819 => some (.leaf 3485)
  | 820 => some (.leaf 3486)
  | 821 => some (.leaf 3487)
  | 822 => some (.triangle 10 5386 5429)
  | 823 => some (.leaf 3488)
  | 824 => some (.triangle 10 5386 5431)
  | 825 => some (.leaf 3489)
  | 826 => some (.leaf 3490)
  | 827 => some (.positive 1 (![5430, 2665, 2633, 5432, 5433, 5434]))
  | 828 => some (.leaf 3491)
  | 829 => some (.triangle 18 5435 5436)
  | 830 => some (.leaf 3492)
  | 831 => some (.triangle 17 5437 5438)
  | 832 => some (.leaf 3493)
  | 833 => some (.leaf 3494)
  | 834 => some (.triangle 17 5440 5441)
  | 835 => some (.triangle 18 5442 5436)
  | 836 => some (.triangle 16 5439 5443)
  | 837 => some (.leaf 3495)
  | 838 => some (.leaf 3496)
  | 839 => some (.positive 0 (![5426, 5427, 5428, 5444, 5445, 5446]))
  | 840 => some (.triangle 12 1879 5447)
  | 841 => some (.triangle 13 5448 5358)
  | 842 => some (.leaf 3497)
  | 843 => some (.leaf 3498)
  | 844 => some (.leaf 3499)
  | 845 => some (.leaf 3500)
  | 846 => some (.leaf 3501)
  | 847 => some (.triangle 10 5386 5454)
  | 848 => some (.leaf 3502)
  | 849 => some (.leaf 3503)
  | 850 => some (.positive 1 (![5453, 2665, 2666, 5455, 5456, 5457]))
  | 851 => some (.leaf 3504)
  | 852 => some (.triangle 18 5458 5459)
  | 853 => some (.leaf 3505)
  | 854 => some (.triangle 17 5460 5461)
  | 855 => some (.leaf 3506)
  | 856 => some (.triangle 18 5463 5459)
  | 857 => some (.triangle 16 5462 5464)
  | 858 => some (.leaf 3507)
  | 859 => some (.leaf 3508)
  | 860 => some (.positive 0 (![5450, 5451, 5452, 5465, 5466, 5467]))
  | 861 => some (.triangle 12 1879 5468)
  | 862 => some (.triangle 13 5469 5358)
  | 863 => some (.leaf 3509)
  | 864 => some (.leaf 3510)
  | 865 => some (.leaf 3511)
  | 866 => some (.leaf 3512)
  | 867 => some (.leaf 3513)
  | 868 => some (.leaf 3514)
  | 869 => some (.leaf 3515)
  | 870 => some (.leaf 3516)
  | 871 => some (.positive 1 (![5475, 5476, 5477, 5478, 2760, 5457]))
  | 872 => some (.leaf 3517)
  | 873 => some (.triangle 18 5479 5480)
  | 874 => some (.leaf 3518)
  | 875 => some (.triangle 17 5481 5482)
  | 876 => some (.leaf 3519)
  | 877 => some (.triangle 18 5484 5480)
  | 878 => some (.triangle 16 5483 5485)
  | 879 => some (.leaf 3520)
  | 880 => some (.positive 0 (![5472, 5473, 5474, 5486, 5466, 5487]))
  | 881 => some (.triangle 12 5471 5488)
  | 882 => some (.leaf 3521)
  | 883 => some (.triangle 13 5489 5490)
  | 884 => some (.leaf 3522)
  | 885 => some (.leaf 3523)
  | 886 => some (.leaf 3524)
  | 887 => some (.leaf 3525)
  | 888 => some (.leaf 3526)
  | 889 => some (.leaf 3527)
  | 890 => some (.leaf 3528)
  | 891 => some (.leaf 3529)
  | 892 => some (.leaf 3530)
  | 893 => some (.leaf 3531)
  | 894 => some (.heavy (![5418, 5419, 5420, 5421, 5422, 5423, 5424, 5425, 5449, 5470, 5491, 5492, 5493, 5494, 5495, 5496, 5497, 5498, 5499, 5500, 5501]))
  | 895 => some (.triangle 6 5385 5502)
  | 896 => some (.leaf 3532)
  | 897 => some (.leaf 3533)
  | 898 => some (.leaf 3534)
  | 899 => some (.triangle 10 5505 5506)
  | 900 => some (.leaf 3535)
  | 901 => some (.leaf 3536)
  | 902 => some (.triangle 19 5508 5509)
  | 903 => some (.triangle 10 5505 5510)
  | 904 => some (.leaf 3537)
  | 905 => some (.leaf 3538)
  | 906 => some (.positive 1 (![5507, 4478, 3812, 5511, 5512, 5513]))
  | 907 => some (.triangle 6 3552 5514)
  | 908 => some (.triangle 18 5515 2170)
  | 909 => some (.triangle 5 4457 5516)
  | 910 => some (.triangle 17 5517 2452)
  | 911 => some (.triangle 16 5518 2536)
  | 912 => some (.triangle 4 5504 5519)
  | 913 => some (.leaf 3539)
  | 914 => some (.leaf 3540)
  | 915 => some (.leaf 3541)
  | 916 => some (.triangle 10 5505 5523)
  | 917 => some (.leaf 3542)
  | 918 => some (.triangle 10 5505 5525)
  | 919 => some (.leaf 3543)
  | 920 => some (.positive 1 (![5524, 4478, 3812, 5526, 5527, 5513]))
  | 921 => some (.triangle 6 3552 5528)
  | 922 => some (.triangle 18 5529 2170)
  | 923 => some (.triangle 5 4457 5530)
  | 924 => some (.triangle 17 5531 2452)
  | 925 => some (.triangle 16 5532 2536)
  | 926 => some (.triangle 4 5504 5533)
  | 927 => some (.leaf 3544)
  | 928 => some (.leaf 3545)
  | 929 => some (.positive 0 (![5520, 5521, 5522, 5534, 5535, 5536]))
  | 930 => some (.leaf 3546)
  | 931 => some (.triangle 15 5537 5538)
  | 932 => some (.leaf 3547)
  | 933 => some (.triangle 14 5539 5540)
  | 934 => some (.leaf 3548)
  | 935 => some (.triangle 13 5541 5542)
  | 936 => some (.leaf 3549)
  | 937 => some (.leaf 3550)
  | 938 => some (.leaf 3551)
  | 939 => some (.leaf 3552)
  | 940 => some (.leaf 3553)
  | 941 => some (.leaf 3554)
  | 942 => some (.leaf 3555)
  | 943 => some (.leaf 3556)
  | 944 => some (.leaf 3557)
  | 945 => some (.leaf 3558)
  | 946 => some (.leaf 3559)
  | 947 => some (.leaf 3560)
  | 948 => some (.leaf 3561)
  | 949 => some (.leaf 3562)
  | 950 => some (.leaf 3563)
  | 951 => some (.leaf 3564)
  | 952 => some (.leaf 3565)
  | 953 => some (.leaf 3566)
  | 954 => some (.leaf 3567)
  | 955 => some (.triangle 10 5561 5562)
  | 956 => some (.leaf 3568)
  | 957 => some (.leaf 3569)
  | 958 => some (.positive 1 (![5558, 5559, 5560, 5563, 5564, 5565]))
  | 959 => some (.triangle 6 5557 5566)
  | 960 => some (.triangle 18 5567 2170)
  | 961 => some (.triangle 5 5556 5568)
  | 962 => some (.triangle 17 5569 2452)
  | 963 => some (.triangle 16 5570 2536)
  | 964 => some (.triangle 4 5504 5571)
  | 965 => some (.leaf 3570)
  | 966 => some (.positive 0 (![5552, 5553, 5554, 5555, 5572, 5573]))
  | 967 => some (.triangle 15 5574 4448)
  | 968 => some (.triangle 14 5575 5170)
  | 969 => some (.triangle 13 5576 5358)
  | 970 => some (.leaf 3571)
  | 971 => some (.leaf 3572)
  | 972 => some (.leaf 3573)
  | 973 => some (.leaf 3574)
  | 974 => some (.leaf 3575)
  | 975 => some (.leaf 3576)
  | 976 => some (.leaf 3577)
  | 977 => some (.leaf 3578)
  | 978 => some (.leaf 3579)
  | 979 => some (.positive 1 (![5582, 5583, 5584, 5585, 2760, 5586]))
  | 980 => some (.triangle 6 5557 5587)
  | 981 => some (.triangle 18 5588 2170)
  | 982 => some (.triangle 5 5556 5589)
  | 983 => some (.leaf 3580)
  | 984 => some (.triangle 17 5590 5591)
  | 985 => some (.leaf 3581)
  | 986 => some (.triangle 16 5592 5593)
  | 987 => some (.triangle 4 5504 5594)
  | 988 => some (.leaf 3582)
  | 989 => some (.positive 0 (![5578, 5579, 5580, 5581, 5595, 5596]))
  | 990 => some (.leaf 3583)
  | 991 => some (.triangle 15 5597 5598)
  | 992 => some (.leaf 3584)
  | 993 => some (.triangle 14 5599 5600)
  | 994 => some (.leaf 3585)
  | 995 => some (.triangle 13 5601 5602)
  | 996 => some (.leaf 3586)
  | 997 => some (.leaf 3587)
  | 998 => some (.leaf 3588)
  | 999 => some (.leaf 3589)
  | 1000 => some (.leaf 3590)
  | 1001 => some (.leaf 3591)
  | 1002 => some (.leaf 3592)
  | 1003 => some (.leaf 3593)
  | 1004 => some (.leaf 3594)
  | 1005 => some (.leaf 3595)
  | 1006 => some (.heavy (![5543, 5544, 5545, 5546, 5547, 5548, 5549, 5550, 5551, 5577, 5603, 5604, 5605, 5606, 5607, 5608, 5609, 5610, 5611, 5612, 5613]))
  | 1007 => some (.triangle 3 5503 5614)
  | 1008 => some (.leaf 3596)
  | 1009 => some (.leaf 3597)
  | 1010 => some (.leaf 3598)
  | 1011 => some (.leaf 3599)
  | 1012 => some (.leaf 3600)
  | 1013 => some (.triangle 10 5619 5620)
  | 1014 => some (.leaf 3601)
  | 1015 => some (.leaf 3602)
  | 1016 => some (.leaf 3603)
  | 1017 => some (.positive 1 (![5621, 4671, 4672, 5622, 5623, 5624]))
  | 1018 => some (.triangle 18 4669 5625)
  | 1019 => some (.triangle 5 4021 5626)
  | 1020 => some (.triangle 17 5627 2452)
  | 1021 => some (.triangle 16 5628 2536)
  | 1022 => some (.triangle 4 5367 5629)
  | 1023 => some (.leaf 3604)
  | 1024 => some (.leaf 3605)
  | 1025 => some (.positive 0 (![5616, 5617, 5618, 5630, 5631, 5632]))
  | 1026 => some (.triangle 3 4640 5633)
  | 1027 => some (.triangle 15 5634 4645)
  | 1028 => some (.leaf 3606)
  | 1029 => some (.triangle 14 5635 5636)
  | 1030 => some (.leaf 3607)
  | 1031 => some (.triangle 13 5637 5638)
  | 1032 => some (.leaf 3608)
  | 1033 => some (.leaf 3609)
  | 1034 => some (.leaf 3610)
  | 1035 => some (.leaf 3611)
  | 1036 => some (.leaf 3612)
  | 1037 => some (.leaf 3613)
  | 1038 => some (.leaf 3614)
  | 1039 => some (.leaf 3615)
  | 1040 => some (.leaf 3616)
  | 1041 => some (.leaf 3617)
  | 1042 => some (.triangle 15 5649 4645)
  | 1043 => some (.leaf 3618)
  | 1044 => some (.triangle 14 5650 5651)
  | 1045 => some (.leaf 3619)
  | 1046 => some (.triangle 13 5652 5653)
  | 1047 => some (.leaf 3620)
  | 1048 => some (.leaf 3621)
  | 1049 => some (.leaf 3622)
  | 1050 => some (.leaf 3623)
  | 1051 => some (.leaf 3624)
  | 1052 => some (.leaf 3625)
  | 1053 => some (.leaf 3626)
  | 1054 => some (.leaf 3627)
  | 1055 => some (.leaf 3628)
  | 1056 => some (.heavy (![5639, 5640, 5641, 5642, 5643, 5644, 5645, 5646, 5647, 5648, 5654, 5655, 5656, 5657, 5658, 5659, 5660, 5661, 5662, 5647, 5663]))
  | 1057 => some (.triangle 9 5615 5664)
  | 1058 => some (.triangle 2 5335 5665)
  | 1059 => some (.leaf 3629)
  | 1060 => some (.leaf 3630)
  | 1061 => some (.leaf 3631)
  | 1062 => some (.triangle 11 5668 5669)
  | 1063 => some (.triangle 3 5667 5670)
  | 1064 => some (.leaf 3632)
  | 1065 => some (.triangle 14 5671 5672)
  | 1066 => some (.leaf 3633)
  | 1067 => some (.leaf 3634)
  | 1068 => some (.leaf 3635)
  | 1069 => some (.leaf 3636)
  | 1070 => some (.leaf 3637)
  | 1071 => some (.leaf 3638)
  | 1072 => some (.leaf 3639)
  | 1073 => some (.leaf 3640)
  | 1074 => some (.leaf 3641)
  | 1075 => some (.triangle 14 5682 5672)
  | 1076 => some (.leaf 3642)
  | 1077 => some (.triangle 14 5684 5672)
  | 1078 => some (.leaf 3643)
  | 1079 => some (.leaf 3644)
  | 1080 => some (.leaf 3645)
  | 1081 => some (.leaf 3646)
  | 1082 => some (.leaf 3647)
  | 1083 => some (.leaf 3648)
  | 1084 => some (.leaf 3649)
  | 1085 => some (.leaf 3650)
  | 1086 => some (.heavy (![5673, 5674, 5675, 5676, 5677, 5678, 5679, 5680, 5681, 5683, 5685, 5686, 5687, 5688, 5689, 5690, 5680, 5680, 5691, 5692, 5693]))
  | 1087 => some (.leaf 3651)
  | 1088 => some (.leaf 3652)
  | 1089 => some (.leaf 3653)
  | 1090 => some (.leaf 3654)
  | 1091 => some (.leaf 3655)
  | 1092 => some (.leaf 3656)
  | 1093 => some (.leaf 3657)
  | 1094 => some (.leaf 3658)
  | 1095 => some (.leaf 3659)
  | 1096 => some (.leaf 3660)
  | 1097 => some (.positive 2 (![5699, 5700, 5701, 5702, 5703, 5704]))
  | 1098 => some (.triangle 4 5698 5705)
  | 1099 => some (.leaf 3661)
  | 1100 => some (.leaf 3662)
  | 1101 => some (.leaf 3663)
  | 1102 => some (.leaf 3664)
  | 1103 => some (.positive 1 (![5706, 5707, 5708, 5709, 4301, 5710]))
  | 1104 => some (.triangle 17 5697 5711)
  | 1105 => some (.leaf 3665)
  | 1106 => some (.triangle 16 5712 5713)
  | 1107 => some (.leaf 3666)
  | 1108 => some (.leaf 3667)
  | 1109 => some (.leaf 3668)
  | 1110 => some (.positive 0 (![5695, 5696, 5714, 5715, 5716, 5717]))
  | 1111 => some (.triangle 11 2017 5718)
  | 1112 => some (.triangle 3 5667 5719)
  | 1113 => some (.triangle 14 5720 5672)
  | 1114 => some (.leaf 3669)
  | 1115 => some (.leaf 3670)
  | 1116 => some (.leaf 3671)
  | 1117 => some (.leaf 3672)
  | 1118 => some (.leaf 3673)
  | 1119 => some (.leaf 3674)
  | 1120 => some (.leaf 3675)
  | 1121 => some (.leaf 3676)
  | 1122 => some (.leaf 3677)
  | 1123 => some (.leaf 3678)
  | 1124 => some (.triangle 14 5731 5672)
  | 1125 => some (.leaf 3679)
  | 1126 => some (.leaf 3680)
  | 1127 => some (.leaf 3681)
  | 1128 => some (.leaf 3682)
  | 1129 => some (.leaf 3683)
  | 1130 => some (.leaf 3684)
  | 1131 => some (.leaf 3685)
  | 1132 => some (.leaf 3686)
  | 1133 => some (.leaf 3687)
  | 1134 => some (.heavy (![5721, 5722, 5723, 5724, 5725, 5726, 5727, 5728, 5729, 5730, 5732, 5733, 5734, 5735, 5736, 5737, 5738, 5728, 5739, 5740, 5741]))
  | 1135 => some (.triangle 5 5694 5742)
  | 1136 => some (.leaf 3688)
  | 1137 => some (.leaf 3689)
  | 1138 => some (.leaf 3690)
  | 1139 => some (.leaf 3691)
  | 1140 => some (.leaf 3692)
  | 1141 => some (.leaf 3693)
  | 1142 => some (.leaf 3694)
  | 1143 => some (.leaf 3695)
  | 1144 => some (.leaf 3696)
  | 1145 => some (.leaf 3697)
  | 1146 => some (.leaf 3698)
  | 1147 => some (.leaf 3699)
  | 1148 => some (.positive 2 (![5750, 5751, 5752, 5753, 5754, 5755]))
  | 1149 => some (.leaf 3700)
  | 1150 => some (.positive 1 (![5756, 4298, 4299, 5709, 4301, 5757]))
  | 1151 => some (.triangle 5 5749 5758)
  | 1152 => some (.triangle 17 5748 5759)
  | 1153 => some (.triangle 16 5760 2536)
  | 1154 => some (.triangle 4 5367 5761)
  | 1155 => some (.leaf 3701)
  | 1156 => some (.leaf 3702)
  | 1157 => some (.positive 0 (![5745, 5746, 5747, 5762, 5763, 5764]))
  | 1158 => some (.triangle 3 5744 5765)
  | 1159 => some (.triangle 15 5766 4645)
  | 1160 => some (.leaf 3703)
  | 1161 => some (.triangle 14 5767 5768)
  | 1162 => some (.leaf 3704)
  | 1163 => some (.triangle 13 5769 5770)
  | 1164 => some (.leaf 3705)
  | 1165 => some (.leaf 3706)
  | 1166 => some (.leaf 3707)
  | 1167 => some (.leaf 3708)
  | 1168 => some (.leaf 3709)
  | 1169 => some (.leaf 3710)
  | 1170 => some (.leaf 3711)
  | 1171 => some (.leaf 3712)
  | 1172 => some (.leaf 3713)
  | 1173 => some (.leaf 3714)
  | 1174 => some (.triangle 14 5781 5768)
  | 1175 => some (.leaf 3715)
  | 1176 => some (.triangle 13 5782 5783)
  | 1177 => some (.leaf 3716)
  | 1178 => some (.leaf 3717)
  | 1179 => some (.leaf 3718)
  | 1180 => some (.leaf 3719)
  | 1181 => some (.leaf 3720)
  | 1182 => some (.leaf 3721)
  | 1183 => some (.leaf 3722)
  | 1184 => some (.leaf 3723)
  | 1185 => some (.heavy (![5771, 5772, 5773, 5774, 5775, 5776, 5777, 5778, 5779, 5780, 5784, 5785, 5786, 5787, 5788, 5789, 5790, 5778, 5791, 5779, 5792]))
  | 1186 => some (.triangle 2 5743 5793)
  | 1187 => some (.triangle 8 5666 5794)
  | 1188 => some (.leaf 3724)
  | 1189 => some (.leaf 3725)
  | 1190 => some (.leaf 3726)
  | 1191 => some (.triangle 12 5797 5798)
  | 1192 => some (.triangle 2 5796 5799)
  | 1193 => some (.leaf 3727)
  | 1194 => some (.triangle 13 5800 5801)
  | 1195 => some (.leaf 3728)
  | 1196 => some (.leaf 3729)
  | 1197 => some (.leaf 3730)
  | 1198 => some (.leaf 3731)
  | 1199 => some (.leaf 3732)
  | 1200 => some (.leaf 3733)
  | 1201 => some (.leaf 3734)
  | 1202 => some (.leaf 3735)
  | 1203 => some (.leaf 3736)
  | 1204 => some (.triangle 13 5811 5801)
  | 1205 => some (.leaf 3737)
  | 1206 => some (.triangle 13 5813 5801)
  | 1207 => some (.leaf 3738)
  | 1208 => some (.leaf 3739)
  | 1209 => some (.leaf 3740)
  | 1210 => some (.leaf 3741)
  | 1211 => some (.leaf 3742)
  | 1212 => some (.leaf 3743)
  | 1213 => some (.leaf 3744)
  | 1214 => some (.leaf 3745)
  | 1215 => some (.heavy (![5802, 5803, 5804, 5805, 5806, 5807, 5808, 5809, 5810, 5812, 5814, 5815, 5816, 5817, 5818, 5819, 5809, 5809, 5820, 5821, 5822]))
  | 1216 => some (.leaf 3746)
  | 1217 => some (.leaf 3747)
  | 1218 => some (.leaf 3748)
  | 1219 => some (.leaf 3749)
  | 1220 => some (.leaf 3750)
  | 1221 => some (.leaf 3751)
  | 1222 => some (.leaf 3752)
  | 1223 => some (.leaf 3753)
  | 1224 => some (.leaf 3754)
  | 1225 => some (.leaf 3755)
  | 1226 => some (.positive 2 (![5828, 5829, 5830, 5831, 5832, 5833]))
  | 1227 => some (.triangle 4 5827 5834)
  | 1228 => some (.leaf 3756)
  | 1229 => some (.leaf 3757)
  | 1230 => some (.leaf 3758)
  | 1231 => some (.leaf 3759)
  | 1232 => some (.leaf 3760)
  | 1233 => some (.positive 1 (![5835, 5836, 5837, 5838, 5839, 5840]))
  | 1234 => some (.leaf 3761)
  | 1235 => some (.triangle 17 5841 5842)
  | 1236 => some (.leaf 3762)
  | 1237 => some (.triangle 18 5843 5844)
  | 1238 => some (.triangle 16 5826 5845)
  | 1239 => some (.leaf 3763)
  | 1240 => some (.leaf 3764)
  | 1241 => some (.leaf 3765)
  | 1242 => some (.positive 0 (![5824, 5825, 5846, 5847, 5848, 5849]))
  | 1243 => some (.triangle 12 1879 5850)
  | 1244 => some (.triangle 2 5796 5851)
  | 1245 => some (.triangle 13 5852 5801)
  | 1246 => some (.leaf 3766)
  | 1247 => some (.leaf 3767)
  | 1248 => some (.leaf 3768)
  | 1249 => some (.leaf 3769)
  | 1250 => some (.leaf 3770)
  | 1251 => some (.leaf 3771)
  | 1252 => some (.leaf 3772)
  | 1253 => some (.leaf 3773)
  | 1254 => some (.leaf 3774)
  | 1255 => some (.leaf 3775)
  | 1256 => some (.triangle 13 5863 5801)
  | 1257 => some (.leaf 3776)
  | 1258 => some (.leaf 3777)
  | 1259 => some (.leaf 3778)
  | 1260 => some (.leaf 3779)
  | 1261 => some (.leaf 3780)
  | 1262 => some (.leaf 3781)
  | 1263 => some (.leaf 3782)
  | 1264 => some (.leaf 3783)
  | 1265 => some (.leaf 3784)
  | 1266 => some (.heavy (![5853, 5854, 5855, 5856, 5857, 5858, 5859, 5860, 5861, 5862, 5864, 5865, 5866, 5867, 5868, 5869, 5870, 5860, 5871, 5872, 5873]))
  | 1267 => some (.triangle 6 5823 5874)
  | 1268 => some (.leaf 3785)
  | 1269 => some (.leaf 3786)
  | 1270 => some (.leaf 3787)
  | 1271 => some (.leaf 3788)
  | 1272 => some (.leaf 3789)
  | 1273 => some (.leaf 3790)
  | 1274 => some (.leaf 3791)
  | 1275 => some (.leaf 3792)
  | 1276 => some (.leaf 3793)
  | 1277 => some (.positive 2 (![5879, 5880, 5881, 5882, 5883, 5884]))
  | 1278 => some (.leaf 3794)
  | 1279 => some (.positive 1 (![5885, 3835, 3836, 5838, 3837, 5886]))
  | 1280 => some (.triangle 6 5878 5887)
  | 1281 => some (.triangle 17 5888 2452)
  | 1282 => some (.leaf 3795)
  | 1283 => some (.triangle 18 5889 5890)
  | 1284 => some (.triangle 16 3813 5891)
  | 1285 => some (.triangle 4 5179 5892)
  | 1286 => some (.leaf 3796)
  | 1287 => some (.leaf 3797)
  | 1288 => some (.positive 0 (![5876, 5877, 5522, 5893, 5894, 5895]))
  | 1289 => some (.leaf 3798)
  | 1290 => some (.triangle 15 5896 5897)
  | 1291 => some (.leaf 3799)
  | 1292 => some (.triangle 14 5898 5899)
  | 1293 => some (.triangle 13 5900 5801)
  | 1294 => some (.leaf 3800)
  | 1295 => some (.leaf 3801)
  | 1296 => some (.leaf 3802)
  | 1297 => some (.leaf 3803)
  | 1298 => some (.leaf 3804)
  | 1299 => some (.leaf 3805)
  | 1300 => some (.leaf 3806)
  | 1301 => some (.leaf 3807)
  | 1302 => some (.leaf 3808)
  | 1303 => some (.leaf 3809)
  | 1304 => some (.triangle 13 5911 5801)
  | 1305 => some (.leaf 3810)
  | 1306 => some (.leaf 3811)
  | 1307 => some (.leaf 3812)
  | 1308 => some (.leaf 3813)
  | 1309 => some (.leaf 3814)
  | 1310 => some (.leaf 3815)
  | 1311 => some (.leaf 3816)
  | 1312 => some (.leaf 3817)
  | 1313 => some (.heavy (![5901, 5902, 5903, 5904, 5905, 5906, 5907, 5908, 5909, 5910, 5912, 5913, 5914, 5915, 5916, 5917, 5918, 5908, 5919, 5909, 5920]))
  | 1314 => some (.triangle 3 5875 5921)
  | 1315 => some (.leaf 3818)
  | 1316 => some (.leaf 3819)
  | 1317 => some (.leaf 3820)
  | 1318 => some (.leaf 3821)
  | 1319 => some (.leaf 3822)
  | 1320 => some (.leaf 3823)
  | 1321 => some (.leaf 3824)
  | 1322 => some (.leaf 3825)
  | 1323 => some (.leaf 3826)
  | 1324 => some (.leaf 3827)
  | 1325 => some (.leaf 3828)
  | 1326 => some (.leaf 3829)
  | 1327 => some (.leaf 3830)
  | 1328 => some (.leaf 3831)
  | 1329 => some (.leaf 3832)
  | 1330 => some (.leaf 3833)
  | 1331 => some (.leaf 3834)
  | 1332 => some (.positive 3 (![5934, 5935, 5936, 5937, 5938, 5939]))
  | 1333 => some (.triangle 6 5933 5940)
  | 1334 => some (.positive 2 (![5928, 5929, 5930, 5931, 5932, 5941]))
  | 1335 => some (.leaf 3835)
  | 1336 => some (.triangle 19 5942 5943)
  | 1337 => some (.leaf 3836)
  | 1338 => some (.leaf 3837)
  | 1339 => some (.leaf 3838)
  | 1340 => some (.leaf 3839)
  | 1341 => some (.positive 1 (![5944, 5945, 5946, 5947, 3846, 5948]))
  | 1342 => some (.triangle 17 5927 5949)
  | 1343 => some (.leaf 3840)
  | 1344 => some (.triangle 18 5950 5951)
  | 1345 => some (.triangle 16 5926 5952)
  | 1346 => some (.triangle 4 4775 5953)
  | 1347 => some (.leaf 3841)
  | 1348 => some (.leaf 3842)
  | 1349 => some (.positive 0 (![5923, 5924, 5925, 5954, 5955, 5956]))
  | 1350 => some (.triangle 3 5667 5957)
  | 1351 => some (.leaf 3843)
  | 1352 => some (.triangle 15 5958 5959)
  | 1353 => some (.triangle 2 5796 5960)
  | 1354 => some (.leaf 3844)
  | 1355 => some (.triangle 14 5961 5962)
  | 1356 => some (.triangle 13 5963 5801)
  | 1357 => some (.leaf 3845)
  | 1358 => some (.leaf 3846)
  | 1359 => some (.leaf 3847)
  | 1360 => some (.leaf 3848)
  | 1361 => some (.leaf 3849)
  | 1362 => some (.leaf 3850)
  | 1363 => some (.leaf 3851)
  | 1364 => some (.leaf 3852)
  | 1365 => some (.leaf 3853)
  | 1366 => some (.leaf 3854)
  | 1367 => some (.triangle 13 5974 5801)
  | 1368 => some (.leaf 3855)
  | 1369 => some (.leaf 3856)
  | 1370 => some (.leaf 3857)
  | 1371 => some (.leaf 3858)
  | 1372 => some (.leaf 3859)
  | 1373 => some (.leaf 3860)
  | 1374 => some (.leaf 3861)
  | 1375 => some (.leaf 3862)
  | 1376 => some (.heavy (![5964, 5965, 5966, 5967, 5968, 5969, 5970, 5971, 5972, 5973, 5975, 5976, 5977, 5978, 5979, 5980, 5973, 5981, 5982, 5972, 5983]))
  | 1377 => some (.triangle 8 5922 5984)
  | 1378 => some (.leaf 3863)
  | 1379 => some (.leaf 3864)
  | 1380 => some (.leaf 3865)
  | 1381 => some (.leaf 3866)
  | 1382 => some (.leaf 3867)
  | 1383 => some (.leaf 3868)
  | 1384 => some (.leaf 3869)
  | 1385 => some (.triangle 19 5991 5992)
  | 1386 => some (.leaf 3870)
  | 1387 => some (.leaf 3871)
  | 1388 => some (.leaf 3872)
  | 1389 => some (.leaf 3873)
  | 1390 => some (.positive 1 (![5993, 5994, 5995, 5996, 3850, 5997]))
  | 1391 => some (.triangle 18 5990 5998)
  | 1392 => some (.triangle 16 5926 5999)
  | 1393 => some (.triangle 4 4775 6000)
  | 1394 => some (.leaf 3874)
  | 1395 => some (.leaf 3875)
  | 1396 => some (.positive 0 (![5987, 5988, 5989, 6001, 6002, 6003]))
  | 1397 => some (.triangle 3 5986 6004)
  | 1398 => some (.leaf 3876)
  | 1399 => some (.triangle 15 6005 6006)
  | 1400 => some (.triangle 2 5796 6007)
  | 1401 => some (.triangle 14 6008 5962)
  | 1402 => some (.triangle 13 6009 5801)
  | 1403 => some (.leaf 3877)
  | 1404 => some (.leaf 3878)
  | 1405 => some (.leaf 3879)
  | 1406 => some (.leaf 3880)
  | 1407 => some (.leaf 3881)
  | 1408 => some (.leaf 3882)
  | 1409 => some (.leaf 3883)
  | 1410 => some (.leaf 3884)
  | 1411 => some (.leaf 3885)
  | 1412 => some (.leaf 3886)
  | 1413 => some (.triangle 13 6020 5801)
  | 1414 => some (.leaf 3887)
  | 1415 => some (.leaf 3888)
  | 1416 => some (.leaf 3889)
  | 1417 => some (.leaf 3890)
  | 1418 => some (.leaf 3891)
  | 1419 => some (.leaf 3892)
  | 1420 => some (.leaf 3893)
  | 1421 => some (.leaf 3894)
  | 1422 => some (.heavy (![6010, 6011, 6012, 6013, 6014, 6015, 6016, 6017, 6018, 6019, 6021, 6022, 6023, 6024, 6025, 6026, 6027, 6017, 6028, 6018, 6029]))
  | 1423 => some (.triangle 9 5985 6030)
  | 1424 => some (.triangle 7 5795 6031)
  | 1425 => some (.triangle 1 4722 6032)
  | 1426 => some (.leaf 3895)
  | 1427 => some (.leaf 3896)
  | 1428 => some (.triangle 13 6034 6035)
  | 1429 => some (.leaf 3897)
  | 1430 => some (.leaf 3898)
  | 1431 => some (.leaf 3899)
  | 1432 => some (.leaf 3900)
  | 1433 => some (.leaf 3901)
  | 1434 => some (.leaf 3902)
  | 1435 => some (.leaf 3903)
  | 1436 => some (.leaf 3904)
  | 1437 => some (.leaf 3905)
  | 1438 => some (.leaf 3906)
  | 1439 => some (.leaf 3907)
  | 1440 => some (.leaf 3908)
  | 1441 => some (.leaf 3909)
  | 1442 => some (.leaf 3910)
  | 1443 => some (.positive 0 (![6045, 6046, 6047, 6048, 6049, 6050]))
  | 1444 => some (.leaf 3911)
  | 1445 => some (.triangle 15 6051 6052)
  | 1446 => some (.leaf 3912)
  | 1447 => some (.triangle 14 6053 6054)
  | 1448 => some (.leaf 3913)
  | 1449 => some (.leaf 3914)
  | 1450 => some (.triangle 14 6056 6057)
  | 1451 => some (.leaf 3915)
  | 1452 => some (.triangle 15 6058 6059)
  | 1453 => some (.triangle 13 6055 6060)
  | 1454 => some (.leaf 3916)
  | 1455 => some (.leaf 3917)
  | 1456 => some (.leaf 3918)
  | 1457 => some (.positive 0 (![6062, 6063, 6047, 6048, 6049, 6064]))
  | 1458 => some (.leaf 3919)
  | 1459 => some (.leaf 3920)
  | 1460 => some (.leaf 3921)
  | 1461 => some (.leaf 3922)
  | 1462 => some (.leaf 3923)
  | 1463 => some (.leaf 3924)
  | 1464 => some (.positive 0 (![6066, 6067, 6068, 6069, 6070, 6071]))
  | 1465 => some (.triangle 15 6065 6072)
  | 1466 => some (.leaf 3925)
  | 1467 => some (.triangle 14 6073 6074)
  | 1468 => some (.leaf 3926)
  | 1469 => some (.leaf 3927)
  | 1470 => some (.leaf 3928)
  | 1471 => some (.leaf 3929)
  | 1472 => some (.leaf 3930)
  | 1473 => some (.leaf 3931)
  | 1474 => some (.positive 0 (![6076, 6077, 6078, 6079, 6080, 6081]))
  | 1475 => some (.triangle 14 6056 6082)
  | 1476 => some (.leaf 3932)
  | 1477 => some (.leaf 3933)
  | 1478 => some (.leaf 3934)
  | 1479 => some (.leaf 3935)
  | 1480 => some (.leaf 3936)
  | 1481 => some (.leaf 3937)
  | 1482 => some (.leaf 3938)
  | 1483 => some (.leaf 3939)
  | 1484 => some (.triangle 19 6090 6091)
  | 1485 => some (.leaf 3940)
  | 1486 => some (.leaf 3941)
  | 1487 => some (.leaf 3942)
  | 1488 => some (.positive 1 (![6088, 6089, 6092, 6093, 6094, 6095]))
  | 1489 => some (.triangle 18 6087 6096)
  | 1490 => some (.triangle 16 6086 6097)
  | 1491 => some (.leaf 3943)
  | 1492 => some (.leaf 3944)
  | 1493 => some (.leaf 3945)
  | 1494 => some (.positive 0 (![6084, 6085, 6098, 6099, 6100, 6101]))
  | 1495 => some (.triangle 15 6083 6102)
  | 1496 => some (.triangle 13 6075 6103)
  | 1497 => some (.leaf 3946)
  | 1498 => some (.leaf 3947)
  | 1499 => some (.leaf 3948)
  | 1500 => some (.leaf 3949)
  | 1501 => some (.leaf 3950)
  | 1502 => some (.leaf 3951)
  | 1503 => some (.leaf 3952)
  | 1504 => some (.leaf 3953)
  | 1505 => some (.leaf 3954)
  | 1506 => some (.leaf 3955)
  | 1507 => some (.heavy (![6036, 6037, 6038, 6039, 6040, 6041, 6042, 6043, 6044, 6061, 6104, 6105, 6106, 6107, 6108, 6109, 6110, 6111, 6112, 6113, 6114]))
  | 1508 => some (.leaf 3956)
  | 1509 => some (.leaf 3957)
  | 1510 => some (.triangle 13 6116 6117)
  | 1511 => some (.leaf 3958)
  | 1512 => some (.leaf 3959)
  | 1513 => some (.leaf 3960)
  | 1514 => some (.leaf 3961)
  | 1515 => some (.leaf 3962)
  | 1516 => some (.leaf 3963)
  | 1517 => some (.leaf 3964)
  | 1518 => some (.leaf 3965)
  | 1519 => some (.leaf 3966)
  | 1520 => some (.leaf 3967)
  | 1521 => some (.leaf 3968)
  | 1522 => some (.leaf 3969)
  | 1523 => some (.leaf 3970)
  | 1524 => some (.positive 0 (![6126, 6127, 6128, 6129, 6130, 6131]))
  | 1525 => some (.triangle 15 1161 6132)
  | 1526 => some (.leaf 3971)
  | 1527 => some (.triangle 14 6133 6134)
  | 1528 => some (.leaf 3972)
  | 1529 => some (.triangle 13 6135 6136)
  | 1530 => some (.leaf 3973)
  | 1531 => some (.leaf 3974)
  | 1532 => some (.leaf 3975)
  | 1533 => some (.leaf 3976)
  | 1534 => some (.positive 0 (![6138, 6139, 6128, 6129, 6140, 6141]))
  | 1535 => some (.triangle 15 1161 6142)
  | _ => none

end Jsp404.SevenLowerBranchShard03
