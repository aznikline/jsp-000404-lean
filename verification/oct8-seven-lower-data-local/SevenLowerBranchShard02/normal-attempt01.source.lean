import Jsp000404.SevenLowerReplay

/-! SOURCE_ONLY literal certificate data; no kernel PASS is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerBranchShard02
open SevenLowerReplay
def cycle0000 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (0), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![4, 5, 2, 0, 1]), .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 9 1, .triangle 2 1]

def cycle0001 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 2, 0, 1]), .triangle 1 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 3 1]

def cycle0002 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (4), (0), (-1), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .gapLower 1 5 (![0, 4, 5, 3, 2]), .gapLower 2 4 (![4, 5, 3, 0, 1]), .triangle 4 0, .triangle 16 0, .triangle 19 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 5, 3, 2])]

def cycle0003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1]), .triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 3 1]

def cycle0004 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 9 1, .triangle 2 1]

def cycle0005 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (0), (-1), (0), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 0, .triangle 16 2, .triangle 18 0, .triangle 15 0, .triangle 2 0]

def cycle0006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 3 0]

def cycle0007 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 5, 3, 2]), .triangle 1 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 9 1, .triangle 2 1]

def cycle0008 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 9 1, .triangle 2 1]

def cycle0009 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (0), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 9 1, .gapLower 4 2 (![2, 3, 0, 5, 1]), .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0010 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .gapLower 2 0 (![4, 5, 3, 0, 1]), .corridorUpper 1 2]

def cycle0011 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 2, .gapLower 2 1 (![4, 5, 3, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2]

def cycle0012 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 3 1]

def cycle0013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (4), (0), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .gapLower 2 4 (![5, 4, 3, 0, 1]), .triangle 4 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 5, 3, 2])]

def cycle0014 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1]), .triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 9 1, .triangle 2 1]

def cycle0015 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0016 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 2 1]

def cycle0017 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0018 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 0]

def cycle0019 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 1 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 9 1, .triangle 2 1]

def cycle0020 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 9 1, .triangle 2 1]

def cycle0021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 4, 5, 3, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0022 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .gapLower 0 5 (![1, 4, 5, 3, 2]), .triangle 4 0, .triangle 10 0, .triangle 0 0]

def cycle0023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 5, 3, 2])]

def cycle0024 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 5, 3, 2])]

def cycle0025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 5, 3, 2]), .triangle 1 0]

def cycle0026 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .gapLower 0 5 (![1, 4, 5, 3, 2]), .triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 0 0]

def cycle0027 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .gapLower 0 5 (![1, 4, 5, 3, 2]), .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 0 0]

def cycle0028 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (2), (-1), (-1), (-1), (0), (3), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 4, 5, 3, 2]), .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 5, 3, 2])]

def cycle0029 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .gapLower 0 5 (![1, 4, 5, 3, 2]), .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0030 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 5, 3, 2])]

def cycle0031 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 5, 3, 2])]

def cycle0032 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .gapLower 0 1 (![1, 4, 5, 3, 2])]

def cycle0033 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 9 1, .gapLower 0 1 (![1, 4, 5, 3, 2])]

def cycle0034 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![1, 4, 5, 3, 2]), .triangle 8 2, .triangle 9 1, .gapLower 0 1 (![1, 4, 5, 3, 2])]

def cycle0035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 4, 5, 3, 2]), .triangle 4 2, .triangle 8 2, .triangle 9 1, .gapLower 0 1 (![1, 4, 5, 3, 2])]

def cycle0036 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0037 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 4, 5, 3, 2]), .triangle 8 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0038 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .corridorLower 0 4, .gapLower 0 5 (![1, 4, 5, 3, 2])]

def cycle0039 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .distance 0 2]
    constant := ![(0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 1]
    strict := ![true, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .corridorLower 0 5, .gapLower 0 5 (![1, 4, 5, 3, 2])]

def cycle0040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![1, 4, 5, 3, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 5, 3, 2])]

def cycle0041 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 2, .triangle 5 0]

def cycle0042 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 2, .triangle 6 0]

def cycle0043 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 0, .gapLower 2 1 (![3, 4, 5, 0, 1]), .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0044 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-2), (-1), (4), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 0, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2]

def cycle0045 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 2, .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def cycle0046 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 19 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0047 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 19 0, .triangle 18 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0048 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 0, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1])]

def cycle0049 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 0]

def cycle0050 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .gapLower 2 0 (![3, 5, 4, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0051 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 2, .triangle 18 2, .gapLower 2 1 (![3, 5, 4, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-1), (0), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.triangle 7 0, .triangle 16 2, .gapLower 2 2 (![3, 5, 4, 0, 1]), .triangle 18 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0053 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 4 (![3, 5, 4, 0, 1])]

def cycle0054 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 0]

def cycle0055 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0056 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 0, .gapLower 2 0 (![4, 3, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0057 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 5, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 2, .gapLower 2 2 (![4, 3, 5, 0, 1]), .gapLower 2 1 (![4, 3, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def cycle0058 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 2, .gapLower 2 2 (![4, 3, 5, 0, 1]), .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 2 3 (![4, 3, 5, 0, 1]), .triangle 17 1, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0060 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 0, .gapLower 4 1 (![3, 2, 5, 0, 1]), .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 3, 5, 0, 1])]

def cycle0061 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 3, 5, 0, 1]), .triangle 0 0]

def cycle0062 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 0, .gapLower 2 0 (![4, 5, 3, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0063 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 2, .gapLower 2 1 (![4, 5, 3, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def cycle0064 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 0, .gapLower 4 1 (![3, 2, 5, 0, 1]), .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1])]

def cycle0065 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 0]

def cycle0066 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.triangle 4 0, .triangle 16 2, .triangle 18 0, .triangle 19 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0067 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.triangle 4 0, .triangle 16 0, .triangle 19 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0068 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 4 0, .triangle 16 2, .gapLower 2 1 (![5, 4, 3, 0, 1]), .corridorLower 2 5, .corridorUpper 1 2, .triangle 0 2]

def cycle0069 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 4 0, .gapLower 2 2 (![5, 4, 3, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def cycle0070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.gapLower 2 3 (![5, 4, 3, 0, 1]), .triangle 16 2, .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0071 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.triangle 4 0, .triangle 16 2, .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 4 (![5, 4, 3, 0, 1])]

def cycle0072 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 4, 3, 0, 1]), .triangle 0 0]

def cycle0073 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0074 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0075 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 0]

def cycle0076 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 1 0]

def cycle0077 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 0 0]

def cycle0078 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (0), (0), (-3)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0079 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0080 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 4 (![4, 3, 5, 0, 1])]

def cycle0082 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 3, 5, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .triangle 18 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1])]

def cycle0084 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0085 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![5, 4, 3, 0, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0086 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 4, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0087 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0088 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0089 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0090 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(0), (2), (0), (0), (0), (0), (-3)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0091 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(0), (-3), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, true] }
  origin := ![.triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0092 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-3), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 3 (![1, 5, 4, 3, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0093 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (0), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 5, 4, 3, 2]), .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0094 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (0), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, true, true, true, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 4, 3, 2])]

def cycle0095 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (4), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0096 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaLower 1, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0097 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (4), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .gapLower 2 4 (![3, 5, 4, 0, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0098 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaLower 1, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0099 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (4), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .gapLower 2 4 (![4, 3, 5, 0, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0100 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaLower 1, .thetaUpper 2, .gapLower 2 5 (![4, 3, 5, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0101 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (4), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .gapLower 2 4 (![4, 5, 3, 0, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0102 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaLower 1, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0103 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (4), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .gapLower 2 4 (![5, 4, 3, 0, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0104 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaLower 1, .thetaUpper 2, .gapLower 2 5 (![5, 4, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0105 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0106 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0107 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 5, 4, 0, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0108 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0109 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 3, 5, 0, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0110 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 3, 5, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0111 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0112 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0113 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![5, 4, 3, 0, 1]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0114 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 4, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0115 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0116 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0117 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0118 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0119 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-2), (0), (-1), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 9 1, .triangle 18 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0120 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .gapLower 2 0 (![3, 5, 4, 0, 1]), .corridorUpper 1 2, .gapLower 2 4 (![3, 5, 4, 0, 1])]

def cycle0121 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 3 1]

def cycle0122 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-2), (0), (-1), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, false, true, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 9 1, .triangle 18 0, .triangle 16 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0123 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-2), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, true, false, true] }
  origin := ![.triangle 4 2, .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 9 1, .triangle 19 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0124 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![5, 4, 3, 0, 1]), .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 3 1]

def cycle0125 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 4, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 3 1]

def cycle0126 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 5, 4, 0, 1]), .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 3 1]

def cycle0127 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0128 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 4, 3, 0, 1]), .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0129 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0130 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 3 1]

def cycle0131 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 1 2, .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 3 1]

def cycle0132 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 3 1]

def cycle0133 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 3 (![1, 5, 4, 3, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0134 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 5, 4, 3, 2]), .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0135 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .gapLower 0 5 (![1, 5, 4, 3, 2]), .triangle 4 0, .triangle 10 0, .triangle 0 0]

def cycle0136 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 4, 3, 2])]

def cycle0137 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 4, 3, 2])]

def cycle0138 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (-1), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .gapLower 0 5 (![1, 5, 4, 3, 2]), .triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0139 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .gapLower 0 5 (![1, 5, 4, 3, 2]), .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0140 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 0]

def cycle0141 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 1 0]

def cycle0142 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .gapLower 0 5 (![1, 5, 4, 3, 2]), .triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 0 0]

def cycle0143 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 3, 2]), .gapLower 0 5 (![1, 5, 4, 3, 2]), .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 0 0]

def cycle0144 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0145 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![1, 5, 4, 3, 2]), .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0146 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![1, 5, 4, 3, 2]), .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0147 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 5, 4, 3, 2]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 3, 2])]

def cycle0148 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 3 (![1, 5, 4, 3, 2]), .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0149 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 5, 4, 3, 2]), .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0150 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 4 2, .triangle 7 2, .gapLower 0 2 (![1, 5, 4, 3, 2]), .corridorLower 0 5, .gapLower 0 5 (![1, 5, 4, 3, 2])]

def cycle0151 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-2), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 5, 4, 3, 2]), .gapLower 0 3 (![1, 5, 4, 3, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0152 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, true, true, false] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![1, 5, 4, 3, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 4, 3, 2])]

def cycle0153 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 4 (![1, 5, 4, 3, 2]), .triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 4, 3, 2])]

def cycle0154 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0155 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0156 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0157 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![5, 1, 2, 3, 4])]

def cycle0158 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![5, 1, 2, 3, 4]), .triangle 0 1]

def cycle0159 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 1, 2, 3, 4]), .triangle 4 1, .triangle 0 1]

def cycle0160 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 2, 3, 4]), .triangle 2 1]

def cycle0161 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 3, 4]), .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0162 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![5, 1, 2, 3, 4])]

def cycle0163 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![5, 1, 2, 3, 4]), .triangle 0 1]

def cycle0164 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 2, 3, 4]), .gapLower 1 5 (![5, 0, 2, 3, 4]), .triangle 2 2, .gapLower 0 4 (![5, 1, 2, 3, 4]), .triangle 1 1]

def cycle0165 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 1 (![5, 0, 2, 3, 4]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![5, 1, 2, 3, 4]), .triangle 4 1, .triangle 0 1]

def cycle0166 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![5, 0, 2, 3, 4])]

def cycle0167 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 3 (![5, 0, 2, 3, 4]), .triangle 0 0]

def cycle0168 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![5, 0, 2, 3, 4]), .triangle 1 0]

def cycle0169 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 2, 3, 4]), .triangle 2 2, .gapLower 0 4 (![5, 1, 2, 3, 4]), .triangle 1 1]

def cycle0170 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![5, 1, 2, 3, 4]), .triangle 4 1, .triangle 0 1]

def cycle0171 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![5, 1, 2, 3, 4]), .triangle 4 1, .triangle 0 1]

def cycle0172 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0173 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![5, 1, 2, 3, 4]), .triangle 4 1, .triangle 0 1]

def cycle0174 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![5, 1, 2, 3, 4]), .triangle 4 1, .triangle 0 1]

def cycle0175 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 2, 3, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0176 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![5, 0, 2, 3, 4]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0177 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 2, 3, 4]), .triangle 2 0]

def cycle0178 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 2, 4, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0179 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![5, 0, 2, 4, 3]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0180 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![5, 0, 2, 4, 3])]

def cycle0181 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![5, 0, 2, 4, 3]), .triangle 0 0]

def cycle0182 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![5, 0, 2, 4, 3]), .triangle 2 0]

def cycle0183 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 2, 4, 3]), .triangle 13 0, .triangle 7 0, .gapLower 0 3 (![5, 1, 2, 3, 4]), .triangle 0 1]

def cycle0184 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0185 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 3, 4, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0186 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1 (![5, 0, 3, 4, 2]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0187 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![5, 0, 3, 4, 2])]

def cycle0188 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![5, 0, 3, 4, 2]), .triangle 1 0]

def cycle0189 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![5, 0, 3, 4, 2]), .triangle 2 0]

def cycle0190 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 3, 4, 2]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0191 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 4, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 3 (![5, 1, 2, 3, 4]), .gapLower 0 2 (![5, 1, 2, 3, 4])]

def cycle0192 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 1 (![5, 0, 4, 3, 2]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 3 (![5, 1, 2, 3, 4]), .triangle 0 1]

def cycle0193 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0)]
    coefficient := ![0, 0, 0]
    strict := ![true, true, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 0 1]

def cycle0194 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 3 (![5, 1, 2, 3, 4])]

def cycle0195 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![5, 0, 4, 3, 2]), .triangle 2 0]

def cycle0196 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![5, 0, 4, 3, 2]), .triangle 13 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0197 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 3 (![5, 1, 2, 3, 4]), .gapLower 0 2 (![5, 1, 2, 3, 4])]

def cycle0198 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![5, 1, 2, 3, 4])]

def cycle0199 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![5, 1, 2, 3, 4]), .triangle 0 1]

def cycle0200 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 1, 2, 3, 4]), .triangle 4 1, .triangle 0 1]

def cycle0201 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 3, 4]), .corridorLower 0 5, .gapLower 0 5 (![5, 1, 2, 3, 4]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0202 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![5, 1, 2, 3, 4]), .gapLower 0 2 (![5, 1, 2, 3, 4])]

def cycle0203 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 1, 2, 3, 4]), .triangle 4 1, .gapLower 0 2 (![5, 1, 2, 3, 4])]

def cycle0204 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 2, 3, 4]), .triangle 7 1, .triangle 4 1, .gapLower 0 2 (![5, 1, 2, 3, 4])]

def cycle0205 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 1, 2, 3, 4]), .gapLower 0 3 (![5, 1, 2, 3, 4]), .triangle 0 1]

def cycle0206 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 2, 3, 4]), .triangle 7 1, .gapLower 0 3 (![5, 1, 2, 3, 4]), .triangle 0 1]

def cycle0207 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 2, 3, 4]), .gapLower 0 4 (![5, 1, 2, 3, 4]), .triangle 1 1]

def cycle0208 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0209 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0210 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 4, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0211 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![5, 1, 2, 4, 3])]

def cycle0212 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![5, 1, 2, 4, 3]), .triangle 0 1]

def cycle0213 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 1, 2, 4, 3]), .triangle 5 1, .triangle 0 1]

def cycle0214 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 2, 4, 3]), .triangle 1 1]

def cycle0215 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 4, 3]), .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0216 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![5, 1, 2, 4, 3])]

def cycle0217 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 2, 4, 3]), .gapLower 1 5 (![5, 0, 2, 4, 3]), .triangle 13 2, .triangle 2 2, .gapLower 0 3 (![5, 1, 2, 4, 3]), .triangle 0 1]

def cycle0218 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1 (![5, 0, 2, 4, 3]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![5, 1, 2, 4, 3]), .triangle 0 1]

def cycle0219 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![5, 0, 2, 4, 3])]

def cycle0220 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![5, 0, 2, 4, 3]), .triangle 0 0]

def cycle0221 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![5, 0, 2, 4, 3]), .triangle 2 2, .gapLower 0 3 (![5, 1, 2, 4, 3]), .triangle 0 1]

def cycle0222 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 2, 4, 3]), .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![5, 1, 2, 4, 3]), .triangle 0 1]

def cycle0223 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 2, .gapLower 0 3 (![5, 1, 2, 4, 3]), .triangle 0 1]

def cycle0224 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .triangle 7 2, .gapLower 0 3 (![5, 1, 2, 4, 3]), .triangle 0 1]

def cycle0225 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 2, 4, 3]), .gapLower 1 5 (![5, 0, 2, 4, 3]), .triangle 1 2, .gapLower 0 4 (![5, 1, 2, 4, 3]), .triangle 2 1]

def cycle0226 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 1 (![5, 0, 2, 4, 3]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![5, 1, 2, 4, 3]), .triangle 5 1, .triangle 0 1]

def cycle0227 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![5, 0, 2, 4, 3]), .triangle 2 0]

def cycle0228 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 2, 4, 3]), .triangle 1 2, .gapLower 0 4 (![5, 1, 2, 4, 3]), .triangle 2 1]

def cycle0229 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0230 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .gapLower 0 4 (![5, 1, 2, 4, 3]), .triangle 5 1, .triangle 0 1]

def cycle0231 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .gapLower 0 5 (![5, 1, 2, 4, 3]), .triangle 7 0, .triangle 13 0, .gapLower 1 3 (![5, 0, 2, 3, 4]), .triangle 0 0]

def cycle0232 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 2, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0233 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 2, 4, 3]), .triangle 1 0]

def cycle0234 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .gapLower 0 5 (![5, 1, 2, 4, 3]), .triangle 7 0, .triangle 13 0, .triangle 1 0]

def cycle0235 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 4, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .gapLower 0 2 (![5, 1, 2, 4, 3])]

def cycle0236 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1 (![5, 0, 4, 3, 2]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0237 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![5, 0, 4, 3, 2]), .triangle 2 0]

def cycle0238 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 2, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![5, 0, 4, 3, 2]), .triangle 1 0]

def cycle0239 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 10 0, .triangle 4 0, .gapLower 0 2 (![5, 1, 2, 4, 3])]

def cycle0240 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 4, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![5, 1, 2, 4, 3])]

def cycle0241 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 4, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![5, 1, 2, 4, 3]), .triangle 0 1]

def cycle0242 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 4, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 1, 2, 4, 3]), .triangle 5 1, .triangle 0 1]

def cycle0243 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 1 (![5, 1, 2, 4, 3]), .corridorLower 0 5, .gapLower 0 5 (![5, 1, 2, 4, 3]), .triangle 4 1, .triangle 0 1]

def cycle0244 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![5, 1, 2, 4, 3]), .gapLower 0 2 (![5, 1, 2, 4, 3])]

def cycle0245 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 1, 2, 4, 3]), .triangle 5 1, .gapLower 0 2 (![5, 1, 2, 4, 3])]

def cycle0246 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 2, 4, 3]), .triangle 4 1, .gapLower 0 2 (![5, 1, 2, 4, 3])]

def cycle0247 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 1, 2, 4, 3]), .gapLower 0 3 (![5, 1, 2, 4, 3]), .triangle 0 1]

def cycle0248 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 2, 4, 3]), .triangle 7 2, .gapLower 0 3 (![5, 1, 2, 4, 3]), .triangle 0 1]

def cycle0249 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 2, 4, 3]), .gapLower 0 4 (![5, 1, 2, 4, 3]), .triangle 2 1]

def cycle0250 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0251 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 5 2, .triangle 2 1]

def cycle0252 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 2, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 2 (![5, 1, 4, 2, 3])]

def cycle0253 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 2 (![5, 1, 4, 2, 3])]

def cycle0254 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![5, 1, 4, 2, 3]), .triangle 2 1]

def cycle0255 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 1, 4, 2, 3]), .triangle 0 1]

def cycle0256 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 4, 2, 3]), .triangle 4 1, .triangle 5 2, .gapLower 0 2 (![5, 1, 4, 2, 3])]

def cycle0257 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 2, 3]), .gapLower 0 0 (![5, 1, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 2 (![5, 1, 4, 2, 3])]

def cycle0258 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 2 (![5, 1, 4, 2, 3])]

def cycle0259 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![5, 1, 4, 2, 3]), .triangle 2 1]

def cycle0260 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 4, 2, 3]), .gapLower 1 5 (![5, 0, 4, 2, 3]), .triangle 1 2, .gapLower 0 4 (![5, 1, 4, 2, 3]), .triangle 0 1]

def cycle0261 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![5, 0, 4, 2, 3]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![5, 1, 4, 2, 3]), .triangle 0 1]

def cycle0262 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .gapLower 1 2 (![5, 0, 4, 2, 3])]

def cycle0263 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 3 (![5, 0, 4, 2, 3]), .triangle 2 0]

def cycle0264 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![5, 0, 4, 2, 3]), .triangle 0 0]

def cycle0265 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 4, 2, 3]), .triangle 1 2, .gapLower 0 4 (![5, 1, 4, 2, 3]), .triangle 0 1]

def cycle0266 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .gapLower 0 4 (![5, 1, 4, 2, 3])]

def cycle0267 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 4, 2, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .triangle 2 0]

def cycle0268 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1 (![5, 0, 4, 2, 3]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .triangle 2 0]

def cycle0269 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 4, 2, 3]), .triangle 1 0]

def cycle0270 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 2, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 2 (![5, 1, 4, 2, 3])]

def cycle0271 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 2, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![5, 1, 4, 2, 3]), .triangle 2 1]

def cycle0272 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 2, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 1, 4, 2, 3]), .triangle 0 1]

def cycle0273 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 2, 3]), .corridorLower 0 5, .gapLower 0 5 (![5, 1, 4, 2, 3]), .triangle 4 1, .triangle 5 2, .gapLower 0 2 (![5, 1, 4, 2, 3])]

def cycle0274 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![5, 1, 4, 2, 3]), .gapLower 0 2 (![5, 1, 4, 2, 3])]

def cycle0275 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 1, 4, 2, 3]), .triangle 5 2, .gapLower 0 2 (![5, 1, 4, 2, 3])]

def cycle0276 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 4, 2, 3]), .triangle 4 1, .triangle 5 2, .gapLower 0 2 (![5, 1, 4, 2, 3])]

def cycle0277 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 1, 4, 2, 3]), .gapLower 0 3 (![5, 1, 4, 2, 3]), .triangle 2 1]

def cycle0278 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 4, 2, 3]), .triangle 4 1, .gapLower 0 3 (![5, 1, 4, 2, 3]), .triangle 2 1]

def cycle0279 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 4, 2, 3]), .gapLower 0 4 (![5, 1, 4, 2, 3]), .triangle 0 1]

def cycle0280 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0281 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0282 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 2, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0283 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![5, 1, 3, 2, 4])]

def cycle0284 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![5, 1, 3, 2, 4]), .triangle 1 1]

def cycle0285 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 1, 3, 2, 4]), .triangle 0 1]

def cycle0286 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 3, 2, 4]), .triangle 2 1]

def cycle0287 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 2, 4]), .gapLower 0 0 (![5, 1, 3, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0288 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 4 2, .gapLower 0 2 (![5, 1, 3, 2, 4])]

def cycle0289 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![5, 1, 3, 2, 4]), .triangle 1 1]

def cycle0290 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 3, 2, 4]), .gapLower 1 5 (![5, 0, 3, 2, 4]), .triangle 2 2, .gapLower 0 4 (![5, 1, 3, 2, 4]), .triangle 0 1]

def cycle0291 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![5, 0, 3, 2, 4]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![5, 1, 3, 2, 4]), .triangle 0 1]

def cycle0292 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 2, .gapLower 1 2 (![5, 0, 3, 2, 4])]

def cycle0293 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 3 (![5, 0, 3, 2, 4]), .triangle 1 0]

def cycle0294 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![5, 0, 3, 2, 4]), .triangle 0 0]

def cycle0295 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 3, 2, 4]), .triangle 2 2, .gapLower 0 4 (![5, 1, 3, 2, 4]), .triangle 0 1]

def cycle0296 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![5, 1, 3, 2, 4])]

def cycle0297 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![5, 1, 3, 2, 4])]

def cycle0298 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 3, 2, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0299 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![5, 0, 3, 2, 4]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0300 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 3, 2, 4]), .triangle 2 0]

def cycle0301 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 4, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![5, 1, 3, 2, 4])]

def cycle0302 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 1 (![5, 0, 4, 3, 2]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0303 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0304 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0305 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 2 (![5, 2, 0, 4, 1]), .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0]

def cycle0306 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![5, 0, 4, 3, 2]), .triangle 2 0]

def cycle0307 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![5, 0, 4, 3, 2]), .triangle 1 0]

def cycle0308 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![5, 1, 3, 2, 4])]

def cycle0309 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 2, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![5, 1, 3, 2, 4])]

def cycle0310 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 2, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![5, 1, 3, 2, 4]), .triangle 1 1]

def cycle0311 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 2, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 1, 3, 2, 4]), .triangle 0 1]

def cycle0312 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 2, 4]), .corridorLower 0 5, .gapLower 0 5 (![5, 1, 3, 2, 4]), .triangle 5 1, .triangle 0 1]

def cycle0313 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![5, 1, 3, 2, 4]), .gapLower 0 2 (![5, 1, 3, 2, 4])]

def cycle0314 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 1, 3, 2, 4]), .triangle 4 2, .gapLower 0 2 (![5, 1, 3, 2, 4])]

def cycle0315 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 3, 2, 4]), .triangle 5 1, .triangle 4 2, .gapLower 0 2 (![5, 1, 3, 2, 4])]

def cycle0316 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![5, 1, 3, 2, 4]), .gapLower 0 3 (![5, 1, 3, 2, 4]), .triangle 1 1]

def cycle0317 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 3, 2, 4]), .triangle 5 1, .gapLower 0 3 (![5, 1, 3, 2, 4]), .triangle 1 1]

def cycle0318 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 3, 2, 4]), .gapLower 0 4 (![5, 1, 3, 2, 4]), .triangle 0 1]

def cycle0319 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0320 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0321 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 4, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0322 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![5, 1, 3, 4, 2])]

def cycle0323 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![5, 1, 3, 4, 2]), .triangle 1 1]

def cycle0324 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 7 1, .triangle 1 1]

def cycle0325 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 3, 4, 2]), .triangle 5 2, .triangle 7 1, .gapLower 0 2 (![5, 1, 3, 4, 2])]

def cycle0326 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 4, 2]), .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0327 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![5, 1, 3, 4, 2])]

def cycle0328 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 3, 4, 2]), .gapLower 1 5 (![5, 0, 3, 4, 2]), .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![5, 1, 3, 4, 2]), .triangle 1 1]

def cycle0329 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![5, 0, 3, 4, 2]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![5, 1, 3, 4, 2]), .triangle 1 1]

def cycle0330 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![5, 0, 3, 4, 2])]

def cycle0331 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![5, 0, 3, 4, 2]), .triangle 1 0]

def cycle0332 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![5, 0, 3, 4, 2]), .triangle 2 2, .gapLower 0 3 (![5, 1, 3, 4, 2]), .triangle 1 1]

def cycle0333 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 3, 4, 2]), .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![5, 1, 3, 4, 2]), .triangle 1 1]

def cycle0334 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 3 (![5, 1, 3, 4, 2]), .triangle 1 1]

def cycle0335 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 3, 4, 2]), .gapLower 1 5 (![5, 0, 3, 4, 2]), .triangle 0 2, .gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 2 1]

def cycle0336 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 1 (![5, 0, 3, 4, 2]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 7 1, .triangle 1 1]

def cycle0337 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![5, 0, 3, 4, 2]), .triangle 2 0]

def cycle0338 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 3, 4, 2]), .triangle 0 2, .gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 2 1]

def cycle0339 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 4, 3, 2]), .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 0 2, .gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 2 1]

def cycle0340 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 1 (![5, 0, 4, 3, 2]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 7 1, .triangle 1 1]

def cycle0341 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0342 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0343 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0344 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0)]
    coefficient := ![0, 0, 0]
    strict := ![true, true, true] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 1 1]

def cycle0345 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 7 1, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0346 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 7 1, .triangle 1 1]

def cycle0347 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0348 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 5 1, .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0349 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2]

def cycle0350 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![5, 0, 4, 3, 2]), .triangle 2 0]

def cycle0351 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![5, 0, 4, 3, 2]), .triangle 1 0]

def cycle0352 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 0 2, .gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 2 1]

def cycle0353 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .gapLower 0 5 (![5, 1, 3, 4, 2]), .triangle 4 0, .triangle 10 0, .triangle 0 0]

def cycle0354 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .gapLower 0 5 (![5, 1, 3, 4, 2]), .triangle 5 0, .triangle 11 0, .gapLower 1 3 (![5, 0, 3, 2, 4]), .gapLower 1 2 (![5, 0, 3, 2, 4])]

def cycle0355 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![5, 0, 3, 4, 2]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0356 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 3, 4, 2]), .triangle 0 0]

def cycle0357 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 4, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![5, 1, 3, 4, 2])]

def cycle0358 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (0), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .gapLower 0 5 (![5, 1, 3, 4, 2]), .triangle 6 0, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0359 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .gapLower 0 5 (![5, 1, 3, 4, 2]), .triangle 6 0, .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0360 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (2), (-2), (0), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .gapLower 0 5 (![5, 1, 3, 4, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0361 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .gapLower 0 5 (![5, 1, 3, 4, 2]), .triangle 5 0, .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0362 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 3, 4, 2]), .gapLower 0 5 (![5, 1, 3, 4, 2]), .triangle 4 0, .triangle 16 0, .triangle 7 0, .gapLower 0 2 (![5, 1, 3, 4, 2])]

def cycle0363 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![5, 1, 3, 4, 2])]

def cycle0364 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 4, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![5, 1, 3, 4, 2])]

def cycle0365 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 4, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![5, 1, 3, 4, 2]), .triangle 1 1]

def cycle0366 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 4, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 7 1, .triangle 1 1]

def cycle0367 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![5, 1, 3, 4, 2]), .corridorLower 0 5, .gapLower 0 5 (![5, 1, 3, 4, 2]), .triangle 5 2, .triangle 7 1, .gapLower 0 2 (![5, 1, 3, 4, 2])]

def cycle0368 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![5, 1, 3, 4, 2]), .gapLower 0 2 (![5, 1, 3, 4, 2])]

def cycle0369 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 7 1, .gapLower 0 2 (![5, 1, 3, 4, 2])]

def cycle0370 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 3, 4, 2]), .triangle 5 2, .triangle 7 1, .gapLower 0 2 (![5, 1, 3, 4, 2])]

def cycle0371 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 1, 3, 4, 2]), .gapLower 0 3 (![5, 1, 3, 4, 2]), .triangle 1 1]

def cycle0372 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 3, 4, 2]), .triangle 5 2, .gapLower 0 3 (![5, 1, 3, 4, 2]), .triangle 1 1]

def cycle0373 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 3, 4, 2]), .gapLower 0 4 (![5, 1, 3, 4, 2]), .triangle 2 1]

def cycle0374 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def cycle0375 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0376 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 2, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0377 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def cycle0378 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def cycle0379 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (0), (-1), (-2), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 19 1, .triangle 16 0, .gapLower 3 0 (![2, 4, 5, 0, 1]), .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0380 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 19 1, .gapLower 3 1 (![2, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0381 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-2), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .gapLower 3 2 (![2, 4, 5, 0, 1]), .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0382 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 3 3 (![2, 4, 5, 0, 1]), .triangle 19 1, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0383 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![(-1), (0), (-1), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 8 0, .triangle 19 1, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![2, 4, 5, 0, 1])]

def cycle0384 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![2, 4, 5, 0, 1]), .triangle 1 0]

def cycle0385 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1])]

def cycle0386 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 0]

def cycle0387 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 0]

def cycle0388 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0389 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 17 0, .gapLower 2 1 (![4, 3, 5, 0, 1]), .gapLower 2 0 (![4, 3, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0390 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 17 1, .gapLower 2 1 (![4, 3, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def cycle0391 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![4, 3, 5, 0, 1]), .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0392 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 6 0, .triangle 17 1, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 3, 5, 0, 1])]

def cycle0393 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 3, 5, 0, 1]), .triangle 0 0]

def cycle0394 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 4, 3, 2]), .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 10 2, .gapLower 3 4 (![4, 5, 2, 0, 1]), .triangle 1 1]

def cycle0395 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 2, 0, 1]), .triangle 1 0]

def cycle0396 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1), (-2), (4), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.triangle 4 0, .triangle 16 0, .triangle 19 0, .triangle 18 0, .gapLower 2 0 (![4, 5, 3, 0, 1]), .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 2]

def cycle0397 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1])]

def cycle0398 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 0]

def cycle0399 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 4 (![5, 4, 3, 0, 1])]

def cycle0400 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 4, 3, 0, 1]), .triangle 0 0]

def cycle0401 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![(0), (0), (0), (-2), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, true, false, false, true, false] }
  origin := ![.triangle 4 1, .triangle 17 2, .triangle 18 1, .gapLower 2 0 (![4, 5, 3, 0, 1]), .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![4, 5, 2, 0, 1])]

def cycle0402 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0403 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![5, 0, 4, 3, 2]), .triangle 2 0]

def cycle0404 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![5, 0, 4, 3, 2]), .triangle 1 0]

def cycle0405 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 0 0]

def cycle0406 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 3, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0407 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0408 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0409 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![5, 1, 4, 3, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0410 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 4, 3, 2]), .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0411 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 3, 2]), .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0412 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 4, 3, 2]), .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0413 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 1 (![5, 0, 4, 3, 2]), .corridorLower 1 5, .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0414 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0415 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0416 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0417 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true, true, true, false] }
  origin := ![.triangle 3 2, .triangle 8 1, .triangle 19 1, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0418 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0419 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0420 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 5, 4, 0, 1]), .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0421 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0422 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0423 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, true, false, true, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 17 1, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0424 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![4, 5, 2, 0, 1]), .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0425 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 2, 0, 1]), .triangle 1 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0426 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1]), .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0427 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0428 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![5, 4, 3, 0, 1]), .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0429 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 4, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0430 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![5, 0, 4, 3, 2]), .triangle 2 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0431 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![5, 0, 4, 3, 2]), .triangle 1 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0432 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0433 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 4, 3, 2]), .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0434 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![5, 0, 4, 3, 2]), .corridorLower 1 5, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0435 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 7 1, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0436 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, true, false, true, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 17 1, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0437 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![4, 5, 2, 0, 1]), .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0438 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 2, 0, 1]), .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0439 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 3 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (-1), (-2), (4), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 7 1, .triangle 19 0, .triangle 18 0, .gapLower 2 0 (![4, 5, 3, 0, 1]), .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 2]

def cycle0440 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1]), .triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0441 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0442 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 7 1, .triangle 19 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0443 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![5, 4, 3, 0, 1]), .triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0444 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 4, 3, 0, 1]), .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0445 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![5, 0, 4, 3, 2]), .triangle 2 0]

def cycle0446 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![5, 0, 4, 3, 2]), .triangle 1 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0447 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0448 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![5, 1, 4, 3, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0449 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .gapLower 0 5 (![5, 1, 4, 3, 2]), .triangle 4 0, .triangle 10 0, .triangle 0 0]

def cycle0450 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (0), (2), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .gapLower 1 0 (![5, 0, 4, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![5, 1, 4, 3, 2]), .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0451 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (2), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 1 (![5, 0, 4, 3, 2]), .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 4, 3, 2]), .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0452 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (2), (0), (-1), (-1), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .gapLower 0 5 (![5, 1, 4, 3, 2]), .triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0453 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .gapLower 0 5 (![5, 1, 4, 3, 2]), .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![5, 0, 4, 3, 2])]

def cycle0454 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 0 (![5, 1, 4, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![5, 0, 4, 3, 2]), .triangle 1 0]

def cycle0455 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .gapLower 1 5 (![5, 0, 4, 3, 2]), .triangle 0 0]

def cycle0456 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 3, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0457 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 3, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0458 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 3, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 1, 4, 3, 2]), .triangle 1 1]

def cycle0459 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![5, 1, 4, 3, 2]), .corridorLower 0 5, .gapLower 0 5 (![5, 1, 4, 3, 2]), .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0460 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0461 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 1, 4, 3, 2]), .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0462 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 4, 3, 2]), .triangle 4 2, .triangle 7 2, .gapLower 0 2 (![5, 1, 4, 3, 2])]

def cycle0463 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 1, 4, 3, 2]), .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0464 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 4, 3, 2]), .triangle 4 2, .gapLower 0 3 (![5, 1, 4, 3, 2]), .triangle 2 1]

def cycle0465 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 3 0, .corridorLower 1 5, .thetaOrder 0, .gapLower 0 5 (![5, 1, 4, 3, 2]), .gapLower 0 4 (![5, 1, 4, 3, 2]), .triangle 1 1]

def cycle0466 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0467 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0468 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0469 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![4, 1, 2, 3, 5])]

def cycle0470 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![4, 1, 2, 3, 5]), .triangle 0 1]

def cycle0471 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 1, 2, 3, 5]), .triangle 4 1, .triangle 0 1]

def cycle0472 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 2, 3, 5]), .triangle 8 1, .triangle 4 1, .triangle 0 1]

def cycle0473 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 3, 5]), .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0474 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![4, 1, 2, 3, 5])]

def cycle0475 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![4, 1, 2, 3, 5]), .triangle 0 1]

def cycle0476 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 2, 3, 5]), .gapLower 1 5 (![4, 0, 2, 3, 5]), .triangle 3 2, .gapLower 0 4 (![4, 1, 2, 3, 5]), .triangle 1 1]

def cycle0477 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 1 (![4, 0, 2, 3, 5]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![4, 1, 2, 3, 5]), .triangle 4 1, .triangle 0 1]

def cycle0478 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![4, 0, 2, 3, 5])]

def cycle0479 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 3 (![4, 0, 2, 3, 5]), .triangle 0 0]

def cycle0480 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![4, 0, 2, 3, 5]), .triangle 1 0]

def cycle0481 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 2, 3, 5]), .triangle 3 2, .gapLower 0 4 (![4, 1, 2, 3, 5]), .triangle 1 1]

def cycle0482 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![4, 1, 2, 3, 5]), .triangle 4 1, .triangle 0 1]

def cycle0483 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![4, 1, 2, 3, 5]), .triangle 4 1, .triangle 0 1]

def cycle0484 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0485 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![4, 1, 2, 3, 5]), .triangle 4 1, .triangle 0 1]

def cycle0486 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![4, 1, 2, 3, 5]), .triangle 4 1, .triangle 0 1]

def cycle0487 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 2, 3, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0488 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![4, 0, 2, 3, 5]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0489 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 2, 3, 5]), .triangle 3 0]

def cycle0490 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 2, 5, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0491 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![4, 0, 2, 5, 3]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0492 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![4, 0, 2, 5, 3])]

def cycle0493 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 2, .gapLower 1 3 (![4, 0, 2, 5, 3]), .triangle 0 0]

def cycle0494 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![4, 0, 2, 5, 3]), .triangle 12 1, .triangle 0 0]

def cycle0495 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 2, 5, 3]), .triangle 14 0, .triangle 8 0, .gapLower 0 3 (![4, 1, 2, 3, 5]), .triangle 0 1]

def cycle0496 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0497 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 3, 5, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0498 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1 (![4, 0, 3, 5, 2]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0499 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 2 (![4, 0, 3, 5, 2])]

def cycle0500 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![4, 0, 3, 5, 2]), .triangle 1 0]

def cycle0501 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 0, 3, 5, 2]), .triangle 14 1, .triangle 10 1, .triangle 4 0, .triangle 0 1]

def cycle0502 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 3, 5, 2]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0503 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 5, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 0, .triangle 4 1, .triangle 0 1]

def cycle0504 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 1 (![4, 0, 5, 3, 2]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 3 (![4, 1, 2, 3, 5]), .triangle 0 1]

def cycle0505 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0)]
    coefficient := ![0, 0, 0]
    strict := ![true, true, true] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 0 1]

def cycle0506 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 3 (![4, 1, 2, 3, 5])]

def cycle0507 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 3, 5]), .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 0, 5, 3, 2]), .triangle 3 0]

def cycle0508 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 0, 5, 3, 2]), .triangle 14 0, .triangle 8 0, .triangle 4 1, .triangle 0 1]

def cycle0509 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 3 (![4, 1, 2, 3, 5]), .gapLower 0 2 (![4, 1, 2, 3, 5])]

def cycle0510 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![4, 1, 2, 3, 5])]

def cycle0511 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![4, 1, 2, 3, 5]), .triangle 0 1]

def cycle0512 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 1, 2, 3, 5]), .triangle 4 1, .triangle 0 1]

def cycle0513 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 3, 5]), .corridorLower 0 4, .gapLower 0 5 (![4, 1, 2, 3, 5]), .triangle 8 1, .triangle 4 1, .triangle 0 1]

def cycle0514 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![4, 1, 2, 3, 5]), .gapLower 0 2 (![4, 1, 2, 3, 5])]

def cycle0515 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 1, 2, 3, 5]), .triangle 4 1, .gapLower 0 2 (![4, 1, 2, 3, 5])]

def cycle0516 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 2, 3, 5]), .triangle 8 1, .triangle 4 1, .gapLower 0 2 (![4, 1, 2, 3, 5])]

def cycle0517 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 1, 2, 3, 5]), .gapLower 0 3 (![4, 1, 2, 3, 5]), .triangle 0 1]

def cycle0518 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 2, 3, 5]), .triangle 8 1, .gapLower 0 3 (![4, 1, 2, 3, 5]), .triangle 0 1]

def cycle0519 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 2, 3, 5]), .gapLower 0 4 (![4, 1, 2, 3, 5]), .triangle 1 1]

def cycle0520 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0521 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0522 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 5, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0523 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![4, 1, 2, 5, 3])]

def cycle0524 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![4, 1, 2, 5, 3]), .triangle 0 1]

def cycle0525 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 1, 2, 5, 3]), .triangle 3 1]

def cycle0526 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 2, 5, 3]), .triangle 1 1]

def cycle0527 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 5, 3]), .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0528 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![4, 1, 2, 5, 3])]

def cycle0529 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 2, 5, 3]), .gapLower 1 5 (![4, 0, 2, 5, 3]), .triangle 14 2, .triangle 3 2, .gapLower 0 3 (![4, 1, 2, 5, 3]), .triangle 0 1]

def cycle0530 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1 (![4, 0, 2, 5, 3]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![4, 1, 2, 5, 3]), .triangle 0 1]

def cycle0531 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![4, 0, 2, 5, 3])]

def cycle0532 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 2, .gapLower 1 3 (![4, 0, 2, 5, 3]), .triangle 0 0]

def cycle0533 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![4, 0, 2, 5, 3]), .triangle 3 2, .gapLower 0 3 (![4, 1, 2, 5, 3]), .triangle 0 1]

def cycle0534 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 2, 5, 3]), .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![4, 1, 2, 5, 3]), .triangle 0 1]

def cycle0535 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 2, .gapLower 0 3 (![4, 1, 2, 5, 3]), .triangle 0 1]

def cycle0536 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .triangle 8 2, .gapLower 0 3 (![4, 1, 2, 5, 3]), .triangle 0 1]

def cycle0537 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 2, 5, 3]), .gapLower 1 5 (![4, 0, 2, 5, 3]), .triangle 1 2, .gapLower 0 4 (![4, 1, 2, 5, 3]), .triangle 3 1]

def cycle0538 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 1 (![4, 0, 2, 5, 3]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![4, 1, 2, 5, 3]), .triangle 6 1, .triangle 0 1]

def cycle0539 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![4, 0, 2, 5, 3]), .triangle 12 1, .triangle 0 0]

def cycle0540 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 3]
    constant := ![(-2), (0), (-2), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 4 (![4, 1, 2, 5, 3]), .triangle 9 1, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![4, 0, 2, 5, 3]), .triangle 1 2]

def cycle0541 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0542 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .gapLower 0 4 (![4, 1, 2, 5, 3]), .triangle 3 1]

def cycle0543 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .gapLower 0 5 (![4, 1, 2, 5, 3]), .triangle 8 0, .triangle 14 0, .gapLower 1 3 (![4, 0, 2, 3, 5]), .triangle 0 0]

def cycle0544 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 2, 5, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0545 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 2, 5, 3]), .triangle 1 0]

def cycle0546 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 3, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .gapLower 0 5 (![4, 1, 2, 5, 3]), .triangle 8 0, .triangle 14 0, .triangle 1 0]

def cycle0547 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 5, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .gapLower 0 2 (![4, 1, 2, 5, 3])]

def cycle0548 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1 (![4, 0, 5, 3, 2]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0549 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 0, 5, 3, 2]), .triangle 3 0]

def cycle0550 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 2, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 0, 5, 3, 2]), .triangle 1 0]

def cycle0551 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 10 0, .triangle 4 0, .gapLower 0 2 (![4, 1, 2, 5, 3])]

def cycle0552 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 5, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![4, 1, 2, 5, 3])]

def cycle0553 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 5, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![4, 1, 2, 5, 3]), .triangle 0 1]

def cycle0554 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 5, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 1, 2, 5, 3]), .triangle 6 1, .triangle 0 1]

def cycle0555 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 1 (![4, 1, 2, 5, 3]), .corridorLower 0 4, .gapLower 0 5 (![4, 1, 2, 5, 3]), .triangle 4 1, .triangle 0 1]

def cycle0556 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![4, 1, 2, 5, 3]), .gapLower 0 2 (![4, 1, 2, 5, 3])]

def cycle0557 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 1, 2, 5, 3]), .triangle 6 1, .gapLower 0 2 (![4, 1, 2, 5, 3])]

def cycle0558 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 2, 5, 3]), .triangle 4 1, .gapLower 0 2 (![4, 1, 2, 5, 3])]

def cycle0559 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 1, 2, 5, 3]), .gapLower 0 3 (![4, 1, 2, 5, 3]), .triangle 0 1]

def cycle0560 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 2, 5, 3]), .triangle 8 2, .gapLower 0 3 (![4, 1, 2, 5, 3]), .triangle 0 1]

def cycle0561 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 2, 5, 3]), .gapLower 0 4 (![4, 1, 2, 5, 3]), .triangle 3 1]

def cycle0562 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0563 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 9 1, .gapLower 0 0 (![4, 1, 5, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0]

def cycle0564 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 2, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 2 (![4, 1, 5, 2, 3])]

def cycle0565 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 2 (![4, 1, 5, 2, 3])]

def cycle0566 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 1, 5, 2, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0567 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 1, 5, 2, 3]), .triangle 0 1]

def cycle0568 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 1, 5, 2, 3]), .triangle 4 1]

def cycle0569 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 2, 3]), .gapLower 0 0 (![4, 1, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 2 (![4, 1, 5, 2, 3])]

def cycle0570 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 2 (![4, 1, 5, 2, 3])]

def cycle0571 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![4, 1, 5, 2, 3]), .triangle 9 1, .gapLower 0 0 (![4, 1, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0572 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 5, 2, 3]), .gapLower 1 5 (![4, 0, 5, 2, 3]), .triangle 1 2, .gapLower 0 4 (![4, 1, 5, 2, 3]), .triangle 0 1]

def cycle0573 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![4, 0, 5, 2, 3]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![4, 1, 5, 2, 3]), .triangle 0 1]

def cycle0574 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 2, .gapLower 1 2 (![4, 0, 5, 2, 3])]

def cycle0575 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 2, 3]), .gapLower 0 0 (![4, 1, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 3 (![4, 0, 5, 2, 3]), .triangle 3 0]

def cycle0576 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![4, 0, 5, 2, 3]), .triangle 0 0]

def cycle0577 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 5, 2, 3]), .triangle 1 2, .gapLower 0 4 (![4, 1, 5, 2, 3]), .triangle 0 1]

def cycle0578 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .gapLower 0 4 (![4, 1, 5, 2, 3])]

def cycle0579 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 5, 2, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 2, .triangle 3 0]

def cycle0580 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1 (![4, 0, 5, 2, 3]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 2, .triangle 3 0]

def cycle0581 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 5, 2, 3]), .triangle 1 0]

def cycle0582 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 2, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 2 (![4, 1, 5, 2, 3])]

def cycle0583 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 2, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![4, 1, 5, 2, 3]), .triangle 3 1]

def cycle0584 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 2, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 1, 5, 2, 3]), .triangle 0 1]

def cycle0585 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 2, 3]), .corridorLower 0 4, .gapLower 0 5 (![4, 1, 5, 2, 3]), .triangle 4 1, .triangle 6 2, .gapLower 0 2 (![4, 1, 5, 2, 3])]

def cycle0586 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![4, 1, 5, 2, 3]), .gapLower 0 2 (![4, 1, 5, 2, 3])]

def cycle0587 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 1, 5, 2, 3]), .triangle 6 2, .gapLower 0 2 (![4, 1, 5, 2, 3])]

def cycle0588 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 5, 2, 3]), .triangle 4 1, .triangle 6 2, .gapLower 0 2 (![4, 1, 5, 2, 3])]

def cycle0589 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 1, 5, 2, 3]), .gapLower 0 3 (![4, 1, 5, 2, 3]), .triangle 3 1]

def cycle0590 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 5, 2, 3]), .triangle 4 1, .gapLower 0 3 (![4, 1, 5, 2, 3]), .triangle 3 1]

def cycle0591 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 5, 2, 3]), .gapLower 0 4 (![4, 1, 5, 2, 3]), .triangle 0 1]

def cycle0592 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0593 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0594 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 2, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0595 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![4, 1, 3, 2, 5])]

def cycle0596 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![4, 1, 3, 2, 5]), .triangle 1 1]

def cycle0597 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 1, 3, 2, 5]), .triangle 0 1]

def cycle0598 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 3, 2, 5]), .triangle 6 1, .triangle 0 1]

def cycle0599 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 2, 5]), .gapLower 0 0 (![4, 1, 3, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0600 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .triangle 4 2, .gapLower 0 2 (![4, 1, 3, 2, 5])]

def cycle0601 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![4, 1, 3, 2, 5]), .triangle 1 1]

def cycle0602 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 3, 2, 5]), .gapLower 1 5 (![4, 0, 3, 2, 5]), .triangle 3 2, .gapLower 0 4 (![4, 1, 3, 2, 5]), .triangle 0 1]

def cycle0603 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![4, 0, 3, 2, 5]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![4, 1, 3, 2, 5]), .triangle 0 1]

def cycle0604 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 10 2, .gapLower 1 2 (![4, 0, 3, 2, 5])]

def cycle0605 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .gapLower 1 3 (![4, 0, 3, 2, 5]), .triangle 1 0]

def cycle0606 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![4, 0, 3, 2, 5]), .triangle 0 0]

def cycle0607 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 3, 2, 5]), .triangle 3 2, .gapLower 0 4 (![4, 1, 3, 2, 5]), .triangle 0 1]

def cycle0608 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![4, 1, 3, 2, 5])]

def cycle0609 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![4, 1, 3, 2, 5])]

def cycle0610 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 3, 2, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 0 0]

def cycle0611 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![4, 0, 3, 2, 5]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 0 0]

def cycle0612 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 3, 2, 5]), .triangle 3 0]

def cycle0613 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 5, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0614 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 1 (![4, 0, 5, 3, 2]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0615 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0616 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 10 2, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0617 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 2 (![4, 2, 0, 5, 1]), .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 0]

def cycle0618 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 2, 5]), .gapLower 0 0 (![4, 1, 3, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 0, 5, 3, 2]), .triangle 3 0]

def cycle0619 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 0, 5, 3, 2]), .triangle 1 0]

def cycle0620 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![4, 1, 3, 2, 5])]

def cycle0621 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 2, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![4, 1, 3, 2, 5])]

def cycle0622 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 2, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![4, 1, 3, 2, 5]), .triangle 1 1]

def cycle0623 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 2, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 1, 3, 2, 5]), .triangle 0 1]

def cycle0624 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 2, 5]), .corridorLower 0 4, .gapLower 0 5 (![4, 1, 3, 2, 5]), .triangle 6 1, .triangle 0 1]

def cycle0625 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![4, 1, 3, 2, 5]), .gapLower 0 2 (![4, 1, 3, 2, 5])]

def cycle0626 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 1, 3, 2, 5]), .triangle 4 2, .gapLower 0 2 (![4, 1, 3, 2, 5])]

def cycle0627 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 3, 2, 5]), .triangle 6 1, .triangle 4 2, .gapLower 0 2 (![4, 1, 3, 2, 5])]

def cycle0628 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![4, 1, 3, 2, 5]), .gapLower 0 3 (![4, 1, 3, 2, 5]), .triangle 1 1]

def cycle0629 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 3, 2, 5]), .triangle 6 1, .gapLower 0 3 (![4, 1, 3, 2, 5]), .triangle 1 1]

def cycle0630 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 3, 2, 5]), .gapLower 0 4 (![4, 1, 3, 2, 5]), .triangle 0 1]

def cycle0631 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0632 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0633 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 5, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0634 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![4, 1, 3, 5, 2])]

def cycle0635 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![4, 1, 3, 5, 2]), .triangle 1 1]

def cycle0636 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 3 1]

def cycle0637 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 3, 5, 2]), .triangle 6 2, .triangle 8 1, .gapLower 0 2 (![4, 1, 3, 5, 2])]

def cycle0638 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 5, 2]), .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0639 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![4, 1, 3, 5, 2])]

def cycle0640 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 3, 5, 2]), .gapLower 1 5 (![4, 0, 3, 5, 2]), .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![4, 1, 3, 5, 2]), .triangle 1 1]

def cycle0641 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![4, 0, 3, 5, 2]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![4, 1, 3, 5, 2]), .triangle 1 1]

def cycle0642 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 2 (![4, 0, 3, 5, 2])]

def cycle0643 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![4, 0, 3, 5, 2]), .triangle 1 0]

def cycle0644 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 0, 3, 5, 2]), .triangle 3 2, .gapLower 0 3 (![4, 1, 3, 5, 2]), .triangle 1 1]

def cycle0645 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 3, 5, 2]), .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![4, 1, 3, 5, 2]), .triangle 1 1]

def cycle0646 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 3 (![4, 1, 3, 5, 2]), .triangle 1 1]

def cycle0647 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 3, 5, 2]), .gapLower 1 5 (![4, 0, 3, 5, 2]), .triangle 0 2, .gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 3 1]

def cycle0648 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 1 (![4, 0, 3, 5, 2]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 8 1, .triangle 1 1]

def cycle0649 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 0, 3, 5, 2]), .triangle 14 1, .triangle 1 0]

def cycle0650 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 9 1, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![4, 0, 3, 5, 2]), .triangle 0 2]

def cycle0651 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 5, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 8 1, .triangle 1 1]

def cycle0652 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 1 (![4, 0, 5, 3, 2]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 8 1, .triangle 1 1]

def cycle0653 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 17 0, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2]

def cycle0654 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 6 1, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0655 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0656 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0)]
    coefficient := ![0, 0, 0]
    strict := ![true, true, true] }
  origin := ![.triangle 2 2, .triangle 7 1, .triangle 1 1]

def cycle0657 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 8 1, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0658 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 3 1]

def cycle0659 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0660 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (-1), (-2), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 6 1, .triangle 18 1, .triangle 9 0, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0661 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 8 1, .gapLower 3 2 (![4, 2, 0, 5, 1]), .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0662 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 5, 2]), .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 0, 5, 3, 2]), .triangle 3 0]

def cycle0663 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 0, 5, 3, 2]), .triangle 1 0]

def cycle0664 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 0 2, .gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 3 1]

def cycle0665 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .gapLower 0 5 (![4, 1, 3, 5, 2]), .triangle 4 0, .triangle 10 0, .triangle 0 0]

def cycle0666 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .gapLower 0 5 (![4, 1, 3, 5, 2]), .triangle 6 0, .triangle 12 0, .gapLower 1 3 (![4, 0, 3, 2, 5]), .gapLower 1 2 (![4, 0, 3, 2, 5])]

def cycle0667 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![4, 0, 3, 5, 2]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 1 0]

def cycle0668 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 3, 5, 2]), .triangle 0 0]

def cycle0669 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 5, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![4, 1, 3, 5, 2])]

def cycle0670 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (0), (0), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .gapLower 0 5 (![4, 1, 3, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0671 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (0), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .gapLower 0 5 (![4, 1, 3, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0672 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (-2), (0), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, true, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 3, 5, 2]), .gapLower 0 5 (![4, 1, 3, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0673 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .triangle 9 0, .gapLower 0 0 (![4, 1, 3, 5, 2]), .gapLower 0 5 (![4, 1, 3, 5, 2])]

def cycle0674 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 4 0, .triangle 17 0, .triangle 8 2, .triangle 9 1, .gapLower 0 0 (![4, 1, 3, 5, 2]), .gapLower 0 5 (![4, 1, 3, 5, 2])]

def cycle0675 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![4, 1, 3, 5, 2])]

def cycle0676 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 5, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![4, 1, 3, 5, 2])]

def cycle0677 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 5, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![4, 1, 3, 5, 2]), .triangle 1 1]

def cycle0678 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 5, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 8 1, .triangle 1 1]

def cycle0679 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![4, 1, 3, 5, 2]), .corridorLower 0 4, .gapLower 0 5 (![4, 1, 3, 5, 2]), .triangle 6 2, .triangle 8 1, .gapLower 0 2 (![4, 1, 3, 5, 2])]

def cycle0680 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![4, 1, 3, 5, 2]), .gapLower 0 2 (![4, 1, 3, 5, 2])]

def cycle0681 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 8 1, .gapLower 0 2 (![4, 1, 3, 5, 2])]

def cycle0682 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 3, 5, 2]), .triangle 6 2, .triangle 8 1, .gapLower 0 2 (![4, 1, 3, 5, 2])]

def cycle0683 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 1, 3, 5, 2]), .gapLower 0 3 (![4, 1, 3, 5, 2]), .triangle 1 1]

def cycle0684 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 3, 5, 2]), .triangle 6 2, .gapLower 0 3 (![4, 1, 3, 5, 2]), .triangle 1 1]

def cycle0685 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 3, 5, 2]), .gapLower 0 4 (![4, 1, 3, 5, 2]), .triangle 3 1]

def cycle0686 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def cycle0687 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 17 2, .triangle 6 0]

def cycle0688 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 17 0, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0689 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 17 2, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0690 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 17 2, .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def cycle0691 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 17 0, .gapLower 3 0 (![2, 4, 5, 0, 1]), .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0692 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![(-1), (-1), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 8 0, .triangle 17 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![2, 4, 5, 0, 1])]

def cycle0693 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![2, 4, 5, 0, 1]), .triangle 1 0]

def cycle0694 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (0), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 19 1, .triangle 9 0, .gapLower 0 0 (![4, 1, 5, 3, 2]), .gapLower 0 5 (![4, 1, 5, 3, 2])]

def cycle0695 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1])]

def cycle0696 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 10 2, .triangle 14 2, .triangle 3 0]

def cycle0697 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 3 (![3, 5, 4, 0, 1]), .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 1, 5, 3, 2]), .gapLower 0 5 (![4, 1, 5, 3, 2])]

def cycle0698 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0699 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 0 3]
    constant := ![(0), (0), (0)]
    coefficient := ![0, 0, 0]
    strict := ![true, true, true] }
  origin := ![.triangle 8 2, .triangle 9 1, .triangle 7 1]

def cycle0700 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 2 5, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, true] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .triangle 17 2, .gapLower 2 0 (![5, 3, 4, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0701 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 2 3, .distance 2 5, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 16 1, .gapLower 2 1 (![5, 3, 4, 0, 1]), .corridorLower 2 5, .corridorUpper 1 2, .triangle 0 0]

def cycle0702 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 2 2 (![5, 3, 4, 0, 1]), .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0703 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 2 3 (![5, 3, 4, 0, 1]), .triangle 16 1, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0704 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 4 (![5, 3, 4, 0, 1])]

def cycle0705 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 3, 4, 0, 1]), .triangle 10 2, .triangle 14 2, .triangle 3 0]

def cycle0706 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 5, 3, 2]), .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 10 2, .gapLower 3 4 (![4, 5, 2, 0, 1]), .triangle 1 1]

def cycle0707 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 2, 0, 1]), .triangle 1 0]

def cycle0708 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 3 (![4, 5, 3, 0, 1]), .gapLower 3 2 (![5, 4, 2, 0, 1]), .triangle 19 0, .triangle 9 0, .gapLower 0 0 (![4, 1, 5, 3, 2]), .gapLower 0 5 (![4, 1, 5, 3, 2])]

def cycle0709 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 10 2, .triangle 14 2, .triangle 3 0]

def cycle0710 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 2 3 (![5, 4, 3, 0, 1]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 1, 5, 3, 2]), .gapLower 0 5 (![4, 1, 5, 3, 2])]

def cycle0711 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0712 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 3, 2]), .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 0, 5, 3, 2]), .triangle 3 0]

def cycle0713 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 0, 5, 3, 2]), .triangle 1 0]

def cycle0714 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (2), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 10 2, .triangle 14 2, .triangle 3 0]

def cycle0715 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 3, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0716 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0717 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 3 1]

def cycle0718 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![4, 1, 5, 3, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0719 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, true, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![4, 1, 5, 3, 2])]

def cycle0720 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 3, 2]), .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0721 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 5, 3, 2]), .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0722 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 1 (![4, 0, 5, 3, 2]), .corridorLower 1 4, .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0723 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 2, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0724 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0725 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![2, 4, 5, 0, 1]), .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0726 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![2, 4, 5, 0, 1]), .triangle 1 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0727 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 4 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 8 0, .triangle 19 1, .triangle 9 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0728 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0729 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0730 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 4 0, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0731 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, true, false, true, true, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 16 1, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0732 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![4, 5, 2, 0, 1]), .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0733 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 2, 0, 1]), .triangle 1 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0734 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 16 0, .triangle 19 0, .triangle 9 0, .gapLower 0 0 (![4, 1, 5, 3, 2]), .gapLower 0 5 (![4, 1, 5, 3, 2])]

def cycle0735 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1]), .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0736 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0737 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 0, .triangle 16 2, .triangle 18 0, .triangle 9 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0738 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 0, 5, 3, 2]), .triangle 3 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0739 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 0, 5, 3, 2]), .triangle 1 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0740 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0741 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 5, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 3 1]

def cycle0742 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1 (![4, 0, 5, 3, 2]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 3 1]

def cycle0743 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 8 1, .triangle 17 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0744 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, true, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 16 1, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0745 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 8 1, .triangle 17 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0746 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-2), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 8 1, .gapLower 3 1 (![4, 5, 2, 0, 1]), .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0747 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![4, 5, 2, 0, 1]), .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 3 1]

def cycle0748 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 2, 0, 1]), .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0749 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 3 (![4, 5, 3, 0, 1]), .triangle 16 0, .triangle 19 0, .triangle 9 0, .gapLower 0 0 (![4, 1, 5, 3, 2]), .gapLower 0 5 (![4, 1, 5, 3, 2])]

def cycle0750 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1]), .triangle 4 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 3 1]

def cycle0751 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0752 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 1, 5, 3, 2]), .gapLower 0 5 (![4, 1, 5, 3, 2])]

def cycle0753 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 0, 5, 3, 2]), .triangle 3 0]

def cycle0754 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 0, 5, 3, 2]), .triangle 1 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 3 1]

def cycle0755 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 3 1]

def cycle0756 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![4, 1, 5, 3, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0757 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .gapLower 0 5 (![4, 1, 5, 3, 2]), .triangle 4 0, .triangle 10 0, .triangle 0 0]

def cycle0758 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-2), (0), (2), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true] }
  origin := ![.triangle 2 0, .gapLower 1 0 (![4, 0, 5, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![4, 1, 5, 3, 2]), .triangle 4 2, .triangle 8 2, .triangle 3 1]

def cycle0759 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (2), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 1 (![4, 0, 5, 3, 2]), .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 5, 3, 2]), .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0760 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (0), (-1), (-1), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .gapLower 0 5 (![4, 1, 5, 3, 2]), .triangle 4 2, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0761 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .gapLower 0 5 (![4, 1, 5, 3, 2]), .triangle 4 0, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0762 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (2), (-1), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .gapLower 0 5 (![4, 1, 5, 3, 2]), .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![4, 0, 5, 3, 2])]

def cycle0763 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0 (![4, 1, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 0, 5, 3, 2]), .triangle 1 0]

def cycle0764 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .gapLower 1 5 (![4, 0, 5, 3, 2]), .triangle 10 2, .triangle 14 2, .triangle 3 0]

def cycle0765 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 3, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0766 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 3, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 3 1]

def cycle0767 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 3, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 1, 5, 3, 2]), .triangle 1 1]

def cycle0768 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 1 (![4, 1, 5, 3, 2]), .corridorLower 0 4, .gapLower 0 5 (![4, 1, 5, 3, 2]), .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0769 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0770 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 1, 5, 3, 2]), .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0771 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 5, 3, 2]), .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![4, 1, 5, 3, 2])]

def cycle0772 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 1, 5, 3, 2]), .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 3 1]

def cycle0773 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 5, 3, 2]), .triangle 4 2, .gapLower 0 3 (![4, 1, 5, 3, 2]), .triangle 3 1]

def cycle0774 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 1, 5, 3, 2]), .gapLower 0 4 (![4, 1, 5, 3, 2]), .triangle 1 1]

def cycle0775 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0776 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0777 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 1, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0778 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![4, 5, 1, 2, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0779 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 2, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0780 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![4, 5, 1, 2, 3])]

def cycle0781 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 5, 1, 2, 3]), .triangle 0 1]

def cycle0782 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 5, 1, 2, 3]), .triangle 1 1]

def cycle0783 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![4, 5, 1, 2, 3]), .gapLower 0 0 (![4, 5, 1, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0784 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 2, 3]), .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0785 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![4, 5, 1, 2, 3])]

def cycle0786 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 0 (![4, 5, 0, 2, 3]), .gapLower 1 5 (![4, 5, 0, 2, 3]), .triangle 1 2, .gapLower 0 4 (![4, 5, 1, 2, 3]), .triangle 0 1]

def cycle0787 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![4, 5, 0, 2, 3]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0788 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2 (![4, 5, 0, 2, 3]), .triangle 15 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![4, 5, 1, 2, 3]), .triangle 0 1]

def cycle0789 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 3 (![4, 5, 0, 2, 3])]

def cycle0790 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![4, 5, 0, 2, 3]), .triangle 0 0]

def cycle0791 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 2, 3]), .triangle 1 2, .gapLower 0 4 (![4, 5, 1, 2, 3]), .triangle 0 1]

def cycle0792 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .gapLower 0 4 (![4, 5, 1, 2, 3]), .triangle 0 1]

def cycle0793 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 1 4, .distance 4 5, .distance 0 4]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 2 1, .triangle 15 0, .triangle 9 0]

def cycle0794 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 0 (![4, 5, 0, 2, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0795 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2 (![4, 5, 0, 2, 3]), .triangle 15 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0796 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 2, 3]), .triangle 1 0]

def cycle0797 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 0 (![4, 5, 0, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .gapLower 0 3 (![4, 5, 1, 2, 3])]

def cycle0798 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![4, 5, 0, 3, 2]), .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 10 0, .triangle 4 0, .gapLower 0 3 (![4, 5, 1, 2, 3])]

def cycle0799 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2 (![4, 5, 0, 3, 2]), .triangle 15 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0800 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0), (0)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, true] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .triangle 0 1]

def cycle0801 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 5, 0, 3, 2]), .triangle 1 0]

def cycle0802 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 10 0, .triangle 4 0, .gapLower 0 3 (![4, 5, 1, 2, 3])]

def cycle0803 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.triangle 2 0, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 1, 2, 3]), .gapLower 0 5 (![4, 5, 1, 2, 3]), .triangle 4 1, .triangle 0 1]

def cycle0804 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 2, 3]), .gapLower 0 1 (![4, 5, 1, 2, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0805 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![4, 5, 1, 2, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![4, 5, 1, 2, 3])]

def cycle0806 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![4, 5, 1, 2, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 5, 1, 2, 3]), .triangle 0 1]

def cycle0807 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![4, 5, 1, 2, 3]), .corridorLower 0 4, .gapLower 0 5 (![4, 5, 1, 2, 3]), .triangle 4 1, .triangle 0 1]

def cycle0808 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 2, 3]), .triangle 9 1, .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![4, 5, 1, 2, 3])]

def cycle0809 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 2, 3]), .triangle 9 1, .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 5, 1, 2, 3]), .triangle 0 1]

def cycle0810 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 2, 3]), .corridorLower 0 5, .gapLower 0 5 (![4, 5, 1, 2, 3]), .triangle 4 1, .triangle 0 1]

def cycle0811 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![4, 5, 1, 2, 3]), .gapLower 0 3 (![4, 5, 1, 2, 3])]

def cycle0812 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 5, 1, 2, 3]), .triangle 4 1, .gapLower 0 3 (![4, 5, 1, 2, 3])]

def cycle0813 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 5, 1, 2, 3]), .gapLower 0 4 (![4, 5, 1, 2, 3]), .triangle 0 1]

def cycle0814 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (0)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, true] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .triangle 1 1]

def cycle0815 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def cycle0816 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![2, 4, 5, 0, 1]), .triangle 1 0]

def cycle0817 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 0 (![4, 5, 0, 3, 2]), .gapLower 1 5 (![4, 5, 0, 3, 2]), .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 0 1]

def cycle0818 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 0]

def cycle0819 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 3 (![3, 5, 4, 0, 1]), .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2])]

def cycle0820 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .triangle 4 0, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0821 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 2 4, .distance 2 3, .distance 2 5, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (0), (-2), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .triangle 16 1, .gapLower 2 1 (![5, 3, 4, 0, 1]), .corridorLower 2 5, .corridorUpper 1 2, .triangle 0 0]

def cycle0822 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .gapLower 2 2 (![5, 3, 4, 0, 1]), .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0823 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 3, 4, 0, 1]), .triangle 0 0]

def cycle0824 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 17 0, .triangle 16 2, .gapLower 2 0 (![4, 3, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0825 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 3, 5, 0, 1]), .triangle 0 0]

def cycle0826 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 0 (![4, 5, 0, 3, 2]), .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 10 2, .gapLower 3 4 (![4, 5, 2, 0, 1]), .triangle 1 1]

def cycle0827 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 2, 0, 1]), .triangle 1 0]

def cycle0828 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 3 (![4, 5, 3, 0, 1]), .gapLower 3 2 (![5, 4, 2, 0, 1]), .triangle 19 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2])]

def cycle0829 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 0]

def cycle0830 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-3), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 2 3 (![5, 4, 3, 0, 1]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2])]

def cycle0831 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![4, 5, 0, 3, 2]), .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 0]

def cycle0832 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 0 1]

def cycle0833 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0834 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 5, 0, 3, 2]), .triangle 1 0]

def cycle0835 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 0]

def cycle0836 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-3), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0837 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![4, 5, 1, 3, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0838 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 3, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0839 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0840 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 1 1]

def cycle0841 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 0 1]

def cycle0842 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![4, 5, 1, 3, 2]), .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0843 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 3, 2]), .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0844 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 0 (![4, 5, 0, 3, 2]), .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0845 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![4, 5, 0, 3, 2]), .gapLower 1 1 (![4, 5, 0, 3, 2]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0846 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 1 2 (![4, 5, 0, 3, 2]), .corridorLower 1 5, .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0847 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0848 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 5 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0849 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (0), (-2), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0850 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0851 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0852 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 7 1, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0853 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0854 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0855 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .triangle 4 0, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0856 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (0), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, false, true, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .triangle 5 1, .triangle 16 1, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0857 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0858 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, true, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 17 1, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0859 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![4, 5, 2, 0, 1]), .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0860 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 2, 0, 1]), .triangle 1 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0861 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 3 (![4, 5, 3, 0, 1]), .triangle 16 0, .triangle 19 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2])]

def cycle0862 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1]), .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0863 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0864 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (-2), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2])]

def cycle0865 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 5, 0, 3, 2]), .triangle 1 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0866 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0867 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 0 (![4, 5, 0, 3, 2]), .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 2, .gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 1 1]

def cycle0868 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![4, 5, 0, 3, 2]), .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0869 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 2 (![4, 5, 0, 3, 2]), .triangle 15 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 1 1]

def cycle0870 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (0), (0), (-2), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 1 1]

def cycle0871 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0872 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0873 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0874 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 1 1]

def cycle0875 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0876 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 4 1, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0877 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 4 1, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0878 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![4, 5, 0, 3, 2]), .triangle 1 0]

def cycle0879 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 2, .gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 1 1]

def cycle0880 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 4 0, .triangle 10 0, .gapLower 1 3 (![4, 5, 0, 2, 3])]

def cycle0881 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (-2), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 15 1, .gapLower 1 0 (![4, 5, 0, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 0 1]

def cycle0882 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 1 (![4, 5, 0, 3, 2]), .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 0 1]

def cycle0883 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.gapLower 1 2 (![4, 5, 0, 3, 2]), .triangle 15 1, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 0 1]

def cycle0884 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (0), (0), (-2), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, true, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 6 0, .triangle 18 1, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0885 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (0), (-2), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 6 0, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0886 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (-2), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 6 0, .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0887 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-2), (0), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true, true, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0888 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 3 (![3, 5, 4, 0, 1]), .triangle 18 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2])]

def cycle0889 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 4 0, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0890 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-2), (2), (-1), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 9 1, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0891 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 15 1, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 0]

def cycle0892 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .distance 0 4, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (-2), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 15 0, .triangle 9 0, .gapLower 0 0 (![4, 5, 1, 3, 2]), .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 0 1]

def cycle0893 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 3, 2]), .gapLower 0 1 (![4, 5, 1, 3, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0894 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![4, 5, 1, 3, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0895 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![4, 5, 1, 3, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 1 1]

def cycle0896 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 1 (![4, 5, 1, 3, 2]), .corridorLower 0 4, .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 0 1]

def cycle0897 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 3, 2]), .triangle 9 1, .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0898 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 3, 2]), .triangle 9 1, .corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 1 1]

def cycle0899 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 2 (![4, 5, 1, 3, 2]), .corridorLower 0 5, .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 0 1]

def cycle0900 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![4, 5, 1, 3, 2]), .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0901 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 5, 1, 3, 2]), .triangle 4 2, .gapLower 0 3 (![4, 5, 1, 3, 2])]

def cycle0902 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![4, 5, 1, 3, 2]), .gapLower 0 4 (![4, 5, 1, 3, 2]), .triangle 1 1]

def cycle0903 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 2, .triangle 3 0]

def cycle0904 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 1, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0905 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 1, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0906 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0907 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![5, 4, 1, 2, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0908 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 1, 2, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0909 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![5, 4, 1, 2, 3])]

def cycle0910 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 4, 1, 2, 3]), .triangle 0 1]

def cycle0911 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![5, 4, 1, 2, 3]), .triangle 1 1]

def cycle0912 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![5, 4, 1, 2, 3]), .gapLower 0 0 (![5, 4, 1, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0913 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 1, 2, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0914 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![5, 4, 1, 2, 3])]

def cycle0915 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 4, 1, 2, 3]), .triangle 0 1]

def cycle0916 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![5, 4, 1, 2, 3]), .triangle 1 1]

def cycle0917 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 1, 2, 3]), .gapLower 0 1 (![5, 4, 1, 2, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0918 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![5, 4, 1, 2, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![5, 4, 1, 2, 3])]

def cycle0919 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![5, 4, 1, 2, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 4, 1, 2, 3]), .triangle 0 1]

def cycle0920 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (3), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![5, 4, 1, 2, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0, .triangle 0 1]

def cycle0921 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 1, 2, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![5, 4, 1, 2, 3])]

def cycle0922 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 2 (![5, 4, 1, 2, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 4, 1, 2, 3]), .triangle 0 1]

def cycle0923 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![5, 4, 1, 2, 3]), .gapLower 0 3 (![5, 4, 1, 2, 3])]

def cycle0924 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![5, 4, 1, 2, 3]), .gapLower 0 4 (![5, 4, 1, 2, 3]), .triangle 0 1]

def cycle0925 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-2), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .gapLower 1 0 (![4, 5, 0, 3, 2]), .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 0]

def cycle0926 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (0), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 2, .gapLower 1 1 (![4, 5, 0, 3, 2]), .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 0]

def cycle0927 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 18 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def cycle0928 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (0), (-2), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .triangle 18 2, .gapLower 2 1 (![3, 5, 4, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def cycle0929 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 2 4, .distance 2 5, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-2), (-1), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 2 2 (![3, 5, 4, 0, 1]), .corridorLower 2 5, .corridorUpper 1 2, .triangle 0 0]

def cycle0930 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (-1), (0), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 2 3 (![3, 5, 4, 0, 1]), .triangle 18 0, .triangle 15 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0931 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1), (4), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 18 0, .triangle 15 0, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 3, 2]), .gapLower 2 4 (![3, 5, 4, 0, 1])]

def cycle0932 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 0]

def cycle0933 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 3, 4, 0, 1]), .triangle 0 0]

def cycle0934 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (-1), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 4 0, .triangle 16 0, .triangle 19 0, .triangle 15 0, .corridorLower 1 4, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0935 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 4 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-2), (0), (-1), (-1), (4), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.triangle 4 0, .triangle 16 2, .gapLower 2 1 (![5, 4, 3, 0, 1]), .triangle 18 1, .triangle 15 0, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 2]

def cycle0936 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (-1), (0), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 2 3 (![5, 4, 3, 0, 1]), .triangle 16 2, .triangle 18 0, .triangle 15 0, .corridorLower 1 4, .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0937 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 4, 3, 0, 1]), .triangle 0 0]

def cycle0938 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (0), (-3), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 2, .gapLower 0 0 (![5, 4, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![4, 5, 0, 3, 2])]

def cycle0939 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (4), (-2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .gapLower 1 0 (![4, 5, 0, 3, 2]), .gapLower 1 5 (![4, 5, 0, 3, 2]), .gapLower 1 4 (![4, 5, 0, 3, 2]), .triangle 1 0]

def cycle0940 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .corridorLower 1 4, .gapLower 1 5 (![4, 5, 0, 3, 2]), .triangle 0 0]

def cycle0941 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![5, 4, 1, 3, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0942 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 1, 3, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0943 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 3 (![5, 4, 1, 3, 2])]

def cycle0944 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 4, 1, 3, 2]), .triangle 1 1]

def cycle0945 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![5, 4, 1, 3, 2]), .triangle 0 1]

def cycle0946 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![5, 4, 1, 3, 2]), .gapLower 0 0 (![5, 4, 1, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0947 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 1, 3, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 0]

def cycle0948 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 3 (![5, 4, 1, 3, 2])]

def cycle0949 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 4, 1, 3, 2]), .triangle 1 1]

def cycle0950 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-1), (-1), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 9 0, .triangle 15 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![5, 4, 1, 3, 2]), .triangle 0 1]

def cycle0951 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 0 2 (![5, 4, 1, 3, 2]), .gapLower 0 1 (![5, 4, 1, 3, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0952 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![5, 4, 1, 3, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 3 (![5, 4, 1, 3, 2])]

def cycle0953 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (-2), (0), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, true, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![5, 4, 1, 3, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 4, 1, 3, 2]), .triangle 1 1]

def cycle0954 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 1 (![5, 4, 1, 3, 2]), .corridorLower 0 5, .gapLower 0 5 (![5, 4, 1, 3, 2]), .triangle 0 1]

def cycle0955 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 2 (![5, 4, 1, 3, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 3 (![5, 4, 1, 3, 2])]

def cycle0956 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true] }
  origin := ![.gapLower 0 2 (![5, 4, 1, 3, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 4, 1, 3, 2]), .triangle 1 1]

def cycle0957 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![5, 4, 1, 3, 2]), .gapLower 0 3 (![5, 4, 1, 3, 2])]

def cycle0958 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![5, 4, 1, 3, 2]), .triangle 4 2, .gapLower 0 3 (![5, 4, 1, 3, 2])]

def cycle0959 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 5 (![5, 4, 1, 3, 2]), .gapLower 0 4 (![5, 4, 1, 3, 2]), .triangle 1 1]

def cycle0960 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0961 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0962 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 4, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0963 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 2 (![3, 1, 2, 4, 5])]

def cycle0964 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![3, 1, 2, 4, 5]), .triangle 0 1]

def cycle0965 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 1, 2, 4, 5]), .triangle 2 1]

def cycle0966 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 2, 4, 5]), .triangle 9 1, .triangle 5 1, .triangle 0 1]

def cycle0967 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 4, 5]), .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle0968 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 2 (![3, 1, 2, 4, 5])]

def cycle0969 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![3, 1, 2, 4, 5]), .triangle 0 1]

def cycle0970 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 2, 4, 5]), .gapLower 1 5 (![3, 0, 2, 4, 5]), .triangle 3 2, .gapLower 0 4 (![3, 1, 2, 4, 5]), .triangle 2 1]

def cycle0971 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 1 (![3, 0, 2, 4, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![3, 1, 2, 4, 5]), .triangle 5 1, .triangle 0 1]

def cycle0972 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 2 (![3, 0, 2, 4, 5])]

def cycle0973 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 3 (![3, 0, 2, 4, 5]), .triangle 0 0]

def cycle0974 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![3, 0, 2, 4, 5]), .triangle 11 1, .triangle 0 0]

def cycle0975 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![3, 0, 2, 4, 5]), .triangle 3 2, .gapLower 0 4 (![3, 1, 2, 4, 5]), .triangle 7 1]

def cycle0976 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![3, 1, 2, 4, 5]), .triangle 2 1]

def cycle0977 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![3, 1, 2, 4, 5]), .triangle 2 1]

def cycle0978 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0979 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![3, 1, 2, 4, 5]), .triangle 2 1]

def cycle0980 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![3, 1, 2, 4, 5]), .triangle 2 1]

def cycle0981 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 2, 4, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0982 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![3, 0, 2, 4, 5]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0983 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 2, 4, 5]), .triangle 3 0]

def cycle0984 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 2, 5, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0985 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1 (![3, 0, 2, 5, 4]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle0986 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 2 (![3, 0, 2, 5, 4])]

def cycle0987 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 2, .gapLower 1 3 (![3, 0, 2, 5, 4]), .triangle 0 0]

def cycle0988 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![3, 0, 2, 5, 4]), .triangle 12 1, .triangle 0 0]

def cycle0989 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 2, 5, 4]), .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![3, 1, 2, 4, 5]), .triangle 0 1]

def cycle0990 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0991 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 4, 5, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0992 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1 (![3, 0, 4, 5, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0993 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![3, 0, 4, 5, 2])]

def cycle0994 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 4, 5]), .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![3, 0, 4, 5, 2]), .triangle 2 0]

def cycle0995 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 4, 5]), .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 0, 4, 5, 2]), .triangle 3 0]

def cycle0996 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 4, 5, 2]), .triangle 11 0, .triangle 5 0, .gapLower 0 2 (![3, 1, 2, 4, 5])]

def cycle0997 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 5, 4, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 5 1, .triangle 0 1]

def cycle0998 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 1 (![3, 0, 5, 4, 2]), .corridorLower 1 3, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![3, 1, 2, 4, 5]), .triangle 0 1]

def cycle0999 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (0), (0)]
    coefficient := ![0, 0, 0]
    strict := ![true, true, true] }
  origin := ![.triangle 1 2, .triangle 4 1, .triangle 0 1]

def cycle1000 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![3, 1, 2, 4, 5])]

def cycle1001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 4, 5]), .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![3, 0, 5, 4, 2]), .triangle 3 0]

def cycle1002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 4, 5]), .gapLower 0 0 (![3, 1, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![3, 0, 5, 4, 2]), .triangle 2 0]

def cycle1003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 5 (![3, 0, 5, 4, 2]), .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![3, 1, 2, 4, 5]), .gapLower 0 2 (![3, 1, 2, 4, 5])]

def cycle1004 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 4, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 2 (![3, 1, 2, 4, 5])]

def cycle1005 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 4, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![3, 1, 2, 4, 5]), .triangle 0 1]

def cycle1006 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 4, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 1, 2, 4, 5]), .triangle 5 1, .triangle 0 1]

def cycle1007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (-1), (2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 4, 5]), .corridorLower 0 3, .gapLower 0 5 (![3, 1, 2, 4, 5]), .triangle 9 1, .triangle 5 1, .triangle 0 1]

def cycle1008 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![3, 1, 2, 4, 5]), .gapLower 0 2 (![3, 1, 2, 4, 5])]

def cycle1009 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 1, 2, 4, 5]), .triangle 5 1, .gapLower 0 2 (![3, 1, 2, 4, 5])]

def cycle1010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 2, 4, 5]), .triangle 9 1, .triangle 5 1, .gapLower 0 2 (![3, 1, 2, 4, 5])]

def cycle1011 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![3, 1, 2, 4, 5]), .gapLower 0 3 (![3, 1, 2, 4, 5]), .triangle 0 1]

def cycle1012 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 2, 4, 5]), .triangle 9 1, .gapLower 0 3 (![3, 1, 2, 4, 5]), .triangle 0 1]

def cycle1013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (-1), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 2, 4, 5]), .gapLower 0 4 (![3, 1, 2, 4, 5]), .triangle 2 1]

def cycle1014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 0 0]

def cycle1015 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle1016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 5, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle1017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 2 (![3, 1, 2, 5, 4])]

def cycle1018 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![3, 1, 2, 5, 4]), .triangle 0 1]

def cycle1019 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![3, 1, 2, 5, 4]), .triangle 3 1]

def cycle1020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-1), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, true] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .thetaOrder 0, .gapLower 0 5 (![3, 1, 2, 5, 4]), .triangle 5 1, .triangle 0 1]

def cycle1021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![(-2), (-2), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1 (![3, 1, 2, 5, 4]), .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

def cycle1022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0 (![3, 1, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 2 (![3, 1, 2, 5, 4])]

def cycle1023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (-2), (4), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0 (![3, 0, 2, 5, 4]), .gapLower 1 5 (![3, 0, 2, 5, 4]), .triangle 15 2, .triangle 3 2, .gapLower 0 3 (![3, 1, 2, 5, 4]), .triangle 0 1]

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
  | 0 => some (.leaf 1950)
  | 1 => some (.leaf 1951)
  | 2 => some (.leaf 1952)
  | 3 => some (.positive 0 (![3069, 3070, 3071, 3072, 3073, 3074]))
  | 4 => some (.leaf 1953)
  | 5 => some (.triangle 12 3075 3076)
  | 6 => some (.leaf 1954)
  | 7 => some (.triangle 14 3077 3078)
  | 8 => some (.leaf 1955)
  | 9 => some (.triangle 15 3079 3080)
  | 10 => some (.triangle 13 1425 3081)
  | 11 => some (.triangle 10 2251 3082)
  | 12 => some (.leaf 1956)
  | 13 => some (.leaf 1957)
  | 14 => some (.triangle 16 3084 3085)
  | 15 => some (.leaf 1958)
  | 16 => some (.leaf 1959)
  | 17 => some (.triangle 16 3087 3088)
  | 18 => some (.positive 0 (![3086, 3070, 3071, 3072, 3073, 3089]))
  | 19 => some (.leaf 1960)
  | 20 => some (.triangle 12 3090 3091)
  | 21 => some (.triangle 14 3092 1503)
  | 22 => some (.leaf 1961)
  | 23 => some (.leaf 1962)
  | 24 => some (.triangle 16 3094 3095)
  | 25 => some (.leaf 1963)
  | 26 => some (.leaf 1964)
  | 27 => some (.triangle 16 3097 3098)
  | 28 => some (.leaf 1965)
  | 29 => some (.leaf 1966)
  | 30 => some (.leaf 1967)
  | 31 => some (.leaf 1968)
  | 32 => some (.positive 0 (![3096, 3099, 3100, 3101, 3102, 3103]))
  | 33 => some (.triangle 15 3093 3104)
  | 34 => some (.triangle 13 1425 3105)
  | 35 => some (.triangle 10 2251 3106)
  | 36 => some (.leaf 1969)
  | 37 => some (.leaf 1970)
  | 38 => some (.leaf 1971)
  | 39 => some (.leaf 1972)
  | 40 => some (.leaf 1973)
  | 41 => some (.leaf 1974)
  | 42 => some (.leaf 1975)
  | 43 => some (.leaf 1976)
  | 44 => some (.leaf 1977)
  | 45 => some (.leaf 1978)
  | 46 => some (.heavy (![3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3083, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117]))
  | 47 => some (.leaf 1979)
  | 48 => some (.leaf 1980)
  | 49 => some (.triangle 15 3119 3120)
  | 50 => some (.triangle 13 1425 3121)
  | 51 => some (.triangle 10 2251 3122)
  | 52 => some (.leaf 1981)
  | 53 => some (.leaf 1982)
  | 54 => some (.leaf 1983)
  | 55 => some (.leaf 1984)
  | 56 => some (.leaf 1985)
  | 57 => some (.leaf 1986)
  | 58 => some (.leaf 1987)
  | 59 => some (.leaf 1988)
  | 60 => some (.leaf 1989)
  | 61 => some (.leaf 1990)
  | 62 => some (.leaf 1991)
  | 63 => some (.leaf 1992)
  | 64 => some (.leaf 1993)
  | 65 => some (.triangle 16 3135 3136)
  | 66 => some (.leaf 1994)
  | 67 => some (.leaf 1995)
  | 68 => some (.leaf 1996)
  | 69 => some (.leaf 1997)
  | 70 => some (.leaf 1998)
  | 71 => some (.leaf 1999)
  | 72 => some (.triangle 16 3142 3143)
  | 73 => some (.positive 0 (![3137, 3138, 3139, 3140, 3141, 3144]))
  | 74 => some (.triangle 12 3134 3145)
  | 75 => some (.triangle 14 3146 1503)
  | 76 => some (.leaf 2000)
  | 77 => some (.triangle 16 3097 3148)
  | 78 => some (.leaf 2001)
  | 79 => some (.triangle 16 3097 3150)
  | 80 => some (.leaf 2002)
  | 81 => some (.leaf 2003)
  | 82 => some (.leaf 2004)
  | 83 => some (.leaf 2005)
  | 84 => some (.positive 0 (![3149, 3151, 3152, 3153, 3154, 3155]))
  | 85 => some (.triangle 15 3147 3156)
  | 86 => some (.triangle 13 1425 3157)
  | 87 => some (.triangle 10 3133 3158)
  | 88 => some (.leaf 2006)
  | 89 => some (.leaf 2007)
  | 90 => some (.leaf 2008)
  | 91 => some (.leaf 2009)
  | 92 => some (.leaf 2010)
  | 93 => some (.leaf 2011)
  | 94 => some (.leaf 2012)
  | 95 => some (.leaf 2013)
  | 96 => some (.leaf 2014)
  | 97 => some (.leaf 2015)
  | 98 => some (.heavy (![3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169]))
  | 99 => some (.triangle 6 3118 3170)
  | 100 => some (.leaf 2016)
  | 101 => some (.leaf 2017)
  | 102 => some (.triangle 15 3172 3173)
  | 103 => some (.triangle 13 1425 3174)
  | 104 => some (.triangle 10 2251 3175)
  | 105 => some (.leaf 2018)
  | 106 => some (.leaf 2019)
  | 107 => some (.leaf 2020)
  | 108 => some (.leaf 2021)
  | 109 => some (.leaf 2022)
  | 110 => some (.leaf 2023)
  | 111 => some (.leaf 2024)
  | 112 => some (.leaf 2025)
  | 113 => some (.leaf 2026)
  | 114 => some (.leaf 2027)
  | 115 => some (.leaf 2028)
  | 116 => some (.leaf 2029)
  | 117 => some (.leaf 2030)
  | 118 => some (.leaf 2031)
  | 119 => some (.positive 2 (![3185, 3186, 3187, 3188, 3189, 3190]))
  | 120 => some (.leaf 2032)
  | 121 => some (.triangle 19 3191 3192)
  | 122 => some (.leaf 2033)
  | 123 => some (.leaf 2034)
  | 124 => some (.leaf 2035)
  | 125 => some (.leaf 2036)
  | 126 => some (.leaf 2037)
  | 127 => some (.positive 1 (![3193, 3194, 3195, 3196, 3197, 3198]))
  | 128 => some (.triangle 17 3184 3199)
  | 129 => some (.leaf 2038)
  | 130 => some (.triangle 18 3200 3201)
  | 131 => some (.triangle 16 3183 3202)
  | 132 => some (.leaf 2039)
  | 133 => some (.leaf 2040)
  | 134 => some (.leaf 2041)
  | 135 => some (.leaf 2042)
  | 136 => some (.leaf 2043)
  | 137 => some (.positive 0 (![3203, 3204, 3205, 3206, 3207, 3208]))
  | 138 => some (.triangle 14 1345 3209)
  | 139 => some (.leaf 2044)
  | 140 => some (.triangle 15 3210 3211)
  | 141 => some (.triangle 13 1425 3212)
  | 142 => some (.triangle 10 2251 3213)
  | 143 => some (.leaf 2045)
  | 144 => some (.leaf 2046)
  | 145 => some (.leaf 2047)
  | 146 => some (.leaf 2048)
  | 147 => some (.leaf 2049)
  | 148 => some (.positive 2 (![3185, 3217, 3187, 3188, 3218, 3219]))
  | 149 => some (.leaf 2050)
  | 150 => some (.triangle 19 3220 3221)
  | 151 => some (.leaf 2051)
  | 152 => some (.leaf 2052)
  | 153 => some (.positive 1 (![3222, 3194, 3195, 3196, 3223, 3224]))
  | 154 => some (.triangle 17 3216 3225)
  | 155 => some (.leaf 2053)
  | 156 => some (.triangle 18 3226 3227)
  | 157 => some (.triangle 16 3215 3228)
  | 158 => some (.leaf 2054)
  | 159 => some (.leaf 2055)
  | 160 => some (.leaf 2056)
  | 161 => some (.positive 0 (![3229, 3204, 3205, 3230, 3231, 3232]))
  | 162 => some (.triangle 14 1345 3233)
  | 163 => some (.leaf 2057)
  | 164 => some (.leaf 2058)
  | 165 => some (.leaf 2059)
  | 166 => some (.leaf 2060)
  | 167 => some (.positive 1 (![3236, 3237, 3195, 3196, 3223, 3238]))
  | 168 => some (.triangle 17 3216 3239)
  | 169 => some (.leaf 2061)
  | 170 => some (.triangle 18 3240 3241)
  | 171 => some (.triangle 16 3235 3242)
  | 172 => some (.leaf 2062)
  | 173 => some (.leaf 2063)
  | 174 => some (.positive 1 (![3236, 3237, 3195, 3196, 3244, 3245]))
  | 175 => some (.triangle 17 3216 3246)
  | 176 => some (.leaf 2064)
  | 177 => some (.triangle 18 3247 3248)
  | 178 => some (.triangle 16 3235 3249)
  | 179 => some (.leaf 2065)
  | 180 => some (.leaf 2066)
  | 181 => some (.leaf 2067)
  | 182 => some (.leaf 2068)
  | 183 => some (.positive 0 (![3243, 3250, 3251, 3252, 3253, 3254]))
  | 184 => some (.triangle 15 3234 3255)
  | 185 => some (.triangle 13 1425 3256)
  | 186 => some (.triangle 10 2251 3257)
  | 187 => some (.leaf 2069)
  | 188 => some (.leaf 2070)
  | 189 => some (.leaf 2071)
  | 190 => some (.leaf 2072)
  | 191 => some (.triangle 16 3261 3262)
  | 192 => some (.leaf 2073)
  | 193 => some (.leaf 2074)
  | 194 => some (.leaf 2075)
  | 195 => some (.triangle 16 3265 3266)
  | 196 => some (.positive 0 (![3263, 3204, 3205, 3230, 3264, 3267]))
  | 197 => some (.triangle 14 1345 3268)
  | 198 => some (.leaf 2076)
  | 199 => some (.triangle 16 3097 3270)
  | 200 => some (.leaf 2077)
  | 201 => some (.triangle 16 3097 3272)
  | 202 => some (.leaf 2078)
  | 203 => some (.leaf 2079)
  | 204 => some (.positive 0 (![3271, 3273, 3251, 3252, 3274, 3275]))
  | 205 => some (.triangle 15 3269 3276)
  | 206 => some (.triangle 13 1425 3277)
  | 207 => some (.triangle 10 3260 3278)
  | 208 => some (.leaf 2080)
  | 209 => some (.leaf 2081)
  | 210 => some (.leaf 2082)
  | 211 => some (.leaf 2083)
  | 212 => some (.leaf 2084)
  | 213 => some (.leaf 2085)
  | 214 => some (.leaf 2086)
  | 215 => some (.leaf 2087)
  | 216 => some (.leaf 2088)
  | 217 => some (.heavy (![3176, 3177, 3178, 3179, 3180, 3181, 3182, 3214, 3258, 3259, 3279, 3280, 3281, 3282, 3283, 3284, 3285, 3286, 3259, 3287, 3288]))
  | 218 => some (.triangle 8 3171 3289)
  | 219 => some (.leaf 2089)
  | 220 => some (.leaf 2090)
  | 221 => some (.leaf 2091)
  | 222 => some (.leaf 2092)
  | 223 => some (.leaf 2093)
  | 224 => some (.leaf 2094)
  | 225 => some (.leaf 2095)
  | 226 => some (.triangle 19 3296 3297)
  | 227 => some (.leaf 2096)
  | 228 => some (.leaf 2097)
  | 229 => some (.positive 1 (![3293, 3294, 3295, 3298, 3299, 3300]))
  | 230 => some (.triangle 6 3292 3301)
  | 231 => some (.leaf 2098)
  | 232 => some (.leaf 2099)
  | 233 => some (.leaf 2100)
  | 234 => some (.leaf 2101)
  | 235 => some (.leaf 2102)
  | 236 => some (.positive 1 (![3303, 3304, 3305, 2865, 3306, 3307]))
  | 237 => some (.triangle 18 3302 3308)
  | 238 => some (.triangle 5 3291 3309)
  | 239 => some (.leaf 2103)
  | 240 => some (.triangle 17 3310 3311)
  | 241 => some (.leaf 2104)
  | 242 => some (.leaf 2105)
  | 243 => some (.leaf 2106)
  | 244 => some (.leaf 2107)
  | 245 => some (.leaf 2108)
  | 246 => some (.leaf 2109)
  | 247 => some (.positive 1 (![3313, 3314, 3315, 3316, 3317, 3318]))
  | 248 => some (.triangle 6 3292 3319)
  | 249 => some (.leaf 2110)
  | 250 => some (.leaf 2111)
  | 251 => some (.leaf 2112)
  | 252 => some (.leaf 2113)
  | 253 => some (.positive 1 (![3321, 3322, 3195, 3196, 3323, 3324]))
  | 254 => some (.triangle 17 3320 3325)
  | 255 => some (.leaf 2114)
  | 256 => some (.leaf 2115)
  | 257 => some (.triangle 19 3327 3328)
  | 258 => some (.leaf 2116)
  | 259 => some (.leaf 2117)
  | 260 => some (.leaf 2118)
  | 261 => some (.leaf 2119)
  | 262 => some (.leaf 2120)
  | 263 => some (.positive 1 (![3329, 3330, 3331, 3332, 3333, 3334]))
  | 264 => some (.triangle 18 3326 3335)
  | 265 => some (.triangle 16 3312 3336)
  | 266 => some (.leaf 2121)
  | 267 => some (.leaf 2122)
  | 268 => some (.leaf 2123)
  | 269 => some (.leaf 2124)
  | 270 => some (.leaf 2125)
  | 271 => some (.positive 0 (![3337, 3338, 3339, 3340, 3341, 3342]))
  | 272 => some (.triangle 15 1161 3343)
  | 273 => some (.triangle 13 1425 3344)
  | 274 => some (.triangle 10 2251 3345)
  | 275 => some (.leaf 2126)
  | 276 => some (.leaf 2127)
  | 277 => some (.positive 1 (![3293, 3294, 3295, 3298, 3299, 3348]))
  | 278 => some (.triangle 6 3292 3349)
  | 279 => some (.leaf 2128)
  | 280 => some (.positive 1 (![3303, 3304, 3305, 2865, 3306, 3351]))
  | 281 => some (.triangle 18 3350 3352)
  | 282 => some (.triangle 5 3291 3353)
  | 283 => some (.triangle 17 3354 3311)
  | 284 => some (.leaf 2129)
  | 285 => some (.leaf 2130)
  | 286 => some (.positive 1 (![3313, 3314, 3315, 3316, 3356, 3357]))
  | 287 => some (.triangle 6 3292 3358)
  | 288 => some (.leaf 2131)
  | 289 => some (.leaf 2132)
  | 290 => some (.positive 1 (![3321, 3322, 3195, 3196, 3360, 3361]))
  | 291 => some (.triangle 17 3359 3362)
  | 292 => some (.leaf 2133)
  | 293 => some (.leaf 2134)
  | 294 => some (.positive 1 (![3329, 3330, 3331, 3332, 3364, 3365]))
  | 295 => some (.triangle 18 3363 3366)
  | 296 => some (.triangle 16 3355 3367)
  | 297 => some (.leaf 2135)
  | 298 => some (.leaf 2136)
  | 299 => some (.leaf 2137)
  | 300 => some (.leaf 2138)
  | 301 => some (.positive 0 (![3347, 3368, 3369, 3370, 3371, 3372]))
  | 302 => some (.triangle 15 1161 3373)
  | 303 => some (.triangle 13 1425 3374)
  | 304 => some (.triangle 10 2251 3375)
  | 305 => some (.leaf 2139)
  | 306 => some (.leaf 2140)
  | 307 => some (.leaf 2141)
  | 308 => some (.leaf 2142)
  | 309 => some (.leaf 2143)
  | 310 => some (.leaf 2144)
  | 311 => some (.positive 1 (![3293, 3294, 3295, 3298, 3381, 3382]))
  | 312 => some (.triangle 6 3292 3383)
  | 313 => some (.leaf 2145)
  | 314 => some (.leaf 2146)
  | 315 => some (.positive 1 (![3303, 3304, 3305, 2865, 3385, 3386]))
  | 316 => some (.triangle 18 3384 3387)
  | 317 => some (.triangle 5 3291 3388)
  | 318 => some (.triangle 17 3389 3311)
  | 319 => some (.leaf 2147)
  | 320 => some (.leaf 2148)
  | 321 => some (.positive 1 (![3313, 3314, 3315, 3316, 3391, 3392]))
  | 322 => some (.triangle 6 3292 3393)
  | 323 => some (.leaf 2149)
  | 324 => some (.leaf 2150)
  | 325 => some (.positive 1 (![3321, 3322, 3195, 3196, 3395, 3396]))
  | 326 => some (.triangle 17 3394 3397)
  | 327 => some (.leaf 2151)
  | 328 => some (.leaf 2152)
  | 329 => some (.positive 1 (![3329, 3330, 3331, 3332, 3399, 3400]))
  | 330 => some (.triangle 18 3398 3401)
  | 331 => some (.triangle 16 3390 3402)
  | 332 => some (.leaf 2153)
  | 333 => some (.leaf 2154)
  | 334 => some (.positive 1 (![3293, 3294, 3295, 3298, 3404, 3405]))
  | 335 => some (.triangle 6 3292 3406)
  | 336 => some (.leaf 2155)
  | 337 => some (.leaf 2156)
  | 338 => some (.positive 1 (![3303, 3304, 3305, 2865, 3408, 3409]))
  | 339 => some (.triangle 18 3407 3410)
  | 340 => some (.triangle 5 3291 3411)
  | 341 => some (.triangle 17 3412 3311)
  | 342 => some (.leaf 2157)
  | 343 => some (.leaf 2158)
  | 344 => some (.positive 1 (![3313, 3314, 3315, 3316, 3414, 3415]))
  | 345 => some (.triangle 6 3292 3416)
  | 346 => some (.leaf 2159)
  | 347 => some (.leaf 2160)
  | 348 => some (.positive 1 (![3321, 3322, 3195, 3196, 3418, 3419]))
  | 349 => some (.triangle 17 3417 3420)
  | 350 => some (.leaf 2161)
  | 351 => some (.leaf 2162)
  | 352 => some (.positive 1 (![3329, 3330, 3331, 3332, 3422, 3423]))
  | 353 => some (.triangle 18 3421 3424)
  | 354 => some (.triangle 16 3413 3425)
  | 355 => some (.leaf 2163)
  | 356 => some (.leaf 2164)
  | 357 => some (.leaf 2165)
  | 358 => some (.leaf 2166)
  | 359 => some (.positive 0 (![3403, 3426, 3427, 3428, 3429, 3430]))
  | 360 => some (.triangle 15 1161 3431)
  | 361 => some (.triangle 13 1425 3432)
  | 362 => some (.triangle 10 2251 3433)
  | 363 => some (.leaf 2167)
  | 364 => some (.leaf 2168)
  | 365 => some (.leaf 2169)
  | 366 => some (.positive 1 (![3303, 3304, 3305, 2865, 3436, 3437]))
  | 367 => some (.triangle 18 3435 3438)
  | 368 => some (.triangle 5 3291 3439)
  | 369 => some (.triangle 17 3440 3311)
  | 370 => some (.leaf 2170)
  | 371 => some (.leaf 2171)
  | 372 => some (.triangle 19 3443 3328)
  | 373 => some (.leaf 2172)
  | 374 => some (.leaf 2173)
  | 375 => some (.positive 1 (![3444, 3330, 3331, 3332, 3445, 3446]))
  | 376 => some (.triangle 18 3442 3447)
  | 377 => some (.triangle 16 3441 3448)
  | 378 => some (.leaf 2174)
  | 379 => some (.leaf 2175)
  | 380 => some (.positive 1 (![3303, 3304, 3305, 2865, 3450, 3451]))
  | 381 => some (.triangle 18 3435 3452)
  | 382 => some (.triangle 5 3291 3453)
  | 383 => some (.triangle 17 3454 3311)
  | 384 => some (.leaf 2176)
  | 385 => some (.positive 1 (![3444, 3330, 3331, 3332, 3445, 3456]))
  | 386 => some (.triangle 18 3442 3457)
  | 387 => some (.triangle 16 3455 3458)
  | 388 => some (.leaf 2177)
  | 389 => some (.leaf 2178)
  | 390 => some (.leaf 2179)
  | 391 => some (.leaf 2180)
  | 392 => some (.positive 0 (![3449, 3459, 3460, 3461, 3462, 3463]))
  | 393 => some (.triangle 15 1161 3464)
  | 394 => some (.triangle 13 1425 3465)
  | 395 => some (.triangle 10 2251 3466)
  | 396 => some (.leaf 2181)
  | 397 => some (.leaf 2182)
  | 398 => some (.leaf 2183)
  | 399 => some (.leaf 2184)
  | 400 => some (.leaf 2185)
  | 401 => some (.triangle 16 3471 3472)
  | 402 => some (.leaf 2186)
  | 403 => some (.leaf 2187)
  | 404 => some (.triangle 16 3474 3475)
  | 405 => some (.leaf 2188)
  | 406 => some (.leaf 2189)
  | 407 => some (.leaf 2190)
  | 408 => some (.leaf 2191)
  | 409 => some (.triangle 16 3479 3480)
  | 410 => some (.positive 0 (![3473, 3476, 3460, 3477, 3478, 3481]))
  | 411 => some (.triangle 15 1161 3482)
  | 412 => some (.triangle 13 1425 3483)
  | 413 => some (.triangle 10 3470 3484)
  | 414 => some (.leaf 2192)
  | 415 => some (.leaf 2193)
  | 416 => some (.leaf 2194)
  | 417 => some (.leaf 2195)
  | 418 => some (.leaf 2196)
  | 419 => some (.leaf 2197)
  | 420 => some (.leaf 2198)
  | 421 => some (.leaf 2199)
  | 422 => some (.leaf 2200)
  | 423 => some (.leaf 2201)
  | 424 => some (.heavy (![3346, 3376, 3377, 3378, 3379, 3380, 3434, 3467, 3468, 3469, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3494, 3495]))
  | 425 => some (.triangle 9 3290 3496)
  | 426 => some (.triangle 7 3053 3497)
  | 427 => some (.triangle 4 2250 3498)
  | 428 => some (.leaf 2202)
  | 429 => some (.leaf 2203)
  | 430 => some (.triangle 10 3500 3501)
  | 431 => some (.leaf 2204)
  | 432 => some (.leaf 2205)
  | 433 => some (.leaf 2206)
  | 434 => some (.leaf 2207)
  | 435 => some (.leaf 2208)
  | 436 => some (.leaf 2209)
  | 437 => some (.leaf 2210)
  | 438 => some (.leaf 2211)
  | 439 => some (.leaf 2212)
  | 440 => some (.leaf 2213)
  | 441 => some (.leaf 2214)
  | 442 => some (.leaf 2215)
  | 443 => some (.leaf 2216)
  | 444 => some (.leaf 2217)
  | 445 => some (.positive 0 (![3511, 3512, 3513, 3514, 3515, 3516]))
  | 446 => some (.leaf 2218)
  | 447 => some (.triangle 13 3517 3518)
  | 448 => some (.leaf 2219)
  | 449 => some (.triangle 11 3519 3520)
  | 450 => some (.leaf 2220)
  | 451 => some (.leaf 2221)
  | 452 => some (.triangle 11 3522 3523)
  | 453 => some (.leaf 2222)
  | 454 => some (.triangle 13 3524 3525)
  | 455 => some (.triangle 10 3521 3526)
  | 456 => some (.leaf 2223)
  | 457 => some (.leaf 2224)
  | 458 => some (.leaf 2225)
  | 459 => some (.positive 0 (![3528, 3529, 3513, 3514, 3515, 3530]))
  | 460 => some (.leaf 2226)
  | 461 => some (.leaf 2227)
  | 462 => some (.leaf 2228)
  | 463 => some (.leaf 2229)
  | 464 => some (.leaf 2230)
  | 465 => some (.leaf 2231)
  | 466 => some (.positive 0 (![3532, 3533, 3534, 3535, 3536, 3537]))
  | 467 => some (.triangle 13 3531 3538)
  | 468 => some (.leaf 2232)
  | 469 => some (.triangle 11 3539 3540)
  | 470 => some (.leaf 2233)
  | 471 => some (.leaf 2234)
  | 472 => some (.leaf 2235)
  | 473 => some (.leaf 2236)
  | 474 => some (.leaf 2237)
  | 475 => some (.leaf 2238)
  | 476 => some (.positive 0 (![3542, 3543, 3544, 3545, 3546, 3547]))
  | 477 => some (.triangle 11 3522 3548)
  | 478 => some (.leaf 2239)
  | 479 => some (.leaf 2240)
  | 480 => some (.leaf 2241)
  | 481 => some (.leaf 2242)
  | 482 => some (.triangle 6 3552 3553)
  | 483 => some (.leaf 2243)
  | 484 => some (.leaf 2244)
  | 485 => some (.leaf 2245)
  | 486 => some (.positive 0 (![3550, 3551, 3554, 3555, 3556, 3557]))
  | 487 => some (.triangle 13 3549 3558)
  | 488 => some (.triangle 10 3541 3559)
  | 489 => some (.leaf 2246)
  | 490 => some (.leaf 2247)
  | 491 => some (.leaf 2248)
  | 492 => some (.leaf 2249)
  | 493 => some (.leaf 2250)
  | 494 => some (.leaf 2251)
  | 495 => some (.leaf 2252)
  | 496 => some (.leaf 2253)
  | 497 => some (.leaf 2254)
  | 498 => some (.leaf 2255)
  | 499 => some (.heavy (![3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3527, 3560, 3561, 3562, 3563, 3564, 3565, 3566, 3567, 3568, 3569, 3570]))
  | 500 => some (.leaf 2256)
  | 501 => some (.leaf 2257)
  | 502 => some (.triangle 10 3572 3573)
  | 503 => some (.leaf 2258)
  | 504 => some (.leaf 2259)
  | 505 => some (.leaf 2260)
  | 506 => some (.leaf 2261)
  | 507 => some (.leaf 2262)
  | 508 => some (.leaf 2263)
  | 509 => some (.leaf 2264)
  | 510 => some (.leaf 2265)
  | 511 => some (.leaf 2266)
  | 512 => some (.leaf 2267)
  | 513 => some (.leaf 2268)
  | 514 => some (.leaf 2269)
  | 515 => some (.leaf 2270)
  | 516 => some (.positive 0 (![3582, 3583, 3584, 3585, 3586, 3587]))
  | 517 => some (.triangle 13 1425 3588)
  | 518 => some (.leaf 2271)
  | 519 => some (.triangle 11 3589 3590)
  | 520 => some (.leaf 2272)
  | 521 => some (.triangle 10 3591 3592)
  | 522 => some (.leaf 2273)
  | 523 => some (.leaf 2274)
  | 524 => some (.leaf 2275)
  | 525 => some (.leaf 2276)
  | 526 => some (.positive 0 (![3594, 3595, 3584, 3585, 3596, 3597]))
  | 527 => some (.triangle 13 1425 3598)
  | 528 => some (.leaf 2277)
  | 529 => some (.triangle 11 3599 3600)
  | 530 => some (.leaf 2278)
  | 531 => some (.triangle 10 3601 3602)
  | 532 => some (.leaf 2279)
  | 533 => some (.leaf 2280)
  | 534 => some (.leaf 2281)
  | 535 => some (.positive 0 (![3605, 3533, 3584, 3585, 3596, 3606]))
  | 536 => some (.triangle 13 3604 3607)
  | 537 => some (.triangle 11 3608 3600)
  | 538 => some (.leaf 2282)
  | 539 => some (.leaf 2283)
  | 540 => some (.leaf 2284)
  | 541 => some (.triangle 6 3552 1894)
  | 542 => some (.leaf 2285)
  | 543 => some (.leaf 2286)
  | 544 => some (.leaf 2287)
  | 545 => some (.positive 0 (![3611, 3612, 3613, 3614, 3615, 3616]))
  | 546 => some (.triangle 13 3610 3617)
  | 547 => some (.triangle 10 3609 3618)
  | 548 => some (.leaf 2288)
  | 549 => some (.leaf 2289)
  | 550 => some (.leaf 2290)
  | 551 => some (.leaf 2291)
  | 552 => some (.leaf 2292)
  | 553 => some (.leaf 2293)
  | 554 => some (.leaf 2294)
  | 555 => some (.leaf 2295)
  | 556 => some (.leaf 2296)
  | 557 => some (.leaf 2297)
  | 558 => some (.heavy (![3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3593, 3603, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629]))
  | 559 => some (.triangle 7 3571 3630)
  | 560 => some (.leaf 2298)
  | 561 => some (.leaf 2299)
  | 562 => some (.triangle 10 3632 3633)
  | 563 => some (.leaf 2300)
  | 564 => some (.leaf 2301)
  | 565 => some (.leaf 2302)
  | 566 => some (.leaf 2303)
  | 567 => some (.leaf 2304)
  | 568 => some (.leaf 2305)
  | 569 => some (.leaf 2306)
  | 570 => some (.leaf 2307)
  | 571 => some (.leaf 2308)
  | 572 => some (.leaf 2309)
  | 573 => some (.leaf 2310)
  | 574 => some (.leaf 2311)
  | 575 => some (.leaf 2312)
  | 576 => some (.leaf 2313)
  | 577 => some (.positive 0 (![3643, 3644, 3645, 3646, 3647, 3648]))
  | 578 => some (.triangle 11 2017 3649)
  | 579 => some (.leaf 2314)
  | 580 => some (.triangle 10 3650 3651)
  | 581 => some (.leaf 2315)
  | 582 => some (.leaf 2316)
  | 583 => some (.leaf 2317)
  | 584 => some (.positive 0 (![3653, 3654, 3645, 3646, 3647, 3655]))
  | 585 => some (.triangle 11 2017 3656)
  | 586 => some (.triangle 10 3657 2034)
  | 587 => some (.leaf 2318)
  | 588 => some (.leaf 2319)
  | 589 => some (.leaf 2320)
  | 590 => some (.leaf 2321)
  | 591 => some (.leaf 2322)
  | 592 => some (.leaf 2323)
  | 593 => some (.leaf 2324)
  | 594 => some (.leaf 2325)
  | 595 => some (.leaf 2326)
  | 596 => some (.leaf 2327)
  | 597 => some (.heavy (![3634, 3635, 3636, 3637, 3638, 3639, 3640, 3641, 3642, 3652, 3658, 3659, 3660, 3661, 3662, 3663, 3664, 3665, 3666, 3667, 3668]))
  | 598 => some (.triangle 5 3631 3669)
  | 599 => some (.leaf 2328)
  | 600 => some (.leaf 2329)
  | 601 => some (.triangle 13 3671 3672)
  | 602 => some (.triangle 10 2251 3673)
  | 603 => some (.leaf 2330)
  | 604 => some (.leaf 2331)
  | 605 => some (.leaf 2332)
  | 606 => some (.leaf 2333)
  | 607 => some (.leaf 2334)
  | 608 => some (.leaf 2335)
  | 609 => some (.leaf 2336)
  | 610 => some (.leaf 2337)
  | 611 => some (.leaf 2338)
  | 612 => some (.leaf 2339)
  | 613 => some (.leaf 2340)
  | 614 => some (.leaf 2341)
  | 615 => some (.leaf 2342)
  | 616 => some (.leaf 2343)
  | 617 => some (.positive 0 (![3683, 3684, 3685, 3686, 3687, 3688]))
  | 618 => some (.leaf 2344)
  | 619 => some (.triangle 11 3689 3690)
  | 620 => some (.leaf 2345)
  | 621 => some (.triangle 13 3691 3692)
  | 622 => some (.triangle 10 2251 3693)
  | 623 => some (.leaf 2346)
  | 624 => some (.leaf 2347)
  | 625 => some (.leaf 2348)
  | 626 => some (.positive 0 (![3695, 3696, 3685, 3686, 3687, 3697]))
  | 627 => some (.triangle 11 3698 2277)
  | 628 => some (.leaf 2349)
  | 629 => some (.leaf 2350)
  | 630 => some (.leaf 2351)
  | 631 => some (.leaf 2352)
  | 632 => some (.triangle 11 3703 2487)
  | 633 => some (.triangle 6 3702 3704)
  | 634 => some (.leaf 2353)
  | 635 => some (.triangle 17 3705 3706)
  | 636 => some (.leaf 2354)
  | 637 => some (.leaf 2355)
  | 638 => some (.leaf 2356)
  | 639 => some (.positive 0 (![3700, 3701, 3707, 3708, 3709, 3710]))
  | 640 => some (.triangle 13 3699 3711)
  | 641 => some (.triangle 10 2251 3712)
  | 642 => some (.leaf 2357)
  | 643 => some (.leaf 2358)
  | 644 => some (.leaf 2359)
  | 645 => some (.leaf 2360)
  | 646 => some (.leaf 2361)
  | 647 => some (.leaf 2362)
  | 648 => some (.leaf 2363)
  | 649 => some (.leaf 2364)
  | 650 => some (.leaf 2365)
  | 651 => some (.leaf 2366)
  | 652 => some (.heavy (![3674, 3675, 3676, 3677, 3678, 3679, 3680, 3681, 3682, 3694, 3713, 3714, 3715, 3716, 3717, 3718, 3719, 3720, 3721, 3722, 3723]))
  | 653 => some (.leaf 2367)
  | 654 => some (.leaf 2368)
  | 655 => some (.triangle 13 3725 3726)
  | 656 => some (.triangle 10 2251 3727)
  | 657 => some (.leaf 2369)
  | 658 => some (.leaf 2370)
  | 659 => some (.leaf 2371)
  | 660 => some (.leaf 2372)
  | 661 => some (.leaf 2373)
  | 662 => some (.leaf 2374)
  | 663 => some (.leaf 2375)
  | 664 => some (.leaf 2376)
  | 665 => some (.leaf 2377)
  | 666 => some (.leaf 2378)
  | 667 => some (.leaf 2379)
  | 668 => some (.leaf 2380)
  | 669 => some (.leaf 2381)
  | 670 => some (.positive 0 (![3736, 3737, 3738, 3739, 3740, 3741]))
  | 671 => some (.triangle 11 2017 3742)
  | 672 => some (.leaf 2382)
  | 673 => some (.triangle 13 3743 3744)
  | 674 => some (.triangle 10 2251 3745)
  | 675 => some (.leaf 2383)
  | 676 => some (.leaf 2384)
  | 677 => some (.leaf 2385)
  | 678 => some (.leaf 2386)
  | 679 => some (.positive 0 (![3747, 3748, 3738, 3739, 3749, 3750]))
  | 680 => some (.triangle 11 2017 3751)
  | 681 => some (.leaf 2387)
  | 682 => some (.leaf 2388)
  | 683 => some (.leaf 2389)
  | 684 => some (.leaf 2390)
  | 685 => some (.leaf 2391)
  | 686 => some (.leaf 2392)
  | 687 => some (.leaf 2393)
  | 688 => some (.triangle 8 3758 3759)
  | 689 => some (.leaf 2394)
  | 690 => some (.leaf 2395)
  | 691 => some (.positive 1 (![2704, 3756, 3757, 3760, 3761, 3762]))
  | 692 => some (.triangle 6 3755 3763)
  | 693 => some (.leaf 2396)
  | 694 => some (.triangle 18 3764 3765)
  | 695 => some (.leaf 2397)
  | 696 => some (.triangle 17 3766 3767)
  | 697 => some (.triangle 16 3768 2536)
  | 698 => some (.leaf 2398)
  | 699 => some (.leaf 2399)
  | 700 => some (.leaf 2400)
  | 701 => some (.positive 0 (![3753, 3754, 3769, 3770, 3771, 3772]))
  | 702 => some (.triangle 13 3752 3773)
  | 703 => some (.triangle 10 2251 3774)
  | 704 => some (.leaf 2401)
  | 705 => some (.leaf 2402)
  | 706 => some (.leaf 2403)
  | 707 => some (.leaf 2404)
  | 708 => some (.positive 0 (![3542, 3778, 3738, 3739, 3749, 3779]))
  | 709 => some (.triangle 11 3777 3780)
  | 710 => some (.leaf 2405)
  | 711 => some (.leaf 2406)
  | 712 => some (.leaf 2407)
  | 713 => some (.leaf 2408)
  | 714 => some (.positive 1 (![2704, 3783, 3784, 3785, 2760, 3762]))
  | 715 => some (.triangle 6 3755 3786)
  | 716 => some (.leaf 2409)
  | 717 => some (.triangle 18 3787 3788)
  | 718 => some (.triangle 17 3789 3767)
  | 719 => some (.leaf 2410)
  | 720 => some (.triangle 16 3790 3791)
  | 721 => some (.leaf 2411)
  | 722 => some (.positive 0 (![3782, 3701, 3792, 3770, 3771, 3793]))
  | 723 => some (.triangle 13 3781 3794)
  | 724 => some (.triangle 10 3776 3795)
  | 725 => some (.leaf 2412)
  | 726 => some (.leaf 2413)
  | 727 => some (.leaf 2414)
  | 728 => some (.leaf 2415)
  | 729 => some (.leaf 2416)
  | 730 => some (.leaf 2417)
  | 731 => some (.leaf 2418)
  | 732 => some (.leaf 2419)
  | 733 => some (.leaf 2420)
  | 734 => some (.leaf 2421)
  | 735 => some (.heavy (![3728, 3729, 3730, 3731, 3732, 3733, 3734, 3735, 3746, 3775, 3796, 3797, 3798, 3799, 3800, 3801, 3802, 3803, 3804, 3805, 3806]))
  | 736 => some (.triangle 5 3724 3807)
  | 737 => some (.leaf 2422)
  | 738 => some (.leaf 2423)
  | 739 => some (.leaf 2424)
  | 740 => some (.leaf 2425)
  | 741 => some (.leaf 2426)
  | 742 => some (.leaf 2427)
  | 743 => some (.leaf 2428)
  | 744 => some (.leaf 2429)
  | 745 => some (.leaf 2430)
  | 746 => some (.leaf 2431)
  | 747 => some (.leaf 2432)
  | 748 => some (.positive 2 (![3814, 3815, 3816, 3817, 3818, 3819]))
  | 749 => some (.triangle 8 3813 3820)
  | 750 => some (.triangle 19 3821 3297)
  | 751 => some (.leaf 2433)
  | 752 => some (.leaf 2434)
  | 753 => some (.positive 1 (![3810, 3811, 3812, 3822, 3823, 3824]))
  | 754 => some (.triangle 6 3809 3825)
  | 755 => some (.leaf 2435)
  | 756 => some (.positive 1 (![3303, 3304, 3305, 2865, 3306, 3827]))
  | 757 => some (.triangle 18 3826 3828)
  | 758 => some (.triangle 5 3291 3829)
  | 759 => some (.triangle 17 3830 3311)
  | 760 => some (.leaf 2436)
  | 761 => some (.leaf 2437)
  | 762 => some (.triangle 8 3758 3833)
  | 763 => some (.leaf 2438)
  | 764 => some (.leaf 2439)
  | 765 => some (.leaf 2440)
  | 766 => some (.leaf 2441)
  | 767 => some (.positive 1 (![3834, 3835, 3836, 3316, 3837, 3838]))
  | 768 => some (.triangle 6 3832 3839)
  | 769 => some (.leaf 2442)
  | 770 => some (.leaf 2443)
  | 771 => some (.positive 2 (![3185, 3186, 3187, 3188, 3841, 3842]))
  | 772 => some (.leaf 2444)
  | 773 => some (.triangle 19 3843 3844)
  | 774 => some (.leaf 2445)
  | 775 => some (.leaf 2446)
  | 776 => some (.positive 1 (![3845, 3194, 3195, 3196, 3846, 3847]))
  | 777 => some (.triangle 17 3840 3848)
  | 778 => some (.leaf 2447)
  | 779 => some (.leaf 2448)
  | 780 => some (.positive 1 (![3329, 3330, 3331, 3332, 3850, 3851]))
  | 781 => some (.triangle 18 3849 3852)
  | 782 => some (.triangle 16 3831 3853)
  | 783 => some (.leaf 2449)
  | 784 => some (.positive 2 (![3185, 3186, 3187, 3188, 3855, 3842]))
  | 785 => some (.triangle 19 3856 3844)
  | 786 => some (.positive 1 (![3857, 3194, 3195, 3196, 3846, 3847]))
  | 787 => some (.triangle 17 3840 3858)
  | 788 => some (.positive 1 (![3329, 3330, 3331, 3332, 3333, 3851]))
  | 789 => some (.triangle 18 3859 3860)
  | 790 => some (.triangle 16 3831 3861)
  | 791 => some (.leaf 2450)
  | 792 => some (.leaf 2451)
  | 793 => some (.leaf 2452)
  | 794 => some (.leaf 2453)
  | 795 => some (.positive 0 (![3854, 3862, 3863, 3864, 3865, 3866]))
  | 796 => some (.triangle 13 1425 3867)
  | 797 => some (.triangle 10 2251 3868)
  | 798 => some (.leaf 2454)
  | 799 => some (.leaf 2455)
  | 800 => some (.leaf 2456)
  | 801 => some (.leaf 2457)
  | 802 => some (.leaf 2458)
  | 803 => some (.leaf 2459)
  | 804 => some (.leaf 2460)
  | 805 => some (.leaf 2461)
  | 806 => some (.leaf 2462)
  | 807 => some (.leaf 2463)
  | 808 => some (.leaf 2464)
  | 809 => some (.leaf 2465)
  | 810 => some (.triangle 8 3880 3881)
  | 811 => some (.triangle 19 3882 3297)
  | 812 => some (.leaf 2466)
  | 813 => some (.leaf 2467)
  | 814 => some (.positive 1 (![3810, 3811, 3879, 3883, 3884, 3885]))
  | 815 => some (.triangle 6 3878 3886)
  | 816 => some (.leaf 2468)
  | 817 => some (.leaf 2469)
  | 818 => some (.positive 1 (![3303, 3304, 3305, 2865, 3888, 3889]))
  | 819 => some (.triangle 18 3887 3890)
  | 820 => some (.triangle 5 3291 3891)
  | 821 => some (.triangle 17 3892 3311)
  | 822 => some (.leaf 2470)
  | 823 => some (.leaf 2471)
  | 824 => some (.triangle 6 3894 3895)
  | 825 => some (.leaf 2472)
  | 826 => some (.leaf 2473)
  | 827 => some (.positive 2 (![3185, 3186, 3187, 3188, 3897, 3898]))
  | 828 => some (.triangle 19 3899 3844)
  | 829 => some (.leaf 2474)
  | 830 => some (.leaf 2475)
  | 831 => some (.positive 1 (![3900, 3194, 3195, 3196, 3901, 3902]))
  | 832 => some (.triangle 17 3896 3903)
  | 833 => some (.leaf 2476)
  | 834 => some (.leaf 2477)
  | 835 => some (.positive 1 (![3329, 3330, 3331, 3332, 3905, 3906]))
  | 836 => some (.triangle 18 3904 3907)
  | 837 => some (.triangle 16 3893 3908)
  | 838 => some (.leaf 2478)
  | 839 => some (.leaf 2479)
  | 840 => some (.leaf 2480)
  | 841 => some (.positive 0 (![3876, 3877, 3909, 3910, 3911, 3912]))
  | 842 => some (.triangle 13 1425 3913)
  | 843 => some (.triangle 10 2251 3914)
  | 844 => some (.leaf 2481)
  | 845 => some (.leaf 2482)
  | 846 => some (.leaf 2483)
  | 847 => some (.leaf 2484)
  | 848 => some (.triangle 6 3894 3919)
  | 849 => some (.leaf 2485)
  | 850 => some (.leaf 2486)
  | 851 => some (.positive 2 (![3185, 3186, 3187, 3188, 3921, 3922]))
  | 852 => some (.leaf 2487)
  | 853 => some (.triangle 19 3923 3924)
  | 854 => some (.leaf 2488)
  | 855 => some (.leaf 2489)
  | 856 => some (.positive 1 (![3925, 3194, 3195, 3196, 3926, 3927]))
  | 857 => some (.triangle 17 3920 3928)
  | 858 => some (.leaf 2490)
  | 859 => some (.triangle 19 3327 3930)
  | 860 => some (.leaf 2491)
  | 861 => some (.leaf 2492)
  | 862 => some (.positive 1 (![3931, 3330, 3331, 3332, 3932, 3933]))
  | 863 => some (.triangle 18 3929 3934)
  | 864 => some (.triangle 16 3918 3935)
  | 865 => some (.leaf 2493)
  | 866 => some (.leaf 2494)
  | 867 => some (.leaf 2495)
  | 868 => some (.positive 0 (![3916, 3917, 3936, 3937, 3938, 3939]))
  | 869 => some (.triangle 13 1425 3940)
  | 870 => some (.triangle 10 2251 3941)
  | 871 => some (.leaf 2496)
  | 872 => some (.leaf 2497)
  | 873 => some (.leaf 2498)
  | 874 => some (.leaf 2499)
  | 875 => some (.leaf 2500)
  | 876 => some (.leaf 2501)
  | 877 => some (.triangle 16 3947 3948)
  | 878 => some (.leaf 2502)
  | 879 => some (.leaf 2503)
  | 880 => some (.positive 0 (![3945, 3946, 3949, 3937, 3950, 3951]))
  | 881 => some (.triangle 13 1425 3952)
  | 882 => some (.triangle 10 3944 3953)
  | 883 => some (.leaf 2504)
  | 884 => some (.leaf 2505)
  | 885 => some (.leaf 2506)
  | 886 => some (.leaf 2507)
  | 887 => some (.leaf 2508)
  | 888 => some (.leaf 2509)
  | 889 => some (.leaf 2510)
  | 890 => some (.leaf 2511)
  | 891 => some (.leaf 2512)
  | 892 => some (.leaf 2513)
  | 893 => some (.heavy (![3869, 3870, 3871, 3872, 3873, 3874, 3875, 3915, 3942, 3943, 3954, 3955, 3956, 3957, 3958, 3959, 3960, 3961, 3962, 3963, 3964]))
  | 894 => some (.triangle 7 3808 3965)
  | 895 => some (.triangle 4 3670 3966)
  | 896 => some (.triangle 3 3499 3967)
  | 897 => some (.leaf 2514)
  | 898 => some (.leaf 2515)
  | 899 => some (.triangle 10 3969 3970)
  | 900 => some (.leaf 2516)
  | 901 => some (.leaf 2517)
  | 902 => some (.leaf 2518)
  | 903 => some (.leaf 2519)
  | 904 => some (.leaf 2520)
  | 905 => some (.leaf 2521)
  | 906 => some (.leaf 2522)
  | 907 => some (.leaf 2523)
  | 908 => some (.leaf 2524)
  | 909 => some (.leaf 2525)
  | 910 => some (.leaf 2526)
  | 911 => some (.leaf 2527)
  | 912 => some (.leaf 2528)
  | 913 => some (.leaf 2529)
  | 914 => some (.positive 0 (![3980, 3981, 3982, 3983, 3984, 3985]))
  | 915 => some (.leaf 2530)
  | 916 => some (.triangle 14 3986 3987)
  | 917 => some (.leaf 2531)
  | 918 => some (.triangle 12 3988 3989)
  | 919 => some (.leaf 2532)
  | 920 => some (.leaf 2533)
  | 921 => some (.triangle 12 3991 3992)
  | 922 => some (.leaf 2534)
  | 923 => some (.triangle 14 3993 3994)
  | 924 => some (.triangle 10 3990 3995)
  | 925 => some (.leaf 2535)
  | 926 => some (.leaf 2536)
  | 927 => some (.leaf 2537)
  | 928 => some (.positive 0 (![3997, 3998, 3982, 3983, 3984, 3999]))
  | 929 => some (.leaf 2538)
  | 930 => some (.leaf 2539)
  | 931 => some (.leaf 2540)
  | 932 => some (.leaf 2541)
  | 933 => some (.leaf 2542)
  | 934 => some (.leaf 2543)
  | 935 => some (.positive 0 (![4001, 4002, 4003, 4004, 4005, 4006]))
  | 936 => some (.triangle 14 4000 4007)
  | 937 => some (.leaf 2544)
  | 938 => some (.triangle 12 4008 4009)
  | 939 => some (.leaf 2545)
  | 940 => some (.leaf 2546)
  | 941 => some (.leaf 2547)
  | 942 => some (.leaf 2548)
  | 943 => some (.leaf 2549)
  | 944 => some (.leaf 2550)
  | 945 => some (.positive 0 (![4011, 4012, 4013, 4014, 4015, 4016]))
  | 946 => some (.triangle 12 3991 4017)
  | 947 => some (.leaf 2551)
  | 948 => some (.leaf 2552)
  | 949 => some (.leaf 2553)
  | 950 => some (.leaf 2554)
  | 951 => some (.triangle 5 4021 4022)
  | 952 => some (.leaf 2555)
  | 953 => some (.leaf 2556)
  | 954 => some (.leaf 2557)
  | 955 => some (.positive 0 (![4019, 4020, 4023, 4024, 4025, 4026]))
  | 956 => some (.triangle 14 4018 4027)
  | 957 => some (.triangle 10 4010 4028)
  | 958 => some (.leaf 2558)
  | 959 => some (.leaf 2559)
  | 960 => some (.leaf 2560)
  | 961 => some (.leaf 2561)
  | 962 => some (.leaf 2562)
  | 963 => some (.leaf 2563)
  | 964 => some (.leaf 2564)
  | 965 => some (.leaf 2565)
  | 966 => some (.leaf 2566)
  | 967 => some (.leaf 2567)
  | 968 => some (.heavy (![3971, 3972, 3973, 3974, 3975, 3976, 3977, 3978, 3979, 3996, 4029, 4030, 4031, 4032, 4033, 4034, 4035, 4036, 4037, 4038, 4039]))
  | 969 => some (.leaf 2568)
  | 970 => some (.leaf 2569)
  | 971 => some (.triangle 10 4041 4042)
  | 972 => some (.leaf 2570)
  | 973 => some (.leaf 2571)
  | 974 => some (.leaf 2572)
  | 975 => some (.leaf 2573)
  | 976 => some (.leaf 2574)
  | 977 => some (.leaf 2575)
  | 978 => some (.leaf 2576)
  | 979 => some (.leaf 2577)
  | 980 => some (.leaf 2578)
  | 981 => some (.leaf 2579)
  | 982 => some (.leaf 2580)
  | 983 => some (.leaf 2581)
  | 984 => some (.leaf 2582)
  | 985 => some (.positive 0 (![4051, 4052, 4053, 4054, 4055, 4056]))
  | 986 => some (.triangle 14 1345 4057)
  | 987 => some (.leaf 2583)
  | 988 => some (.triangle 12 4058 4059)
  | 989 => some (.leaf 2584)
  | 990 => some (.triangle 10 4060 4061)
  | 991 => some (.leaf 2585)
  | 992 => some (.leaf 2586)
  | 993 => some (.leaf 2587)
  | 994 => some (.leaf 2588)
  | 995 => some (.positive 0 (![4063, 4064, 4053, 4054, 4065, 4066]))
  | 996 => some (.triangle 14 1345 4067)
  | 997 => some (.leaf 2589)
  | 998 => some (.triangle 12 4068 4069)
  | 999 => some (.leaf 2590)
  | 1000 => some (.triangle 10 4070 4071)
  | 1001 => some (.leaf 2591)
  | 1002 => some (.leaf 2592)
  | 1003 => some (.leaf 2593)
  | 1004 => some (.positive 0 (![4074, 4002, 4053, 4054, 4065, 4075]))
  | 1005 => some (.triangle 14 4073 4076)
  | 1006 => some (.triangle 12 4077 4069)
  | 1007 => some (.leaf 2594)
  | 1008 => some (.leaf 2595)
  | 1009 => some (.leaf 2596)
  | 1010 => some (.triangle 5 4021 2034)
  | 1011 => some (.leaf 2597)
  | 1012 => some (.leaf 2598)
  | 1013 => some (.leaf 2599)
  | 1014 => some (.positive 0 (![4080, 4081, 4082, 4083, 4084, 4085]))
  | 1015 => some (.triangle 14 4079 4086)
  | 1016 => some (.triangle 10 4078 4087)
  | 1017 => some (.leaf 2600)
  | 1018 => some (.leaf 2601)
  | 1019 => some (.leaf 2602)
  | 1020 => some (.leaf 2603)
  | 1021 => some (.leaf 2604)
  | 1022 => some (.leaf 2605)
  | 1023 => some (.leaf 2606)
  | 1024 => some (.leaf 2607)
  | 1025 => some (.leaf 2608)
  | 1026 => some (.leaf 2609)
  | 1027 => some (.heavy (![4043, 4044, 4045, 4046, 4047, 4048, 4049, 4050, 4062, 4072, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095, 4096, 4097, 4098]))
  | 1028 => some (.triangle 8 4040 4099)
  | 1029 => some (.leaf 2610)
  | 1030 => some (.leaf 2611)
  | 1031 => some (.triangle 10 4101 4102)
  | 1032 => some (.leaf 2612)
  | 1033 => some (.leaf 2613)
  | 1034 => some (.leaf 2614)
  | 1035 => some (.leaf 2615)
  | 1036 => some (.leaf 2616)
  | 1037 => some (.leaf 2617)
  | 1038 => some (.leaf 2618)
  | 1039 => some (.leaf 2619)
  | 1040 => some (.leaf 2620)
  | 1041 => some (.leaf 2621)
  | 1042 => some (.leaf 2622)
  | 1043 => some (.leaf 2623)
  | 1044 => some (.leaf 2624)
  | 1045 => some (.leaf 2625)
  | 1046 => some (.positive 0 (![4112, 4113, 4114, 4115, 4116, 4117]))
  | 1047 => some (.triangle 12 1879 4118)
  | 1048 => some (.leaf 2626)
  | 1049 => some (.triangle 10 4119 4120)
  | 1050 => some (.leaf 2627)
  | 1051 => some (.leaf 2628)
  | 1052 => some (.leaf 2629)
  | 1053 => some (.positive 0 (![4122, 4123, 4114, 4115, 4116, 4124]))
  | 1054 => some (.triangle 12 1879 4125)
  | 1055 => some (.triangle 10 4126 1894)
  | 1056 => some (.leaf 2630)
  | 1057 => some (.leaf 2631)
  | 1058 => some (.leaf 2632)
  | 1059 => some (.leaf 2633)
  | 1060 => some (.leaf 2634)
  | 1061 => some (.leaf 2635)
  | 1062 => some (.leaf 2636)
  | 1063 => some (.leaf 2637)
  | 1064 => some (.leaf 2638)
  | 1065 => some (.leaf 2639)
  | 1066 => some (.heavy (![4103, 4104, 4105, 4106, 4107, 4108, 4109, 4110, 4111, 4121, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4136, 4137]))
  | 1067 => some (.triangle 6 4100 4138)
  | 1068 => some (.leaf 2640)
  | 1069 => some (.leaf 2641)
  | 1070 => some (.triangle 14 4140 4141)
  | 1071 => some (.triangle 10 2251 4142)
  | 1072 => some (.leaf 2642)
  | 1073 => some (.leaf 2643)
  | 1074 => some (.leaf 2644)
  | 1075 => some (.leaf 2645)
  | 1076 => some (.leaf 2646)
  | 1077 => some (.leaf 2647)
  | 1078 => some (.leaf 2648)
  | 1079 => some (.leaf 2649)
  | 1080 => some (.leaf 2650)
  | 1081 => some (.leaf 2651)
  | 1082 => some (.leaf 2652)
  | 1083 => some (.leaf 2653)
  | 1084 => some (.leaf 2654)
  | 1085 => some (.leaf 2655)
  | 1086 => some (.positive 0 (![4152, 4153, 4154, 4155, 4156, 4157]))
  | 1087 => some (.leaf 2656)
  | 1088 => some (.triangle 12 4158 4159)
  | 1089 => some (.leaf 2657)
  | 1090 => some (.triangle 14 4160 4161)
  | 1091 => some (.triangle 10 2251 4162)
  | 1092 => some (.leaf 2658)
  | 1093 => some (.leaf 2659)
  | 1094 => some (.leaf 2660)
  | 1095 => some (.positive 0 (![4164, 4165, 4154, 4155, 4156, 4166]))
  | 1096 => some (.triangle 12 4167 2571)
  | 1097 => some (.leaf 2661)
  | 1098 => some (.leaf 2662)
  | 1099 => some (.leaf 2663)
  | 1100 => some (.leaf 2664)
  | 1101 => some (.triangle 12 4172 2574)
  | 1102 => some (.triangle 5 4171 4173)
  | 1103 => some (.leaf 2665)
  | 1104 => some (.triangle 16 4174 4175)
  | 1105 => some (.leaf 2666)
  | 1106 => some (.leaf 2667)
  | 1107 => some (.leaf 2668)
  | 1108 => some (.positive 0 (![4169, 4170, 4176, 4177, 4178, 4179]))
  | 1109 => some (.triangle 14 4168 4180)
  | 1110 => some (.triangle 10 2251 4181)
  | 1111 => some (.leaf 2669)
  | 1112 => some (.leaf 2670)
  | 1113 => some (.leaf 2671)
  | 1114 => some (.leaf 2672)
  | 1115 => some (.leaf 2673)
  | 1116 => some (.leaf 2674)
  | 1117 => some (.leaf 2675)
  | 1118 => some (.leaf 2676)
  | 1119 => some (.leaf 2677)
  | 1120 => some (.leaf 2678)
  | 1121 => some (.heavy (![4143, 4144, 4145, 4146, 4147, 4148, 4149, 4150, 4151, 4163, 4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4190, 4191, 4192]))
  | 1122 => some (.leaf 2679)
  | 1123 => some (.leaf 2680)
  | 1124 => some (.triangle 14 4194 4195)
  | 1125 => some (.triangle 10 2251 4196)
  | 1126 => some (.leaf 2681)
  | 1127 => some (.leaf 2682)
  | 1128 => some (.leaf 2683)
  | 1129 => some (.leaf 2684)
  | 1130 => some (.leaf 2685)
  | 1131 => some (.leaf 2686)
  | 1132 => some (.leaf 2687)
  | 1133 => some (.leaf 2688)
  | 1134 => some (.leaf 2689)
  | 1135 => some (.leaf 2690)
  | 1136 => some (.leaf 2691)
  | 1137 => some (.leaf 2692)
  | 1138 => some (.leaf 2693)
  | 1139 => some (.positive 0 (![4205, 4206, 4207, 4208, 4209, 4210]))
  | 1140 => some (.triangle 12 1879 4211)
  | 1141 => some (.leaf 2694)
  | 1142 => some (.triangle 14 4212 4213)
  | 1143 => some (.triangle 10 2251 4214)
  | 1144 => some (.leaf 2695)
  | 1145 => some (.leaf 2696)
  | 1146 => some (.leaf 2697)
  | 1147 => some (.leaf 2698)
  | 1148 => some (.positive 0 (![4216, 4217, 4207, 4208, 4218, 4219]))
  | 1149 => some (.triangle 12 1879 4220)
  | 1150 => some (.leaf 2699)
  | 1151 => some (.leaf 2700)
  | 1152 => some (.leaf 2701)
  | 1153 => some (.leaf 2702)
  | 1154 => some (.leaf 2703)
  | 1155 => some (.leaf 2704)
  | 1156 => some (.leaf 2705)
  | 1157 => some (.triangle 7 4227 4228)
  | 1158 => some (.leaf 2706)
  | 1159 => some (.leaf 2707)
  | 1160 => some (.positive 1 (![4224, 4225, 4226, 4229, 4230, 4231]))
  | 1161 => some (.leaf 2708)
  | 1162 => some (.triangle 18 4232 4233)
  | 1163 => some (.triangle 17 4234 2452)
  | 1164 => some (.leaf 2709)
  | 1165 => some (.triangle 16 4235 4236)
  | 1166 => some (.leaf 2710)
  | 1167 => some (.leaf 2711)
  | 1168 => some (.leaf 2712)
  | 1169 => some (.positive 0 (![4222, 4223, 4237, 4238, 4239, 4240]))
  | 1170 => some (.triangle 14 4221 4241)
  | 1171 => some (.triangle 10 2251 4242)
  | 1172 => some (.leaf 2713)
  | 1173 => some (.leaf 2714)
  | 1174 => some (.leaf 2715)
  | 1175 => some (.leaf 2716)
  | 1176 => some (.positive 0 (![4011, 4246, 4207, 4208, 4218, 4247]))
  | 1177 => some (.triangle 12 4245 4248)
  | 1178 => some (.leaf 2717)
  | 1179 => some (.leaf 2718)
  | 1180 => some (.leaf 2719)
  | 1181 => some (.leaf 2720)
  | 1182 => some (.positive 1 (![4224, 4251, 4252, 4253, 2760, 4231]))
  | 1183 => some (.leaf 2721)
  | 1184 => some (.triangle 18 4254 4255)
  | 1185 => some (.leaf 2722)
  | 1186 => some (.triangle 17 4256 4257)
  | 1187 => some (.triangle 16 4258 4175)
  | 1188 => some (.leaf 2723)
  | 1189 => some (.positive 0 (![4250, 4170, 4259, 4238, 4239, 4260]))
  | 1190 => some (.triangle 14 4249 4261)
  | 1191 => some (.triangle 10 4244 4262)
  | 1192 => some (.leaf 2724)
  | 1193 => some (.leaf 2725)
  | 1194 => some (.leaf 2726)
  | 1195 => some (.leaf 2727)
  | 1196 => some (.leaf 2728)
  | 1197 => some (.leaf 2729)
  | 1198 => some (.leaf 2730)
  | 1199 => some (.leaf 2731)
  | 1200 => some (.leaf 2732)
  | 1201 => some (.leaf 2733)
  | 1202 => some (.heavy (![4197, 4198, 4199, 4200, 4201, 4202, 4203, 4204, 4215, 4243, 4263, 4264, 4265, 4266, 4267, 4268, 4269, 4270, 4271, 4272, 4273]))
  | 1203 => some (.triangle 6 4193 4274)
  | 1204 => some (.leaf 2734)
  | 1205 => some (.leaf 2735)
  | 1206 => some (.leaf 2736)
  | 1207 => some (.leaf 2737)
  | 1208 => some (.leaf 2738)
  | 1209 => some (.leaf 2739)
  | 1210 => some (.leaf 2740)
  | 1211 => some (.leaf 2741)
  | 1212 => some (.positive 2 (![4281, 3815, 3816, 3817, 4282, 4283]))
  | 1213 => some (.leaf 2742)
  | 1214 => some (.triangle 19 4284 4285)
  | 1215 => some (.leaf 2743)
  | 1216 => some (.leaf 2744)
  | 1217 => some (.positive 1 (![4278, 4279, 4280, 4286, 4287, 4288]))
  | 1218 => some (.triangle 6 4277 4289)
  | 1219 => some (.leaf 2745)
  | 1220 => some (.triangle 18 4290 4291)
  | 1221 => some (.triangle 5 4276 4292)
  | 1222 => some (.leaf 2746)
  | 1223 => some (.leaf 2747)
  | 1224 => some (.leaf 2748)
  | 1225 => some (.triangle 7 4295 4296)
  | 1226 => some (.leaf 2749)
  | 1227 => some (.leaf 2750)
  | 1228 => some (.leaf 2751)
  | 1229 => some (.leaf 2752)
  | 1230 => some (.leaf 2753)
  | 1231 => some (.positive 1 (![4297, 4298, 4299, 4300, 4301, 4302]))
  | 1232 => some (.triangle 5 4294 4303)
  | 1233 => some (.triangle 17 4293 4304)
  | 1234 => some (.leaf 2754)
  | 1235 => some (.leaf 2755)
  | 1236 => some (.positive 2 (![3185, 3186, 3187, 3188, 4306, 4307]))
  | 1237 => some (.leaf 2756)
  | 1238 => some (.triangle 19 4308 4309)
  | 1239 => some (.leaf 2757)
  | 1240 => some (.positive 1 (![4310, 3194, 3195, 3196, 3846, 4311]))
  | 1241 => some (.triangle 17 3184 4312)
  | 1242 => some (.leaf 2758)
  | 1243 => some (.triangle 18 4313 4314)
  | 1244 => some (.triangle 16 4305 4315)
  | 1245 => some (.positive 2 (![3185, 3186, 3187, 3188, 3855, 4307]))
  | 1246 => some (.triangle 19 4317 4309)
  | 1247 => some (.positive 1 (![4318, 3194, 3195, 3196, 3846, 4311]))
  | 1248 => some (.triangle 17 3184 4319)
  | 1249 => some (.triangle 18 4320 4314)
  | 1250 => some (.triangle 16 4305 4321)
  | 1251 => some (.leaf 2759)
  | 1252 => some (.leaf 2760)
  | 1253 => some (.leaf 2761)
  | 1254 => some (.leaf 2762)
  | 1255 => some (.positive 0 (![4316, 4322, 4323, 4324, 4325, 4326]))
  | 1256 => some (.triangle 14 1345 4327)
  | 1257 => some (.triangle 10 2251 4328)
  | 1258 => some (.leaf 2763)
  | 1259 => some (.leaf 2764)
  | 1260 => some (.leaf 2765)
  | 1261 => some (.leaf 2766)
  | 1262 => some (.leaf 2767)
  | 1263 => some (.leaf 2768)
  | 1264 => some (.leaf 2769)
  | 1265 => some (.leaf 2770)
  | 1266 => some (.leaf 2771)
  | 1267 => some (.leaf 2772)
  | 1268 => some (.leaf 2773)
  | 1269 => some (.leaf 2774)
  | 1270 => some (.positive 2 (![4281, 3815, 3816, 3817, 4340, 4341]))
  | 1271 => some (.leaf 2775)
  | 1272 => some (.triangle 19 4342 4343)
  | 1273 => some (.leaf 2776)
  | 1274 => some (.leaf 2777)
  | 1275 => some (.positive 1 (![4278, 4339, 4280, 4344, 4345, 4346]))
  | 1276 => some (.triangle 6 4277 4347)
  | 1277 => some (.triangle 18 4348 2170)
  | 1278 => some (.triangle 5 4338 4349)
  | 1279 => some (.leaf 2778)
  | 1280 => some (.leaf 2779)
  | 1281 => some (.triangle 5 4351 4352)
  | 1282 => some (.triangle 17 4350 4353)
  | 1283 => some (.leaf 2780)
  | 1284 => some (.leaf 2781)
  | 1285 => some (.positive 2 (![3185, 3186, 3187, 3188, 4355, 4356]))
  | 1286 => some (.leaf 2782)
  | 1287 => some (.triangle 19 4357 4358)
  | 1288 => some (.leaf 2783)
  | 1289 => some (.leaf 2784)
  | 1290 => some (.positive 1 (![4359, 3194, 3195, 3196, 4360, 4361]))
  | 1291 => some (.triangle 17 3184 4362)
  | 1292 => some (.leaf 2785)
  | 1293 => some (.triangle 18 4363 4364)
  | 1294 => some (.triangle 16 4354 4365)
  | 1295 => some (.leaf 2786)
  | 1296 => some (.leaf 2787)
  | 1297 => some (.leaf 2788)
  | 1298 => some (.positive 0 (![4336, 4337, 4366, 4367, 4368, 4369]))
  | 1299 => some (.triangle 14 1345 4370)
  | 1300 => some (.triangle 10 2251 4371)
  | 1301 => some (.leaf 2789)
  | 1302 => some (.leaf 2790)
  | 1303 => some (.leaf 2791)
  | 1304 => some (.leaf 2792)
  | 1305 => some (.triangle 5 4351 4376)
  | 1306 => some (.triangle 17 4375 4377)
  | 1307 => some (.leaf 2793)
  | 1308 => some (.leaf 2794)
  | 1309 => some (.leaf 2795)
  | 1310 => some (.leaf 2796)
  | 1311 => some (.positive 2 (![3185, 4380, 3187, 3188, 4381, 4382]))
  | 1312 => some (.leaf 2797)
  | 1313 => some (.triangle 19 4383 4384)
  | 1314 => some (.leaf 2798)
  | 1315 => some (.leaf 2799)
  | 1316 => some (.positive 1 (![4385, 3194, 3195, 3196, 4386, 4387]))
  | 1317 => some (.triangle 17 4379 4388)
  | 1318 => some (.leaf 2800)
  | 1319 => some (.triangle 18 4389 4390)
  | 1320 => some (.triangle 16 4378 4391)
  | 1321 => some (.leaf 2801)
  | 1322 => some (.leaf 2802)
  | 1323 => some (.leaf 2803)
  | 1324 => some (.positive 0 (![4373, 4374, 4392, 4393, 4394, 4395]))
  | 1325 => some (.triangle 14 1345 4396)
  | 1326 => some (.triangle 10 2251 4397)
  | 1327 => some (.leaf 2804)
  | 1328 => some (.leaf 2805)
  | 1329 => some (.leaf 2806)
  | 1330 => some (.leaf 2807)
  | 1331 => some (.leaf 2808)
  | 1332 => some (.leaf 2809)
  | 1333 => some (.triangle 17 4403 4404)
  | 1334 => some (.leaf 2810)
  | 1335 => some (.triangle 16 4405 4406)
  | 1336 => some (.leaf 2811)
  | 1337 => some (.leaf 2812)
  | 1338 => some (.positive 0 (![4401, 4402, 4407, 4393, 4408, 4409]))
  | 1339 => some (.triangle 14 1345 4410)
  | 1340 => some (.triangle 10 4400 4411)
  | 1341 => some (.leaf 2813)
  | 1342 => some (.leaf 2814)
  | 1343 => some (.leaf 2815)
  | 1344 => some (.leaf 2816)
  | 1345 => some (.leaf 2817)
  | 1346 => some (.leaf 2818)
  | 1347 => some (.leaf 2819)
  | 1348 => some (.leaf 2820)
  | 1349 => some (.leaf 2821)
  | 1350 => some (.leaf 2822)
  | 1351 => some (.heavy (![4329, 4330, 4331, 4332, 4333, 4334, 4335, 4372, 4398, 4399, 4412, 4413, 4414, 4415, 4416, 4417, 4418, 4419, 4420, 4421, 4422]))
  | 1352 => some (.triangle 8 4275 4423)
  | 1353 => some (.triangle 4 4139 4424)
  | 1354 => some (.leaf 2823)
  | 1355 => some (.leaf 2824)
  | 1356 => some (.triangle 10 4426 4427)
  | 1357 => some (.leaf 2825)
  | 1358 => some (.triangle 15 4428 4429)
  | 1359 => some (.leaf 2826)
  | 1360 => some (.leaf 2827)
  | 1361 => some (.leaf 2828)
  | 1362 => some (.leaf 2829)
  | 1363 => some (.leaf 2830)
  | 1364 => some (.leaf 2831)
  | 1365 => some (.leaf 2832)
  | 1366 => some (.leaf 2833)
  | 1367 => some (.leaf 2834)
  | 1368 => some (.leaf 2835)
  | 1369 => some (.leaf 2836)
  | 1370 => some (.leaf 2837)
  | 1371 => some (.leaf 2838)
  | 1372 => some (.leaf 2839)
  | 1373 => some (.positive 0 (![4439, 4440, 4441, 4442, 4443, 4444]))
  | 1374 => some (.leaf 2840)
  | 1375 => some (.triangle 10 4445 4446)
  | 1376 => some (.leaf 2841)
  | 1377 => some (.triangle 15 4447 4448)
  | 1378 => some (.leaf 2842)
  | 1379 => some (.leaf 2843)
  | 1380 => some (.leaf 2844)
  | 1381 => some (.positive 0 (![4450, 4440, 4451, 4442, 4443, 4452]))
  | 1382 => some (.leaf 2845)
  | 1383 => some (.leaf 2846)
  | 1384 => some (.leaf 2847)
  | 1385 => some (.leaf 2848)
  | 1386 => some (.triangle 5 4457 2034)
  | 1387 => some (.leaf 2849)
  | 1388 => some (.leaf 2850)
  | 1389 => some (.positive 0 (![4454, 4455, 4456, 4458, 4459, 4460]))
  | 1390 => some (.triangle 10 4453 4461)
  | 1391 => some (.leaf 2851)
  | 1392 => some (.triangle 15 4462 4463)
  | 1393 => some (.leaf 2852)
  | 1394 => some (.leaf 2853)
  | 1395 => some (.leaf 2854)
  | 1396 => some (.leaf 2855)
  | 1397 => some (.leaf 2856)
  | 1398 => some (.leaf 2857)
  | 1399 => some (.leaf 2858)
  | 1400 => some (.leaf 2859)
  | 1401 => some (.leaf 2860)
  | 1402 => some (.leaf 2861)
  | 1403 => some (.heavy (![4430, 4431, 4432, 4433, 4434, 4435, 4436, 4437, 4438, 4449, 4464, 4465, 4466, 4467, 4468, 4469, 4470, 4471, 4472, 4473, 4474]))
  | 1404 => some (.leaf 2862)
  | 1405 => some (.triangle 7 4476 3810)
  | 1406 => some (.leaf 2863)
  | 1407 => some (.leaf 2864)
  | 1408 => some (.positive 2 (![3814, 3815, 3816, 3817, 3818, 4479]))
  | 1409 => some (.triangle 8 3813 4480)
  | 1410 => some (.triangle 19 4481 1579)
  | 1411 => some (.triangle 7 4476 4482)
  | 1412 => some (.leaf 2865)
  | 1413 => some (.leaf 2866)
  | 1414 => some (.positive 1 (![4477, 4478, 3812, 4483, 4484, 4485]))
  | 1415 => some (.triangle 6 3552 4486)
  | 1416 => some (.leaf 2867)
  | 1417 => some (.triangle 18 4487 4488)
  | 1418 => some (.triangle 5 4457 4489)
  | 1419 => some (.leaf 2868)
  | 1420 => some (.triangle 7 4476 4296)
  | 1421 => some (.leaf 2869)
  | 1422 => some (.leaf 2870)
  | 1423 => some (.leaf 2871)
  | 1424 => some (.positive 1 (![4492, 4493, 4494, 4300, 4301, 4495]))
  | 1425 => some (.triangle 5 4491 4496)
  | 1426 => some (.triangle 17 4490 4497)
  | 1427 => some (.leaf 2872)
  | 1428 => some (.triangle 8 3758 4499)
  | 1429 => some (.leaf 2873)
  | 1430 => some (.positive 1 (![4500, 3835, 3836, 3316, 3837, 4501]))
  | 1431 => some (.triangle 6 3832 4502)
  | 1432 => some (.leaf 2874)
  | 1433 => some (.leaf 2875)
  | 1434 => some (.positive 2 (![3185, 3186, 3187, 3188, 4504, 4505]))
  | 1435 => some (.leaf 2876)
  | 1436 => some (.triangle 19 4506 4507)
  | 1437 => some (.leaf 2877)
  | 1438 => some (.positive 1 (![4508, 3194, 3195, 3196, 3846, 4509]))
  | 1439 => some (.triangle 17 4503 4510)
  | 1440 => some (.leaf 2878)
  | 1441 => some (.triangle 18 4511 4512)
  | 1442 => some (.triangle 16 4498 4513)
  | 1443 => some (.leaf 2879)
  | 1444 => some (.leaf 2880)
  | 1445 => some (.positive 1 (![4477, 4478, 3812, 4483, 4516, 4485]))
  | 1446 => some (.triangle 6 3552 4517)
  | 1447 => some (.triangle 18 4518 4488)
  | 1448 => some (.triangle 5 4457 4519)
  | 1449 => some (.triangle 17 4520 4497)
  | 1450 => some (.positive 2 (![3185, 3186, 3187, 3188, 3855, 4505]))
  | 1451 => some (.triangle 19 4522 4507)
  | 1452 => some (.positive 1 (![4523, 3194, 3195, 3196, 3846, 4509]))
  | 1453 => some (.triangle 17 4503 4524)
  | 1454 => some (.triangle 18 4525 4512)
  | 1455 => some (.triangle 16 4521 4526)
  | 1456 => some (.leaf 2881)
  | 1457 => some (.leaf 2882)
  | 1458 => some (.leaf 2883)
  | 1459 => some (.positive 0 (![4514, 4515, 4527, 4528, 4529, 4530]))
  | 1460 => some (.triangle 10 2251 4531)
  | 1461 => some (.leaf 2884)
  | 1462 => some (.triangle 15 4532 4533)
  | 1463 => some (.leaf 2885)
  | 1464 => some (.leaf 2886)
  | 1465 => some (.leaf 2887)
  | 1466 => some (.leaf 2888)
  | 1467 => some (.leaf 2889)
  | 1468 => some (.leaf 2890)
  | 1469 => some (.leaf 2891)
  | 1470 => some (.leaf 2892)
  | 1471 => some (.leaf 2893)
  | 1472 => some (.leaf 2894)
  | 1473 => some (.leaf 2895)
  | 1474 => some (.leaf 2896)
  | 1475 => some (.leaf 2897)
  | 1476 => some (.leaf 2898)
  | 1477 => some (.leaf 2899)
  | 1478 => some (.leaf 2900)
  | 1479 => some (.triangle 7 4476 4550)
  | 1480 => some (.leaf 2901)
  | 1481 => some (.leaf 2902)
  | 1482 => some (.positive 1 (![4547, 4548, 4549, 4551, 4552, 4553]))
  | 1483 => some (.triangle 6 4546 4554)
  | 1484 => some (.triangle 18 4555 2170)
  | 1485 => some (.triangle 5 4545 4556)
  | 1486 => some (.leaf 2903)
  | 1487 => some (.leaf 2904)
  | 1488 => some (.triangle 5 4558 4559)
  | 1489 => some (.triangle 17 4557 4560)
  | 1490 => some (.leaf 2905)
  | 1491 => some (.leaf 2906)
  | 1492 => some (.triangle 6 4562 4563)
  | 1493 => some (.leaf 2907)
  | 1494 => some (.leaf 2908)
  | 1495 => some (.positive 2 (![3185, 3186, 3187, 3188, 4565, 4566]))
  | 1496 => some (.leaf 2909)
  | 1497 => some (.triangle 19 4567 4568)
  | 1498 => some (.leaf 2910)
  | 1499 => some (.leaf 2911)
  | 1500 => some (.positive 1 (![4569, 3194, 3195, 3196, 4570, 4571]))
  | 1501 => some (.triangle 17 4564 4572)
  | 1502 => some (.leaf 2912)
  | 1503 => some (.triangle 18 4573 4574)
  | 1504 => some (.triangle 16 4561 4575)
  | 1505 => some (.leaf 2913)
  | 1506 => some (.leaf 2914)
  | 1507 => some (.positive 0 (![4542, 4543, 4544, 4576, 4577, 4578]))
  | 1508 => some (.triangle 10 2251 4579)
  | 1509 => some (.triangle 15 4580 4448)
  | 1510 => some (.leaf 2915)
  | 1511 => some (.leaf 2916)
  | 1512 => some (.leaf 2917)
  | 1513 => some (.leaf 2918)
  | 1514 => some (.leaf 2919)
  | 1515 => some (.leaf 2920)
  | 1516 => some (.leaf 2921)
  | 1517 => some (.triangle 7 4476 4588)
  | 1518 => some (.leaf 2922)
  | 1519 => some (.leaf 2923)
  | 1520 => some (.positive 1 (![4585, 4586, 4587, 4589, 4590, 4591]))
  | 1521 => some (.triangle 6 4546 4592)
  | 1522 => some (.triangle 18 4593 2170)
  | 1523 => some (.triangle 5 4545 4594)
  | 1524 => some (.leaf 2924)
  | 1525 => some (.triangle 17 4595 4596)
  | 1526 => some (.leaf 2925)
  | 1527 => some (.triangle 16 4597 4598)
  | 1528 => some (.leaf 2926)
  | 1529 => some (.leaf 2927)
  | 1530 => some (.positive 0 (![4582, 4583, 4584, 4599, 4600, 4601]))
  | 1531 => some (.triangle 10 2251 4602)
  | 1532 => some (.triangle 15 4603 4448)
  | 1533 => some (.leaf 2928)
  | 1534 => some (.leaf 2929)
  | 1535 => some (.leaf 2930)
  | _ => none

end Jsp404.SevenLowerBranchShard02
