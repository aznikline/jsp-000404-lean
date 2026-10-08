import Jsp000404.SevenLowerReplay

/-! SOURCE_ONLY literal certificate data; no kernel PASS is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerBranchShard01
open SevenLowerReplay
def cycle0000 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-1), (0), (-1), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 8 0, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2])]

def cycle0001 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaLower 2, .thetaUpper 3, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 5, 3])]

def cycle0002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .gapLower 0 5 (![1, 2, 4, 5, 3]), .triangle 7 0, .triangle 19 0, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 5, 3]), .triangle 0 1]

def cycle0003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 0, .triangle 0 0]

def cycle0004 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 5, 3]), .triangle 0 1]

def cycle0005 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (3), (-1), (0), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .corridorUpper 1 2, .triangle 10 0, .triangle 17 2, .triangle 18 1, .triangle 5 0]

def cycle0006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 0, .triangle 17 2, .triangle 18 1, .gapLower 2 1 (![0, 4, 5, 3, 1]), .triangle 0 1]

def cycle0007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .gapLower 1 5 (![0, 4, 5, 3, 2]), .gapLower 2 4 (![0, 4, 5, 3, 1]), .triangle 17 2, .gapLower 2 2 (![0, 4, 5, 3, 1]), .triangle 5 0, .gapLower 0 1 (![1, 2, 4, 5, 3])]

def cycle0008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .gapLower 1 5 (![0, 4, 5, 3, 2]), .gapLower 2 4 (![0, 4, 5, 3, 1]), .gapLower 2 3 (![0, 4, 5, 3, 1]), .triangle 6 0, .gapLower 0 1 (![1, 2, 4, 5, 3])]

def cycle0009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 4, 5, 3, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 4, 5, 3])]

def cycle0010 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (-1), (0), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 4, 5, 3, 1]), .triangle 10 0, .triangle 17 2, .triangle 18 1, .triangle 5 0, .triangle 0 1]

def cycle0011 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (0), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 15 0, .triangle 2 0]

def cycle0012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 1 (![0, 4, 5, 3, 2])]

def cycle0013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 2 0]

def cycle0014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 3 0]

def cycle0015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 5, 3, 2]), .triangle 1 0]

def cycle0016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0017 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .triangle 5 0, .gapLower 0 1 (![1, 2, 4, 5, 3])]

def cycle0018 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .triangle 5 0, .triangle 0 1]

def cycle0019 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 5 1, .triangle 0 1]

def cycle0020 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0021 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 15 0, .triangle 9 0, .triangle 5 1, .triangle 0 1]

def cycle0022 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 5, 3]), .triangle 0 1]

def cycle0023 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 5, 3]), .gapLower 0 1 (![1, 2, 4, 5, 3])]

def cycle0024 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 5, 3]), .gapLower 0 1 (![1, 2, 4, 5, 3])]

def cycle0025 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![1, 2, 4, 5, 3]), .triangle 5 1, .gapLower 0 1 (![1, 2, 4, 5, 3])]

def cycle0026 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 2, 4, 5, 3]), .triangle 9 1, .triangle 5 1, .gapLower 0 1 (![1, 2, 4, 5, 3])]

def cycle0027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 4, 5, 3]), .triangle 8 2, .triangle 9 1, .gapLower 0 2 (![1, 2, 4, 5, 3]), .gapLower 0 1 (![1, 2, 4, 5, 3])]

def cycle0028 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![1, 2, 4, 5, 3]), .gapLower 0 2 (![1, 2, 4, 5, 3]), .triangle 0 1]

def cycle0029 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 2, 4, 5, 3]), .triangle 9 1, .gapLower 0 2 (![1, 2, 4, 5, 3]), .triangle 0 1]

def cycle0030 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 2, .gapLower 0 5 (![1, 2, 4, 5, 3]), .triangle 8 2, .triangle 9 1, .gapLower 0 2 (![1, 2, 4, 5, 3])]

def cycle0031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 2, 4, 5, 3]), .gapLower 0 3 (![1, 2, 4, 5, 3]), .triangle 7 1, .corridorLower 3 4, .corridorUpper 1 3, .triangle 1 2]

def cycle0032 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .distance 0 3]
    constant := ![(0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 1]
    strict := ![true, false, false, false] }
  origin := ![.triangle 8 2, .gapLower 0 3 (![1, 2, 4, 5, 3]), .corridorLower 0 4, .gapLower 0 5 (![1, 2, 4, 5, 3])]

def cycle0033 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .distance 0 3]
    constant := ![(-2), (-1), (2)]
    coefficient := ![0, 0, 1]
    strict := ![false, false, false] }
  origin := ![.gapLower 0 4 (![1, 2, 4, 5, 3]), .corridorLower 0 5, .gapLower 0 5 (![1, 2, 4, 5, 3])]

def cycle0034 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0036 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0037 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 2, .triangle 15 2, .triangle 3 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (0), (0), (-3)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 2, .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0039 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 0 3]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 7 2, .triangle 9 0, .triangle 19 2, .triangle 8 0]

def cycle0040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(0), (-1), (-1), (-2), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true, true] }
  origin := ![.triangle 7 2, .triangle 9 0, .triangle 19 0, .gapLower 3 0 (![4, 5, 0, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0041 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![(-1), (0), (-2), (-1), (3), (0), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 9 0, .triangle 19 2, .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 2 2]

def cycle0042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-2), (0), (0), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, true] }
  origin := ![.gapLower 3 2 (![4, 5, 0, 1, 2]), .gapLower 5 0 (![3, 4, 0, 1, 2]), .thetaOrder 4, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0043 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![(-1), (-2), (-1), (3), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.triangle 9 0, .gapLower 5 1 (![3, 4, 0, 1, 2]), .corridorLower 3 5, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 2 2]

def cycle0044 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(0), (0), (-2), (-1), (-1), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, true] }
  origin := ![.triangle 7 2, .triangle 9 2, .gapLower 5 2 (![3, 4, 0, 1, 2]), .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0045 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (0), (-2), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 5 3 (![3, 4, 0, 1, 2]), .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0046 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![3, 4, 0, 1, 2]), .triangle 3 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![3, 4, 0, 1, 2]), .triangle 12 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0048 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(0), (-1), (-1), (-1), (3), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true] }
  origin := ![.triangle 7 2, .triangle 9 0, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 1 2]

def cycle0050 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0051 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 7 0, .triangle 19 2, .triangle 8 0]

def cycle0052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 4 5, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-1), (-1), (-2), (0), (0), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.triangle 7 0, .triangle 19 0, .gapLower 5 0 (![4, 3, 0, 1, 2]), .thetaOrder 4, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0053 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-1), (0), (-2), (-1), (0), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.triangle 7 0, .triangle 19 2, .gapLower 5 1 (![4, 3, 0, 1, 2]), .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0054 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5]
    constant := ![(-2), (-2), (3), (0), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.gapLower 5 2 (![4, 3, 0, 1, 2]), .gapLower 3 0 (![5, 4, 0, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .triangle 3 2]

def cycle0055 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (0), (-2), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 5 3 (![4, 3, 0, 1, 2]), .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0056 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![4, 3, 0, 1, 2]), .triangle 3 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0057 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![4, 3, 0, 1, 2]), .triangle 12 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0058 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-1), (-2), (-1), (3), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, true] }
  origin := ![.triangle 7 0, .gapLower 3 1 (![5, 4, 0, 1, 2]), .corridorLower 3 5, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.gapLower 3 2 (![5, 4, 0, 1, 2]), .triangle 19 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0060 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![5, 4, 0, 1, 2]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0061 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![5, 4, 0, 1, 2]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0062 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![5, 4, 0, 1, 2]), .triangle 10 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0063 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(0), (2), (0), (0), (0), (-3)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0064 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![3, 4, 0, 1, 2]), .triangle 6 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0065 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![4, 3, 0, 1, 2]), .triangle 6 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0066 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![5, 4, 0, 1, 2]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0067 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![0, 1, 5, 4, 3]), .triangle 6 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0068 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0069 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 3 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0070 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 5, 4, 3]), .triangle 2 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0071 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0072 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0073 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0074 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (0), (-3), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0075 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(0), (-3), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, true] }
  origin := ![.triangle 7 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0076 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-3), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 2, 5, 4, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0077 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 3]
    constant := ![(0), (-1), (-1), (0), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, true, true, false] }
  origin := ![.triangle 7 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 5, 4, 3])]

def cycle0078 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0079 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (0), (-2), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 13 2, .triangle 15 2, .gapLower 5 3 (![3, 4, 0, 1, 2]), .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![3, 4, 0, 1, 2]), .triangle 3 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaLower 2, .thetaUpper 5, .gapLower 5 5 (![3, 4, 0, 1, 2]), .triangle 12 2, .triangle 3 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (4), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .gapLower 3 4 (![4, 5, 0, 1, 2]), .gapLower 3 3 (![4, 5, 0, 1, 2]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (4), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0084 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaLower 2, .thetaUpper 3, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 2, .triangle 3 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0085 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (0), (-2), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .gapLower 3 4 (![5, 4, 0, 1, 2]), .triangle 13 2, .triangle 15 2, .gapLower 5 3 (![4, 3, 0, 1, 2]), .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0086 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![4, 3, 0, 1, 2]), .triangle 3 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0087 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaLower 2, .thetaUpper 5, .gapLower 5 5 (![4, 3, 0, 1, 2]), .triangle 12 2, .triangle 3 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0088 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (4), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .gapLower 3 4 (![5, 4, 0, 1, 2]), .gapLower 3 3 (![5, 4, 0, 1, 2]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0089 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (4), (-2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .gapLower 3 4 (![5, 4, 0, 1, 2]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0090 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaLower 2, .thetaUpper 3, .gapLower 3 5 (![5, 4, 0, 1, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 2, .triangle 3 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0091 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 1 (![0, 1, 5, 4, 3]), .triangle 0 1]

def cycle0092 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![0, 1, 5, 4, 3]), .triangle 0 0]

def cycle0093 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![0, 1, 5, 4, 3]), .triangle 6 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0094 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0095 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0096 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0097 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0098 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 3 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0099 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 5, 4, 3]), .triangle 2 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0100 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0101 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0102 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0103 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0104 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(0), (-2), (0), (-1), (-1), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 7 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .gapLower 5 2 (![3, 4, 0, 1, 2]), .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0105 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![(-2), (0), (-2), (3), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true] }
  origin := ![.gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 8 1, .gapLower 3 0 (![5, 4, 0, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 2 2]

def cycle0106 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (4), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 2, .gapLower 3 3 (![5, 4, 0, 1, 2]), .triangle 7 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 6 1]

def cycle0107 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![5, 4, 0, 1, 2]), .triangle 1 0]

def cycle0108 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (0), (0), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaOrder 1, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![5, 4, 0, 1, 2]), .triangle 4 2, .triangle 7 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 6 1]

def cycle0109 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 5 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 6 1, .triangle 0 1]

def cycle0110 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 4 2, .triangle 7 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 6 1, .triangle 0 1]

def cycle0111 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 3 0]

def cycle0112 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 5, 4, 3]), .triangle 2 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 6 1, .triangle 0 1]

def cycle0113 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 6 1, .triangle 0 1]

def cycle0114 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0115 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 6 1, .triangle 0 1]

def cycle0116 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .triangle 7 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 6 1, .triangle 0 1]

def cycle0117 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 2, 5, 4, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0118 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .gapLower 0 5 (![1, 2, 5, 4, 3]), .triangle 7 0, .triangle 13 0, .triangle 1 0]

def cycle0119 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (-1), (3), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .gapLower 0 5 (![1, 2, 5, 4, 3]), .triangle 7 2, .triangle 9 0, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0120 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (3), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .gapLower 0 5 (![1, 2, 5, 4, 3]), .triangle 7 0, .triangle 19 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0121 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 0, .triangle 0 0]

def cycle0122 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 5, 4, 3]), .triangle 2 0]

def cycle0123 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![0, 1, 5, 4, 3]), .triangle 12 0, .triangle 0 0]

def cycle0124 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 11 0, .triangle 0 0]

def cycle0125 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0126 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2]
    constant := ![(-2), (3), (-1), (0), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 5, 4, 3, 1]), .corridorUpper 1 2, .triangle 10 0, .triangle 16 2, .triangle 18 2, .triangle 6 0]

def cycle0127 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 0, .triangle 16 2, .triangle 18 2, .gapLower 2 1 (![0, 5, 4, 3, 1]), .triangle 0 1]

def cycle0128 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .gapLower 2 4 (![0, 5, 4, 3, 1]), .triangle 16 2, .gapLower 2 2 (![0, 5, 4, 3, 1]), .triangle 6 0, .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0129 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .gapLower 2 4 (![0, 5, 4, 3, 1]), .gapLower 2 3 (![0, 5, 4, 3, 1]), .triangle 5 0, .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0130 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 5, 4, 3, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0131 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (-1), (0), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 5, 4, 3, 1]), .triangle 10 0, .triangle 16 2, .triangle 18 2, .triangle 6 0, .triangle 0 1]

def cycle0132 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 2, .triangle 18 2, .gapLower 2 1 (![0, 5, 4, 3, 1]), .triangle 0 1]

def cycle0133 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 2, .gapLower 2 2 (![0, 5, 4, 3, 1]), .triangle 6 0, .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0134 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .gapLower 2 3 (![0, 5, 4, 3, 1]), .triangle 5 0, .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0135 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 5, 4, 3, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0136 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 5, 4, 3, 1]), .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0137 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0138 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 0]

def cycle0139 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 1 0]

def cycle0140 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 4, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 0, .triangle 4 0, .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0141 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0142 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 6 1, .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0143 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 2, 5, 4, 3]), .triangle 5 1, .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0144 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 5, 4, 3]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .gapLower 0 1 (![1, 2, 5, 4, 3])]

def cycle0145 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0146 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 2, 5, 4, 3]), .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3]), .triangle 0 1]

def cycle0147 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 2, .gapLower 0 5 (![1, 2, 5, 4, 3]), .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 2, 5, 4, 3])]

def cycle0148 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 2, 5, 4, 3]), .gapLower 0 3 (![1, 2, 5, 4, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2]

def cycle0149 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .theta 0, .distance 0 3]
    constant := ![(0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 1]
    strict := ![true, false, false, false] }
  origin := ![.triangle 7 2, .gapLower 0 3 (![1, 2, 5, 4, 3]), .corridorLower 0 5, .gapLower 0 5 (![1, 2, 5, 4, 3])]

def cycle0150 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 3]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 4 (![1, 2, 5, 4, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 5, 4, 3])]

def cycle0151 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0152 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 6 2, .triangle 3 1]

def cycle0153 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 3, 4])]

def cycle0154 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![1, 5, 2, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0155 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![1, 5, 2, 3, 4])]

def cycle0156 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 5, 2, 3, 4]), .triangle 4 1]

def cycle0157 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 2, 3, 4]), .triangle 7 1, .triangle 4 1]

def cycle0158 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 3, 4])]

def cycle0159 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![1, 5, 2, 3, 4]), .triangle 3 1]

def cycle0160 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![1, 5, 2, 3, 4]), .triangle 0 1]

def cycle0161 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 6 0, .triangle 12 0, .triangle 0 2]

def cycle0162 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 2, 3, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .triangle 12 2, .triangle 3 0]

def cycle0163 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true] }
  origin := ![.gapLower 1 0 (![0, 5, 2, 3, 4]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 2, .triangle 2 2, .gapLower 0 4 (![1, 5, 2, 3, 4]), .triangle 4 1, .triangle 6 2, .triangle 3 1]

def cycle0164 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 2, .gapLower 1 1 (![0, 5, 2, 3, 4])]

def cycle0165 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![0, 5, 2, 3, 4]), .triangle 3 0]

def cycle0166 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 3 (![0, 5, 2, 3, 4]), .triangle 0 0]

def cycle0167 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 5, 2, 3, 4]), .triangle 1 0]

def cycle0168 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![0, 5, 2, 3, 4]), .triangle 2 2, .gapLower 0 4 (![1, 5, 2, 3, 4]), .triangle 4 1]

def cycle0169 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![1, 5, 2, 3, 4]), .triangle 4 1, .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 3, 4])]

def cycle0170 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![1, 5, 2, 3, 4]), .triangle 4 1, .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 3, 4])]

def cycle0171 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0]

def cycle0172 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .gapLower 1 3 (![0, 5, 2, 3, 4]), .triangle 0 0]

def cycle0173 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .triangle 12 2, .triangle 3 0]

def cycle0174 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 6 0, .gapLower 2 0 (![5, 0, 1, 4, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 4 1]

def cycle0175 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 2 1 (![5, 0, 1, 4, 3]), .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 4 1]

def cycle0176 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 2 (![5, 0, 1, 4, 3]), .triangle 0 1]

def cycle0177 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![5, 0, 1, 4, 3]), .triangle 0 0]

def cycle0178 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-2), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0 (![0, 5, 2, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![5, 0, 1, 4, 3]), .triangle 11 0, .triangle 12 2, .triangle 3 0]

def cycle0179 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .gapLower 2 5 (![5, 0, 1, 4, 3]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 3 (![1, 5, 2, 3, 4])]

def cycle0180 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 2, .gapLower 1 1 (![0, 5, 2, 4, 3])]

def cycle0181 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![0, 5, 2, 4, 3]), .triangle 3 0]

def cycle0182 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 5, 2, 4, 3]), .triangle 0 0]

def cycle0183 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 5, 2, 4, 3]), .triangle 2 0]

def cycle0184 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![0, 5, 2, 4, 3]), .triangle 13 0, .triangle 7 0, .gapLower 0 3 (![1, 5, 2, 3, 4])]

def cycle0185 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .triangle 6 2, .triangle 3 1]

def cycle0186 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![1, 5, 2, 3, 4]), .gapLower 0 1 (![1, 5, 2, 3, 4])]

def cycle0187 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![1, 5, 2, 3, 4]), .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 3, 4])]

def cycle0188 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 5, 2, 3, 4]), .triangle 4 1, .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 3, 4])]

def cycle0189 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 5, 2, 3, 4]), .triangle 7 1, .triangle 4 1, .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 3, 4])]

def cycle0190 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![1, 5, 2, 3, 4]), .gapLower 0 2 (![1, 5, 2, 3, 4]), .triangle 3 1]

def cycle0191 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 5, 2, 3, 4]), .triangle 4 1, .gapLower 0 2 (![1, 5, 2, 3, 4]), .triangle 3 1]

def cycle0192 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 2 (![1, 5, 2, 3, 4]), .corridorLower 0 5, .gapLower 0 5 (![1, 5, 2, 3, 4]), .triangle 7 1, .triangle 4 1]

def cycle0193 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 5, 2, 3, 4]), .gapLower 0 3 (![1, 5, 2, 3, 4])]

def cycle0194 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 2, 3, 4]), .triangle 7 1, .gapLower 0 3 (![1, 5, 2, 3, 4])]

def cycle0195 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 2, 3, 4]), .gapLower 0 4 (![1, 5, 2, 3, 4]), .triangle 4 1]

def cycle0196 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0197 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 6 2, .triangle 3 1]

def cycle0198 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 4, 3])]

def cycle0199 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![1, 5, 2, 4, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0200 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![1, 5, 2, 4, 3])]

def cycle0201 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 5, 2, 4, 3]), .triangle 5 1]

def cycle0202 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 2, 4, 3]), .triangle 4 1]

def cycle0203 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 4, 3])]

def cycle0204 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![1, 5, 2, 4, 3]), .triangle 3 1]

def cycle0205 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-2), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 6 0, .gapLower 2 0 (![5, 0, 1, 4, 3]), .gapLower 2 5 (![5, 0, 1, 4, 3]), .triangle 10 2, .triangle 13 2, .triangle 2 2, .gapLower 0 3 (![1, 5, 2, 4, 3])]

def cycle0206 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 1 (![5, 0, 1, 4, 3]), .corridorLower 2 5, .gapLower 2 5 (![5, 0, 1, 4, 3]), .triangle 10 2, .triangle 13 2, .triangle 2 2, .gapLower 0 3 (![1, 5, 2, 4, 3])]

def cycle0207 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 2 (![5, 0, 1, 4, 3]), .triangle 0 1]

def cycle0208 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![5, 0, 1, 4, 3]), .triangle 0 0]

def cycle0209 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 5, 2, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![5, 0, 1, 4, 3]), .triangle 5 2, .gapLower 0 3 (![1, 5, 2, 4, 3]), .triangle 0 1]

def cycle0210 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .gapLower 2 5 (![5, 0, 1, 4, 3]), .triangle 4 2, .triangle 7 2, .gapLower 0 3 (![1, 5, 2, 4, 3])]

def cycle0211 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 2, .gapLower 1 1 (![0, 5, 2, 4, 3])]

def cycle0212 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![0, 5, 2, 4, 3]), .triangle 3 0]

def cycle0213 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 5, 2, 4, 3]), .triangle 0 0]

def cycle0214 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 5, 2, 4, 3]), .triangle 2 2, .gapLower 0 3 (![1, 5, 2, 4, 3]), .triangle 0 1]

def cycle0215 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![0, 5, 2, 4, 3]), .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![1, 5, 2, 4, 3])]

def cycle0216 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 2, .gapLower 0 3 (![1, 5, 2, 4, 3]), .triangle 0 1]

def cycle0217 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .triangle 7 2, .gapLower 0 3 (![1, 5, 2, 4, 3])]

def cycle0218 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-2), (4), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 6 0, .gapLower 2 0 (![5, 0, 1, 4, 3]), .gapLower 2 5 (![5, 0, 1, 4, 3]), .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![1, 5, 2, 4, 3]), .triangle 5 1]

def cycle0219 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 2 1 (![5, 0, 1, 4, 3]), .corridorLower 2 5, .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![1, 5, 2, 4, 3]), .triangle 5 1]

def cycle0220 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .gapLower 2 5 (![5, 0, 1, 4, 3]), .triangle 4 2, .gapLower 0 4 (![1, 5, 2, 4, 3]), .triangle 5 1]

def cycle0221 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 5, 2, 4, 3]), .triangle 2 0]

def cycle0222 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![0, 5, 2, 4, 3]), .triangle 1 2, .gapLower 0 4 (![1, 5, 2, 4, 3]), .triangle 5 1]

def cycle0223 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .triangle 6 2, .triangle 3 1]

def cycle0224 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .gapLower 0 4 (![1, 5, 2, 4, 3]), .triangle 5 1]

def cycle0225 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .gapLower 0 5 (![1, 5, 2, 4, 3]), .triangle 7 0, .triangle 13 0, .gapLower 1 3 (![0, 5, 2, 3, 4]), .triangle 0 0]

def cycle0226 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .gapLower 0 5 (![1, 5, 2, 4, 3]), .triangle 7 0, .triangle 16 0, .triangle 4 0, .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 4, 3])]

def cycle0227 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-2), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 6 0, .gapLower 2 0 (![5, 0, 1, 4, 3]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 2, 4, 3]), .triangle 4 1]

def cycle0228 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.gapLower 2 1 (![5, 0, 1, 4, 3]), .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 2, 4, 3]), .triangle 4 1]

def cycle0229 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![5, 0, 1, 4, 3]), .triangle 10 0, .triangle 12 2, .triangle 3 0]

def cycle0230 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-2), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .gapLower 0 5 (![1, 5, 2, 4, 3]), .triangle 4 1, .triangle 6 0, .gapLower 2 0 (![5, 0, 1, 4, 3]), .thetaOrder 1, .gapLower 1 5 (![0, 5, 2, 4, 3]), .triangle 1 0]

def cycle0231 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (0), (-2), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .gapLower 0 5 (![1, 5, 2, 4, 3]), .triangle 4 1, .gapLower 2 1 (![5, 0, 1, 4, 3]), .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![0, 5, 2, 4, 3]), .triangle 1 0]

def cycle0232 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![0, 5, 2, 4, 3]), .triangle 10 1, .gapLower 2 2 (![5, 0, 1, 4, 3])]

def cycle0233 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 2, 4, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![5, 0, 1, 4, 3]), .triangle 11 0, .triangle 12 2, .triangle 3 0]

def cycle0234 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![1, 5, 2, 4, 3]), .gapLower 0 1 (![1, 5, 2, 4, 3])]

def cycle0235 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![1, 5, 2, 4, 3]), .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 4, 3])]

def cycle0236 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 5, 2, 4, 3]), .triangle 5 1, .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 4, 3])]

def cycle0237 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 5, 2, 4, 3]), .triangle 4 1, .triangle 6 2, .gapLower 0 1 (![1, 5, 2, 4, 3])]

def cycle0238 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 7 2, .gapLower 0 3 (![1, 5, 2, 4, 3]), .gapLower 0 2 (![1, 5, 2, 4, 3]), .triangle 3 1]

def cycle0239 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 5, 2, 4, 3]), .triangle 5 1, .gapLower 0 2 (![1, 5, 2, 4, 3]), .triangle 3 1]

def cycle0240 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 2 (![1, 5, 2, 4, 3]), .corridorLower 0 5, .gapLower 0 5 (![1, 5, 2, 4, 3]), .triangle 4 1]

def cycle0241 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 5, 2, 4, 3]), .gapLower 0 3 (![1, 5, 2, 4, 3])]

def cycle0242 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 2, 4, 3]), .triangle 7 2, .gapLower 0 3 (![1, 5, 2, 4, 3])]

def cycle0243 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 2, 4, 3]), .gapLower 0 4 (![1, 5, 2, 4, 3]), .triangle 5 1]

def cycle0244 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0245 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 5 2, .triangle 2 1]

def cycle0246 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 3, 5])]

def cycle0247 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![1, 4, 2, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0248 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![1, 4, 2, 3, 5])]

def cycle0249 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 4, 2, 3, 5]), .triangle 4 1]

def cycle0250 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 2, 3, 5]), .triangle 8 1, .triangle 4 1]

def cycle0251 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 3, 5])]

def cycle0252 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![1, 4, 2, 3, 5]), .triangle 2 1]

def cycle0253 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![1, 4, 2, 3, 5]), .triangle 0 1]

def cycle0254 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 5 0, .triangle 11 0, .triangle 0 2]

def cycle0255 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0 (![0, 4, 2, 3, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 10 0, .triangle 11 2, .triangle 2 0]

def cycle0256 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true] }
  origin := ![.gapLower 1 0 (![0, 4, 2, 3, 5]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .triangle 14 2, .triangle 3 2, .gapLower 0 4 (![1, 4, 2, 3, 5]), .triangle 4 1, .triangle 5 2, .triangle 2 1]

def cycle0257 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .gapLower 1 1 (![0, 4, 2, 3, 5])]

def cycle0258 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![0, 4, 2, 3, 5]), .triangle 2 0]

def cycle0259 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 3 (![0, 4, 2, 3, 5]), .triangle 0 0]

def cycle0260 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![0, 4, 2, 3, 5]), .triangle 1 0]

def cycle0261 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 4, 2, 3, 5]), .triangle 3 2, .gapLower 0 4 (![1, 4, 2, 3, 5]), .triangle 4 1]

def cycle0262 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 4, 2, 3, 5]), .triangle 4 1, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 3, 5])]

def cycle0263 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![1, 4, 2, 3, 5]), .triangle 4 1, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 3, 5])]

def cycle0264 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 4, 2, 3, 5]), .triangle 4 1, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 3, 5])]

def cycle0265 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0]

def cycle0266 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .triangle 14 0, .gapLower 1 3 (![0, 4, 2, 3, 5]), .triangle 0 0]

def cycle0267 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 10 0, .triangle 11 2, .triangle 2 0]

def cycle0268 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 5 0, .gapLower 2 0 (![4, 0, 1, 5, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 0, .triangle 8 0, .triangle 4 1]

def cycle0269 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 2 1 (![4, 0, 1, 5, 3]), .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 0, .triangle 8 0, .triangle 4 1]

def cycle0270 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 2 (![4, 0, 1, 5, 3]), .triangle 0 1]

def cycle0271 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![4, 0, 1, 5, 3]), .triangle 0 0]

def cycle0272 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 2, 5, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![4, 0, 1, 5, 3]), .triangle 12 0, .triangle 0 0]

def cycle0273 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .gapLower 2 5 (![4, 0, 1, 5, 3]), .triangle 10 2, .triangle 14 0, .triangle 8 0, .gapLower 0 3 (![1, 4, 2, 3, 5])]

def cycle0274 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .gapLower 1 1 (![0, 4, 2, 5, 3])]

def cycle0275 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![0, 4, 2, 5, 3]), .triangle 2 0]

def cycle0276 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 2, .gapLower 1 3 (![0, 4, 2, 5, 3]), .triangle 0 0]

def cycle0277 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 4, 2, 5, 3]), .triangle 3 0]

def cycle0278 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 4, 2, 5, 3]), .triangle 14 0, .triangle 8 0, .gapLower 0 3 (![1, 4, 2, 3, 5])]

def cycle0279 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0280 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0281 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![1, 4, 2, 3, 5]), .gapLower 0 1 (![1, 4, 2, 3, 5])]

def cycle0282 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![1, 4, 2, 3, 5]), .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 3, 5])]

def cycle0283 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 4, 2, 3, 5]), .triangle 4 1, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 3, 5])]

def cycle0284 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 4, 2, 3, 5]), .triangle 6 1, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 3, 5])]

def cycle0285 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![1, 4, 2, 3, 5]), .gapLower 0 2 (![1, 4, 2, 3, 5]), .triangle 2 1]

def cycle0286 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 4, 2, 3, 5]), .triangle 4 1, .gapLower 0 2 (![1, 4, 2, 3, 5]), .triangle 2 1]

def cycle0287 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 2 (![1, 4, 2, 3, 5]), .corridorLower 0 4, .gapLower 0 5 (![1, 4, 2, 3, 5]), .triangle 8 1, .triangle 4 1]

def cycle0288 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 4, 2, 3, 5]), .gapLower 0 3 (![1, 4, 2, 3, 5])]

def cycle0289 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 2, 3, 5]), .triangle 8 1, .gapLower 0 3 (![1, 4, 2, 3, 5])]

def cycle0290 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 2, 3, 5]), .gapLower 0 4 (![1, 4, 2, 3, 5]), .triangle 4 1]

def cycle0291 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0292 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 5 2, .triangle 2 1]

def cycle0293 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 5, 3])]

def cycle0294 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![1, 4, 2, 5, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0295 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![1, 4, 2, 5, 3])]

def cycle0296 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 4, 2, 5, 3]), .triangle 8 1, .corridorLower 3 5, .corridorUpper 1 3, .triangle 1 2]

def cycle0297 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 2, 5, 3]), .triangle 8 2, .triangle 6 1]

def cycle0298 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 5, 3])]

def cycle0299 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![1, 4, 2, 5, 3]), .triangle 2 1]

def cycle0300 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-2), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 5 0, .gapLower 2 0 (![4, 0, 1, 5, 3]), .gapLower 2 5 (![4, 0, 1, 5, 3]), .triangle 10 2, .triangle 14 2, .triangle 3 2, .gapLower 0 3 (![1, 4, 2, 5, 3])]

def cycle0301 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (-1), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 1 (![4, 0, 1, 5, 3]), .corridorLower 2 4, .gapLower 2 5 (![4, 0, 1, 5, 3]), .triangle 10 2, .triangle 14 2, .triangle 3 2, .gapLower 0 3 (![1, 4, 2, 5, 3])]

def cycle0302 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 2 (![4, 0, 1, 5, 3]), .triangle 0 1]

def cycle0303 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![4, 0, 1, 5, 3]), .triangle 0 0]

def cycle0304 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 2, 5, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![4, 0, 1, 5, 3]), .triangle 12 2, .triangle 3 2, .gapLower 0 3 (![1, 4, 2, 5, 3]), .triangle 0 1]

def cycle0305 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .gapLower 2 5 (![4, 0, 1, 5, 3]), .triangle 4 2, .triangle 8 2, .gapLower 0 3 (![1, 4, 2, 5, 3])]

def cycle0306 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .gapLower 1 1 (![0, 4, 2, 5, 3])]

def cycle0307 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![0, 4, 2, 5, 3]), .triangle 2 0]

def cycle0308 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 2, .gapLower 1 3 (![0, 4, 2, 5, 3]), .triangle 0 0]

def cycle0309 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 4, 2, 5, 3]), .triangle 3 2, .gapLower 0 3 (![1, 4, 2, 5, 3]), .triangle 0 1]

def cycle0310 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 4, 2, 5, 3]), .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![1, 4, 2, 5, 3])]

def cycle0311 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .gapLower 5 2 (![3, 0, 2, 1, 4]), .gapLower 0 3 (![1, 4, 2, 5, 3]), .triangle 0 1]

def cycle0312 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 3 (![1, 4, 2, 5, 3]), .triangle 0 1]

def cycle0313 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .triangle 8 2, .gapLower 0 3 (![1, 4, 2, 5, 3])]

def cycle0314 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 5 0, .gapLower 2 0 (![4, 0, 1, 5, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![1, 4, 2, 5, 3]), .triangle 6 1]

def cycle0315 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 2 1 (![4, 0, 1, 5, 3]), .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![1, 4, 2, 5, 3]), .triangle 6 1]

def cycle0316 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .gapLower 2 5 (![4, 0, 1, 5, 3]), .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![1, 4, 2, 5, 3]), .triangle 6 1]

def cycle0317 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 4, 2, 5, 3]), .triangle 3 0]

def cycle0318 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 4, 2, 5, 3]), .triangle 1 2, .gapLower 0 4 (![1, 4, 2, 5, 3]), .triangle 6 1]

def cycle0319 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0320 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0321 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .gapLower 0 4 (![1, 4, 2, 5, 3]), .triangle 6 1]

def cycle0322 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (-1), (0), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .gapLower 0 5 (![1, 4, 2, 5, 3]), .triangle 8 0, .triangle 14 2, .triangle 15 1, .gapLower 1 1 (![0, 4, 2, 3, 5])]

def cycle0323 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .gapLower 0 5 (![1, 4, 2, 5, 3]), .triangle 8 0, .triangle 17 0, .triangle 4 0, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 5, 3])]

def cycle0324 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-2), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 5 0, .gapLower 2 0 (![4, 0, 1, 5, 3]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 2, 5, 3]), .triangle 4 1]

def cycle0325 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.gapLower 2 1 (![4, 0, 1, 5, 3]), .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 2, 5, 3]), .triangle 4 1]

def cycle0326 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 0, 1, 5, 3]), .triangle 10 0, .triangle 11 2, .triangle 2 0]

def cycle0327 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-2), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .gapLower 0 5 (![1, 4, 2, 5, 3]), .triangle 4 1, .triangle 5 0, .gapLower 2 0 (![4, 0, 1, 5, 3]), .thetaOrder 1, .gapLower 1 5 (![0, 4, 2, 5, 3]), .triangle 1 0]

def cycle0328 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (0), (-2), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .gapLower 0 5 (![1, 4, 2, 5, 3]), .triangle 4 1, .gapLower 2 1 (![4, 0, 1, 5, 3]), .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 4, 2, 5, 3]), .triangle 1 0]

def cycle0329 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 4, 2, 5, 3]), .triangle 10 1, .gapLower 2 2 (![4, 0, 1, 5, 3])]

def cycle0330 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 2, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![4, 0, 1, 5, 3]), .triangle 12 0, .triangle 0 0]

def cycle0331 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 2 (![1, 4, 2, 5, 3]), .gapLower 0 1 (![1, 4, 2, 5, 3])]

def cycle0332 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![1, 4, 2, 5, 3]), .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 5, 3])]

def cycle0333 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 4, 2, 5, 3]), .triangle 6 1, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 5, 3])]

def cycle0334 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 4, 2, 5, 3]), .triangle 8 2, .triangle 6 1, .triangle 5 2, .gapLower 0 1 (![1, 4, 2, 5, 3])]

def cycle0335 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![1, 4, 2, 5, 3]), .gapLower 0 2 (![1, 4, 2, 5, 3]), .triangle 2 1]

def cycle0336 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 4, 2, 5, 3]), .triangle 6 1, .gapLower 0 2 (![1, 4, 2, 5, 3]), .triangle 2 1]

def cycle0337 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 2 (![1, 4, 2, 5, 3]), .corridorLower 0 4, .gapLower 0 5 (![1, 4, 2, 5, 3]), .triangle 4 1]

def cycle0338 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 4, 2, 5, 3]), .gapLower 0 3 (![1, 4, 2, 5, 3])]

def cycle0339 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 2, 5, 3]), .triangle 8 2, .gapLower 0 3 (![1, 4, 2, 5, 3])]

def cycle0340 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 2, 5, 3]), .gapLower 0 4 (![1, 4, 2, 5, 3]), .triangle 6 1]

def cycle0341 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0342 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 6 2, .triangle 9 1, .triangle 2 1]

def cycle0343 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .triangle 9 1, .gapLower 0 1 (![1, 4, 5, 2, 3])]

def cycle0344 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 2 (![1, 4, 5, 2, 3]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0345 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![1, 4, 5, 2, 3]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0346 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 4, 5, 2, 3])]

def cycle0347 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 5, 2, 3]), .triangle 4 1]

def cycle0348 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .triangle 9 1, .gapLower 0 1 (![1, 4, 5, 2, 3])]

def cycle0349 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 2 (![1, 4, 5, 2, 3]), .triangle 2 1]

def cycle0350 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![1, 4, 5, 2, 3]), .triangle 3 1]

def cycle0351 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .gapLower 2 0 (![4, 5, 0, 1, 3]), .gapLower 2 5 (![4, 5, 0, 1, 3]), .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![1, 4, 5, 2, 3])]

def cycle0352 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 2 2 (![4, 5, 0, 1, 3]), .gapLower 2 1 (![4, 5, 0, 1, 3]), .corridorLower 2 4, .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![1, 4, 5, 2, 3])]

def cycle0353 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2 (![4, 5, 0, 1, 3]), .corridorLower 2 5, .gapLower 2 5 (![4, 5, 0, 1, 3]), .triangle 10 2, .triangle 1 2, .gapLower 0 4 (![1, 4, 5, 2, 3])]

def cycle0354 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 3 (![4, 5, 0, 1, 3]), .triangle 6 2, .triangle 9 1, .gapLower 0 1 (![1, 4, 5, 2, 3])]

def cycle0355 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![4, 5, 0, 1, 3]), .triangle 0 0]

def cycle0356 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (-1), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .corridorLower 2 4, .gapLower 2 5 (![4, 5, 0, 1, 3]), .triangle 4 2, .gapLower 0 4 (![1, 4, 5, 2, 3])]

def cycle0357 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 2 4, .distance 4 5, .distance 0 4]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 5 1, .triangle 18 0, .triangle 9 0]

def cycle0358 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 2, .triangle 15 1, .gapLower 1 1 (![0, 4, 5, 2, 3])]

def cycle0359 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 2, .gapLower 1 2 (![0, 4, 5, 2, 3]), .triangle 2 0]

def cycle0360 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 3 (![0, 4, 5, 2, 3]), .triangle 3 0]

def cycle0361 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 4, 5, 2, 3]), .triangle 0 0]

def cycle0362 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 4, 5, 2, 3]), .triangle 1 2, .gapLower 0 4 (![1, 4, 5, 2, 3])]

def cycle0363 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0364 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .gapLower 0 4 (![1, 4, 5, 2, 3])]

def cycle0365 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (-2), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.triangle 6 0, .triangle 18 1, .gapLower 2 0 (![4, 5, 0, 1, 3]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 5, 2, 3]), .triangle 4 1]

def cycle0366 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-2), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 6 0, .gapLower 2 1 (![4, 5, 0, 1, 3]), .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 5, 2, 3]), .triangle 4 1]

def cycle0367 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.gapLower 2 2 (![4, 5, 0, 1, 3]), .triangle 18 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 5, 2, 3]), .triangle 4 1]

def cycle0368 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 0, 1, 3]), .triangle 10 0, .triangle 12 2, .triangle 15 1, .triangle 2 0]

def cycle0369 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .gapLower 0 5 (![1, 4, 5, 2, 3]), .triangle 4 1, .triangle 5 0, .triangle 18 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 5, 2, 3])]

def cycle0370 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (0), (-2), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .gapLower 0 5 (![1, 4, 5, 2, 3]), .triangle 4 1, .triangle 6 0, .triangle 18 1, .gapLower 2 0 (![4, 5, 0, 1, 3]), .thetaOrder 1, .gapLower 1 5 (![0, 4, 5, 2, 3]), .triangle 1 0]

def cycle0371 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-2), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .gapLower 0 5 (![1, 4, 5, 2, 3]), .triangle 4 1, .triangle 6 0, .gapLower 2 1 (![4, 5, 0, 1, 3]), .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 4, 5, 2, 3]), .triangle 1 0]

def cycle0372 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (0), (-2), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 2, 3]), .gapLower 0 5 (![1, 4, 5, 2, 3]), .triangle 4 1, .gapLower 2 2 (![4, 5, 0, 1, 3]), .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![0, 4, 5, 2, 3]), .triangle 1 0]

def cycle0373 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 4, 5, 2, 3]), .triangle 10 1, .gapLower 2 3 (![4, 5, 0, 1, 3])]

def cycle0374 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 6 2, .gapLower 0 2 (![1, 4, 5, 2, 3]), .gapLower 0 1 (![1, 4, 5, 2, 3])]

def cycle0375 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![1, 4, 5, 2, 3]), .triangle 9 1, .gapLower 0 1 (![1, 4, 5, 2, 3])]

def cycle0376 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 4, 5, 2, 3]), .triangle 6 2, .triangle 9 1, .gapLower 0 1 (![1, 4, 5, 2, 3])]

def cycle0377 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 4, 5, 2, 3]), .triangle 4 1, .triangle 6 2, .triangle 9 1, .gapLower 0 1 (![1, 4, 5, 2, 3])]

def cycle0378 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![1, 4, 5, 2, 3]), .gapLower 0 2 (![1, 4, 5, 2, 3]), .triangle 2 1]

def cycle0379 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 4, 5, 2, 3]), .triangle 6 2, .gapLower 0 2 (![1, 4, 5, 2, 3]), .triangle 2 1]

def cycle0380 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 2 (![1, 4, 5, 2, 3]), .corridorLower 0 4, .gapLower 0 5 (![1, 4, 5, 2, 3]), .triangle 4 1]

def cycle0381 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 4, 5, 2, 3]), .gapLower 0 3 (![1, 4, 5, 2, 3]), .triangle 9 1, .triangle 2 1]

def cycle0382 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 3 (![1, 4, 5, 2, 3]), .corridorLower 0 5, .gapLower 0 5 (![1, 4, 5, 2, 3]), .triangle 4 1]

def cycle0383 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 5, 2, 3]), .gapLower 0 4 (![1, 4, 5, 2, 3])]

def cycle0384 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0385 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 2, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 5 2, .triangle 9 2, .triangle 3 1]

def cycle0386 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 2, 3])]

def cycle0387 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-3), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 2 (![1, 5, 4, 2, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0388 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![1, 5, 4, 2, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0389 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 5, 4, 2, 3])]

def cycle0390 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 4, 2, 3]), .triangle 4 1]

def cycle0391 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 2, 3])]

def cycle0392 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 2 (![1, 5, 4, 2, 3]), .triangle 3 1]

def cycle0393 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 3 (![1, 5, 4, 2, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0394 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 5, 4, 2, 3])]

def cycle0395 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 18 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 4, 2, 3]), .triangle 4 1]

def cycle0396 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (3), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.triangle 5 0, .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 2]

def cycle0397 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 2, 3])]

def cycle0398 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .gapLower 1 2 (![0, 5, 4, 2, 3]), .triangle 3 0]

def cycle0399 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 3 (![0, 5, 4, 2, 3]), .triangle 2 0]

def cycle0400 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 2, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 5, 4, 2, 3]), .triangle 0 0]

def cycle0401 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (0), (0), (-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 4, 2, 3]), .gapLower 0 5 (![1, 5, 4, 2, 3]), .triangle 4 1, .triangle 5 2, .triangle 9 0, .triangle 18 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 5, 4, 2, 3]), .triangle 1 0]

def cycle0402 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .triangle 5 2, .gapLower 0 2 (![1, 5, 4, 2, 3]), .gapLower 0 1 (![1, 5, 4, 2, 3])]

def cycle0403 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 3 (![1, 5, 4, 2, 3]), .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 2, 3])]

def cycle0404 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 5, 4, 2, 3]), .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 2, 3])]

def cycle0405 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 5, 4, 2, 3]), .triangle 4 1, .triangle 5 2, .triangle 9 2, .gapLower 0 1 (![1, 5, 4, 2, 3])]

def cycle0406 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 0 3 (![1, 5, 4, 2, 3]), .gapLower 0 2 (![1, 5, 4, 2, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0407 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 2 (![1, 5, 4, 2, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 5, 4, 2, 3])]

def cycle0408 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 2 (![1, 5, 4, 2, 3]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 4 0]

def cycle0409 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3 (![1, 5, 4, 2, 3]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 1 2, .gapLower 0 4 (![1, 5, 4, 2, 3])]

def cycle0410 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 5 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 4, 2, 3]), .gapLower 0 4 (![1, 5, 4, 2, 3])]

def cycle0411 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 4 0, .triangle 10 0, .triangle 0 2]

def cycle0412 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0413 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0414 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 4 2, .gapLower 0 1 (![1, 3, 2, 4, 5])]

def cycle0415 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![1, 3, 2, 4, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0416 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![1, 3, 2, 4, 5])]

def cycle0417 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 3, 2, 4, 5]), .triangle 5 1]

def cycle0418 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 2, 4, 5]), .triangle 9 1, .triangle 5 1]

def cycle0419 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 4 2, .gapLower 0 1 (![1, 3, 2, 4, 5])]

def cycle0420 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 2 (![1, 3, 2, 4, 5]), .triangle 1 1]

def cycle0421 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![1, 3, 2, 4, 5]), .triangle 0 1]

def cycle0422 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 2, 4, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .triangle 0 0]

def cycle0423 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 3, 2, 4, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 0, .triangle 15 2, .triangle 3 2, .gapLower 0 4 (![1, 3, 2, 4, 5]), .triangle 5 1, .triangle 0 1]

def cycle0424 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 2, .gapLower 1 1 (![0, 3, 2, 4, 5])]

def cycle0425 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 2 (![0, 3, 2, 4, 5]), .triangle 1 0]

def cycle0426 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 3 (![0, 3, 2, 4, 5]), .triangle 0 0]

def cycle0427 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![0, 3, 2, 4, 5]), .triangle 2 0]

def cycle0428 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 2, 4, 5]), .triangle 3 2, .gapLower 0 4 (![1, 3, 2, 4, 5]), .triangle 5 1]

def cycle0429 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 3, 2, 4, 5]), .triangle 5 1, .triangle 0 1]

def cycle0430 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![1, 3, 2, 4, 5]), .triangle 5 1, .triangle 0 1]

def cycle0431 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0]

def cycle0432 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 3, 2, 4, 5]), .triangle 5 1, .triangle 0 1]

def cycle0433 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0434 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 3, 2, 4, 5]), .triangle 5 1]

def cycle0435 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 3, 2, 4, 5]), .triangle 5 1]

def cycle0436 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0 (![0, 3, 2, 4, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 0, .triangle 15 0, .triangle 11 1, .triangle 0 0]

def cycle0437 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .triangle 0 0]

def cycle0438 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 0, .triangle 15 0, .triangle 11 1, .triangle 0 0]

def cycle0439 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-2), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 4 0, .gapLower 2 0 (![3, 0, 1, 5, 4]), .thetaLower 2, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 5 1]

def cycle0440 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 2 1 (![3, 0, 1, 5, 4]), .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 5 1]

def cycle0441 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 2 2 (![3, 0, 1, 5, 4]), .triangle 0 1]

def cycle0442 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 2, .gapLower 2 3 (![3, 0, 1, 5, 4]), .triangle 0 0]

def cycle0443 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 2, 5, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![3, 0, 1, 5, 4]), .triangle 12 0, .triangle 0 0]

def cycle0444 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .gapLower 2 5 (![3, 0, 1, 5, 4]), .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 3, 2, 4, 5])]

def cycle0445 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 2, .gapLower 1 1 (![0, 3, 2, 5, 4])]

def cycle0446 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 2 (![0, 3, 2, 5, 4]), .triangle 1 0]

def cycle0447 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 2, .gapLower 1 3 (![0, 3, 2, 5, 4]), .triangle 0 0]

def cycle0448 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 3, 2, 5, 4]), .triangle 3 0]

def cycle0449 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 2, 5, 4]), .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 3, 2, 4, 5])]

def cycle0450 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0451 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0452 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0453 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 1 (![0, 4, 5, 3, 2])]

def cycle0454 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 2 0]

def cycle0455 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 3 0]

def cycle0456 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 5, 3, 2]), .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 2, 4, 5])]

def cycle0457 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 4, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 2, 4, 5])]

def cycle0458 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 3, 2, 4, 5])]

def cycle0459 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 2 (![1, 3, 2, 4, 5]), .gapLower 0 1 (![1, 3, 2, 4, 5])]

def cycle0460 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![1, 3, 2, 4, 5]), .triangle 4 2, .gapLower 0 1 (![1, 3, 2, 4, 5])]

def cycle0461 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 3, 2, 4, 5]), .triangle 5 1, .triangle 4 2, .gapLower 0 1 (![1, 3, 2, 4, 5])]

def cycle0462 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 3, 2, 4, 5]), .triangle 9 1, .triangle 5 1, .triangle 4 2, .gapLower 0 1 (![1, 3, 2, 4, 5])]

def cycle0463 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![1, 3, 2, 4, 5]), .gapLower 0 2 (![1, 3, 2, 4, 5]), .triangle 1 1]

def cycle0464 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 3, 2, 4, 5]), .triangle 5 1, .gapLower 0 2 (![1, 3, 2, 4, 5]), .triangle 1 1]

def cycle0465 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 2 (![1, 3, 2, 4, 5]), .corridorLower 0 3, .gapLower 0 5 (![1, 3, 2, 4, 5]), .triangle 9 1, .triangle 5 1]

def cycle0466 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 3, 2, 4, 5]), .gapLower 0 3 (![1, 3, 2, 4, 5])]

def cycle0467 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 2, 4, 5]), .triangle 9 1, .gapLower 0 3 (![1, 3, 2, 4, 5])]

def cycle0468 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 2, 4, 5]), .gapLower 0 4 (![1, 3, 2, 4, 5]), .triangle 5 1]

def cycle0469 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0470 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0471 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 4 2, .gapLower 0 1 (![1, 3, 2, 5, 4])]

def cycle0472 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![1, 3, 2, 5, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0473 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (0), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![1, 3, 2, 5, 4])]

def cycle0474 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .distance 1 4, .distance 0 4]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 2, 5, 4]), .triangle 9 1, .corridorLower 4 5, .corridorUpper 1 4, .triangle 2 2]

def cycle0475 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4]
    constant := ![(-1), (-1), (0), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 2, 5, 4])]

def cycle0476 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 4 2, .gapLower 0 1 (![1, 3, 2, 5, 4])]

def cycle0477 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 2 (![1, 3, 2, 5, 4]), .triangle 1 1]

def cycle0478 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-2), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 4 0, .gapLower 2 0 (![3, 0, 1, 5, 4]), .gapLower 2 5 (![3, 0, 1, 5, 4]), .triangle 11 2, .triangle 15 2, .triangle 3 2, .gapLower 0 3 (![1, 3, 2, 5, 4])]

def cycle0479 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (-1), (4), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 1 (![3, 0, 1, 5, 4]), .corridorLower 2 3, .gapLower 2 5 (![3, 0, 1, 5, 4]), .triangle 11 2, .triangle 15 2, .triangle 3 2, .gapLower 0 3 (![1, 3, 2, 5, 4])]

def cycle0480 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 2 2 (![3, 0, 1, 5, 4]), .triangle 0 1]

def cycle0481 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 2, .gapLower 2 3 (![3, 0, 1, 5, 4]), .triangle 0 0]

def cycle0482 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 2, 5, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![3, 0, 1, 5, 4]), .triangle 12 2, .triangle 3 2, .gapLower 0 3 (![1, 3, 2, 5, 4]), .triangle 0 1]

def cycle0483 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .gapLower 2 5 (![3, 0, 1, 5, 4]), .triangle 5 2, .triangle 9 2, .gapLower 0 3 (![1, 3, 2, 5, 4])]

def cycle0484 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 2, .gapLower 1 1 (![0, 3, 2, 5, 4])]

def cycle0485 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 2 (![0, 3, 2, 5, 4]), .triangle 1 0]

def cycle0486 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 2, .gapLower 1 3 (![0, 3, 2, 5, 4]), .triangle 0 0]

def cycle0487 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 3, 2, 5, 4]), .triangle 3 2, .gapLower 0 3 (![1, 3, 2, 5, 4]), .triangle 0 1]

def cycle0488 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 2, 5, 4]), .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![1, 3, 2, 5, 4])]

def cycle0489 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .gapLower 5 2 (![4, 0, 2, 1, 3]), .gapLower 0 3 (![1, 3, 2, 5, 4]), .triangle 0 1]

def cycle0490 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 0, .triangle 5 2, .triangle 9 2, .gapLower 0 3 (![1, 3, 2, 5, 4])]

def cycle0491 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 2, .gapLower 0 3 (![1, 3, 2, 5, 4]), .triangle 0 1]

def cycle0492 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .triangle 9 2, .gapLower 0 3 (![1, 3, 2, 5, 4])]

def cycle0493 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-2), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 4 0, .gapLower 2 0 (![3, 0, 1, 5, 4]), .thetaLower 2, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![1, 3, 2, 5, 4]), .triangle 6 1]

def cycle0494 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 2 1 (![3, 0, 1, 5, 4]), .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![1, 3, 2, 5, 4]), .triangle 6 1]

def cycle0495 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .gapLower 2 5 (![3, 0, 1, 5, 4]), .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![1, 3, 2, 5, 4]), .triangle 6 1]

def cycle0496 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 3, 2, 5, 4]), .triangle 3 0]

def cycle0497 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 2, 5, 4]), .triangle 2 2, .gapLower 0 4 (![1, 3, 2, 5, 4]), .triangle 6 1]

def cycle0498 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0499 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![1, 3, 2, 5, 4]), .triangle 6 1]

def cycle0500 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0501 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![1, 3, 2, 5, 4]), .triangle 6 1]

def cycle0502 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .gapLower 0 5 (![1, 3, 2, 5, 4]), .triangle 9 0, .triangle 15 0, .gapLower 1 3 (![0, 3, 2, 4, 5]), .triangle 0 0]

def cycle0503 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .gapLower 0 5 (![1, 3, 2, 5, 4]), .triangle 9 0, .triangle 18 0, .gapLower 2 3 (![3, 0, 1, 4, 5]), .triangle 0 0]

def cycle0504 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-2), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 4 0, .gapLower 2 0 (![3, 0, 1, 5, 4]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 2, 5, 4]), .triangle 5 1]

def cycle0505 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.gapLower 2 1 (![3, 0, 1, 5, 4]), .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 2, 5, 4]), .triangle 5 1]

def cycle0506 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 2, 5, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 0, 1, 5, 4]), .triangle 11 0, .triangle 0 0]

def cycle0507 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-2), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .gapLower 0 5 (![1, 3, 2, 5, 4]), .triangle 5 1, .triangle 4 0, .gapLower 2 0 (![3, 0, 1, 5, 4]), .thetaOrder 1, .gapLower 1 5 (![0, 3, 2, 5, 4]), .triangle 2 0]

def cycle0508 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (0), (-2), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .gapLower 0 5 (![1, 3, 2, 5, 4]), .triangle 5 1, .gapLower 2 1 (![3, 0, 1, 5, 4]), .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 2, 5, 4]), .triangle 2 0]

def cycle0509 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 2, 5, 4]), .triangle 11 1, .gapLower 2 2 (![3, 0, 1, 5, 4])]

def cycle0510 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![3, 0, 1, 5, 4]), .triangle 12 0, .triangle 0 0]

def cycle0511 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 0, 1, 5, 4]), .triangle 11 0, .triangle 0 0]

def cycle0512 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .gapLower 0 5 (![1, 3, 2, 5, 4]), .triangle 9 0, .triangle 15 0, .triangle 2 0]

def cycle0513 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0514 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0515 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 0]

def cycle0516 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 2, 5, 4])]

def cycle0517 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 2, 5, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 2, 5, 4])]

def cycle0518 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 2 (![1, 3, 2, 5, 4]), .gapLower 0 1 (![1, 3, 2, 5, 4])]

def cycle0519 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![1, 3, 2, 5, 4]), .triangle 4 2, .gapLower 0 1 (![1, 3, 2, 5, 4])]

def cycle0520 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 3, 2, 5, 4]), .triangle 6 1, .triangle 4 2, .gapLower 0 1 (![1, 3, 2, 5, 4])]

def cycle0521 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 3, 2, 5, 4]), .triangle 5 1, .triangle 4 2, .gapLower 0 1 (![1, 3, 2, 5, 4])]

def cycle0522 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![1, 3, 2, 5, 4]), .gapLower 0 2 (![1, 3, 2, 5, 4]), .triangle 1 1]

def cycle0523 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 3, 2, 5, 4]), .triangle 6 1, .gapLower 0 2 (![1, 3, 2, 5, 4]), .triangle 1 1]

def cycle0524 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 2 (![1, 3, 2, 5, 4]), .corridorLower 0 3, .gapLower 0 5 (![1, 3, 2, 5, 4]), .triangle 5 1]

def cycle0525 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 3, 2, 5, 4]), .gapLower 0 3 (![1, 3, 2, 5, 4])]

def cycle0526 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 2, 5, 4]), .triangle 9 2, .gapLower 0 3 (![1, 3, 2, 5, 4])]

def cycle0527 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 2, 5, 4]), .gapLower 0 4 (![1, 3, 2, 5, 4]), .triangle 6 1]

def cycle0528 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0529 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0530 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 6 2, .triangle 8 1, .gapLower 0 1 (![1, 3, 5, 2, 4])]

def cycle0531 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 2 (![1, 3, 5, 2, 4]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0532 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![1, 3, 5, 2, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0533 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 3, 5, 2, 4])]

def cycle0534 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 5, 2, 4]), .triangle 5 1]

def cycle0535 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 6 2, .triangle 8 1, .gapLower 0 1 (![1, 3, 5, 2, 4])]

def cycle0536 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 6 2, .gapLower 0 2 (![1, 3, 5, 2, 4]), .triangle 1 1]

def cycle0537 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![1, 3, 5, 2, 4]), .triangle 3 1]

def cycle0538 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 6 0, .triangle 17 1, .gapLower 2 0 (![3, 5, 0, 1, 4]), .gapLower 2 5 (![3, 5, 0, 1, 4]), .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![1, 3, 5, 2, 4])]

def cycle0539 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 2 2 (![3, 5, 0, 1, 4]), .gapLower 2 1 (![3, 5, 0, 1, 4]), .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![1, 3, 5, 2, 4])]

def cycle0540 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2 (![3, 5, 0, 1, 4]), .corridorLower 2 5, .gapLower 2 5 (![3, 5, 0, 1, 4]), .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![1, 3, 5, 2, 4])]

def cycle0541 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 2 3 (![3, 5, 0, 1, 4]), .triangle 6 2, .triangle 8 1, .gapLower 0 1 (![1, 3, 5, 2, 4])]

def cycle0542 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![3, 5, 0, 1, 4]), .triangle 0 0]

def cycle0543 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (-1), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 6 0, .triangle 17 1, .corridorLower 2 3, .gapLower 2 5 (![3, 5, 0, 1, 4]), .triangle 5 2, .gapLower 0 4 (![1, 3, 5, 2, 4])]

def cycle0544 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 5, .distance 0 3]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 4 1, .triangle 17 0, .triangle 8 0]

def cycle0545 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 2, .triangle 14 1, .gapLower 1 1 (![0, 3, 5, 2, 4])]

def cycle0546 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 2, .gapLower 1 2 (![0, 3, 5, 2, 4]), .triangle 1 0]

def cycle0547 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 3 (![0, 3, 5, 2, 4]), .triangle 3 0]

def cycle0548 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 3, 5, 2, 4]), .triangle 0 0]

def cycle0549 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 5, 2, 4]), .triangle 2 2, .gapLower 0 4 (![1, 3, 5, 2, 4])]

def cycle0550 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![1, 3, 5, 2, 4])]

def cycle0551 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0552 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![1, 3, 5, 2, 4])]

def cycle0553 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (-2), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.triangle 6 0, .triangle 17 1, .gapLower 2 0 (![3, 5, 0, 1, 4]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 5, 2, 4]), .triangle 5 1]

def cycle0554 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-2), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 6 0, .gapLower 2 1 (![3, 5, 0, 1, 4]), .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 5, 2, 4]), .triangle 5 1]

def cycle0555 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.gapLower 2 2 (![3, 5, 0, 1, 4]), .triangle 17 1, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 5, 2, 4]), .triangle 5 1]

def cycle0556 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 0, 1, 4]), .triangle 11 0, .triangle 12 2, .triangle 14 1, .triangle 1 0]

def cycle0557 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (0), (-2), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .gapLower 0 5 (![1, 3, 5, 2, 4]), .triangle 5 1, .triangle 6 0, .triangle 17 1, .gapLower 2 0 (![3, 5, 0, 1, 4]), .thetaOrder 1, .gapLower 1 5 (![0, 3, 5, 2, 4]), .triangle 2 0]

def cycle0558 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-2), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .gapLower 0 5 (![1, 3, 5, 2, 4]), .triangle 5 1, .triangle 6 0, .gapLower 2 1 (![3, 5, 0, 1, 4]), .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 5, 2, 4]), .triangle 2 0]

def cycle0559 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (0), (-2), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .gapLower 0 5 (![1, 3, 5, 2, 4]), .triangle 5 1, .gapLower 2 2 (![3, 5, 0, 1, 4]), .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![0, 3, 5, 2, 4]), .triangle 2 0]

def cycle0560 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.triangle 6 0, .triangle 17 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 5, 2, 4]), .triangle 11 1, .gapLower 2 3 (![3, 5, 0, 1, 4])]

def cycle0561 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 6 0, .corridorLower 2 5, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0]

def cycle0562 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0563 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0564 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (-1), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 17 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0]

def cycle0565 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 1 (![0, 4, 5, 3, 2])]

def cycle0566 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 2 0]

def cycle0567 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 3 0]

def cycle0568 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 5, 3, 2]), .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 2, 4])]

def cycle0569 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 2, 4])]

def cycle0570 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0571 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 0]

def cycle0572 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 2, 4])]

def cycle0573 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 2, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 2, 4])]

def cycle0574 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 6 2, .gapLower 0 2 (![1, 3, 5, 2, 4]), .gapLower 0 1 (![1, 3, 5, 2, 4])]

def cycle0575 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![1, 3, 5, 2, 4]), .triangle 8 1, .gapLower 0 1 (![1, 3, 5, 2, 4])]

def cycle0576 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 3, 5, 2, 4]), .triangle 6 2, .triangle 8 1, .gapLower 0 1 (![1, 3, 5, 2, 4])]

def cycle0577 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 3, 5, 2, 4]), .triangle 5 1, .triangle 6 2, .triangle 8 1, .gapLower 0 1 (![1, 3, 5, 2, 4])]

def cycle0578 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![1, 3, 5, 2, 4]), .gapLower 0 2 (![1, 3, 5, 2, 4]), .triangle 1 1]

def cycle0579 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 3, 5, 2, 4]), .triangle 6 2, .gapLower 0 2 (![1, 3, 5, 2, 4]), .triangle 1 1]

def cycle0580 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 2 (![1, 3, 5, 2, 4]), .corridorLower 0 3, .gapLower 0 5 (![1, 3, 5, 2, 4]), .triangle 5 1]

def cycle0581 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 3, 5, 2, 4]), .gapLower 0 3 (![1, 3, 5, 2, 4]), .triangle 8 1, .triangle 1 1]

def cycle0582 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 3 (![1, 3, 5, 2, 4]), .corridorLower 0 5, .gapLower 0 5 (![1, 3, 5, 2, 4]), .triangle 5 1]

def cycle0583 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 5, 2, 4]), .gapLower 0 4 (![1, 3, 5, 2, 4])]

def cycle0584 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0585 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0586 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0587 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 2 (![1, 3, 4, 2, 5]), .corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0588 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![1, 3, 4, 2, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0589 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 3, 4, 2, 5])]

def cycle0590 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 2, 5]), .triangle 6 1]

def cycle0591 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0592 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .triangle 5 2, .gapLower 0 2 (![1, 3, 4, 2, 5]), .triangle 1 1]

def cycle0593 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![1, 3, 4, 2, 5]), .triangle 2 1]

def cycle0594 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (-2), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .gapLower 2 0 (![3, 4, 0, 1, 5]), .gapLower 2 5 (![3, 4, 0, 1, 5]), .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![1, 3, 4, 2, 5])]

def cycle0595 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (-2), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 2 2 (![3, 4, 0, 1, 5]), .gapLower 2 1 (![3, 4, 0, 1, 5]), .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![1, 3, 4, 2, 5])]

def cycle0596 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (-1), (4), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2 (![3, 4, 0, 1, 5]), .corridorLower 2 4, .gapLower 2 5 (![3, 4, 0, 1, 5]), .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![1, 3, 4, 2, 5])]

def cycle0597 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .gapLower 2 3 (![3, 4, 0, 1, 5]), .triangle 5 2, .triangle 7 1, .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0598 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .gapLower 2 4 (![3, 4, 0, 1, 5]), .triangle 0 0]

def cycle0599 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (-1), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .corridorLower 2 3, .gapLower 2 5 (![3, 4, 0, 1, 5]), .triangle 6 2, .gapLower 0 4 (![1, 3, 4, 2, 5])]

def cycle0600 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 4 1, .triangle 16 0, .triangle 7 0]

def cycle0601 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 1 (![0, 3, 4, 2, 5])]

def cycle0602 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 11 2, .gapLower 1 2 (![0, 3, 4, 2, 5]), .triangle 1 0]

def cycle0603 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .gapLower 1 3 (![0, 3, 4, 2, 5]), .triangle 2 0]

def cycle0604 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![0, 3, 4, 2, 5]), .triangle 0 0]

def cycle0605 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 2, 5]), .triangle 3 2, .gapLower 0 4 (![1, 3, 4, 2, 5])]

def cycle0606 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![1, 3, 4, 2, 5])]

def cycle0607 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 3, 4, 2, 5])]

def cycle0608 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 3, 4, 2, 5]), .triangle 5 2, .triangle 7 1, .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0609 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0610 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 3, 4, 2, 5])]

def cycle0611 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 3, 4, 2, 5])]

def cycle0612 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (-2), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.triangle 5 0, .triangle 16 1, .gapLower 2 0 (![3, 4, 0, 1, 5]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 2, 5]), .triangle 6 1]

def cycle0613 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-2), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 5 0, .gapLower 2 1 (![3, 4, 0, 1, 5]), .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 2, 5]), .triangle 6 1]

def cycle0614 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.gapLower 2 2 (![3, 4, 0, 1, 5]), .triangle 16 1, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 2, 5]), .triangle 6 1]

def cycle0615 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 0, 1, 5]), .triangle 12 0, .triangle 0 0]

def cycle0616 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (0), (-2), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .gapLower 0 5 (![1, 3, 4, 2, 5]), .triangle 6 1, .triangle 5 0, .triangle 16 1, .gapLower 2 0 (![3, 4, 0, 1, 5]), .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 2, 5]), .triangle 3 0]

def cycle0617 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-2), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .gapLower 0 5 (![1, 3, 4, 2, 5]), .triangle 6 1, .triangle 5 0, .gapLower 2 1 (![3, 4, 0, 1, 5]), .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 2, 5]), .triangle 3 0]

def cycle0618 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (0), (-2), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .gapLower 0 5 (![1, 3, 4, 2, 5]), .triangle 6 1, .gapLower 2 2 (![3, 4, 0, 1, 5]), .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 2, 5]), .triangle 3 0]

def cycle0619 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 2, 5]), .triangle 12 1, .gapLower 2 3 (![3, 4, 0, 1, 5])]

def cycle0620 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![(-1), (-1), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 12 0, .triangle 6 0]

def cycle0621 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 11 2, .triangle 15 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0622 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (-1), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 12 0, .triangle 6 0]

def cycle0623 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .gapLower 0 5 (![1, 3, 4, 2, 5]), .gapLower 0 4 (![1, 3, 4, 2, 5]), .triangle 4 0, .triangle 16 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0624 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 1 (![0, 3, 5, 4, 2])]

def cycle0625 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0626 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![0, 3, 5, 4, 2]), .triangle 3 0]

def cycle0627 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (3), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .gapLower 0 5 (![1, 3, 4, 2, 5]), .triangle 6 1, .triangle 5 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 5, 4, 2]), .triangle 15 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0628 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 2, 5]), .triangle 1 1]

def cycle0629 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0630 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0631 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 1 (![0, 4, 5, 3, 2])]

def cycle0632 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 2 0]

def cycle0633 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 3 0]

def cycle0634 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 5, 3, 2]), .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0635 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0636 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0637 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0638 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 15 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0639 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 1 0]

def cycle0640 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 2, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 2, 5]), .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0641 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 2, 5]), .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0642 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![1, 3, 4, 2, 5]), .triangle 7 1, .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0643 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 3, 4, 2, 5]), .triangle 5 2, .triangle 7 1, .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0644 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 3, 4, 2, 5]), .triangle 9 1, .triangle 7 1, .gapLower 0 1 (![1, 3, 4, 2, 5])]

def cycle0645 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![1, 3, 4, 2, 5]), .gapLower 0 2 (![1, 3, 4, 2, 5]), .triangle 1 1]

def cycle0646 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 3, 4, 2, 5]), .triangle 5 2, .gapLower 0 2 (![1, 3, 4, 2, 5]), .triangle 1 1]

def cycle0647 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 5 2, .gapLower 0 2 (![1, 3, 4, 2, 5]), .corridorLower 0 3, .gapLower 0 5 (![1, 3, 4, 2, 5]), .triangle 6 1]

def cycle0648 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 3, 4, 2, 5]), .gapLower 0 3 (![1, 3, 4, 2, 5]), .triangle 7 1, .triangle 1 1]

def cycle0649 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 3 (![1, 3, 4, 2, 5]), .corridorLower 0 4, .gapLower 0 5 (![1, 3, 4, 2, 5]), .triangle 6 1]

def cycle0650 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 2, 5]), .gapLower 0 4 (![1, 3, 4, 2, 5])]

def cycle0651 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0652 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0653 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0654 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 5, 2])]

def cycle0655 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 7 1, .triangle 4 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0656 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (0), (0), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 9 1, .triangle 7 1, .triangle 4 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0657 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 5, 2])]

def cycle0658 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0659 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 5, 2]), .triangle 1 1]

def cycle0660 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 5 1, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0661 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 5 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0662 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 6 0, .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def cycle0663 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 13 0, .triangle 1 0]

def cycle0664 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 5 3 (![2, 0, 1, 4, 3]), .triangle 3 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 7 1, .triangle 1 1]

def cycle0665 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 6 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 2 1]

def cycle0666 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 7 1, .triangle 1 1]

def cycle0667 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![(0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 5 1, .triangle 18 0, .triangle 9 2, .gapLower 0 3 (![1, 3, 4, 5, 2])]

def cycle0668 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4]
    constant := ![(0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 5 1, .triangle 16 1, .triangle 17 0, .triangle 8 2, .gapLower 0 3 (![1, 3, 4, 5, 2])]

def cycle0669 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 1 (![0, 3, 4, 5, 2])]

def cycle0670 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![0, 3, 4, 5, 2]), .triangle 1 0]

def cycle0671 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![0, 3, 4, 5, 2]), .triangle 2 0]

def cycle0672 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 3 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 7 1, .triangle 1 1]

def cycle0673 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 7 1, .triangle 1 1]

def cycle0674 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .gapLower 5 2 (![2, 0, 4, 1, 3]), .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 7 1, .triangle 1 1]

def cycle0675 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 7 1, .triangle 1 1]

def cycle0676 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0677 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .gapLower 5 2 (![2, 0, 3, 1, 4]), .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 7 1, .triangle 1 1]

def cycle0678 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 7 1, .triangle 1 1]

def cycle0679 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 6 1, .triangle 17 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0680 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0681 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 6 0, .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0682 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 15 0, .triangle 13 1, .triangle 1 0]

def cycle0683 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 3 1]

def cycle0684 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 9 1, .triangle 7 1, .triangle 1 1]

def cycle0685 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 3 0]

def cycle0686 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 0 2, .gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 9 1, .triangle 7 1, .triangle 1 1]

def cycle0687 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 11 2, .triangle 15 0, .triangle 18 0, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .gapLower 2 5 (![3, 4, 5, 0, 1])]

def cycle0688 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 4, 5, 2]), .gapLower 5 1 (![2, 0, 4, 1, 3]), .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0689 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (-1), (0), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 11 2, .triangle 15 0, .triangle 18 0, .gapLower 2 1 (![3, 4, 5, 0, 1]), .gapLower 3 0 (![2, 0, 1, 5, 4]), .thetaOrder 2, .corridorUpper 1 2]

def cycle0690 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 8 1, .gapLower 3 1 (![2, 0, 1, 5, 4]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0691 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 3 2 (![2, 0, 1, 5, 4]), .triangle 1 1]

def cycle0692 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 3 3 (![2, 0, 1, 5, 4]), .triangle 1 0]

def cycle0693 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![2, 0, 1, 5, 4]), .triangle 14 0, .triangle 1 0]

def cycle0694 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![2, 0, 1, 5, 4]), .triangle 13 0, .triangle 1 0]

def cycle0695 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 3 1]

def cycle0696 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 1 (![0, 3, 5, 4, 2])]

def cycle0697 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0698 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![0, 3, 5, 4, 2]), .triangle 3 0]

def cycle0699 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4]
    constant := ![(0), (-1), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 5 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 5, 4, 2]), .triangle 15 0, .triangle 9 0]

def cycle0700 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 0 2, .gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 9 1, .triangle 7 1, .triangle 1 1]

def cycle0701 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0702 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (-1), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 0, .triangle 16 0, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2]

def cycle0703 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 4, 5, 2]), .gapLower 5 1 (![2, 0, 3, 1, 4]), .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0704 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 4, 5, 2]), .gapLower 5 1 (![2, 0, 3, 1, 4]), .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0705 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (0), (-1), (-2), (0), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 19 1, .triangle 16 0, .gapLower 3 0 (![2, 0, 4, 5, 1]), .thetaOrder 2, .corridorUpper 1 2]

def cycle0706 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3]
    constant := ![(-2), (-1), (3), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 3 1 (![2, 0, 4, 5, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 19 1, .gapLower 3 2 (![2, 0, 4, 5, 1])]

def cycle0707 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (4), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 2, .triangle 14 0, .triangle 19 1, .gapLower 3 2 (![2, 0, 4, 5, 1]), .triangle 1 1]

def cycle0708 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (4), (0), (-1), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 2, .triangle 14 0, .gapLower 3 3 (![2, 0, 4, 5, 1]), .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0709 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (4), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 2, .gapLower 3 4 (![2, 0, 4, 5, 1]), .triangle 8 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0710 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![2, 0, 4, 5, 1]), .triangle 14 0, .triangle 19 1, .triangle 7 0, .triangle 1 1]

def cycle0711 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 1 (![0, 4, 5, 3, 2])]

def cycle0712 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 2 0]

def cycle0713 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 3 0]

def cycle0714 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 5, 3, 2]), .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0715 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 0 2, .gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 9 1, .triangle 7 1, .triangle 1 1]

def cycle0716 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .gapLower 2 1 (![3, 4, 5, 0, 1]), .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2]

def cycle0717 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-1), (-1), (-2), (-1), (4)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .gapLower 2 5 (![3, 4, 5, 0, 1])]

def cycle0718 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 6 1, .gapLower 2 2 (![3, 4, 5, 0, 1]), .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0719 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 19 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0720 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (0), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 19 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0721 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 19 0, .triangle 7 0, .triangle 1 1]

def cycle0722 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 19 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0723 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 9 1, .triangle 7 1, .triangle 1 1]

def cycle0724 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0725 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0726 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 15 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0727 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 1 0]

def cycle0728 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0729 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 4 0, .triangle 10 0, .triangle 0 0]

def cycle0730 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 5 0, .triangle 11 0, .triangle 0 0]

def cycle0731 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (-1), (0), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 6 0, .triangle 12 2, .triangle 14 1, .gapLower 1 1 (![0, 3, 4, 2, 5])]

def cycle0732 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (0), (-2), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 5, 2])]

def cycle0733 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 5, 2])]

def cycle0734 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-1), (-2), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 6 0, .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 5, 2])]

def cycle0735 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-2), (0), (0), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 5, 2])]

def cycle0736 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (0), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1])]

def cycle0737 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 5 0, .triangle 18 0, .triangle 15 0, .gapLower 1 2 (![0, 3, 4, 5, 2]), .triangle 1 0]

def cycle0738 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (2), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 5 0, .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0739 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 4 0, .triangle 16 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0740 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (0), (0), (-2), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 6 0, .triangle 18 1, .triangle 16 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 0 0]

def cycle0741 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (0), (-2), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 6 0, .triangle 18 1, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 0 0]

def cycle0742 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-2), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 6 0, .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 0 0]

def cycle0743 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (0), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.gapLower 2 3 (![3, 4, 5, 0, 1]), .corridorLower 2 5, .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .gapLower 2 4 (![3, 4, 5, 0, 1])]

def cycle0744 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (0), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.triangle 6 0, .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .gapLower 2 4 (![3, 4, 5, 0, 1])]

def cycle0745 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 13 0, .triangle 1 0]

def cycle0746 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 15 0, .triangle 13 1, .triangle 1 0]

def cycle0747 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (-1), (0), (-2), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 11 2, .triangle 15 0, .triangle 18 0, .gapLower 2 1 (![3, 4, 5, 0, 1]), .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2]

def cycle0748 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 5, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (2), (-2), (-1), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .corridorLower 2 5, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 5, 2]), .triangle 1 1]

def cycle0749 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 5, 2]), .triangle 1 1]

def cycle0750 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 5 0, .triangle 18 0, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 5, 2]), .triangle 1 1]

def cycle0751 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 5, 2]), .triangle 1 1]

def cycle0752 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 2, .distance 2 5, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (2), (-2), (-1), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .corridorLower 2 5, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0753 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0754 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 5 0, .triangle 18 0, .triangle 15 0, .gapLower 1 1 (![0, 4, 5, 3, 2])]

def cycle0755 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 4 0, .triangle 16 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0756 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0757 : Cycle where
  length := 14
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (2), (-2), (0), (0), (-1), (3), (0), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 5, 2]), .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0758 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaLower 1, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 5, 2]), .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0759 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 4 0, .triangle 16 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0760 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (0), (-2), (-1), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0761 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (-2), (0), (0), (-1), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .gapLower 0 5 (![1, 3, 4, 5, 2]), .gapLower 2 3 (![3, 4, 5, 0, 1]), .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0762 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 4, 5, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 5, 2]), .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0763 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![1, 3, 4, 5, 2]), .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0764 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 7 1, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0765 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 9 1, .triangle 7 1, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0766 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 3, 4, 5, 2]), .triangle 6 2, .triangle 9 1, .triangle 7 1, .gapLower 0 1 (![1, 3, 4, 5, 2])]

def cycle0767 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .gapLower 0 2 (![1, 3, 4, 5, 2]), .triangle 4 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0768 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 4, 5, 2]), .triangle 9 1, .gapLower 0 2 (![1, 3, 4, 5, 2]), .triangle 4 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0769 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 6 2, .triangle 9 1, .gapLower 0 2 (![1, 3, 4, 5, 2]), .corridorLower 0 3, .gapLower 0 5 (![1, 3, 4, 5, 2])]

def cycle0770 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-2), (0), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 4, 5, 2]), .gapLower 0 3 (![1, 3, 4, 5, 2]), .triangle 7 1, .triangle 4 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0771 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 1]
    strict := ![true, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 0 3 (![1, 3, 4, 5, 2]), .corridorLower 0 4, .gapLower 0 5 (![1, 3, 4, 5, 2])]

def cycle0772 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 5, .theta 0, .distance 0 2]
    constant := ![(-2), (-1), (2)]
    coefficient := ![0, 0, 1]
    strict := ![false, false, false] }
  origin := ![.gapLower 0 4 (![1, 3, 4, 5, 2]), .corridorLower 0 5, .gapLower 0 5 (![1, 3, 4, 5, 2])]

def cycle0773 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0774 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 1 1]

def cycle0775 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0776 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 4 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0777 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .distance 1 4, .distance 0 4]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 3 (![1, 3, 5, 4, 2]), .triangle 9 1, .corridorLower 4 5, .corridorUpper 1 4, .triangle 2 2]

def cycle0778 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 5, 4, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0779 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, true, true, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 5, 4, 2])]

def cycle0780 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0781 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 18 2, .triangle 6 0]

def cycle0782 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-2), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 4 1, .gapLower 2 0 (![3, 4, 5, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0783 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-2), (-1), (4), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 18 0, .gapLower 2 1 (![3, 4, 5, 0, 1]), .corridorLower 2 3, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2]

def cycle0784 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 18 2, .gapLower 2 2 (![3, 4, 5, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def cycle0785 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-2), (0), (-2), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .gapLower 3 1 (![2, 0, 1, 5, 4]), .gapLower 3 0 (![2, 0, 1, 5, 4]), .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0786 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-2), (-2), (-1), (4), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .gapLower 3 1 (![2, 0, 1, 5, 4]), .corridorLower 2 3, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2]

def cycle0787 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 3 2 (![2, 0, 1, 5, 4]), .triangle 1 1]

def cycle0788 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 3 3 (![2, 0, 1, 5, 4]), .triangle 1 0]

def cycle0789 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![2, 0, 1, 5, 4]), .gapLower 5 4 (![2, 4, 0, 1, 3]), .triangle 3 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 1 1]

def cycle0790 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![2, 0, 1, 5, 4]), .triangle 13 2, .triangle 2 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 1 1]

def cycle0791 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 4, 5, 0, 1]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 1 1]

def cycle0792 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 4, 5, 0, 1]), .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 1 1]

def cycle0793 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-2), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 4 1, .gapLower 2 0 (![3, 5, 4, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0794 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 5 0, .triangle 18 2, .gapLower 2 1 (![3, 5, 4, 0, 1]), .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0795 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 5, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 5 0, .gapLower 2 2 (![3, 5, 4, 0, 1]), .corridorLower 2 5, .corridorUpper 1 2, .triangle 0 2]

def cycle0796 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 2 3 (![3, 5, 4, 0, 1]), .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0797 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 5, 4, 0, 1]), .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 1 1]

def cycle0798 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 1 1]

def cycle0799 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 3]
    constant := ![(0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false] }
  origin := ![.triangle 4 1, .triangle 17 0, .gapLower 5 3 (![4, 0, 1, 3, 2]), .triangle 3 2, .gapLower 0 2 (![1, 3, 5, 4, 2])]

def cycle0800 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false] }
  origin := ![.triangle 4 1, .triangle 16 0, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2])]

def cycle0801 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 1 (![0, 3, 5, 4, 2])]

def cycle0802 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0803 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![0, 3, 5, 4, 2]), .triangle 3 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 1 1]

def cycle0804 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 5, 4, 2]), .triangle 2 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 1 1]

def cycle0805 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 1 1]

def cycle0806 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 1 1]

def cycle0807 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 1 1]

def cycle0808 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false, true] }
  origin := ![.triangle 5 2, .gapLower 0 3 (![1, 3, 5, 4, 2]), .gapLower 5 2 (![2, 4, 0, 1, 3]), .triangle 18 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0809 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, true] }
  origin := ![.triangle 5 2, .gapLower 0 3 (![1, 3, 5, 4, 2]), .triangle 8 1, .triangle 4 1, .gapLower 2 0 (![3, 5, 4, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle0810 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![3, 5, 4, 0, 1]), .triangle 5 2, .gapLower 0 3 (![1, 3, 5, 4, 2]), .triangle 3 1]

def cycle0811 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![3, 5, 4, 0, 1]), .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![1, 3, 5, 4, 2]), .triangle 8 1, .triangle 1 1]

def cycle0812 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.triangle 4 1, .triangle 16 0, .triangle 7 2, .gapLower 0 3 (![1, 3, 5, 4, 2]), .triangle 8 1]

def cycle0813 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![0, 3, 5, 4, 2]), .triangle 3 0]

def cycle0814 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 5, 4, 2]), .triangle 2 2, .gapLower 0 3 (![1, 3, 5, 4, 2]), .triangle 8 1, .triangle 1 1]

def cycle0815 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![1, 3, 5, 4, 2]), .triangle 8 1, .triangle 1 1]

def cycle0816 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .triangle 1 1]

def cycle0817 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 3 (![1, 3, 5, 4, 2]), .triangle 8 1, .triangle 1 1]

def cycle0818 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 5, 4, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0819 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .gapLower 0 5 (![1, 3, 5, 4, 2]), .triangle 4 0, .triangle 10 0, .triangle 0 0]

def cycle0820 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .gapLower 0 5 (![1, 3, 5, 4, 2]), .triangle 5 0, .triangle 11 0, .triangle 0 0]

def cycle0821 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 18 0, .triangle 16 1, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 5, 4, 2])]

def cycle0822 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (3), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .gapLower 0 5 (![1, 3, 5, 4, 2]), .triangle 5 0, .triangle 18 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0823 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (0), (0), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .gapLower 0 5 (![1, 3, 5, 4, 2]), .gapLower 2 3 (![5, 3, 4, 0, 1]), .triangle 16 1, .triangle 17 0, .gapLower 5 3 (![4, 0, 1, 3, 2]), .triangle 3 0]

def cycle0824 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .gapLower 0 5 (![1, 3, 5, 4, 2]), .triangle 4 0, .triangle 16 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0825 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 5, 4, 2]), .triangle 2 0]

def cycle0826 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .gapLower 0 5 (![1, 3, 5, 4, 2]), .triangle 5 2, .triangle 9 0, .triangle 18 0, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 0 0]

def cycle0827 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (2), (0), (-1), (-1), (0), (-1), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 3, 5, 4, 2]), .triangle 5 2, .triangle 9 0, .triangle 18 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0828 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (2), (-1), (-1), (-1), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 3, 5, 4, 2]), .triangle 5 0, .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0829 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 3, 5, 4, 2]), .triangle 4 0, .triangle 16 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0830 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (0), (-1), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .gapLower 0 5 (![1, 3, 5, 4, 2]), .triangle 5 2, .triangle 9 0, .triangle 18 0, .triangle 16 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0831 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .gapLower 0 5 (![1, 3, 5, 4, 2]), .triangle 5 0, .triangle 18 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 1 3, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0832 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0833 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 0]

def cycle0834 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0835 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 3, 5, 4, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0836 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0837 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![1, 3, 5, 4, 2]), .triangle 8 1, .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0838 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![1, 3, 5, 4, 2]), .triangle 7 1, .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0839 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 3, 5, 4, 2]), .triangle 5 2, .triangle 7 1, .gapLower 0 1 (![1, 3, 5, 4, 2])]

def cycle0840 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, true] }
  origin := ![.triangle 5 2, .gapLower 0 3 (![1, 3, 5, 4, 2]), .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 4 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0841 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 5, 4, 2]), .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .triangle 4 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle0842 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 2, .gapLower 0 2 (![1, 3, 5, 4, 2]), .corridorLower 0 3, .gapLower 0 5 (![1, 3, 5, 4, 2])]

def cycle0843 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-2), (0), (-1), (0), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 3, 5, 4, 2]), .gapLower 0 3 (![1, 3, 5, 4, 2]), .triangle 9 1, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0844 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .distance 0 2]
    constant := ![(0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 1]
    strict := ![true, false, false, false] }
  origin := ![.triangle 5 2, .gapLower 0 3 (![1, 3, 5, 4, 2]), .corridorLower 0 5, .gapLower 0 5 (![1, 3, 5, 4, 2])]

def cycle0845 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 4 (![1, 3, 5, 4, 2]), .triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 3, 5, 4, 2])]

def cycle0846 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0847 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 2, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 8 2, .triangle 3 1]

def cycle0848 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 4 2, .triangle 8 2, .gapLower 0 1 (![1, 5, 3, 2, 4])]

def cycle0849 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 2 (![1, 5, 3, 2, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0850 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![1, 5, 3, 2, 4]), .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0851 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 5, 3, 2, 4])]

def cycle0852 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, true, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 3, 2, 4]), .triangle 5 1]

def cycle0853 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 4 2, .triangle 8 2, .gapLower 0 1 (![1, 5, 3, 2, 4])]

def cycle0854 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .triangle 4 2, .gapLower 0 2 (![1, 5, 3, 2, 4]), .triangle 3 1]

def cycle0855 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![1, 5, 3, 2, 4]), .triangle 1 1]

def cycle0856 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![1, 5, 3, 2, 4])]

def cycle0857 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 4 0, .triangle 17 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 2 2, .gapLower 0 4 (![1, 5, 3, 2, 4])]

def cycle0858 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 2, .triangle 14 2, .gapLower 1 1 (![0, 5, 3, 2, 4])]

def cycle0859 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 2, .gapLower 1 2 (![0, 5, 3, 2, 4]), .triangle 3 0]

def cycle0860 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 3 (![0, 5, 3, 2, 4]), .triangle 1 0]

def cycle0861 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 2, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 5, 3, 2, 4]), .triangle 0 0]

def cycle0862 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 5, 3, 2, 4]), .triangle 2 2, .gapLower 0 4 (![1, 5, 3, 2, 4])]

def cycle0863 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![1, 5, 3, 2, 4])]

def cycle0864 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 4 2, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![1, 5, 3, 2, 4])]

def cycle0865 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 3, 2, 4]), .triangle 5 1]

def cycle0866 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, true, false, true] }
  origin := ![.triangle 4 0, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 3, 2, 4]), .triangle 5 1]

def cycle0867 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 2, 4]), .gapLower 0 5 (![1, 5, 3, 2, 4]), .triangle 7 1, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 5, 3, 2, 4]), .triangle 2 0]

def cycle0868 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (-1), (0), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 2, 4]), .gapLower 0 5 (![1, 5, 3, 2, 4]), .triangle 5 1, .triangle 4 0, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![0, 5, 3, 2, 4]), .triangle 2 0]

def cycle0869 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3 (![1, 5, 3, 2, 4]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 0]

def cycle0870 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![1, 5, 3, 2, 4]), .gapLower 0 1 (![1, 5, 3, 2, 4])]

def cycle0871 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![1, 5, 3, 2, 4]), .triangle 8 2, .gapLower 0 1 (![1, 5, 3, 2, 4])]

def cycle0872 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 5, 3, 2, 4]), .triangle 4 2, .triangle 8 2, .gapLower 0 1 (![1, 5, 3, 2, 4])]

def cycle0873 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 5, 3, 2, 4]), .triangle 5 1, .triangle 4 2, .triangle 8 2, .gapLower 0 1 (![1, 5, 3, 2, 4])]

def cycle0874 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0, .gapLower 0 3 (![1, 5, 3, 2, 4]), .gapLower 0 2 (![1, 5, 3, 2, 4]), .triangle 3 1]

def cycle0875 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 5, 3, 2, 4]), .triangle 4 2, .gapLower 0 2 (![1, 5, 3, 2, 4]), .triangle 3 1]

def cycle0876 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 2 (![1, 5, 3, 2, 4]), .corridorLower 0 5, .gapLower 0 5 (![1, 5, 3, 2, 4]), .triangle 5 1]

def cycle0877 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![1, 5, 3, 2, 4]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaLower 2, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 5, 3, 2, 4])]

def cycle0878 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 2 4, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![1, 5, 3, 2, 4]), .triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 2 4, .triangle 5 0]

def cycle0879 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 3, 2, 4]), .gapLower 0 4 (![1, 5, 3, 2, 4])]

def cycle0880 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 1 0]

def cycle0881 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 8 2, .triangle 3 1]

def cycle0882 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 1 (![1, 5, 3, 4, 2])]

def cycle0883 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![1, 5, 3, 4, 2]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0884 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-3), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 5 2, .gapLower 0 3 (![1, 5, 3, 4, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0885 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 5, 3, 4, 2]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0886 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, true, true, false] }
  origin := ![.triangle 5 2, .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 3, 4, 2])]

def cycle0887 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 1 (![1, 5, 3, 4, 2])]

def cycle0888 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![1, 5, 3, 4, 2]), .triangle 3 1]

def cycle0889 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 5 2, .gapLower 0 3 (![1, 5, 3, 4, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0890 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 5, 3, 4, 2]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0891 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .gapLower 0 5 (![1, 5, 3, 4, 2]), .triangle 4 0, .triangle 10 0, .triangle 0 0]

def cycle0892 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (0), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .gapLower 0 5 (![1, 5, 3, 4, 2]), .triangle 5 0, .triangle 11 0, .gapLower 1 3 (![0, 5, 3, 2, 4]), .triangle 14 2, .gapLower 1 1 (![0, 5, 3, 2, 4])]

def cycle0893 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 5 2, .triangle 7 1, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 3, 4, 2])]

def cycle0894 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-1), (0), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.triangle 5 0, .triangle 16 1, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 3, 4, 2])]

def cycle0895 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .gapLower 0 5 (![1, 5, 3, 4, 2]), .triangle 4 0, .triangle 16 0, .triangle 7 0, .triangle 8 2, .gapLower 0 1 (![1, 5, 3, 4, 2])]

def cycle0896 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 2, .gapLower 1 1 (![0, 5, 3, 4, 2])]

def cycle0897 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![0, 5, 3, 4, 2]), .triangle 3 0]

def cycle0898 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![0, 5, 3, 4, 2]), .triangle 1 0]

def cycle0899 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 3, 4, 2]), .triangle 2 0]

def cycle0900 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (0), (0), (-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .gapLower 0 5 (![1, 5, 3, 4, 2]), .triangle 5 2, .triangle 7 1, .triangle 8 0, .triangle 17 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 5, 3, 4, 2]), .triangle 0 0]

def cycle0901 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (0), (-1), (-1), (0), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 5, 3, 4, 2]), .gapLower 0 5 (![1, 5, 3, 4, 2]), .triangle 5 0, .triangle 16 1, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![0, 5, 3, 4, 2]), .triangle 0 0]

def cycle0902 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![1, 5, 3, 4, 2]), .gapLower 0 1 (![1, 5, 3, 4, 2])]

def cycle0903 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 3 (![1, 5, 3, 4, 2]), .triangle 8 2, .gapLower 0 1 (![1, 5, 3, 4, 2])]

def cycle0904 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![1, 5, 3, 4, 2]), .triangle 7 1, .triangle 8 2, .gapLower 0 1 (![1, 5, 3, 4, 2])]

def cycle0905 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 5, 3, 4, 2]), .triangle 5 2, .triangle 7 1, .triangle 8 2, .gapLower 0 1 (![1, 5, 3, 4, 2])]

def cycle0906 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 5 2, .gapLower 0 3 (![1, 5, 3, 4, 2]), .gapLower 0 2 (![1, 5, 3, 4, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0907 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 5, 3, 4, 2]), .triangle 7 1, .gapLower 0 2 (![1, 5, 3, 4, 2]), .triangle 8 1, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0908 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 0 5, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 5 2, .triangle 7 1, .gapLower 0 2 (![1, 5, 3, 4, 2]), .corridorLower 0 5, .gapLower 0 5 (![1, 5, 3, 4, 2])]

def cycle0909 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 5, 3, 4, 2]), .gapLower 0 3 (![1, 5, 3, 4, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0910 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, true, false] }
  origin := ![.triangle 5 2, .gapLower 0 3 (![1, 5, 3, 4, 2]), .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 3, 4, 2])]

def cycle0911 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![1, 5, 3, 4, 2]), .triangle 7 1, .triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 5, 3, 4, 2])]

def cycle0912 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0913 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0914 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .triangle 7 2, .gapLower 0 1 (![1, 4, 3, 2, 5])]

def cycle0915 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(0), (-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 2 (![1, 4, 3, 2, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0916 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![1, 4, 3, 2, 5]), .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0917 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 4, 3, 2, 5])]

def cycle0918 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, true] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 2, 5]), .triangle 8 1]

def cycle0919 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .triangle 7 2, .gapLower 0 1 (![1, 4, 3, 2, 5])]

def cycle0920 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .triangle 4 2, .gapLower 0 2 (![1, 4, 3, 2, 5]), .triangle 2 1]

def cycle0921 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![1, 4, 3, 2, 5]), .triangle 1 1]

def cycle0922 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![1, 4, 3, 2, 5])]

def cycle0923 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (0), (3), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![1, 4, 3, 2, 5])]

def cycle0924 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 2, .gapLower 1 1 (![0, 4, 3, 2, 5])]

def cycle0925 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 10 2, .gapLower 1 2 (![0, 4, 3, 2, 5]), .triangle 2 0]

def cycle0926 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .gapLower 1 3 (![0, 4, 3, 2, 5]), .triangle 1 0]

def cycle0927 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![0, 4, 3, 2, 5]), .triangle 0 0]

def cycle0928 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 4, 3, 2, 5]), .triangle 3 2, .gapLower 0 4 (![1, 4, 3, 2, 5])]

def cycle0929 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![1, 4, 3, 2, 5])]

def cycle0930 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 4, 3, 2, 5])]

def cycle0931 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false, true, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 4, 3, 2, 5])]

def cycle0932 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, true] }
  origin := ![.triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 2, 5]), .triangle 6 1]

def cycle0933 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (2), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, true, false, true] }
  origin := ![.triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 2, 5]), .triangle 6 1]

def cycle0934 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (0), (0), (-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .gapLower 0 5 (![1, 4, 3, 2, 5]), .triangle 6 1, .triangle 4 2, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 4, 3, 2, 5]), .triangle 3 0]

def cycle0935 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (-1), (0), (0), (2), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .gapLower 0 5 (![1, 4, 3, 2, 5]), .triangle 6 1, .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![0, 4, 3, 2, 5]), .triangle 12 1, .triangle 0 0]

def cycle0936 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3 (![1, 4, 3, 2, 5]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 0]

def cycle0937 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (2), (0), (-1), (-1), (-1), (3), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 2, 5]), .triangle 8 1, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 3, 2, 5])]

def cycle0938 : Cycle where
  length := 14
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (2), (0), (-1), (-1), (-1), (0), (3), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 2, 5]), .triangle 6 1, .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 3, 2, 5])]

def cycle0939 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4]
    constant := ![(0), (-1), (-1), (3), (0), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 2 (![2, 3, 0, 5, 1]), .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0]

def cycle0940 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (-1), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .gapLower 0 5 (![1, 4, 3, 2, 5]), .triangle 6 1, .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0941 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0942 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 0]

def cycle0943 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 3, 2, 5])]

def cycle0944 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 2, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 3, 2, 5])]

def cycle0945 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![1, 4, 3, 2, 5]), .gapLower 0 1 (![1, 4, 3, 2, 5])]

def cycle0946 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![1, 4, 3, 2, 5]), .triangle 7 2, .gapLower 0 1 (![1, 4, 3, 2, 5])]

def cycle0947 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 4, 3, 2, 5]), .triangle 4 2, .triangle 7 2, .gapLower 0 1 (![1, 4, 3, 2, 5])]

def cycle0948 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 4, 3, 2, 5]), .triangle 8 1, .triangle 7 2, .gapLower 0 1 (![1, 4, 3, 2, 5])]

def cycle0949 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0, .gapLower 0 3 (![1, 4, 3, 2, 5]), .gapLower 0 2 (![1, 4, 3, 2, 5]), .triangle 2 1]

def cycle0950 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 4, 3, 2, 5]), .triangle 4 2, .gapLower 0 2 (![1, 4, 3, 2, 5]), .triangle 2 1]

def cycle0951 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(0), (-2), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 2 (![1, 4, 3, 2, 5]), .corridorLower 0 4, .gapLower 0 5 (![1, 4, 3, 2, 5]), .triangle 6 1]

def cycle0952 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (0), (3), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3 (![1, 4, 3, 2, 5]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaLower 2, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 4, 3, 2, 5])]

def cycle0953 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 2 5, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![1, 4, 3, 2, 5]), .triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 2 5, .triangle 6 0]

def cycle0954 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-1), (-1), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 2, 5]), .gapLower 0 4 (![1, 4, 3, 2, 5])]

def cycle0955 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0956 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0957 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .triangle 7 2, .gapLower 0 1 (![1, 4, 3, 5, 2])]

def cycle0958 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2 (![1, 4, 3, 5, 2]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0959 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-3), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 3 (![1, 4, 3, 5, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0960 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 4, 3, 5, 2]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0961 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, true, true, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 5, 2])]

def cycle0962 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .triangle 7 2, .gapLower 0 1 (![1, 4, 3, 5, 2])]

def cycle0963 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![1, 4, 3, 5, 2]), .triangle 2 1]

def cycle0964 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 3 (![1, 4, 3, 5, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0965 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 4, 3, 5, 2]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0966 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .gapLower 0 5 (![1, 4, 3, 5, 2]), .triangle 4 0, .triangle 10 0, .triangle 0 0]

def cycle0967 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (-1), (0), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .gapLower 0 5 (![1, 4, 3, 5, 2]), .triangle 6 0, .triangle 12 2, .triangle 15 1, .gapLower 1 1 (![0, 4, 3, 2, 5])]

def cycle0968 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 5, 2])]

def cycle0969 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-1), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 5, 2])]

def cycle0970 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 2, .gapLower 1 1 (![0, 4, 3, 5, 2])]

def cycle0971 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 2 (![0, 4, 3, 5, 2]), .triangle 2 0]

def cycle0972 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![0, 4, 3, 5, 2]), .triangle 1 0]

def cycle0973 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 3, 5, 2]), .triangle 3 0]

def cycle0974 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (0), (0), (-1), (-1), (-1), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .gapLower 0 5 (![1, 4, 3, 5, 2]), .triangle 6 2, .triangle 8 1, .triangle 7 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 4, 3, 5, 2]), .triangle 0 0]

def cycle0975 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (0), (2), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .gapLower 0 5 (![1, 4, 3, 5, 2]), .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![0, 4, 3, 5, 2]), .triangle 0 0]

def cycle0976 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (2), (-1), (-1), (-1), (0), (3), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 5, 2]), .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 3, 5, 2])]

def cycle0977 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1), (0), (3), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .gapLower 0 5 (![1, 4, 3, 5, 2]), .triangle 4 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 1 (![0, 5, 4, 3, 2])]

def cycle0978 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0979 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 0]

def cycle0980 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 3, 5, 2])]

def cycle0981 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 3, 5, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 1 (![1, 4, 3, 5, 2])]

def cycle0982 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 2 (![1, 4, 3, 5, 2]), .gapLower 0 1 (![1, 4, 3, 5, 2])]

def cycle0983 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 3 (![1, 4, 3, 5, 2]), .triangle 7 2, .gapLower 0 1 (![1, 4, 3, 5, 2])]

def cycle0984 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 4 (![1, 4, 3, 5, 2]), .triangle 8 1, .triangle 7 2, .gapLower 0 1 (![1, 4, 3, 5, 2])]

def cycle0985 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 4, 3, 5, 2]), .triangle 6 2, .triangle 8 1, .triangle 7 2, .gapLower 0 1 (![1, 4, 3, 5, 2])]

def cycle0986 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 6 2, .gapLower 0 3 (![1, 4, 3, 5, 2]), .gapLower 0 2 (![1, 4, 3, 5, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0987 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (0), (-2), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 4, 3, 5, 2]), .triangle 8 1, .gapLower 0 2 (![1, 4, 3, 5, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0988 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![(0), (0), (-2), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 1, .gapLower 0 2 (![1, 4, 3, 5, 2]), .corridorLower 0 4, .gapLower 0 5 (![1, 4, 3, 5, 2])]

def cycle0989 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 4, 3, 5, 2]), .gapLower 0 3 (![1, 4, 3, 5, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0990 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (-2), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, true, false] }
  origin := ![.triangle 6 2, .gapLower 0 3 (![1, 4, 3, 5, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 5, 2])]

def cycle0991 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(-2), (0), (-1), (-1), (0), (0), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 4 (![1, 4, 3, 5, 2]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 3, 5, 2])]

def cycle0992 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .triangle 2 0]

def cycle0993 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 2 1]

def cycle0994 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 1 (![1, 4, 5, 3, 2])]

def cycle0995 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-3), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, false, true] }
  origin := ![.triangle 4 2, .triangle 8 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0996 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-3), (0), (0), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, true, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 9 1, .triangle 7 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0997 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-3), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 0 4 (![1, 4, 5, 3, 2]), .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle0998 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![(0), (-1), (-1), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, true, false] }
  origin := ![.triangle 4 2, .triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 4, 5, 3, 2])]

def cycle0999 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 1 (![1, 4, 5, 3, 2])]

def cycle1000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (0), (-2), (0), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, true] }
  origin := ![.triangle 4 2, .triangle 8 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .gapLower 4 2 (![2, 3, 0, 1, 5]), .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle1001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-1), (-1), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 4 2, .triangle 8 0, .triangle 17 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle1002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (0), (-2), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.triangle 4 0, .triangle 17 0, .triangle 19 1, .gapLower 3 0 (![4, 5, 2, 0, 1]), .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle1003 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-1), (-2), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.triangle 4 0, .triangle 17 0, .gapLower 3 1 (![4, 5, 2, 0, 1]), .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle1004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-2), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 4 0, .gapLower 3 2 (![4, 5, 2, 0, 1]), .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle1005 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (0), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 3 3 (![4, 5, 2, 0, 1]), .triangle 17 2, .triangle 18 1, .gapLower 2 0 (![4, 5, 3, 0, 1]), .corridorUpper 1 2, .triangle 0 2]

def cycle1006 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![4, 5, 2, 0, 1]), .triangle 8 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 2 1]

def cycle1007 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 2, 0, 1]), .triangle 1 2, .triangle 8 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 2 1]

def cycle1008 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![(0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 7 1, .triangle 19 0, .triangle 9 2, .gapLower 0 2 (![1, 4, 5, 3, 2])]

def cycle1009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 4 0, .triangle 17 2, .gapLower 2 1 (![4, 5, 3, 0, 1]), .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def cycle1010 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 5, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-1), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 4 0, .gapLower 2 2 (![4, 5, 3, 0, 1]), .corridorLower 2 5, .corridorUpper 1 2, .triangle 0 2]

def cycle1011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(-2), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 3 (![4, 5, 3, 0, 1]), .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle1012 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![4, 5, 3, 0, 1]), .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 2 1]

def cycle1013 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![4, 5, 3, 0, 1]), .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 2 1]

def cycle1014 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (0), (-1), (0), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 4 0, .triangle 16 2, .triangle 18 0, .gapLower 5 3 (![3, 0, 1, 4, 2]), .triangle 3 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 2 1]

def cycle1015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 1 (![0, 4, 5, 3, 2])]

def cycle1016 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 2 0]

def cycle1017 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 3 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 2 1]

def cycle1018 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 5, 3, 2]), .triangle 1 2, .triangle 8 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 2 1]

def cycle1019 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 0 2, .triangle 4 2, .triangle 8 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 2 1]

def cycle1020 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 4, 5, 3, 2]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 2 (![1, 4, 5, 3, 2]), .triangle 2 1]

def cycle1021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (0), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 9 1, .gapLower 4 2 (![2, 3, 0, 1, 5]), .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def cycle1022 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-1), (-1), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 8 1, .triangle 17 0, .triangle 16 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def cycle1023 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![(0), (-2), (0), (-2), (-1), (0), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true, false, true] }
  origin := ![.triangle 4 2, .gapLower 0 3 (![1, 4, 5, 3, 2]), .triangle 8 1, .gapLower 3 1 (![4, 5, 2, 0, 1]), .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

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
  | 0 => some (.leaf 977)
  | 1 => some (.leaf 978)
  | 2 => some (.leaf 979)
  | 3 => some (.leaf 980)
  | 4 => some (.leaf 981)
  | 5 => some (.leaf 982)
  | 6 => some (.leaf 983)
  | 7 => some (.triangle 18 1058 1542)
  | 8 => some (.triangle 16 1426 1543)
  | 9 => some (.leaf 984)
  | 10 => some (.leaf 985)
  | 11 => some (.leaf 986)
  | 12 => some (.leaf 987)
  | 13 => some (.leaf 988)
  | 14 => some (.positive 0 (![1544, 1545, 1546, 1547, 1548, 1549]))
  | 15 => some (.triangle 14 1345 1550)
  | 16 => some (.leaf 989)
  | 17 => some (.triangle 15 1551 1552)
  | 18 => some (.triangle 13 1425 1553)
  | 19 => some (.leaf 990)
  | 20 => some (.triangle 12 1554 1555)
  | 21 => some (.leaf 991)
  | 22 => some (.triangle 11 1556 1557)
  | 23 => some (.leaf 992)
  | 24 => some (.triangle 10 1558 1559)
  | 25 => some (.triangle 16 1426 1060)
  | 26 => some (.leaf 993)
  | 27 => some (.leaf 994)
  | 28 => some (.positive 0 (![1561, 1545, 1546, 1547, 1562, 1563]))
  | 29 => some (.triangle 14 1345 1564)
  | 30 => some (.leaf 995)
  | 31 => some (.leaf 996)
  | 32 => some (.leaf 997)
  | 33 => some (.leaf 998)
  | 34 => some (.leaf 999)
  | 35 => some (.leaf 1000)
  | 36 => some (.leaf 1001)
  | 37 => some (.leaf 1002)
  | 38 => some (.positive 3 (![1568, 1569, 1570, 1571, 1572, 1573]))
  | 39 => some (.leaf 1003)
  | 40 => some (.leaf 1004)
  | 41 => some (.leaf 1005)
  | 42 => some (.positive 2 (![1566, 1567, 1574, 1575, 1576, 1577]))
  | 43 => some (.leaf 1006)
  | 44 => some (.triangle 19 1578 1579)
  | 45 => some (.leaf 1007)
  | 46 => some (.leaf 1008)
  | 47 => some (.leaf 1009)
  | 48 => some (.leaf 1010)
  | 49 => some (.positive 1 (![1580, 1581, 1582, 1074, 1583, 1584]))
  | 50 => some (.triangle 18 170 1585)
  | 51 => some (.triangle 16 1426 1586)
  | 52 => some (.leaf 1011)
  | 53 => some (.leaf 1012)
  | 54 => some (.leaf 1013)
  | 55 => some (.leaf 1014)
  | 56 => some (.leaf 1015)
  | 57 => some (.positive 0 (![1587, 1588, 1589, 1590, 1591, 1592]))
  | 58 => some (.triangle 15 1565 1593)
  | 59 => some (.triangle 13 1425 1594)
  | 60 => some (.leaf 1016)
  | 61 => some (.triangle 12 1595 1596)
  | 62 => some (.triangle 11 1597 1557)
  | 63 => some (.leaf 1017)
  | 64 => some (.triangle 10 1598 1599)
  | 65 => some (.leaf 1018)
  | 66 => some (.leaf 1019)
  | 67 => some (.leaf 1020)
  | 68 => some (.leaf 1021)
  | 69 => some (.triangle 18 1603 1604)
  | 70 => some (.triangle 16 1426 1605)
  | 71 => some (.positive 0 (![1561, 1545, 1546, 1547, 1562, 1606]))
  | 72 => some (.triangle 14 1602 1607)
  | 73 => some (.leaf 1022)
  | 74 => some (.leaf 1023)
  | 75 => some (.leaf 1024)
  | 76 => some (.leaf 1025)
  | 77 => some (.positive 2 (![1566, 1609, 1610, 1611, 1576, 1612]))
  | 78 => some (.leaf 1026)
  | 79 => some (.triangle 19 1613 1614)
  | 80 => some (.leaf 1027)
  | 81 => some (.positive 1 (![1615, 1581, 1582, 1074, 1583, 1616]))
  | 82 => some (.triangle 18 170 1617)
  | 83 => some (.triangle 16 1426 1618)
  | 84 => some (.leaf 1028)
  | 85 => some (.positive 0 (![1619, 1588, 1589, 1590, 1591, 1620]))
  | 86 => some (.triangle 15 1608 1621)
  | 87 => some (.triangle 13 1601 1622)
  | 88 => some (.triangle 12 1623 1596)
  | 89 => some (.triangle 11 1624 1557)
  | 90 => some (.leaf 1029)
  | 91 => some (.leaf 1030)
  | 92 => some (.leaf 1031)
  | 93 => some (.leaf 1032)
  | 94 => some (.leaf 1033)
  | 95 => some (.leaf 1034)
  | 96 => some (.positive 1 (![1626, 1627, 1628, 1629, 1630, 1631]))
  | 97 => some (.triangle 17 1381 1632)
  | 98 => some (.leaf 1035)
  | 99 => some (.triangle 18 1633 1634)
  | 100 => some (.triangle 16 1426 1635)
  | 101 => some (.leaf 1036)
  | 102 => some (.leaf 1037)
  | 103 => some (.leaf 1038)
  | 104 => some (.leaf 1039)
  | 105 => some (.leaf 1040)
  | 106 => some (.positive 0 (![1636, 1637, 1638, 1639, 1640, 1641]))
  | 107 => some (.triangle 14 1602 1642)
  | 108 => some (.leaf 1041)
  | 109 => some (.triangle 18 1644 1506)
  | 110 => some (.triangle 16 1426 1645)
  | 111 => some (.leaf 1042)
  | 112 => some (.leaf 1043)
  | 113 => some (.triangle 18 1647 1648)
  | 114 => some (.triangle 16 1426 1649)
  | 115 => some (.leaf 1044)
  | 116 => some (.leaf 1045)
  | 117 => some (.leaf 1046)
  | 118 => some (.leaf 1047)
  | 119 => some (.positive 0 (![1646, 1650, 1651, 1652, 1653, 1654]))
  | 120 => some (.triangle 15 1643 1655)
  | 121 => some (.triangle 13 1601 1656)
  | 122 => some (.triangle 10 1625 1657)
  | 123 => some (.leaf 1048)
  | 124 => some (.leaf 1049)
  | 125 => some (.leaf 1050)
  | 126 => some (.leaf 1051)
  | 127 => some (.leaf 1052)
  | 128 => some (.leaf 1053)
  | 129 => some (.leaf 1054)
  | 130 => some (.leaf 1055)
  | 131 => some (.leaf 1056)
  | 132 => some (.leaf 1057)
  | 133 => some (.heavy (![1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541, 1560, 1600, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668]))
  | 134 => some (.triangle 8 1531 1669)
  | 135 => some (.leaf 1058)
  | 136 => some (.leaf 1059)
  | 137 => some (.triangle 10 1671 1672)
  | 138 => some (.leaf 1060)
  | 139 => some (.leaf 1061)
  | 140 => some (.leaf 1062)
  | 141 => some (.leaf 1063)
  | 142 => some (.leaf 1064)
  | 143 => some (.leaf 1065)
  | 144 => some (.leaf 1066)
  | 145 => some (.leaf 1067)
  | 146 => some (.leaf 1068)
  | 147 => some (.leaf 1069)
  | 148 => some (.leaf 1070)
  | 149 => some (.leaf 1071)
  | 150 => some (.positive 3 (![1680, 1681, 1682, 1683, 1684, 1685]))
  | 151 => some (.leaf 1072)
  | 152 => some (.leaf 1073)
  | 153 => some (.leaf 1074)
  | 154 => some (.positive 2 (![1678, 1679, 1686, 1687, 1688, 1689]))
  | 155 => some (.triangle 8 1677 1690)
  | 156 => some (.leaf 1075)
  | 157 => some (.leaf 1076)
  | 158 => some (.leaf 1077)
  | 159 => some (.leaf 1078)
  | 160 => some (.leaf 1079)
  | 161 => some (.leaf 1080)
  | 162 => some (.leaf 1081)
  | 163 => some (.positive 3 (![1693, 1694, 1695, 1696, 1697, 1698]))
  | 164 => some (.triangle 8 1692 1699)
  | 165 => some (.leaf 1082)
  | 166 => some (.leaf 1083)
  | 167 => some (.leaf 1084)
  | 168 => some (.leaf 1085)
  | 169 => some (.leaf 1086)
  | 170 => some (.positive 2 (![1700, 1701, 1702, 1703, 1704, 1705]))
  | 171 => some (.triangle 19 1691 1706)
  | 172 => some (.leaf 1087)
  | 173 => some (.positive 1 (![1676, 1707, 386, 387, 388, 1708]))
  | 174 => some (.triangle 18 1165 1709)
  | 175 => some (.triangle 16 1426 1710)
  | 176 => some (.leaf 1088)
  | 177 => some (.positive 3 (![1680, 1681, 1682, 1683, 1684, 1712]))
  | 178 => some (.positive 2 (![1678, 1679, 1713, 1687, 1688, 1689]))
  | 179 => some (.triangle 8 1677 1714)
  | 180 => some (.leaf 1089)
  | 181 => some (.positive 3 (![1693, 1694, 1695, 1696, 1697, 1716]))
  | 182 => some (.triangle 8 1692 1717)
  | 183 => some (.leaf 1090)
  | 184 => some (.positive 2 (![1718, 1701, 1702, 1703, 1704, 1719]))
  | 185 => some (.triangle 19 1715 1720)
  | 186 => some (.leaf 1091)
  | 187 => some (.leaf 1092)
  | 188 => some (.positive 1 (![1676, 393, 1721, 1722, 1723, 1708]))
  | 189 => some (.triangle 18 1165 1724)
  | 190 => some (.triangle 16 1426 1725)
  | 191 => some (.leaf 1093)
  | 192 => some (.leaf 1094)
  | 193 => some (.leaf 1095)
  | 194 => some (.positive 0 (![1675, 1711, 1726, 1727, 1728, 1729]))
  | 195 => some (.triangle 15 1161 1730)
  | 196 => some (.triangle 13 1425 1731)
  | 197 => some (.leaf 1096)
  | 198 => some (.triangle 12 1732 1733)
  | 199 => some (.leaf 1097)
  | 200 => some (.triangle 11 1734 1735)
  | 201 => some (.leaf 1098)
  | 202 => some (.triangle 10 1736 1737)
  | 203 => some (.leaf 1099)
  | 204 => some (.leaf 1100)
  | 205 => some (.leaf 1101)
  | 206 => some (.leaf 1102)
  | 207 => some (.leaf 1103)
  | 208 => some (.leaf 1104)
  | 209 => some (.leaf 1105)
  | 210 => some (.positive 3 (![1680, 1681, 1682, 1743, 1744, 1745]))
  | 211 => some (.leaf 1106)
  | 212 => some (.leaf 1107)
  | 213 => some (.leaf 1108)
  | 214 => some (.positive 2 (![1678, 1679, 1746, 1747, 1748, 1749]))
  | 215 => some (.triangle 8 1677 1750)
  | 216 => some (.leaf 1109)
  | 217 => some (.leaf 1110)
  | 218 => some (.leaf 1111)
  | 219 => some (.positive 3 (![1693, 1694, 1695, 1752, 1753, 1754]))
  | 220 => some (.triangle 8 1692 1755)
  | 221 => some (.leaf 1112)
  | 222 => some (.leaf 1113)
  | 223 => some (.leaf 1114)
  | 224 => some (.positive 2 (![1756, 1701, 1702, 1757, 1758, 1759]))
  | 225 => some (.triangle 19 1751 1760)
  | 226 => some (.leaf 1115)
  | 227 => some (.leaf 1116)
  | 228 => some (.leaf 1117)
  | 229 => some (.leaf 1118)
  | 230 => some (.leaf 1119)
  | 231 => some (.positive 1 (![1761, 1762, 1763, 1764, 1765, 1766]))
  | 232 => some (.triangle 18 1165 1767)
  | 233 => some (.triangle 16 1426 1768)
  | 234 => some (.leaf 1120)
  | 235 => some (.leaf 1121)
  | 236 => some (.leaf 1122)
  | 237 => some (.leaf 1123)
  | 238 => some (.leaf 1124)
  | 239 => some (.positive 0 (![1769, 1770, 1771, 1772, 1773, 1774]))
  | 240 => some (.triangle 15 1161 1775)
  | 241 => some (.triangle 13 1425 1776)
  | 242 => some (.leaf 1125)
  | 243 => some (.triangle 12 1777 1778)
  | 244 => some (.leaf 1126)
  | 245 => some (.triangle 11 1779 1780)
  | 246 => some (.leaf 1127)
  | 247 => some (.triangle 10 1781 1782)
  | 248 => some (.leaf 1128)
  | 249 => some (.leaf 1129)
  | 250 => some (.triangle 8 1692 1785)
  | 251 => some (.leaf 1130)
  | 252 => some (.leaf 1131)
  | 253 => some (.leaf 1132)
  | 254 => some (.positive 2 (![1786, 1701, 1702, 1787, 1788, 1789]))
  | 255 => some (.triangle 19 1784 1790)
  | 256 => some (.leaf 1133)
  | 257 => some (.leaf 1134)
  | 258 => some (.positive 1 (![1791, 1762, 1763, 1074, 1792, 1793]))
  | 259 => some (.triangle 18 1165 1794)
  | 260 => some (.triangle 16 1426 1795)
  | 261 => some (.leaf 1135)
  | 262 => some (.leaf 1136)
  | 263 => some (.leaf 1137)
  | 264 => some (.positive 0 (![1796, 1770, 1771, 1797, 1798, 1799]))
  | 265 => some (.triangle 15 1161 1800)
  | 266 => some (.triangle 13 1425 1801)
  | 267 => some (.leaf 1138)
  | 268 => some (.triangle 12 1802 1803)
  | 269 => some (.leaf 1139)
  | 270 => some (.triangle 11 1804 1805)
  | 271 => some (.leaf 1140)
  | 272 => some (.triangle 10 1806 1807)
  | 273 => some (.leaf 1141)
  | 274 => some (.leaf 1142)
  | 275 => some (.leaf 1143)
  | 276 => some (.leaf 1144)
  | 277 => some (.triangle 19 1811 1812)
  | 278 => some (.leaf 1145)
  | 279 => some (.positive 1 (![1813, 1762, 1763, 1074, 1275, 1814]))
  | 280 => some (.triangle 18 1165 1815)
  | 281 => some (.triangle 16 1426 1816)
  | 282 => some (.leaf 1146)
  | 283 => some (.leaf 1147)
  | 284 => some (.leaf 1148)
  | 285 => some (.positive 1 (![1813, 1762, 1763, 1819, 1820, 1814]))
  | 286 => some (.triangle 18 1165 1821)
  | 287 => some (.triangle 16 1426 1822)
  | 288 => some (.positive 0 (![1817, 1770, 1771, 1797, 1818, 1823]))
  | 289 => some (.triangle 15 1161 1824)
  | 290 => some (.triangle 13 1810 1825)
  | 291 => some (.triangle 12 1826 1803)
  | 292 => some (.leaf 1149)
  | 293 => some (.triangle 11 1827 1828)
  | 294 => some (.leaf 1150)
  | 295 => some (.leaf 1151)
  | 296 => some (.leaf 1152)
  | 297 => some (.leaf 1153)
  | 298 => some (.leaf 1154)
  | 299 => some (.leaf 1155)
  | 300 => some (.positive 1 (![1830, 1831, 1832, 1833, 1834, 1835]))
  | 301 => some (.triangle 18 1165 1836)
  | 302 => some (.triangle 16 1426 1837)
  | 303 => some (.leaf 1156)
  | 304 => some (.leaf 1157)
  | 305 => some (.leaf 1158)
  | 306 => some (.leaf 1159)
  | 307 => some (.leaf 1160)
  | 308 => some (.positive 1 (![1830, 1839, 1840, 1841, 1842, 1843]))
  | 309 => some (.triangle 18 1165 1844)
  | 310 => some (.triangle 16 1426 1845)
  | 311 => some (.leaf 1161)
  | 312 => some (.leaf 1162)
  | 313 => some (.leaf 1163)
  | 314 => some (.leaf 1164)
  | 315 => some (.positive 0 (![1838, 1846, 1847, 1848, 1849, 1850]))
  | 316 => some (.triangle 15 1161 1851)
  | 317 => some (.triangle 13 1810 1852)
  | 318 => some (.triangle 10 1829 1853)
  | 319 => some (.leaf 1165)
  | 320 => some (.leaf 1166)
  | 321 => some (.leaf 1167)
  | 322 => some (.leaf 1168)
  | 323 => some (.leaf 1169)
  | 324 => some (.leaf 1170)
  | 325 => some (.leaf 1171)
  | 326 => some (.leaf 1172)
  | 327 => some (.leaf 1173)
  | 328 => some (.leaf 1174)
  | 329 => some (.heavy (![1673, 1674, 1738, 1739, 1740, 1741, 1742, 1783, 1808, 1809, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864]))
  | 330 => some (.triangle 9 1670 1865)
  | 331 => some (.triangle 7 1413 1866)
  | 332 => some (.leaf 1175)
  | 333 => some (.leaf 1176)
  | 334 => some (.triangle 10 1868 1869)
  | 335 => some (.leaf 1177)
  | 336 => some (.leaf 1178)
  | 337 => some (.leaf 1179)
  | 338 => some (.leaf 1180)
  | 339 => some (.leaf 1181)
  | 340 => some (.leaf 1182)
  | 341 => some (.leaf 1183)
  | 342 => some (.leaf 1184)
  | 343 => some (.leaf 1185)
  | 344 => some (.leaf 1186)
  | 345 => some (.leaf 1187)
  | 346 => some (.triangle 16 1880 1881)
  | 347 => some (.leaf 1188)
  | 348 => some (.leaf 1189)
  | 349 => some (.leaf 1190)
  | 350 => some (.leaf 1191)
  | 351 => some (.leaf 1192)
  | 352 => some (.positive 0 (![1882, 1883, 1884, 1885, 1886, 1887]))
  | 353 => some (.leaf 1193)
  | 354 => some (.triangle 13 1888 1889)
  | 355 => some (.triangle 12 1879 1890)
  | 356 => some (.leaf 1194)
  | 357 => some (.triangle 11 1891 1892)
  | 358 => some (.leaf 1195)
  | 359 => some (.triangle 10 1893 1894)
  | 360 => some (.leaf 1196)
  | 361 => some (.triangle 16 1880 1896)
  | 362 => some (.leaf 1197)
  | 363 => some (.triangle 16 1898 1896)
  | 364 => some (.positive 0 (![1897, 1883, 1884, 1885, 1886, 1899]))
  | 365 => some (.leaf 1198)
  | 366 => some (.leaf 1199)
  | 367 => some (.leaf 1200)
  | 368 => some (.leaf 1201)
  | 369 => some (.leaf 1202)
  | 370 => some (.leaf 1203)
  | 371 => some (.positive 1 (![1901, 1902, 1903, 1904, 1905, 1906]))
  | 372 => some (.triangle 16 36 1907)
  | 373 => some (.leaf 1204)
  | 374 => some (.leaf 1205)
  | 375 => some (.leaf 1206)
  | 376 => some (.leaf 1207)
  | 377 => some (.leaf 1208)
  | 378 => some (.positive 0 (![1908, 1909, 1910, 1911, 1912, 1913]))
  | 379 => some (.triangle 13 1900 1914)
  | 380 => some (.triangle 12 1879 1915)
  | 381 => some (.leaf 1209)
  | 382 => some (.triangle 11 1916 1917)
  | 383 => some (.triangle 10 1918 1894)
  | 384 => some (.leaf 1210)
  | 385 => some (.leaf 1211)
  | 386 => some (.leaf 1212)
  | 387 => some (.leaf 1213)
  | 388 => some (.leaf 1214)
  | 389 => some (.leaf 1215)
  | 390 => some (.leaf 1216)
  | 391 => some (.leaf 1217)
  | 392 => some (.leaf 1218)
  | 393 => some (.leaf 1219)
  | 394 => some (.heavy (![1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1895, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929]))
  | 395 => some (.leaf 1220)
  | 396 => some (.leaf 1221)
  | 397 => some (.triangle 10 1931 1932)
  | 398 => some (.leaf 1222)
  | 399 => some (.leaf 1223)
  | 400 => some (.leaf 1224)
  | 401 => some (.leaf 1225)
  | 402 => some (.leaf 1226)
  | 403 => some (.leaf 1227)
  | 404 => some (.leaf 1228)
  | 405 => some (.leaf 1229)
  | 406 => some (.leaf 1230)
  | 407 => some (.leaf 1231)
  | 408 => some (.leaf 1232)
  | 409 => some (.leaf 1233)
  | 410 => some (.leaf 1234)
  | 411 => some (.positive 1 (![1941, 1942, 1943, 1944, 1945, 1946]))
  | 412 => some (.triangle 16 1426 1947)
  | 413 => some (.leaf 1235)
  | 414 => some (.leaf 1236)
  | 415 => some (.leaf 1237)
  | 416 => some (.leaf 1238)
  | 417 => some (.leaf 1239)
  | 418 => some (.positive 0 (![1948, 1949, 1950, 1951, 1952, 1953]))
  | 419 => some (.triangle 13 1425 1954)
  | 420 => some (.triangle 12 1879 1955)
  | 421 => some (.leaf 1240)
  | 422 => some (.triangle 11 1956 1957)
  | 423 => some (.leaf 1241)
  | 424 => some (.triangle 10 1958 1959)
  | 425 => some (.leaf 1242)
  | 426 => some (.leaf 1243)
  | 427 => some (.leaf 1244)
  | 428 => some (.positive 1 (![1961, 1962, 1943, 1944, 1905, 1963]))
  | 429 => some (.triangle 16 1426 1964)
  | 430 => some (.leaf 1245)
  | 431 => some (.leaf 1246)
  | 432 => some (.positive 0 (![1965, 1949, 1950, 1951, 1966, 1967]))
  | 433 => some (.triangle 13 1425 1968)
  | 434 => some (.triangle 12 1879 1969)
  | 435 => some (.leaf 1247)
  | 436 => some (.triangle 11 1970 1971)
  | 437 => some (.leaf 1248)
  | 438 => some (.triangle 10 1972 1973)
  | 439 => some (.leaf 1249)
  | 440 => some (.leaf 1250)
  | 441 => some (.leaf 1251)
  | 442 => some (.leaf 1252)
  | 443 => some (.leaf 1253)
  | 444 => some (.positive 1 (![1977, 1978, 1943, 1944, 1905, 1979]))
  | 445 => some (.triangle 16 1976 1980)
  | 446 => some (.leaf 1254)
  | 447 => some (.leaf 1255)
  | 448 => some (.leaf 1256)
  | 449 => some (.leaf 1257)
  | 450 => some (.positive 1 (![1982, 1983, 1984, 1944, 1985, 1979]))
  | 451 => some (.triangle 16 1976 1986)
  | 452 => some (.positive 0 (![1981, 1949, 1950, 1951, 1966, 1987]))
  | 453 => some (.triangle 13 1975 1988)
  | 454 => some (.triangle 12 1879 1989)
  | 455 => some (.triangle 11 1990 1971)
  | 456 => some (.triangle 10 1991 1894)
  | 457 => some (.leaf 1258)
  | 458 => some (.leaf 1259)
  | 459 => some (.leaf 1260)
  | 460 => some (.leaf 1261)
  | 461 => some (.leaf 1262)
  | 462 => some (.leaf 1263)
  | 463 => some (.leaf 1264)
  | 464 => some (.leaf 1265)
  | 465 => some (.leaf 1266)
  | 466 => some (.leaf 1267)
  | 467 => some (.heavy (![1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1960, 1974, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002]))
  | 468 => some (.triangle 7 1930 2003)
  | 469 => some (.triangle 6 1867 2004)
  | 470 => some (.leaf 1268)
  | 471 => some (.leaf 1269)
  | 472 => some (.triangle 10 2006 2007)
  | 473 => some (.leaf 1270)
  | 474 => some (.leaf 1271)
  | 475 => some (.leaf 1272)
  | 476 => some (.leaf 1273)
  | 477 => some (.leaf 1274)
  | 478 => some (.leaf 1275)
  | 479 => some (.leaf 1276)
  | 480 => some (.leaf 1277)
  | 481 => some (.leaf 1278)
  | 482 => some (.leaf 1279)
  | 483 => some (.leaf 1280)
  | 484 => some (.triangle 17 2018 2019)
  | 485 => some (.leaf 1281)
  | 486 => some (.leaf 1282)
  | 487 => some (.leaf 1283)
  | 488 => some (.leaf 1284)
  | 489 => some (.leaf 1285)
  | 490 => some (.positive 0 (![2020, 2021, 2022, 2023, 2024, 2025]))
  | 491 => some (.leaf 1286)
  | 492 => some (.triangle 14 2026 2027)
  | 493 => some (.leaf 1287)
  | 494 => some (.triangle 12 2028 2029)
  | 495 => some (.leaf 1288)
  | 496 => some (.triangle 15 2030 2031)
  | 497 => some (.triangle 11 2017 2032)
  | 498 => some (.leaf 1289)
  | 499 => some (.triangle 10 2033 2034)
  | 500 => some (.leaf 1290)
  | 501 => some (.triangle 17 2018 2036)
  | 502 => some (.leaf 1291)
  | 503 => some (.triangle 17 2038 2036)
  | 504 => some (.positive 0 (![2037, 2021, 2022, 2023, 2024, 2039]))
  | 505 => some (.leaf 1292)
  | 506 => some (.leaf 1293)
  | 507 => some (.leaf 1294)
  | 508 => some (.leaf 1295)
  | 509 => some (.leaf 1296)
  | 510 => some (.leaf 1297)
  | 511 => some (.positive 1 (![2041, 2042, 2043, 2044, 2045, 2046]))
  | 512 => some (.triangle 17 234 2047)
  | 513 => some (.leaf 1298)
  | 514 => some (.leaf 1299)
  | 515 => some (.leaf 1300)
  | 516 => some (.leaf 1301)
  | 517 => some (.leaf 1302)
  | 518 => some (.positive 0 (![2048, 2049, 2050, 2051, 2052, 2053]))
  | 519 => some (.triangle 14 2040 2054)
  | 520 => some (.leaf 1303)
  | 521 => some (.triangle 12 2055 2056)
  | 522 => some (.leaf 1304)
  | 523 => some (.triangle 15 2057 2058)
  | 524 => some (.triangle 11 2017 2059)
  | 525 => some (.triangle 10 2060 2034)
  | 526 => some (.leaf 1305)
  | 527 => some (.leaf 1306)
  | 528 => some (.leaf 1307)
  | 529 => some (.leaf 1308)
  | 530 => some (.leaf 1309)
  | 531 => some (.leaf 1310)
  | 532 => some (.leaf 1311)
  | 533 => some (.leaf 1312)
  | 534 => some (.leaf 1313)
  | 535 => some (.leaf 1314)
  | 536 => some (.heavy (![2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2035, 2061, 2062, 2063, 2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071]))
  | 537 => some (.leaf 1315)
  | 538 => some (.leaf 1316)
  | 539 => some (.triangle 10 2073 2074)
  | 540 => some (.leaf 1317)
  | 541 => some (.leaf 1318)
  | 542 => some (.leaf 1319)
  | 543 => some (.leaf 1320)
  | 544 => some (.leaf 1321)
  | 545 => some (.leaf 1322)
  | 546 => some (.leaf 1323)
  | 547 => some (.leaf 1324)
  | 548 => some (.leaf 1325)
  | 549 => some (.leaf 1326)
  | 550 => some (.leaf 1327)
  | 551 => some (.leaf 1328)
  | 552 => some (.leaf 1329)
  | 553 => some (.positive 1 (![2083, 2084, 2085, 2086, 2087, 2088]))
  | 554 => some (.triangle 17 1381 2089)
  | 555 => some (.leaf 1330)
  | 556 => some (.leaf 1331)
  | 557 => some (.leaf 1332)
  | 558 => some (.leaf 1333)
  | 559 => some (.leaf 1334)
  | 560 => some (.positive 0 (![2090, 2091, 2092, 2093, 2094, 2095]))
  | 561 => some (.triangle 14 1345 2096)
  | 562 => some (.leaf 1335)
  | 563 => some (.triangle 12 2097 2098)
  | 564 => some (.leaf 1336)
  | 565 => some (.triangle 15 2099 2100)
  | 566 => some (.triangle 11 2017 2101)
  | 567 => some (.leaf 1337)
  | 568 => some (.triangle 10 2102 2103)
  | 569 => some (.leaf 1338)
  | 570 => some (.leaf 1339)
  | 571 => some (.leaf 1340)
  | 572 => some (.positive 1 (![2105, 2106, 2085, 2086, 2045, 2107]))
  | 573 => some (.triangle 17 1381 2108)
  | 574 => some (.leaf 1341)
  | 575 => some (.leaf 1342)
  | 576 => some (.positive 0 (![2109, 2091, 2092, 2093, 2110, 2111]))
  | 577 => some (.triangle 14 1345 2112)
  | 578 => some (.leaf 1343)
  | 579 => some (.triangle 12 2113 2114)
  | 580 => some (.leaf 1344)
  | 581 => some (.triangle 15 2115 2116)
  | 582 => some (.triangle 11 2017 2117)
  | 583 => some (.leaf 1345)
  | 584 => some (.triangle 10 2118 2119)
  | 585 => some (.leaf 1346)
  | 586 => some (.leaf 1347)
  | 587 => some (.leaf 1348)
  | 588 => some (.leaf 1349)
  | 589 => some (.leaf 1350)
  | 590 => some (.positive 1 (![2123, 2124, 2085, 2086, 2045, 2125]))
  | 591 => some (.triangle 17 2122 2126)
  | 592 => some (.leaf 1351)
  | 593 => some (.leaf 1352)
  | 594 => some (.leaf 1353)
  | 595 => some (.leaf 1354)
  | 596 => some (.positive 1 (![2128, 2129, 2130, 2086, 2131, 2125]))
  | 597 => some (.triangle 17 2122 2132)
  | 598 => some (.positive 0 (![2127, 2091, 2092, 2093, 2110, 2133]))
  | 599 => some (.triangle 14 2121 2134)
  | 600 => some (.triangle 12 2135 2114)
  | 601 => some (.triangle 15 2136 2116)
  | 602 => some (.triangle 11 2017 2137)
  | 603 => some (.triangle 10 2138 2034)
  | 604 => some (.leaf 1355)
  | 605 => some (.leaf 1356)
  | 606 => some (.leaf 1357)
  | 607 => some (.leaf 1358)
  | 608 => some (.leaf 1359)
  | 609 => some (.leaf 1360)
  | 610 => some (.leaf 1361)
  | 611 => some (.leaf 1362)
  | 612 => some (.leaf 1363)
  | 613 => some (.leaf 1364)
  | 614 => some (.heavy (![2075, 2076, 2077, 2078, 2079, 2080, 2081, 2082, 2104, 2120, 2139, 2140, 2141, 2142, 2143, 2144, 2145, 2146, 2147, 2148, 2149]))
  | 615 => some (.triangle 8 2072 2150)
  | 616 => some (.leaf 1365)
  | 617 => some (.leaf 1366)
  | 618 => some (.triangle 10 2152 2153)
  | 619 => some (.leaf 1367)
  | 620 => some (.leaf 1368)
  | 621 => some (.leaf 1369)
  | 622 => some (.leaf 1370)
  | 623 => some (.leaf 1371)
  | 624 => some (.leaf 1372)
  | 625 => some (.leaf 1373)
  | 626 => some (.leaf 1374)
  | 627 => some (.leaf 1375)
  | 628 => some (.leaf 1376)
  | 629 => some (.leaf 1377)
  | 630 => some (.leaf 1378)
  | 631 => some (.leaf 1379)
  | 632 => some (.leaf 1380)
  | 633 => some (.positive 1 (![2163, 2164, 2165, 2166, 2167, 2168]))
  | 634 => some (.leaf 1381)
  | 635 => some (.triangle 18 2169 2170)
  | 636 => some (.leaf 1382)
  | 637 => some (.leaf 1383)
  | 638 => some (.leaf 1384)
  | 639 => some (.leaf 1385)
  | 640 => some (.leaf 1386)
  | 641 => some (.positive 0 (![2171, 2172, 2173, 2174, 2175, 2176]))
  | 642 => some (.triangle 12 1879 2177)
  | 643 => some (.leaf 1387)
  | 644 => some (.triangle 15 2178 2179)
  | 645 => some (.triangle 11 2017 2180)
  | 646 => some (.leaf 1388)
  | 647 => some (.triangle 10 2181 2182)
  | 648 => some (.leaf 1389)
  | 649 => some (.leaf 1390)
  | 650 => some (.leaf 1391)
  | 651 => some (.leaf 1392)
  | 652 => some (.positive 1 (![2184, 2185, 2186, 2166, 2167, 2187]))
  | 653 => some (.leaf 1393)
  | 654 => some (.triangle 18 2188 2189)
  | 655 => some (.leaf 1394)
  | 656 => some (.leaf 1395)
  | 657 => some (.leaf 1396)
  | 658 => some (.leaf 1397)
  | 659 => some (.positive 1 (![2191, 2192, 2193, 2194, 2167, 2187]))
  | 660 => some (.triangle 18 2195 2189)
  | 661 => some (.positive 0 (![2190, 2172, 2173, 2174, 2175, 2196]))
  | 662 => some (.triangle 12 1879 2197)
  | 663 => some (.triangle 15 2198 2179)
  | 664 => some (.triangle 11 2017 2199)
  | 665 => some (.triangle 10 2200 2034)
  | 666 => some (.leaf 1398)
  | 667 => some (.leaf 1399)
  | 668 => some (.leaf 1400)
  | 669 => some (.leaf 1401)
  | 670 => some (.leaf 1402)
  | 671 => some (.leaf 1403)
  | 672 => some (.leaf 1404)
  | 673 => some (.leaf 1405)
  | 674 => some (.leaf 1406)
  | 675 => some (.leaf 1407)
  | 676 => some (.heavy (![2154, 2155, 2156, 2157, 2158, 2159, 2160, 2161, 2162, 2183, 2201, 2202, 2203, 2204, 2205, 2206, 2207, 2208, 2209, 2210, 2211]))
  | 677 => some (.triangle 6 2151 2212)
  | 678 => some (.leaf 1408)
  | 679 => some (.leaf 1409)
  | 680 => some (.triangle 10 2214 2215)
  | 681 => some (.leaf 1410)
  | 682 => some (.leaf 1411)
  | 683 => some (.leaf 1412)
  | 684 => some (.leaf 1413)
  | 685 => some (.leaf 1414)
  | 686 => some (.leaf 1415)
  | 687 => some (.leaf 1416)
  | 688 => some (.leaf 1417)
  | 689 => some (.leaf 1418)
  | 690 => some (.leaf 1419)
  | 691 => some (.leaf 1420)
  | 692 => some (.triangle 18 2226 2227)
  | 693 => some (.leaf 1421)
  | 694 => some (.leaf 1422)
  | 695 => some (.leaf 1423)
  | 696 => some (.leaf 1424)
  | 697 => some (.leaf 1425)
  | 698 => some (.triangle 18 2233 2227)
  | 699 => some (.positive 0 (![2228, 2229, 2230, 2231, 2232, 2234]))
  | 700 => some (.triangle 15 1161 2235)
  | 701 => some (.triangle 11 2017 2236)
  | 702 => some (.triangle 10 2237 2034)
  | 703 => some (.leaf 1426)
  | 704 => some (.leaf 1427)
  | 705 => some (.leaf 1428)
  | 706 => some (.leaf 1429)
  | 707 => some (.leaf 1430)
  | 708 => some (.leaf 1431)
  | 709 => some (.leaf 1432)
  | 710 => some (.leaf 1433)
  | 711 => some (.leaf 1434)
  | 712 => some (.heavy (![2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223, 2224, 2225, 2238, 2239, 2240, 2241, 2242, 2243, 2244, 2245, 2246, 2224, 2247]))
  | 713 => some (.triangle 9 2213 2248)
  | 714 => some (.triangle 5 2005 2249)
  | 715 => some (.leaf 1435)
  | 716 => some (.leaf 1436)
  | 717 => some (.leaf 1437)
  | 718 => some (.triangle 13 2252 2253)
  | 719 => some (.triangle 10 2251 2254)
  | 720 => some (.leaf 1438)
  | 721 => some (.leaf 1439)
  | 722 => some (.leaf 1440)
  | 723 => some (.leaf 1441)
  | 724 => some (.leaf 1442)
  | 725 => some (.leaf 1443)
  | 726 => some (.leaf 1444)
  | 727 => some (.leaf 1445)
  | 728 => some (.leaf 1446)
  | 729 => some (.leaf 1447)
  | 730 => some (.triangle 18 2264 2265)
  | 731 => some (.leaf 1448)
  | 732 => some (.leaf 1449)
  | 733 => some (.leaf 1450)
  | 734 => some (.leaf 1451)
  | 735 => some (.leaf 1452)
  | 736 => some (.positive 0 (![2266, 2267, 2268, 2269, 2270, 2271]))
  | 737 => some (.leaf 1453)
  | 738 => some (.triangle 15 2272 2273)
  | 739 => some (.leaf 1454)
  | 740 => some (.triangle 12 2274 2275)
  | 741 => some (.leaf 1455)
  | 742 => some (.triangle 11 2276 2277)
  | 743 => some (.leaf 1456)
  | 744 => some (.triangle 14 2278 2279)
  | 745 => some (.leaf 1457)
  | 746 => some (.leaf 1458)
  | 747 => some (.triangle 14 2281 2282)
  | 748 => some (.leaf 1459)
  | 749 => some (.triangle 15 2283 2284)
  | 750 => some (.triangle 13 2280 2285)
  | 751 => some (.triangle 10 2251 2286)
  | 752 => some (.leaf 1460)
  | 753 => some (.triangle 18 2264 2288)
  | 754 => some (.leaf 1461)
  | 755 => some (.leaf 1462)
  | 756 => some (.triangle 18 2290 2291)
  | 757 => some (.positive 0 (![2289, 2267, 2268, 2269, 2270, 2292]))
  | 758 => some (.leaf 1463)
  | 759 => some (.leaf 1464)
  | 760 => some (.leaf 1465)
  | 761 => some (.leaf 1466)
  | 762 => some (.leaf 1467)
  | 763 => some (.leaf 1468)
  | 764 => some (.positive 1 (![2294, 2295, 2296, 2297, 2298, 2299]))
  | 765 => some (.triangle 18 170 2300)
  | 766 => some (.leaf 1469)
  | 767 => some (.leaf 1470)
  | 768 => some (.leaf 1471)
  | 769 => some (.leaf 1472)
  | 770 => some (.leaf 1473)
  | 771 => some (.positive 0 (![2301, 2302, 2303, 2304, 2305, 2306]))
  | 772 => some (.triangle 15 2293 2307)
  | 773 => some (.leaf 1474)
  | 774 => some (.triangle 12 2308 2309)
  | 775 => some (.triangle 11 2310 2277)
  | 776 => some (.leaf 1475)
  | 777 => some (.triangle 14 2311 2312)
  | 778 => some (.leaf 1476)
  | 779 => some (.triangle 11 2314 2277)
  | 780 => some (.leaf 1477)
  | 781 => some (.leaf 1478)
  | 782 => some (.leaf 1479)
  | 783 => some (.leaf 1480)
  | 784 => some (.leaf 1481)
  | 785 => some (.positive 0 (![2315, 2316, 2317, 2318, 2319, 2320]))
  | 786 => some (.triangle 14 2281 2321)
  | 787 => some (.leaf 1482)
  | 788 => some (.triangle 15 2322 2323)
  | 789 => some (.triangle 13 2313 2324)
  | 790 => some (.triangle 10 2251 2325)
  | 791 => some (.leaf 1483)
  | 792 => some (.leaf 1484)
  | 793 => some (.leaf 1485)
  | 794 => some (.leaf 1486)
  | 795 => some (.leaf 1487)
  | 796 => some (.leaf 1488)
  | 797 => some (.leaf 1489)
  | 798 => some (.leaf 1490)
  | 799 => some (.leaf 1491)
  | 800 => some (.leaf 1492)
  | 801 => some (.heavy (![2255, 2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2287, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335, 2336]))
  | 802 => some (.leaf 1493)
  | 803 => some (.leaf 1494)
  | 804 => some (.triangle 13 2338 2339)
  | 805 => some (.triangle 10 2251 2340)
  | 806 => some (.leaf 1495)
  | 807 => some (.leaf 1496)
  | 808 => some (.leaf 1497)
  | 809 => some (.leaf 1498)
  | 810 => some (.leaf 1499)
  | 811 => some (.leaf 1500)
  | 812 => some (.leaf 1501)
  | 813 => some (.leaf 1502)
  | 814 => some (.leaf 1503)
  | 815 => some (.leaf 1504)
  | 816 => some (.leaf 1505)
  | 817 => some (.leaf 1506)
  | 818 => some (.leaf 1507)
  | 819 => some (.positive 1 (![2349, 2350, 2351, 2352, 2353, 2354]))
  | 820 => some (.triangle 18 1165 2355)
  | 821 => some (.leaf 1508)
  | 822 => some (.leaf 1509)
  | 823 => some (.leaf 1510)
  | 824 => some (.leaf 1511)
  | 825 => some (.leaf 1512)
  | 826 => some (.positive 0 (![2356, 2357, 2358, 2359, 2360, 2361]))
  | 827 => some (.triangle 15 1161 2362)
  | 828 => some (.leaf 1513)
  | 829 => some (.triangle 12 2363 2364)
  | 830 => some (.leaf 1514)
  | 831 => some (.triangle 11 2365 2366)
  | 832 => some (.leaf 1515)
  | 833 => some (.triangle 14 2367 2368)
  | 834 => some (.leaf 1516)
  | 835 => some (.triangle 13 2369 2370)
  | 836 => some (.triangle 10 2251 2371)
  | 837 => some (.leaf 1517)
  | 838 => some (.leaf 1518)
  | 839 => some (.leaf 1519)
  | 840 => some (.positive 1 (![2373, 2374, 2351, 2352, 2298, 2375]))
  | 841 => some (.triangle 18 1165 2376)
  | 842 => some (.leaf 1520)
  | 843 => some (.leaf 1521)
  | 844 => some (.positive 0 (![2377, 2357, 2358, 2359, 2378, 2379]))
  | 845 => some (.triangle 15 1161 2380)
  | 846 => some (.leaf 1522)
  | 847 => some (.triangle 12 2381 2382)
  | 848 => some (.leaf 1523)
  | 849 => some (.triangle 11 2383 2384)
  | 850 => some (.leaf 1524)
  | 851 => some (.triangle 14 2385 2386)
  | 852 => some (.leaf 1525)
  | 853 => some (.triangle 13 2387 2388)
  | 854 => some (.triangle 10 2251 2389)
  | 855 => some (.leaf 1526)
  | 856 => some (.leaf 1527)
  | 857 => some (.leaf 1528)
  | 858 => some (.leaf 1529)
  | 859 => some (.leaf 1530)
  | 860 => some (.positive 1 (![2393, 2394, 2351, 2352, 2298, 2395]))
  | 861 => some (.triangle 18 2392 2396)
  | 862 => some (.leaf 1531)
  | 863 => some (.leaf 1532)
  | 864 => some (.leaf 1533)
  | 865 => some (.leaf 1534)
  | 866 => some (.leaf 1535)
  | 867 => some (.positive 1 (![2398, 2399, 2400, 2352, 2401, 2402]))
  | 868 => some (.triangle 18 2392 2403)
  | 869 => some (.positive 0 (![2397, 2357, 2358, 2359, 2378, 2404]))
  | 870 => some (.triangle 15 2391 2405)
  | 871 => some (.triangle 12 2406 2382)
  | 872 => some (.triangle 11 2407 2277)
  | 873 => some (.triangle 14 2408 2386)
  | 874 => some (.leaf 1536)
  | 875 => some (.leaf 1537)
  | 876 => some (.triangle 11 2411 2277)
  | 877 => some (.leaf 1538)
  | 878 => some (.leaf 1539)
  | 879 => some (.leaf 1540)
  | 880 => some (.leaf 1541)
  | 881 => some (.positive 0 (![2412, 2412, 2413, 2414, 2415, 2416]))
  | 882 => some (.triangle 15 2410 2417)
  | 883 => some (.triangle 13 2409 2418)
  | 884 => some (.triangle 10 2251 2419)
  | 885 => some (.leaf 1542)
  | 886 => some (.leaf 1543)
  | 887 => some (.leaf 1544)
  | 888 => some (.leaf 1545)
  | 889 => some (.leaf 1546)
  | 890 => some (.leaf 1547)
  | 891 => some (.leaf 1548)
  | 892 => some (.leaf 1549)
  | 893 => some (.leaf 1550)
  | 894 => some (.leaf 1551)
  | 895 => some (.heavy (![2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2372, 2390, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430]))
  | 896 => some (.triangle 9 2337 2431)
  | 897 => some (.leaf 1552)
  | 898 => some (.leaf 1553)
  | 899 => some (.triangle 13 2433 2434)
  | 900 => some (.triangle 10 2251 2435)
  | 901 => some (.leaf 1554)
  | 902 => some (.leaf 1555)
  | 903 => some (.leaf 1556)
  | 904 => some (.leaf 1557)
  | 905 => some (.leaf 1558)
  | 906 => some (.leaf 1559)
  | 907 => some (.leaf 1560)
  | 908 => some (.leaf 1561)
  | 909 => some (.leaf 1562)
  | 910 => some (.leaf 1563)
  | 911 => some (.leaf 1564)
  | 912 => some (.leaf 1565)
  | 913 => some (.leaf 1566)
  | 914 => some (.leaf 1567)
  | 915 => some (.positive 1 (![2445, 2446, 2447, 2448, 2449, 2450]))
  | 916 => some (.leaf 1568)
  | 917 => some (.triangle 17 2451 2452)
  | 918 => some (.leaf 1569)
  | 919 => some (.leaf 1570)
  | 920 => some (.leaf 1571)
  | 921 => some (.leaf 1572)
  | 922 => some (.leaf 1573)
  | 923 => some (.positive 0 (![2453, 2454, 2455, 2456, 2457, 2458]))
  | 924 => some (.triangle 12 1879 2459)
  | 925 => some (.leaf 1574)
  | 926 => some (.triangle 11 2460 2461)
  | 927 => some (.leaf 1575)
  | 928 => some (.triangle 14 2462 2463)
  | 929 => some (.leaf 1576)
  | 930 => some (.triangle 13 2464 2465)
  | 931 => some (.triangle 10 2251 2466)
  | 932 => some (.leaf 1577)
  | 933 => some (.leaf 1578)
  | 934 => some (.leaf 1579)
  | 935 => some (.leaf 1580)
  | 936 => some (.positive 1 (![2468, 2469, 2470, 2448, 2449, 2471]))
  | 937 => some (.triangle 17 2472 2452)
  | 938 => some (.leaf 1581)
  | 939 => some (.leaf 1582)
  | 940 => some (.leaf 1583)
  | 941 => some (.leaf 1584)
  | 942 => some (.positive 1 (![2474, 2475, 2476, 2477, 2449, 2471]))
  | 943 => some (.triangle 17 2478 2452)
  | 944 => some (.positive 0 (![2473, 2454, 2455, 2456, 2457, 2479]))
  | 945 => some (.triangle 12 1879 2480)
  | 946 => some (.leaf 1585)
  | 947 => some (.triangle 11 2481 2482)
  | 948 => some (.triangle 14 2483 2463)
  | 949 => some (.leaf 1586)
  | 950 => some (.leaf 1587)
  | 951 => some (.leaf 1588)
  | 952 => some (.triangle 11 2486 2487)
  | 953 => some (.triangle 17 2488 2452)
  | 954 => some (.leaf 1589)
  | 955 => some (.leaf 1590)
  | 956 => some (.leaf 1591)
  | 957 => some (.leaf 1592)
  | 958 => some (.leaf 1593)
  | 959 => some (.positive 0 (![2489, 2490, 2491, 2492, 2493, 2494]))
  | 960 => some (.triangle 14 2485 2495)
  | 961 => some (.leaf 1594)
  | 962 => some (.leaf 1595)
  | 963 => some (.leaf 1596)
  | 964 => some (.leaf 1597)
  | 965 => some (.positive 0 (![2489, 2489, 2497, 2498, 2499, 2500]))
  | 966 => some (.triangle 15 2496 2501)
  | 967 => some (.triangle 13 2484 2502)
  | 968 => some (.triangle 10 2251 2503)
  | 969 => some (.leaf 1598)
  | 970 => some (.leaf 1599)
  | 971 => some (.leaf 1600)
  | 972 => some (.leaf 1601)
  | 973 => some (.leaf 1602)
  | 974 => some (.leaf 1603)
  | 975 => some (.leaf 1604)
  | 976 => some (.leaf 1605)
  | 977 => some (.leaf 1606)
  | 978 => some (.leaf 1607)
  | 979 => some (.heavy (![2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2467, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511, 2512, 2513, 2514]))
  | 980 => some (.triangle 6 2432 2515)
  | 981 => some (.leaf 1608)
  | 982 => some (.leaf 1609)
  | 983 => some (.triangle 13 2517 2518)
  | 984 => some (.triangle 10 2251 2519)
  | 985 => some (.leaf 1610)
  | 986 => some (.leaf 1611)
  | 987 => some (.leaf 1612)
  | 988 => some (.leaf 1613)
  | 989 => some (.leaf 1614)
  | 990 => some (.leaf 1615)
  | 991 => some (.leaf 1616)
  | 992 => some (.leaf 1617)
  | 993 => some (.leaf 1618)
  | 994 => some (.leaf 1619)
  | 995 => some (.leaf 1620)
  | 996 => some (.leaf 1621)
  | 997 => some (.leaf 1622)
  | 998 => some (.leaf 1623)
  | 999 => some (.positive 1 (![2529, 2530, 2531, 2532, 2533, 2534]))
  | 1000 => some (.leaf 1624)
  | 1001 => some (.triangle 16 2535 2536)
  | 1002 => some (.leaf 1625)
  | 1003 => some (.leaf 1626)
  | 1004 => some (.leaf 1627)
  | 1005 => some (.leaf 1628)
  | 1006 => some (.leaf 1629)
  | 1007 => some (.positive 0 (![2537, 2538, 2539, 2540, 2541, 2542]))
  | 1008 => some (.leaf 1630)
  | 1009 => some (.triangle 12 2543 2544)
  | 1010 => some (.leaf 1631)
  | 1011 => some (.triangle 15 2545 2546)
  | 1012 => some (.triangle 11 2017 2547)
  | 1013 => some (.leaf 1632)
  | 1014 => some (.triangle 14 2548 2549)
  | 1015 => some (.leaf 1633)
  | 1016 => some (.leaf 1634)
  | 1017 => some (.triangle 14 2551 2552)
  | 1018 => some (.leaf 1635)
  | 1019 => some (.triangle 15 2553 2554)
  | 1020 => some (.triangle 13 2550 2555)
  | 1021 => some (.triangle 10 2251 2556)
  | 1022 => some (.leaf 1636)
  | 1023 => some (.leaf 1637)
  | 1024 => some (.leaf 1638)
  | 1025 => some (.leaf 1639)
  | 1026 => some (.positive 1 (![2558, 2559, 2560, 2532, 2533, 2561]))
  | 1027 => some (.triangle 16 2562 2536)
  | 1028 => some (.leaf 1640)
  | 1029 => some (.leaf 1641)
  | 1030 => some (.leaf 1642)
  | 1031 => some (.leaf 1643)
  | 1032 => some (.positive 1 (![2564, 2565, 2566, 2567, 2533, 2561]))
  | 1033 => some (.triangle 16 2568 2536)
  | 1034 => some (.positive 0 (![2563, 2538, 2539, 2540, 2541, 2569]))
  | 1035 => some (.leaf 1644)
  | 1036 => some (.triangle 12 2570 2571)
  | 1037 => some (.leaf 1645)
  | 1038 => some (.leaf 1646)
  | 1039 => some (.triangle 12 2573 2574)
  | 1040 => some (.leaf 1647)
  | 1041 => some (.triangle 16 2575 2576)
  | 1042 => some (.leaf 1648)
  | 1043 => some (.leaf 1649)
  | 1044 => some (.leaf 1650)
  | 1045 => some (.leaf 1651)
  | 1046 => some (.leaf 1652)
  | 1047 => some (.positive 0 (![2577, 2578, 2579, 2580, 2581, 2582]))
  | 1048 => some (.triangle 15 2572 2583)
  | 1049 => some (.triangle 11 2017 2584)
  | 1050 => some (.leaf 1653)
  | 1051 => some (.triangle 14 2585 2586)
  | 1052 => some (.leaf 1654)
  | 1053 => some (.triangle 12 2588 2574)
  | 1054 => some (.triangle 16 2589 2536)
  | 1055 => some (.leaf 1655)
  | 1056 => some (.leaf 1656)
  | 1057 => some (.leaf 1657)
  | 1058 => some (.leaf 1658)
  | 1059 => some (.leaf 1659)
  | 1060 => some (.positive 0 (![2590, 2591, 2592, 2593, 2594, 2595]))
  | 1061 => some (.triangle 14 2551 2596)
  | 1062 => some (.leaf 1660)
  | 1063 => some (.triangle 12 2598 2574)
  | 1064 => some (.triangle 16 2599 2536)
  | 1065 => some (.leaf 1661)
  | 1066 => some (.leaf 1662)
  | 1067 => some (.leaf 1663)
  | 1068 => some (.leaf 1664)
  | 1069 => some (.positive 0 (![2600, 2600, 2601, 2602, 2603, 2604]))
  | 1070 => some (.triangle 15 2597 2605)
  | 1071 => some (.triangle 13 2587 2606)
  | 1072 => some (.triangle 10 2251 2607)
  | 1073 => some (.leaf 1665)
  | 1074 => some (.leaf 1666)
  | 1075 => some (.leaf 1667)
  | 1076 => some (.leaf 1668)
  | 1077 => some (.leaf 1669)
  | 1078 => some (.leaf 1670)
  | 1079 => some (.leaf 1671)
  | 1080 => some (.leaf 1672)
  | 1081 => some (.leaf 1673)
  | 1082 => some (.leaf 1674)
  | 1083 => some (.heavy (![2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2557, 2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618]))
  | 1084 => some (.leaf 1675)
  | 1085 => some (.leaf 1676)
  | 1086 => some (.triangle 13 2620 2621)
  | 1087 => some (.triangle 10 2251 2622)
  | 1088 => some (.leaf 1677)
  | 1089 => some (.leaf 1678)
  | 1090 => some (.leaf 1679)
  | 1091 => some (.leaf 1680)
  | 1092 => some (.leaf 1681)
  | 1093 => some (.leaf 1682)
  | 1094 => some (.leaf 1683)
  | 1095 => some (.leaf 1684)
  | 1096 => some (.leaf 1685)
  | 1097 => some (.leaf 1686)
  | 1098 => some (.leaf 1687)
  | 1099 => some (.leaf 1688)
  | 1100 => some (.triangle 19 2634 2635)
  | 1101 => some (.leaf 1689)
  | 1102 => some (.leaf 1690)
  | 1103 => some (.positive 1 (![2631, 2632, 2633, 2636, 2637, 2638]))
  | 1104 => some (.leaf 1691)
  | 1105 => some (.triangle 18 2639 2640)
  | 1106 => some (.leaf 1692)
  | 1107 => some (.triangle 17 2641 2642)
  | 1108 => some (.triangle 16 2643 2536)
  | 1109 => some (.leaf 1693)
  | 1110 => some (.leaf 1694)
  | 1111 => some (.leaf 1695)
  | 1112 => some (.leaf 1696)
  | 1113 => some (.leaf 1697)
  | 1114 => some (.positive 0 (![2644, 2645, 2646, 2647, 2648, 2649]))
  | 1115 => some (.triangle 12 1879 2650)
  | 1116 => some (.leaf 1698)
  | 1117 => some (.triangle 15 2651 2652)
  | 1118 => some (.triangle 11 2017 2653)
  | 1119 => some (.leaf 1699)
  | 1120 => some (.triangle 14 2654 2655)
  | 1121 => some (.leaf 1700)
  | 1122 => some (.leaf 1701)
  | 1123 => some (.triangle 14 2657 2658)
  | 1124 => some (.leaf 1702)
  | 1125 => some (.triangle 15 2659 2660)
  | 1126 => some (.triangle 13 2656 2661)
  | 1127 => some (.triangle 10 2251 2662)
  | 1128 => some (.leaf 1703)
  | 1129 => some (.leaf 1704)
  | 1130 => some (.leaf 1705)
  | 1131 => some (.leaf 1706)
  | 1132 => some (.triangle 19 2634 2667)
  | 1133 => some (.leaf 1707)
  | 1134 => some (.leaf 1708)
  | 1135 => some (.positive 1 (![2664, 2665, 2666, 2668, 2669, 2670]))
  | 1136 => some (.triangle 18 2671 2170)
  | 1137 => some (.triangle 17 2672 2452)
  | 1138 => some (.triangle 16 2673 2536)
  | 1139 => some (.leaf 1709)
  | 1140 => some (.leaf 1710)
  | 1141 => some (.positive 0 (![2674, 2645, 2646, 2647, 2675, 2676]))
  | 1142 => some (.triangle 12 1879 2677)
  | 1143 => some (.leaf 1711)
  | 1144 => some (.leaf 1712)
  | 1145 => some (.leaf 1713)
  | 1146 => some (.leaf 1714)
  | 1147 => some (.leaf 1715)
  | 1148 => some (.leaf 1716)
  | 1149 => some (.leaf 1717)
  | 1150 => some (.leaf 1718)
  | 1151 => some (.positive 2 (![2681, 2682, 2683, 2684, 2685, 2686]))
  | 1152 => some (.triangle 19 192 2687)
  | 1153 => some (.leaf 1719)
  | 1154 => some (.positive 1 (![2664, 2679, 2680, 2688, 2669, 2689]))
  | 1155 => some (.triangle 18 2690 2170)
  | 1156 => some (.triangle 17 2691 2452)
  | 1157 => some (.triangle 16 2692 2536)
  | 1158 => some (.leaf 1720)
  | 1159 => some (.leaf 1721)
  | 1160 => some (.leaf 1722)
  | 1161 => some (.leaf 1723)
  | 1162 => some (.leaf 1724)
  | 1163 => some (.positive 0 (![2693, 2694, 2695, 2696, 2697, 2698]))
  | 1164 => some (.triangle 15 2678 2699)
  | 1165 => some (.triangle 11 2017 2700)
  | 1166 => some (.leaf 1725)
  | 1167 => some (.triangle 14 2701 2702)
  | 1168 => some (.leaf 1726)
  | 1169 => some (.leaf 1727)
  | 1170 => some (.leaf 1728)
  | 1171 => some (.leaf 1729)
  | 1172 => some (.leaf 1730)
  | 1173 => some (.leaf 1731)
  | 1174 => some (.leaf 1732)
  | 1175 => some (.leaf 1733)
  | 1176 => some (.leaf 1734)
  | 1177 => some (.positive 2 (![2707, 2708, 2709, 2710, 2711, 2712]))
  | 1178 => some (.triangle 19 2713 317)
  | 1179 => some (.positive 1 (![2704, 2705, 2706, 2714, 2669, 2689]))
  | 1180 => some (.triangle 18 2715 2170)
  | 1181 => some (.triangle 17 2716 2452)
  | 1182 => some (.triangle 16 2717 2536)
  | 1183 => some (.leaf 1735)
  | 1184 => some (.leaf 1736)
  | 1185 => some (.leaf 1737)
  | 1186 => some (.leaf 1738)
  | 1187 => some (.leaf 1739)
  | 1188 => some (.positive 0 (![2718, 2719, 2720, 2721, 2722, 2723]))
  | 1189 => some (.triangle 14 2657 2724)
  | 1190 => some (.leaf 1740)
  | 1191 => some (.leaf 1741)
  | 1192 => some (.leaf 1742)
  | 1193 => some (.leaf 1743)
  | 1194 => some (.leaf 1744)
  | 1195 => some (.triangle 19 2729 2730)
  | 1196 => some (.positive 1 (![2726, 2727, 2728, 2731, 2669, 2689]))
  | 1197 => some (.triangle 18 2732 2170)
  | 1198 => some (.triangle 17 2733 2452)
  | 1199 => some (.triangle 16 2734 2536)
  | 1200 => some (.leaf 1745)
  | 1201 => some (.leaf 1746)
  | 1202 => some (.triangle 19 2736 2737)
  | 1203 => some (.leaf 1747)
  | 1204 => some (.leaf 1748)
  | 1205 => some (.positive 1 (![2726, 2727, 2728, 2738, 2739, 2740]))
  | 1206 => some (.triangle 18 2741 2170)
  | 1207 => some (.triangle 17 2742 2452)
  | 1208 => some (.triangle 16 2743 2536)
  | 1209 => some (.leaf 1749)
  | 1210 => some (.leaf 1750)
  | 1211 => some (.leaf 1751)
  | 1212 => some (.leaf 1752)
  | 1213 => some (.positive 0 (![2735, 2744, 2745, 2746, 2747, 2748]))
  | 1214 => some (.triangle 15 2725 2749)
  | 1215 => some (.triangle 13 2703 2750)
  | 1216 => some (.triangle 10 2251 2751)
  | 1217 => some (.leaf 1753)
  | 1218 => some (.leaf 1754)
  | 1219 => some (.leaf 1755)
  | 1220 => some (.leaf 1756)
  | 1221 => some (.leaf 1757)
  | 1222 => some (.leaf 1758)
  | 1223 => some (.leaf 1759)
  | 1224 => some (.leaf 1760)
  | 1225 => some (.positive 1 (![2756, 2757, 2758, 2759, 2760, 2668]))
  | 1226 => some (.leaf 1761)
  | 1227 => some (.triangle 18 2761 2762)
  | 1228 => some (.leaf 1762)
  | 1229 => some (.triangle 17 2763 2764)
  | 1230 => some (.leaf 1763)
  | 1231 => some (.triangle 16 2765 2766)
  | 1232 => some (.leaf 1764)
  | 1233 => some (.leaf 1765)
  | 1234 => some (.leaf 1766)
  | 1235 => some (.leaf 1767)
  | 1236 => some (.leaf 1768)
  | 1237 => some (.leaf 1769)
  | 1238 => some (.leaf 1770)
  | 1239 => some (.triangle 19 2773 2774)
  | 1240 => some (.positive 1 (![2768, 2769, 2770, 2771, 2772, 2775]))
  | 1241 => some (.triangle 18 2776 2762)
  | 1242 => some (.triangle 17 2777 2764)
  | 1243 => some (.triangle 16 2778 2766)
  | 1244 => some (.positive 0 (![2767, 2645, 2646, 2647, 2675, 2779]))
  | 1245 => some (.triangle 12 2755 2780)
  | 1246 => some (.leaf 1771)
  | 1247 => some (.leaf 1772)
  | 1248 => some (.leaf 1773)
  | 1249 => some (.positive 1 (![2782, 2679, 2758, 2783, 2760, 2784]))
  | 1250 => some (.leaf 1774)
  | 1251 => some (.triangle 18 2785 2786)
  | 1252 => some (.triangle 17 2787 2764)
  | 1253 => some (.triangle 16 2788 2766)
  | 1254 => some (.leaf 1775)
  | 1255 => some (.positive 0 (![2789, 2694, 2695, 2696, 2697, 2790]))
  | 1256 => some (.triangle 15 2781 2791)
  | 1257 => some (.triangle 11 2754 2792)
  | 1258 => some (.triangle 14 2793 2702)
  | 1259 => some (.leaf 1776)
  | 1260 => some (.leaf 1777)
  | 1261 => some (.positive 1 (![2704, 2757, 2758, 2795, 2760, 2796]))
  | 1262 => some (.leaf 1778)
  | 1263 => some (.triangle 18 2797 2798)
  | 1264 => some (.triangle 17 2799 2452)
  | 1265 => some (.leaf 1779)
  | 1266 => some (.triangle 16 2800 2801)
  | 1267 => some (.leaf 1780)
  | 1268 => some (.positive 0 (![2802, 2719, 2720, 2721, 2722, 2803]))
  | 1269 => some (.triangle 14 2657 2804)
  | 1270 => some (.leaf 1781)
  | 1271 => some (.leaf 1782)
  | 1272 => some (.positive 1 (![2726, 2727, 2758, 2806, 2760, 2807]))
  | 1273 => some (.triangle 18 2808 2786)
  | 1274 => some (.triangle 17 2809 2452)
  | 1275 => some (.leaf 1783)
  | 1276 => some (.triangle 16 2810 2811)
  | 1277 => some (.leaf 1784)
  | 1278 => some (.leaf 1785)
  | 1279 => some (.positive 1 (![2726, 2727, 2813, 2814, 2760, 2740]))
  | 1280 => some (.triangle 18 2815 2786)
  | 1281 => some (.triangle 17 2816 2452)
  | 1282 => some (.triangle 16 2817 2766)
  | 1283 => some (.leaf 1786)
  | 1284 => some (.positive 0 (![2812, 2818, 2745, 2746, 2747, 2819]))
  | 1285 => some (.triangle 15 2805 2820)
  | 1286 => some (.triangle 13 2794 2821)
  | 1287 => some (.triangle 10 2753 2822)
  | 1288 => some (.leaf 1787)
  | 1289 => some (.leaf 1788)
  | 1290 => some (.leaf 1789)
  | 1291 => some (.leaf 1790)
  | 1292 => some (.leaf 1791)
  | 1293 => some (.leaf 1792)
  | 1294 => some (.leaf 1793)
  | 1295 => some (.leaf 1794)
  | 1296 => some (.leaf 1795)
  | 1297 => some (.leaf 1796)
  | 1298 => some (.heavy (![2623, 2624, 2625, 2626, 2627, 2628, 2629, 2630, 2663, 2752, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831, 2832, 2833]))
  | 1299 => some (.triangle 6 2619 2834)
  | 1300 => some (.leaf 1797)
  | 1301 => some (.leaf 1798)
  | 1302 => some (.triangle 13 2836 2837)
  | 1303 => some (.triangle 10 2251 2838)
  | 1304 => some (.leaf 1799)
  | 1305 => some (.leaf 1800)
  | 1306 => some (.leaf 1801)
  | 1307 => some (.leaf 1802)
  | 1308 => some (.leaf 1803)
  | 1309 => some (.leaf 1804)
  | 1310 => some (.leaf 1805)
  | 1311 => some (.leaf 1806)
  | 1312 => some (.leaf 1807)
  | 1313 => some (.leaf 1808)
  | 1314 => some (.leaf 1809)
  | 1315 => some (.leaf 1810)
  | 1316 => some (.leaf 1811)
  | 1317 => some (.leaf 1812)
  | 1318 => some (.leaf 1813)
  | 1319 => some (.leaf 1814)
  | 1320 => some (.positive 2 (![2850, 2851, 2852, 2853, 2854, 2855]))
  | 1321 => some (.triangle 19 1264 2856)
  | 1322 => some (.leaf 1815)
  | 1323 => some (.leaf 1816)
  | 1324 => some (.positive 1 (![2847, 2848, 2849, 2857, 2858, 2859]))
  | 1325 => some (.triangle 6 2846 2860)
  | 1326 => some (.leaf 1817)
  | 1327 => some (.leaf 1818)
  | 1328 => some (.leaf 1819)
  | 1329 => some (.leaf 1820)
  | 1330 => some (.leaf 1821)
  | 1331 => some (.leaf 1822)
  | 1332 => some (.positive 1 (![2862, 2863, 2864, 2865, 2866, 2867]))
  | 1333 => some (.triangle 18 2861 2868)
  | 1334 => some (.leaf 1823)
  | 1335 => some (.triangle 17 2869 2870)
  | 1336 => some (.leaf 1824)
  | 1337 => some (.triangle 16 2871 2872)
  | 1338 => some (.leaf 1825)
  | 1339 => some (.leaf 1826)
  | 1340 => some (.leaf 1827)
  | 1341 => some (.leaf 1828)
  | 1342 => some (.leaf 1829)
  | 1343 => some (.positive 0 (![2873, 2874, 2875, 2876, 2877, 2878]))
  | 1344 => some (.triangle 15 1161 2879)
  | 1345 => some (.triangle 11 2017 2880)
  | 1346 => some (.leaf 1830)
  | 1347 => some (.triangle 14 2881 2882)
  | 1348 => some (.leaf 1831)
  | 1349 => some (.triangle 13 2883 2884)
  | 1350 => some (.triangle 10 2251 2885)
  | 1351 => some (.leaf 1832)
  | 1352 => some (.leaf 1833)
  | 1353 => some (.leaf 1834)
  | 1354 => some (.leaf 1835)
  | 1355 => some (.positive 1 (![2888, 2863, 2864, 2865, 2889, 2890]))
  | 1356 => some (.triangle 18 2887 2891)
  | 1357 => some (.triangle 17 2892 2452)
  | 1358 => some (.leaf 1836)
  | 1359 => some (.triangle 16 2893 2894)
  | 1360 => some (.leaf 1837)
  | 1361 => some (.leaf 1838)
  | 1362 => some (.leaf 1839)
  | 1363 => some (.positive 0 (![2895, 2874, 2875, 2896, 2897, 2898]))
  | 1364 => some (.triangle 15 1161 2899)
  | 1365 => some (.triangle 11 2017 2900)
  | 1366 => some (.leaf 1840)
  | 1367 => some (.triangle 14 2901 2902)
  | 1368 => some (.leaf 1841)
  | 1369 => some (.triangle 13 2903 2904)
  | 1370 => some (.triangle 10 2251 2905)
  | 1371 => some (.leaf 1842)
  | 1372 => some (.leaf 1843)
  | 1373 => some (.leaf 1844)
  | 1374 => some (.leaf 1845)
  | 1375 => some (.leaf 1846)
  | 1376 => some (.triangle 18 2910 2911)
  | 1377 => some (.leaf 1847)
  | 1378 => some (.triangle 17 2912 2913)
  | 1379 => some (.leaf 1848)
  | 1380 => some (.triangle 16 2914 2915)
  | 1381 => some (.leaf 1849)
  | 1382 => some (.leaf 1850)
  | 1383 => some (.triangle 18 2918 2911)
  | 1384 => some (.triangle 17 2919 2913)
  | 1385 => some (.triangle 16 2920 2915)
  | 1386 => some (.positive 0 (![2916, 2874, 2875, 2896, 2917, 2921]))
  | 1387 => some (.triangle 15 1161 2922)
  | 1388 => some (.triangle 11 2909 2923)
  | 1389 => some (.triangle 14 2924 2902)
  | 1390 => some (.leaf 1851)
  | 1391 => some (.leaf 1852)
  | 1392 => some (.triangle 18 2926 2927)
  | 1393 => some (.triangle 17 2928 2452)
  | 1394 => some (.leaf 1853)
  | 1395 => some (.triangle 16 2929 2930)
  | 1396 => some (.leaf 1854)
  | 1397 => some (.leaf 1855)
  | 1398 => some (.triangle 18 2932 2933)
  | 1399 => some (.triangle 17 2934 2452)
  | 1400 => some (.triangle 16 2935 2915)
  | 1401 => some (.leaf 1856)
  | 1402 => some (.leaf 1857)
  | 1403 => some (.leaf 1858)
  | 1404 => some (.leaf 1859)
  | 1405 => some (.positive 0 (![2931, 2936, 2937, 2938, 2939, 2940]))
  | 1406 => some (.triangle 15 1161 2941)
  | 1407 => some (.triangle 13 2925 2942)
  | 1408 => some (.triangle 10 2908 2943)
  | 1409 => some (.leaf 1860)
  | 1410 => some (.leaf 1861)
  | 1411 => some (.leaf 1862)
  | 1412 => some (.leaf 1863)
  | 1413 => some (.leaf 1864)
  | 1414 => some (.leaf 1865)
  | 1415 => some (.leaf 1866)
  | 1416 => some (.leaf 1867)
  | 1417 => some (.leaf 1868)
  | 1418 => some (.leaf 1869)
  | 1419 => some (.heavy (![2839, 2840, 2841, 2842, 2843, 2844, 2845, 2886, 2906, 2907, 2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954]))
  | 1420 => some (.triangle 9 2835 2955)
  | 1421 => some (.triangle 5 2516 2956)
  | 1422 => some (.leaf 1870)
  | 1423 => some (.leaf 1871)
  | 1424 => some (.triangle 13 2958 2959)
  | 1425 => some (.triangle 10 2251 2960)
  | 1426 => some (.leaf 1872)
  | 1427 => some (.leaf 1873)
  | 1428 => some (.leaf 1874)
  | 1429 => some (.leaf 1875)
  | 1430 => some (.leaf 1876)
  | 1431 => some (.leaf 1877)
  | 1432 => some (.leaf 1878)
  | 1433 => some (.leaf 1879)
  | 1434 => some (.leaf 1880)
  | 1435 => some (.leaf 1881)
  | 1436 => some (.triangle 17 2970 2971)
  | 1437 => some (.leaf 1882)
  | 1438 => some (.leaf 1883)
  | 1439 => some (.leaf 1884)
  | 1440 => some (.leaf 1885)
  | 1441 => some (.leaf 1886)
  | 1442 => some (.positive 0 (![2972, 2973, 2974, 2975, 2976, 2977]))
  | 1443 => some (.leaf 1887)
  | 1444 => some (.triangle 11 2978 2979)
  | 1445 => some (.triangle 14 1345 2980)
  | 1446 => some (.leaf 1888)
  | 1447 => some (.triangle 13 2981 2982)
  | 1448 => some (.triangle 10 2251 2983)
  | 1449 => some (.leaf 1889)
  | 1450 => some (.leaf 1890)
  | 1451 => some (.triangle 17 2985 2986)
  | 1452 => some (.leaf 1891)
  | 1453 => some (.leaf 1892)
  | 1454 => some (.triangle 17 2988 2989)
  | 1455 => some (.positive 0 (![2987, 2973, 2974, 2975, 2976, 2990]))
  | 1456 => some (.leaf 1893)
  | 1457 => some (.triangle 11 2991 2992)
  | 1458 => some (.triangle 14 1345 2993)
  | 1459 => some (.triangle 13 2994 1399)
  | 1460 => some (.triangle 10 2251 2995)
  | 1461 => some (.leaf 1894)
  | 1462 => some (.leaf 1895)
  | 1463 => some (.leaf 1896)
  | 1464 => some (.leaf 1897)
  | 1465 => some (.leaf 1898)
  | 1466 => some (.leaf 1899)
  | 1467 => some (.leaf 1900)
  | 1468 => some (.leaf 1901)
  | 1469 => some (.leaf 1902)
  | 1470 => some (.leaf 1903)
  | 1471 => some (.heavy (![2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2984, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006]))
  | 1472 => some (.leaf 1904)
  | 1473 => some (.leaf 1905)
  | 1474 => some (.triangle 13 3008 3009)
  | 1475 => some (.triangle 10 2251 3010)
  | 1476 => some (.leaf 1906)
  | 1477 => some (.leaf 1907)
  | 1478 => some (.leaf 1908)
  | 1479 => some (.leaf 1909)
  | 1480 => some (.leaf 1910)
  | 1481 => some (.leaf 1911)
  | 1482 => some (.leaf 1912)
  | 1483 => some (.leaf 1913)
  | 1484 => some (.leaf 1914)
  | 1485 => some (.leaf 1915)
  | 1486 => some (.leaf 1916)
  | 1487 => some (.leaf 1917)
  | 1488 => some (.leaf 1918)
  | 1489 => some (.triangle 17 3023 3024)
  | 1490 => some (.leaf 1919)
  | 1491 => some (.triangle 16 3025 3026)
  | 1492 => some (.leaf 1920)
  | 1493 => some (.leaf 1921)
  | 1494 => some (.leaf 1922)
  | 1495 => some (.leaf 1923)
  | 1496 => some (.leaf 1924)
  | 1497 => some (.leaf 1925)
  | 1498 => some (.triangle 17 3032 3033)
  | 1499 => some (.triangle 16 3034 3026)
  | 1500 => some (.positive 0 (![3027, 3028, 3029, 3030, 3031, 3035]))
  | 1501 => some (.triangle 11 3022 3036)
  | 1502 => some (.triangle 14 1345 3037)
  | 1503 => some (.triangle 13 3038 1399)
  | 1504 => some (.triangle 10 3021 3039)
  | 1505 => some (.leaf 1926)
  | 1506 => some (.leaf 1927)
  | 1507 => some (.leaf 1928)
  | 1508 => some (.leaf 1929)
  | 1509 => some (.leaf 1930)
  | 1510 => some (.leaf 1931)
  | 1511 => some (.leaf 1932)
  | 1512 => some (.leaf 1933)
  | 1513 => some (.leaf 1934)
  | 1514 => some (.leaf 1935)
  | 1515 => some (.heavy (![3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050]))
  | 1516 => some (.triangle 5 3007 3051)
  | 1517 => some (.triangle 8 2957 3052)
  | 1518 => some (.leaf 1936)
  | 1519 => some (.leaf 1937)
  | 1520 => some (.triangle 15 3054 3055)
  | 1521 => some (.triangle 13 1425 3056)
  | 1522 => some (.triangle 10 2251 3057)
  | 1523 => some (.leaf 1938)
  | 1524 => some (.leaf 1939)
  | 1525 => some (.leaf 1940)
  | 1526 => some (.leaf 1941)
  | 1527 => some (.leaf 1942)
  | 1528 => some (.leaf 1943)
  | 1529 => some (.leaf 1944)
  | 1530 => some (.leaf 1945)
  | 1531 => some (.leaf 1946)
  | 1532 => some (.leaf 1947)
  | 1533 => some (.triangle 16 3067 3068)
  | 1534 => some (.leaf 1948)
  | 1535 => some (.leaf 1949)
  | _ => none

end Jsp404.SevenLowerBranchShard01
