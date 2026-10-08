import Jsp000404.SevenLowerReplay

/-! SOURCE_ONLY literal certificate data; no kernel PASS is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerBranchShard00
open SevenLowerReplay
def cycle0000 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0001 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (4), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 3, 4, 5]), .gapLower 1 5 (![0, 2, 3, 4, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 2 1]

def cycle0006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .gapLower 1 1 (![0, 2, 3, 4, 5])]

def cycle0007 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .gapLower 1 2 (![0, 2, 3, 4, 5]), .gapLower 1 1 (![0, 2, 3, 4, 5])]

def cycle0008 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![0, 2, 3, 4, 5]), .triangle 0 0]

def cycle0009 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 3 (![0, 2, 3, 4, 5]), .triangle 10 1, .triangle 0 0]

def cycle0010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 3, 4, 5]), .gapLower 2 5 (![0, 1, 3, 4, 5]), .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 5 1]

def cycle0011 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 2, .triangle 12 2, .gapLower 1 4 (![0, 2, 3, 4, 5]), .triangle 13 1, .triangle 10 1, .gapLower 2 1 (![0, 1, 3, 4, 5]), .triangle 0 1]

def cycle0012 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![0, 1, 3, 4, 5]), .triangle 0 0]

def cycle0013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 3 (![0, 1, 3, 4, 5]), .triangle 10 0, .triangle 0 0]

def cycle0014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 2, .gapLower 2 4 (![0, 1, 3, 4, 5]), .triangle 11 0, .triangle 0 0]

def cycle0015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 2, .distance 2 5, .distance 0 5, .distance 0 4]
    constant := ![(-1), (0), (0), (2), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 3, 4, 5]), .triangle 6 2, .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 4]
    constant := ![(0), (3), (0), (-1), (0), (0), (-3)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 4 0 (![0, 1, 5, 2, 3]), .corridorUpper 3 4, .triangle 16 2, .triangle 18 0, .gapLower 5 2 (![0, 1, 4, 2, 3]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0017 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 14 2, .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0018 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 16 0, .triangle 13 0, .triangle 10 1, .triangle 0 0]

def cycle0019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 4]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .gapLower 5 2 (![0, 1, 3, 2, 4]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0020 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (0), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 15 2, .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4]
    constant := ![(-1), (0), (0), (2), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 3, 4, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0022 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0023 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0024 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (4), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 4, 3, 5]), .gapLower 1 5 (![0, 2, 4, 3, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 2 1]

def cycle0025 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 3, .distance 1 3]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 13 0, .triangle 16 0, .triangle 10 2]

def cycle0026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .gapLower 1 1 (![0, 2, 4, 3, 5])]

def cycle0027 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![(-1), (0), (0), (3), (0), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 4, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0028 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![0, 2, 4, 3, 5]), .triangle 0 0]

def cycle0029 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 3 (![0, 2, 4, 3, 5]), .triangle 11 1, .triangle 0 0]

def cycle0030 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![0, 2, 4, 3, 5]), .triangle 13 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4]
    constant := ![(-1), (0), (0), (2), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 4, 3, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0032 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0033 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-1), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0034 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0035 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (4), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 2, 3, 5]), .gapLower 1 5 (![0, 4, 2, 3, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 2 1]

def cycle0036 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 10 0, .triangle 11 2, .gapLower 1 1 (![0, 4, 2, 3, 5])]

def cycle0037 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .triangle 14 2, .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0038 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![0, 4, 2, 3, 5]), .triangle 11 1, .triangle 5 0, .triangle 0 1]

def cycle0039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 3 (![0, 4, 2, 3, 5]), .triangle 0 0]

def cycle0040 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![0, 4, 2, 3, 5]), .triangle 10 1, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0041 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4]
    constant := ![(-1), (0), (0), (2), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 2, 3, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0042 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-1), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0043 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (4), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 2, 4, 5]), .gapLower 1 5 (![0, 3, 2, 4, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 2 1]

def cycle0044 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .gapLower 1 2 (![0, 3, 2, 4, 5]), .gapLower 1 1 (![0, 3, 2, 4, 5])]

def cycle0045 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 0, .triangle 15 2, .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0046 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 2 (![0, 3, 2, 4, 5]), .triangle 10 1, .triangle 4 0, .triangle 0 1]

def cycle0047 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 3 (![0, 3, 2, 4, 5]), .triangle 0 0]

def cycle0048 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![0, 3, 2, 4, 5]), .triangle 11 1, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0049 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4]
    constant := ![(-1), (0), (0), (2), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 2, 4, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0050 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0051 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (4), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 2, 5]), .gapLower 1 5 (![0, 3, 4, 2, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 2 1]

def cycle0052 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 1, 5]), .gapLower 2 5 (![0, 3, 4, 1, 5]), .triangle 12 2, .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 5 1]

def cycle0053 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 11 0, .triangle 16 1, .gapLower 2 1 (![0, 3, 4, 1, 5]), .triangle 0 1]

def cycle0054 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 11 0, .gapLower 2 2 (![0, 3, 4, 1, 5]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0055 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .gapLower 2 3 (![0, 3, 4, 1, 5]), .triangle 16 1, .triangle 4 0, .triangle 0 1]

def cycle0056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .gapLower 2 4 (![0, 3, 4, 1, 5]), .triangle 11 2, .triangle 13 1, .gapLower 1 1 (![0, 3, 4, 2, 5])]

def cycle0057 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 2, .distance 2 5, .distance 0 5, .distance 0 4]
    constant := ![(-1), (0), (0), (2), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 4, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 4, 1, 5]), .triangle 6 2, .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0058 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 2 3, .distance 3 4, .distance 1 3]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 10 1, .triangle 16 0, .triangle 13 0]

def cycle0059 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![0, 3, 4, 2, 5]), .triangle 10 1, .triangle 4 0, .triangle 0 1]

def cycle0060 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .gapLower 1 3 (![0, 3, 4, 2, 5]), .triangle 13 1, .triangle 10 1, .triangle 4 0, .triangle 0 1]

def cycle0061 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![0, 3, 4, 2, 5]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0062 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4]
    constant := ![(-1), (0), (0), (2), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 4, 2, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0063 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0064 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0065 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![(-2), (4), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 3, 2, 5]), .gapLower 1 5 (![0, 4, 3, 2, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 2 1]

def cycle0066 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 4 0, .triangle 0 1]

def cycle0067 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 10 0, .triangle 16 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0068 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 2 (![0, 4, 3, 2, 5]), .triangle 13 1, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0069 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .gapLower 1 3 (![0, 4, 3, 2, 5]), .triangle 1 0]

def cycle0070 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![0, 4, 3, 2, 5]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0071 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .theta 0, .zero, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4]
    constant := ![(-1), (0), (0), (2), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 3, 2, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0072 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0073 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-1), (0), (-3), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0074 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 3, 4, 5]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0075 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 3, 4, 5]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 6 1]

def cycle0076 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 3, 4, 5]), .triangle 12 2, .gapLower 1 4 (![0, 2, 3, 4, 5]), .triangle 2 0]

def cycle0077 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (0), (-2), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 18 0, .triangle 15 2, .gapLower 1 4 (![0, 2, 3, 4, 5]), .triangle 13 1, .triangle 10 1, .triangle 0 0]

def cycle0078 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 14 2, .gapLower 1 4 (![0, 2, 3, 4, 5]), .triangle 2 0]

def cycle0079 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .triangle 14 2, .gapLower 1 4 (![0, 2, 3, 4, 5]), .triangle 13 1, .triangle 10 1, .triangle 0 0]

def cycle0080 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (0), (-2), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 15 2, .gapLower 1 4 (![0, 2, 3, 4, 5]), .triangle 13 1, .triangle 10 1, .triangle 0 0]

def cycle0081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true] }
  origin := ![.gapLower 2 0 (![0, 1, 3, 4, 5]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 9 1, .triangle 7 1, .triangle 4 1]

def cycle0082 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .gapLower 2 1 (![0, 1, 3, 4, 5]), .triangle 0 1]

def cycle0083 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 16 0, .triangle 10 0, .triangle 0 0]

def cycle0084 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 18 0, .gapLower 2 3 (![0, 1, 3, 4, 5]), .triangle 10 0, .triangle 0 0]

def cycle0085 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true] }
  origin := ![.gapLower 2 0 (![0, 1, 3, 5, 4]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 9 1, .triangle 7 1, .triangle 4 1]

def cycle0086 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .gapLower 2 1 (![0, 1, 3, 5, 4])]

def cycle0087 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 2 (![0, 1, 3, 5, 4]), .triangle 0 0]

def cycle0088 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 18 2, .gapLower 2 3 (![0, 1, 3, 5, 4]), .triangle 10 0, .triangle 0 0]

def cycle0089 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![0, 1, 3, 5, 4]), .triangle 12 0, .triangle 0 0]

def cycle0090 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 3, 5, 4]), .triangle 18 0, .triangle 15 0, .gapLower 1 3 (![0, 2, 3, 4, 5]), .triangle 10 1, .triangle 0 0]

def cycle0091 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 14 0, .gapLower 1 2 (![0, 2, 3, 4, 5]), .triangle 0 0]

def cycle0092 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true] }
  origin := ![.gapLower 2 0 (![0, 1, 4, 5, 3]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 9 1, .triangle 7 1, .triangle 4 1]

def cycle0093 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .triangle 10 1, .gapLower 2 1 (![0, 1, 4, 5, 3]), .triangle 0 1]

def cycle0094 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 2 (![0, 1, 4, 5, 3]), .triangle 0 0]

def cycle0095 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![0, 1, 4, 5, 3]), .triangle 11 0, .triangle 0 0]

def cycle0096 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 4, 5, 3]), .triangle 12 0, .triangle 0 0]

def cycle0097 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 4, 5, 3]), .triangle 16 0, .triangle 13 0, .gapLower 1 2 (![0, 2, 3, 4, 5]), .triangle 0 0]

def cycle0098 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 9 1, .triangle 7 1, .triangle 4 1]

def cycle0099 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (0), (-1), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 15 0, .gapLower 1 3 (![0, 2, 3, 4, 5]), .triangle 10 1, .gapLower 2 1 (![0, 1, 5, 4, 3])]

def cycle0100 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 19 0, .triangle 13 0, .gapLower 1 2 (![0, 2, 3, 4, 5]), .triangle 0 0]

def cycle0101 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 19 0, .triangle 15 0, .gapLower 1 3 (![0, 2, 3, 4, 5]), .triangle 10 1, .triangle 0 0]

def cycle0102 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![0, 1, 5, 4, 3]), .triangle 12 0, .triangle 0 0]

def cycle0103 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 18 0, .triangle 15 0, .gapLower 1 3 (![0, 2, 3, 4, 5]), .triangle 1 0]

def cycle0104 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-1), (-1), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 15 0, .gapLower 1 3 (![0, 2, 3, 4, 5]), .gapLower 1 2 (![0, 2, 3, 4, 5]), .triangle 0 0]

def cycle0105 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 3, 5, 4]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0106 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .gapLower 1 1 (![0, 2, 3, 5, 4])]

def cycle0107 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .gapLower 1 2 (![0, 2, 3, 5, 4]), .gapLower 1 1 (![0, 2, 3, 5, 4])]

def cycle0108 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![0, 2, 3, 5, 4]), .triangle 0 0]

def cycle0109 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 2 4, .distance 1 4]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 15 0, .triangle 18 0, .triangle 11 2]

def cycle0110 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 3, 5, 4]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 6 1]

def cycle0111 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 11 2, .triangle 15 2, .gapLower 1 3 (![0, 2, 3, 5, 4]), .triangle 10 1, .gapLower 2 1 (![0, 1, 3, 5, 4]), .triangle 0 1]

def cycle0112 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![0, 1, 3, 5, 4]), .triangle 12 2, .gapLower 1 3 (![0, 2, 3, 5, 4]), .triangle 1 0]

def cycle0113 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 3, 5, 4]), .triangle 11 2, .triangle 15 2, .gapLower 1 3 (![0, 2, 3, 5, 4]), .triangle 1 0]

def cycle0114 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 14 2, .gapLower 1 3 (![0, 2, 3, 5, 4]), .triangle 1 0]

def cycle0115 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (-2), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 2, .triangle 15 2, .gapLower 1 3 (![0, 2, 3, 5, 4]), .triangle 10 1, .triangle 0 0]

def cycle0116 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true, true] }
  origin := ![.gapLower 2 0 (![0, 1, 3, 5, 4]), .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 11 2, .gapLower 1 4 (![0, 2, 3, 5, 4]), .gapLower 5 2 (![0, 4, 1, 2, 3]), .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0117 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .triangle 11 2, .gapLower 1 4 (![0, 2, 3, 5, 4]), .triangle 14 1, .triangle 10 1, .gapLower 2 1 (![0, 1, 3, 5, 4]), .triangle 0 1]

def cycle0118 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 3, 5, 4]), .gapLower 4 3 (![0, 5, 1, 2, 3]), .gapLower 1 4 (![0, 2, 3, 5, 4]), .triangle 3 0]

def cycle0119 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .triangle 14 0, .gapLower 1 2 (![0, 2, 3, 5, 4]), .triangle 0 0]

def cycle0120 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 2, .gapLower 1 4 (![0, 2, 3, 5, 4]), .triangle 14 1, .triangle 10 1, .triangle 0 0]

def cycle0121 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 3, 5, 4]), .thetaOrder 1, .gapLower 1 5 (![0, 2, 3, 5, 4]), .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 4 1]

def cycle0122 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .gapLower 2 1 (![0, 1, 3, 5, 4]), .triangle 0 1]

def cycle0123 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 3 4, .distance 1 4]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 15 0, .triangle 19 0, .triangle 13 2]

def cycle0124 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-2), (0), (2), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 1, 2, 5, 4]), .thetaOrder 2, .gapLower 2 5 (![0, 1, 3, 5, 4]), .triangle 11 2, .triangle 15 0, .gapLower 4 1 (![0, 5, 1, 2, 3]), .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0125 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .distance 0 5, .theta 5, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-1), (1), (-2), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorLower 0 3, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 5 0 (![0, 4, 1, 2, 3]), .thetaOrder 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 2, .gapLower 3 1 (![0, 1, 2, 5, 4])]

def cycle0126 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .theta 0, .zero, .theta 1, .distance 1 4, .distance 4 5, .distance 0 5]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 5, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 3, 5, 4]), .triangle 15 0, .gapLower 5 1 (![0, 4, 1, 2, 3])]

def cycle0127 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 3, 5, 4]), .triangle 15 2, .gapLower 5 2 (![0, 4, 1, 2, 3]), .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0128 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 3, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 3, 5, 4]), .triangle 18 2, .gapLower 5 3 (![0, 4, 1, 2, 3]), .triangle 14 1, .gapLower 3 1 (![0, 1, 2, 5, 4])]

def cycle0129 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 5 4 (![0, 4, 1, 2, 3]), .triangle 12 2, .triangle 14 1, .gapLower 3 1 (![0, 1, 2, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0130 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 4, 1, 2, 3]), .triangle 14 0, .gapLower 3 1 (![0, 1, 2, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0131 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 3 2 (![0, 1, 2, 5, 4]), .triangle 10 1, .triangle 0 0]

def cycle0132 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 3 3 (![0, 1, 2, 5, 4]), .triangle 10 0, .triangle 0 0]

def cycle0133 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![0, 1, 2, 5, 4]), .triangle 17 0, .triangle 10 0, .triangle 0 0]

def cycle0134 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 1, 2, 5, 4]), .triangle 16 0, .triangle 10 0, .triangle 0 0]

def cycle0135 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaOrder 1, .gapLower 1 5 (![0, 2, 3, 5, 4]), .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 4 1]

def cycle0136 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .triangle 10 1, .gapLower 2 1 (![0, 1, 5, 4, 3]), .triangle 0 1]

def cycle0137 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 1, 5, 4, 2]), .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![0, 2, 3, 5, 4]), .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0138 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-1), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 19 2, .triangle 14 0, .gapLower 3 1 (![0, 1, 5, 4, 2]), .triangle 4 1, .triangle 0 1]

def cycle0139 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 19 2, .gapLower 3 2 (![0, 1, 5, 4, 2]), .triangle 10 1, .triangle 0 0]

def cycle0140 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 3 5, .theta 3, .distance 2 3]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 16 0, .gapLower 3 3 (![0, 1, 5, 4, 2]), .corridorLower 3 5, .corridorUpper 2 3]

def cycle0141 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(0), (3), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 1, 5, 4, 2]), .corridorUpper 2 3, .gapLower 3 4 (![0, 1, 5, 4, 2]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0142 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 1, 5, 4, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![0, 1, 5, 4, 3]), .triangle 0 0]

def cycle0143 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0144 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 16 0, .triangle 13 0, .gapLower 1 2 (![0, 2, 3, 5, 4]), .triangle 0 0]

def cycle0145 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 3, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0146 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .gapLower 1 1 (![0, 2, 5, 3, 4])]

def cycle0147 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .triangle 14 2, .gapLower 1 2 (![0, 2, 5, 3, 4]), .gapLower 1 1 (![0, 2, 5, 3, 4])]

def cycle0148 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 2, .gapLower 1 2 (![0, 2, 5, 3, 4]), .triangle 0 0]

def cycle0149 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 3 (![0, 2, 5, 3, 4]), .triangle 12 1, .triangle 0 0]

def cycle0150 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 2, 5, 3, 4]), .triangle 14 0, .triangle 8 0, .triangle 4 1, .triangle 0 1]

def cycle0151 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .distance 1 3]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 14 0, .triangle 17 0, .triangle 10 2]

def cycle0152 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 3, 4]), .thetaOrder 1, .gapLower 1 5 (![0, 2, 5, 3, 4]), .triangle 13 1, .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0153 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 2, .triangle 12 0, .gapLower 2 1 (![0, 1, 5, 3, 4]), .triangle 0 1]

def cycle0154 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 2, .gapLower 2 2 (![0, 1, 5, 3, 4]), .triangle 0 0]

def cycle0155 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .gapLower 2 3 (![0, 1, 5, 3, 4]), .triangle 12 0, .triangle 0 0]

def cycle0156 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![0, 1, 5, 3, 4]), .triangle 10 2, .triangle 14 0, .triangle 8 0, .triangle 4 1, .triangle 0 1]

def cycle0157 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3]
    constant := ![(-2), (0), (2), (0), (0), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 3 0 (![0, 5, 1, 2, 4]), .thetaOrder 2, .gapLower 2 5 (![0, 1, 5, 3, 4]), .triangle 11 2, .triangle 13 1, .triangle 14 0, .triangle 8 0]

def cycle0158 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .gapLower 3 1 (![0, 5, 1, 2, 4])]

def cycle0159 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 3 2 (![0, 5, 1, 2, 4]), .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0160 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (2), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 3, 4]), .gapLower 2 5 (![0, 1, 5, 3, 4]), .triangle 16 1, .gapLower 3 3 (![0, 5, 1, 2, 4]), .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0161 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![0, 5, 1, 2, 4]), .triangle 10 2, .triangle 14 0, .triangle 8 0, .triangle 4 1, .triangle 0 1]

def cycle0162 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (0), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 5, 1, 2, 4]), .triangle 16 0, .triangle 17 2, .triangle 12 0, .triangle 0 0]

def cycle0163 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0164 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 4, 3, 5]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0165 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 15 0, .gapLower 1 2 (![0, 2, 4, 3, 5]), .gapLower 1 1 (![0, 2, 4, 3, 5])]

def cycle0166 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 4, 3, 5]), .thetaOrder 1, .gapLower 1 5 (![0, 2, 4, 3, 5]), .triangle 14 1, .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0167 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 10 0, .gapLower 2 1 (![0, 1, 4, 3, 5]), .triangle 0 1]

def cycle0168 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .gapLower 2 2 (![0, 1, 4, 3, 5]), .triangle 0 0]

def cycle0169 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .gapLower 2 3 (![0, 1, 4, 3, 5]), .triangle 11 0, .triangle 0 0]

def cycle0170 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 5, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 2, .gapLower 2 4 (![0, 1, 4, 3, 5]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0171 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![(-2), (0), (2), (0), (0), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 3 0 (![0, 4, 1, 2, 5]), .thetaOrder 2, .gapLower 2 5 (![0, 1, 4, 3, 5]), .triangle 12 2, .triangle 14 1, .triangle 13 0, .triangle 7 0]

def cycle0172 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 0, .gapLower 3 1 (![0, 4, 1, 2, 5]), .triangle 4 1, .triangle 0 1]

def cycle0173 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 3 2 (![0, 4, 1, 2, 5]), .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0174 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 5, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (2), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 4, 3, 5]), .gapLower 2 5 (![0, 1, 4, 3, 5]), .triangle 17 1, .gapLower 3 3 (![0, 4, 1, 2, 5]), .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0175 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .gapLower 3 4 (![0, 4, 1, 2, 5]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0176 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 3 5, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 4, 1, 2, 5]), .triangle 17 0, .triangle 10 2, .triangle 13 0, .triangle 7 0, .triangle 4 1]

def cycle0177 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .triangle 14 0, .triangle 13 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0178 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaOrder 1, .gapLower 1 5 (![0, 2, 4, 3, 5]), .triangle 14 1, .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0179 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 15 0, .triangle 11 1, .gapLower 2 1 (![0, 1, 5, 4, 3]), .triangle 0 1]

def cycle0180 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 16 2, .triangle 18 0, .triangle 15 0, .gapLower 1 2 (![0, 2, 4, 3, 5]), .triangle 0 0]

def cycle0181 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4]
    constant := ![(0), (-1), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 4 2 (![0, 3, 1, 5, 2]), .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 18 0, .triangle 15 0]

def cycle0182 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 15 0, .gapLower 1 2 (![0, 2, 4, 3, 5]), .triangle 0 0]

def cycle0183 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 4, 5, 3]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0184 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .gapLower 1 1 (![0, 2, 4, 5, 3])]

def cycle0185 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 15 0, .gapLower 1 2 (![0, 2, 4, 5, 3]), .gapLower 1 1 (![0, 2, 4, 5, 3])]

def cycle0186 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![0, 2, 4, 5, 3]), .triangle 0 0]

def cycle0187 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 4, 5, 3]), .gapLower 2 5 (![0, 1, 4, 5, 3]), .triangle 10 2, .triangle 14 2, .gapLower 1 3 (![0, 2, 4, 5, 3]), .triangle 13 1, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0188 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 2, .gapLower 1 3 (![0, 2, 4, 5, 3]), .triangle 11 1, .gapLower 2 1 (![0, 1, 4, 5, 3]), .triangle 0 1]

def cycle0189 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 2 5, .distance 1 5, .distance 1 4]
    constant := ![(0), (-1), (3), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 4 2 (![0, 3, 1, 2, 5]), .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 4, 5, 3]), .gapLower 5 3 (![0, 3, 1, 2, 4]), .gapLower 1 3 (![0, 2, 4, 5, 3])]

def cycle0190 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (2), (0), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 4, 5, 3]), .gapLower 2 5 (![0, 1, 4, 5, 3]), .triangle 10 2, .triangle 14 2, .gapLower 1 3 (![0, 2, 4, 5, 3]), .triangle 13 1, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0191 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 4]
    constant := ![(0), (-1), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 4 2 (![0, 3, 1, 5, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 15 2, .gapLower 1 3 (![0, 2, 4, 5, 3])]

def cycle0192 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 4, 5, 3]), .gapLower 2 5 (![0, 1, 4, 5, 3]), .triangle 10 2, .gapLower 1 4 (![0, 2, 4, 5, 3]), .triangle 14 1, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0193 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 4, 5, 3]), .triangle 15 1, .triangle 11 1, .gapLower 2 1 (![0, 1, 4, 5, 3]), .triangle 0 1]

def cycle0194 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (2), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 4, 5, 3]), .gapLower 2 5 (![0, 1, 4, 5, 3]), .triangle 10 2, .gapLower 1 4 (![0, 2, 4, 5, 3]), .triangle 14 1, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0195 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 2, .gapLower 1 4 (![0, 2, 4, 5, 3]), .triangle 14 1, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0196 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 4, 5, 3]), .triangle 15 1, .triangle 11 1, .gapLower 2 1 (![0, 1, 5, 4, 3]), .triangle 0 1]

def cycle0197 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![(-2), (4), (0), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 4, 5, 1, 2]), .gapLower 3 5 (![0, 4, 5, 1, 2]), .triangle 16 2, .triangle 18 0, .triangle 19 0, .triangle 7 0]

def cycle0198 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![(0), (3), (0), (-1), (-1), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 4, 5, 1, 2]), .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 19 0, .gapLower 3 1 (![0, 4, 5, 1, 2])]

def cycle0199 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![(-2), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4 (![0, 2, 4, 5, 3]), .gapLower 5 2 (![0, 3, 1, 4, 2]), .gapLower 3 2 (![0, 4, 5, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2]

def cycle0200 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 5, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 5]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 5 0 (![0, 3, 1, 4, 2]), .thetaOrder 4, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![0, 4, 5, 1, 2]), .gapLower 5 1 (![0, 3, 1, 4, 2])]

def cycle0201 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![(0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 3 0 (![0, 4, 5, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 4, 5, 3]), .triangle 14 1, .gapLower 5 1 (![0, 3, 1, 4, 2]), .triangle 8 1]

def cycle0202 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (4), (0), (-2), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 2, .gapLower 1 4 (![0, 2, 4, 5, 3]), .gapLower 5 2 (![0, 3, 1, 4, 2]), .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0203 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .gapLower 5 3 (![0, 3, 1, 4, 2]), .triangle 3 0]

def cycle0204 : Cycle where
  length := 6
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![(0), (0), (-2), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 16 2, .triangle 18 2, .gapLower 5 4 (![0, 3, 1, 4, 2]), .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3]

def cycle0205 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 3, 1, 4, 2]), .gapLower 2 2 (![0, 1, 5, 4, 3]), .triangle 0 0]

def cycle0206 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![(-2), (0), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 4 (![0, 2, 4, 5, 3]), .gapLower 5 2 (![0, 3, 1, 4, 2]), .corridorLower 3 5, .corridorUpper 2 3, .gapLower 3 4 (![0, 4, 5, 1, 2])]

def cycle0207 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 4, 5, 1, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![0, 1, 5, 4, 3]), .triangle 0 0]

def cycle0208 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 3 4, .distance 4 5, .distance 1 4]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 13 1, .triangle 19 0, .triangle 15 0]

def cycle0209 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (2), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 2, .gapLower 1 4 (![0, 2, 4, 5, 3]), .triangle 14 1, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0210 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 4, 5, 3]), .thetaOrder 1, .gapLower 1 5 (![0, 2, 4, 5, 3]), .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0211 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .gapLower 2 1 (![0, 1, 4, 5, 3]), .triangle 0 1]

def cycle0212 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3]
    constant := ![(-2), (0), (2), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 3 0 (![0, 4, 5, 1, 2]), .thetaOrder 2, .gapLower 2 5 (![0, 1, 4, 5, 3]), .triangle 10 2, .triangle 14 0, .triangle 19 1, .gapLower 3 1 (![0, 4, 5, 1, 2])]

def cycle0213 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 4, 5, 3]), .triangle 14 0, .triangle 19 1, .gapLower 3 1 (![0, 4, 5, 1, 2])]

def cycle0214 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (2), (0), (-1), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 4, 5, 3]), .gapLower 2 5 (![0, 1, 4, 5, 3]), .gapLower 3 4 (![0, 4, 5, 1, 2]), .triangle 14 0, .gapLower 3 2 (![0, 4, 5, 1, 2]), .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0215 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (2), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 4, 5, 3]), .gapLower 2 5 (![0, 1, 4, 5, 3]), .gapLower 3 4 (![0, 4, 5, 1, 2]), .gapLower 3 3 (![0, 4, 5, 1, 2]), .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0216 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 2 3, .distance 1 3]
    constant := ![(-1), (0), (-1), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.triangle 14 0, .triangle 19 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 5 (![0, 1, 4, 5, 3]), .gapLower 3 4 (![0, 4, 5, 1, 2])]

def cycle0217 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (1), (-2), (3), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 5 0 (![0, 3, 1, 2, 4]), .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .triangle 0 0]

def cycle0218 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .theta 0, .zero, .theta 1, .distance 1 3, .distance 3 5, .distance 0 5]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 5, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 4, 5, 3]), .triangle 14 0, .gapLower 5 1 (![0, 3, 1, 2, 4])]

def cycle0219 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (2), (0), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 4, 5, 3]), .gapLower 2 5 (![0, 1, 4, 5, 3]), .gapLower 3 4 (![0, 4, 5, 1, 2]), .triangle 14 2, .gapLower 5 2 (![0, 3, 1, 2, 4]), .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0220 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 4, 5, 3]), .triangle 17 2, .gapLower 5 3 (![0, 3, 1, 2, 4]), .triangle 3 0]

def cycle0221 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .gapLower 5 4 (![0, 3, 1, 2, 4]), .triangle 12 0, .triangle 0 0]

def cycle0222 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 3, 1, 2, 4]), .triangle 18 0, .triangle 11 0, .triangle 0 0]

def cycle0223 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaOrder 1, .gapLower 1 5 (![0, 2, 4, 5, 3]), .triangle 13 0, .triangle 7 0, .triangle 4 1]

def cycle0224 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 4, 5, 3]), .triangle 14 0, .gapLower 3 2 (![0, 4, 5, 1, 2]), .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0225 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 4, 5, 3]), .gapLower 3 3 (![0, 4, 5, 1, 2]), .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0226 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![0, 4, 5, 1, 2]), .triangle 14 0, .triangle 19 1, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0227 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 16 2, .triangle 18 0, .triangle 15 0, .gapLower 1 2 (![0, 2, 4, 5, 3]), .triangle 0 0]

def cycle0228 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0229 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 2]
    constant := ![(-2), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 6 1]

def cycle0230 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 13 2, .triangle 15 0, .triangle 19 2, .triangle 14 0]

def cycle0231 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![(-2), (4), (0), (0), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 4, 5, 1, 2]), .gapLower 3 5 (![0, 4, 5, 1, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 19 0, .triangle 7 0]

def cycle0232 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![(0), (3), (0), (0), (-1), (-1), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 4, 5, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 19 0, .gapLower 3 1 (![0, 4, 5, 1, 2])]

def cycle0233 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![(0), (-1), (0), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.triangle 13 2, .triangle 15 0, .triangle 19 2, .gapLower 3 2 (![0, 4, 5, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2]

def cycle0234 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .theta 5, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (1), (-2), (0), (3), (-1), (-2)]
    coefficient := ![0, 1, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 5 0 (![0, 3, 4, 1, 2]), .thetaOrder 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0235 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![(0), (3), (0), (-2), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 3 0 (![0, 4, 5, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![0, 4, 5, 1, 2]), .gapLower 5 1 (![0, 3, 4, 1, 2]), .triangle 8 1]

def cycle0236 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![(0), (-1), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 13 2, .triangle 15 0, .gapLower 5 2 (![0, 3, 4, 1, 2]), .corridorLower 3 5, .corridorUpper 2 3, .triangle 10 2]

def cycle0237 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![(0), (0), (-2), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 13 2, .triangle 15 2, .gapLower 5 3 (![0, 3, 4, 1, 2]), .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2]

def cycle0238 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![0, 3, 4, 1, 2]), .triangle 12 1, .gapLower 2 1 (![0, 1, 5, 4, 3]), .triangle 0 1]

def cycle0239 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 3, 4, 1, 2]), .triangle 12 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0240 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![(0), (-1), (-1), (-1), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 13 2, .triangle 15 0, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 3 4 (![0, 4, 5, 1, 2])]

def cycle0241 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 4, 5, 1, 2]), .triangle 10 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0242 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-2), (4), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 5, 4, 1, 2]), .gapLower 3 5 (![0, 5, 4, 1, 2]), .triangle 10 2, .triangle 13 0, .triangle 19 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0243 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 3 5, .distance 1 3]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 13 0, .triangle 19 2, .triangle 14 0]

def cycle0244 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .theta 5, .theta 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (1), (-2), (0), (3), (-1), (-2)]
    coefficient := ![0, 1, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 5 0 (![0, 4, 3, 1, 2]), .thetaOrder 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0245 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 5, .distance 0 3]
    constant := ![(0), (3), (0), (-1), (-1), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 3 0 (![0, 5, 4, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 19 0, .gapLower 5 1 (![0, 4, 3, 1, 2]), .triangle 8 1]

def cycle0246 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(0), (3), (0), (-1), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 5, 4, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 19 2, .gapLower 5 2 (![0, 4, 3, 1, 2]), .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0247 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (0), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 5 3 (![0, 4, 3, 1, 2]), .gapLower 3 1 (![0, 5, 4, 1, 2]), .triangle 4 1, .triangle 0 1]

def cycle0248 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![0, 4, 3, 1, 2]), .triangle 14 1, .gapLower 3 1 (![0, 5, 4, 1, 2]), .triangle 4 1, .triangle 0 1]

def cycle0249 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 4, 3, 1, 2]), .triangle 12 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0250 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![(-1), (-2), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 13 0, .gapLower 3 2 (![0, 5, 4, 1, 2]), .corridorLower 3 5, .corridorUpper 2 3, .triangle 10 2]

def cycle0251 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 5, 4, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .gapLower 3 3 (![0, 5, 4, 1, 2]), .triangle 19 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0252 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(0), (3), (-2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 5, 4, 1, 2]), .corridorUpper 2 3, .gapLower 3 4 (![0, 5, 4, 1, 2]), .triangle 13 0, .triangle 19 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0253 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 5, 4, 1, 2]), .triangle 10 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0254 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![0, 1, 5, 4, 3]), .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0255 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![0, 1, 5, 4, 3]), .triangle 12 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0256 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 11 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0257 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0258 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (0), (0), (0), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .gapLower 2 1 (![0, 1, 5, 4, 3])]

def cycle0259 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .theta 5, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (1), (-2), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 1, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 5 0 (![0, 3, 4, 1, 2]), .thetaOrder 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0260 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![0, 3, 4, 1, 2]), .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0261 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 3, 4, 1, 2]), .triangle 12 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0262 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![(0), (-1), (-1), (-1), (2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 13 2, .triangle 15 0, .triangle 19 0, .corridorLower 3 4, .gapLower 3 5 (![0, 4, 5, 1, 2]), .triangle 10 2]

def cycle0263 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 5]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 5 0 (![0, 4, 3, 1, 2]), .thetaOrder 4, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 19 0, .gapLower 5 1 (![0, 4, 3, 1, 2])]

def cycle0264 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![0, 4, 3, 1, 2]), .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0265 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 4, 3, 1, 2]), .triangle 12 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0266 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 5, 4, 1, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0267 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![0, 1, 5, 4, 3]), .triangle 12 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0268 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0269 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0270 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (0), (3), (0), (0), (-2), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaOrder 1, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 15 1, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 4 1]

def cycle0271 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 12 1, .gapLower 2 1 (![0, 1, 5, 4, 3]), .triangle 0 1]

def cycle0272 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![(0), (-2), (0), (-1), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 15 1, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2]

def cycle0273 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-2), (4), (0), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 3 0 (![0, 5, 4, 1, 2]), .gapLower 3 5 (![0, 5, 4, 1, 2]), .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 15 1, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0274 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .gapLower 5 3 (![0, 4, 3, 1, 2]), .gapLower 3 1 (![0, 5, 4, 1, 2]), .triangle 4 1, .triangle 0 1]

def cycle0275 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 5, 4, 1, 2]), .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![0, 1, 5, 4, 3]), .triangle 0 0]

def cycle0276 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 11 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 3 0]

def cycle0277 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 3 0]

def cycle0278 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 5, 4, 3]), .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0279 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaOrder 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0280 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 2, .triangle 15 0, .triangle 19 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0281 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 0, .triangle 19 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0282 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 2, .triangle 15 0, .triangle 19 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0283 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 0, .triangle 19 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 4 1, .triangle 0 1]

def cycle0284 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 2, 3, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0285 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .triangle 12 2, .gapLower 1 1 (![0, 5, 2, 3, 4])]

def cycle0286 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .gapLower 1 3 (![0, 5, 2, 3, 4]), .triangle 12 2, .gapLower 1 1 (![0, 5, 2, 3, 4])]

def cycle0287 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![0, 5, 2, 3, 4]), .triangle 12 1, .triangle 6 0, .triangle 0 1]

def cycle0288 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 3 (![0, 5, 2, 3, 4]), .triangle 0 0]

def cycle0289 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 5, 2, 3, 4]), .triangle 10 1, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0290 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0291 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .gapLower 1 3 (![0, 5, 2, 3, 4]), .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0292 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 2, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0293 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![(-2), (4), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 5, 1, 4, 3]), .gapLower 2 5 (![0, 5, 1, 4, 3]), .triangle 10 0, .triangle 12 0, .triangle 6 0]

def cycle0294 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .gapLower 2 1 (![0, 5, 1, 4, 3])]

def cycle0295 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 2 (![0, 5, 1, 4, 3]), .triangle 6 0, .triangle 0 1]

def cycle0296 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![0, 5, 1, 4, 3]), .triangle 12 2, .gapLower 1 1 (![0, 5, 2, 4, 3])]

def cycle0297 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 5, 1, 4, 3]), .triangle 11 0, .triangle 12 2, .gapLower 1 1 (![0, 5, 2, 4, 3])]

def cycle0298 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 5, 1, 4, 3]), .triangle 10 0, .triangle 12 2, .gapLower 1 1 (![0, 5, 2, 4, 3])]

def cycle0299 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![0, 5, 2, 4, 3]), .triangle 12 1, .triangle 6 0, .triangle 0 1]

def cycle0300 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 5, 2, 4, 3]), .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0301 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 5, 2, 4, 3]), .triangle 11 1, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0302 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![(-2), (0), (2), (0), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 5, 1, 4, 3]), .thetaOrder 1, .gapLower 1 5 (![0, 5, 2, 4, 3]), .triangle 10 1, .triangle 12 0, .triangle 6 0]

def cycle0303 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 2 (![0, 5, 1, 4, 3]), .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0304 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![0, 5, 1, 4, 3]), .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0305 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 5, 1, 4, 3]), .triangle 11 0, .triangle 12 0, .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0306 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 5, 1, 4, 3]), .triangle 10 0, .triangle 12 0, .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0307 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 2, 3, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0308 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .triangle 14 0, .gapLower 1 3 (![0, 4, 2, 3, 5]), .triangle 11 2, .gapLower 1 1 (![0, 4, 2, 3, 5])]

def cycle0309 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 17 0, .triangle 10 0, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0310 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 0, .triangle 14 0, .gapLower 1 3 (![0, 4, 2, 3, 5]), .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0311 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 2, 5, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0312 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![(-2), (4), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 1, 5, 3]), .gapLower 2 5 (![0, 4, 1, 5, 3]), .triangle 10 0, .triangle 11 0, .triangle 5 0]

def cycle0313 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .gapLower 2 1 (![0, 4, 1, 5, 3])]

def cycle0314 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 2 (![0, 4, 1, 5, 3]), .triangle 5 0, .triangle 0 1]

def cycle0315 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![0, 4, 1, 5, 3]), .triangle 11 2, .gapLower 1 1 (![0, 4, 2, 5, 3])]

def cycle0316 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 4, 1, 5, 3]), .triangle 12 0, .gapLower 1 2 (![0, 4, 2, 5, 3]), .gapLower 1 1 (![0, 4, 2, 5, 3])]

def cycle0317 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 4, 1, 5, 3]), .triangle 10 0, .triangle 11 2, .gapLower 1 1 (![0, 4, 2, 5, 3])]

def cycle0318 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 2 (![0, 4, 2, 5, 3]), .triangle 11 1, .triangle 5 0, .triangle 0 1]

def cycle0319 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 2, .gapLower 1 3 (![0, 4, 2, 5, 3]), .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0320 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 4, 2, 5, 3]), .triangle 12 1, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0321 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (2), (0), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 1, 5, 3]), .thetaOrder 1, .gapLower 1 5 (![0, 4, 2, 5, 3]), .triangle 10 1, .triangle 11 0, .triangle 5 0]

def cycle0322 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 2 (![0, 4, 1, 5, 3]), .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0323 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 17 2, .gapLower 2 3 (![0, 4, 1, 5, 3]), .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0324 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 4, 1, 5, 3]), .triangle 12 0, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0325 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 4, 1, 5, 3]), .triangle 10 0, .triangle 11 0, .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0326 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 2, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0327 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (4), (-1), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 1, 3]), .gapLower 2 5 (![0, 4, 5, 1, 3]), .triangle 10 0, .triangle 12 0, .triangle 18 1, .triangle 5 0]

def cycle0328 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 18 1, .gapLower 2 1 (![0, 4, 5, 1, 3])]

def cycle0329 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .gapLower 2 2 (![0, 4, 5, 1, 3]), .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0330 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 3 (![0, 4, 5, 1, 3]), .triangle 18 1, .triangle 5 0, .triangle 0 1]

def cycle0331 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 4, 5, 1, 3]), .triangle 12 2, .triangle 15 1, .gapLower 1 1 (![0, 4, 5, 2, 3])]

def cycle0332 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 4, 5, 1, 3]), .triangle 10 0, .triangle 12 2, .triangle 15 1, .gapLower 1 1 (![0, 4, 5, 2, 3])]

def cycle0333 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 18 0, .triangle 15 0, .gapLower 1 1 (![0, 4, 5, 2, 3])]

def cycle0334 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 2, .gapLower 1 2 (![0, 4, 5, 2, 3]), .triangle 11 1, .triangle 5 0, .triangle 0 1]

def cycle0335 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 3 (![0, 4, 5, 2, 3]), .triangle 15 1, .triangle 11 1, .triangle 5 0, .triangle 0 1]

def cycle0336 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 4, 5, 2, 3]), .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0337 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (0), (2), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 1, 3]), .thetaOrder 1, .gapLower 1 5 (![0, 4, 5, 2, 3]), .triangle 10 1, .triangle 12 0, .triangle 18 1, .triangle 5 0]

def cycle0338 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 4, .theta 2, .distance 2 3, .distance 1 2]
    constant := ![(-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 12 0, .gapLower 2 2 (![0, 4, 5, 1, 3]), .corridorLower 2 4, .gapLower 2 5 (![0, 4, 5, 1, 3]), .triangle 10 0]

def cycle0339 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 3 (![0, 4, 5, 1, 3]), .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0340 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 4, 5, 1, 3]), .triangle 12 0, .triangle 18 1, .triangle 5 0, .triangle 0 1]

def cycle0341 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 4, .theta 2, .distance 2 3, .distance 1 2]
    constant := ![(-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 12 0, .triangle 18 1, .corridorLower 2 4, .gapLower 2 5 (![0, 4, 5, 1, 3]), .triangle 10 0]

def cycle0342 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 4 5, .distance 1 4]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 11 1, .triangle 18 0, .triangle 15 0]

def cycle0343 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 2, 3]), .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0344 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .triangle 15 0, .triangle 18 0, .triangle 5 0, .triangle 0 1]

def cycle0345 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 18 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0346 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .gapLower 1 2 (![0, 5, 4, 2, 3]), .triangle 15 1, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0347 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![(-2), (-1), (-1), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 3 (![0, 5, 4, 2, 3]), .triangle 15 0, .corridorLower 4 5, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 0]

def cycle0348 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 5, 4, 2, 3]), .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0349 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 2, .triangle 15 0, .triangle 18 0, .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0350 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 2, 4, 5]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0351 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 0, .triangle 15 0, .gapLower 1 3 (![0, 3, 2, 4, 5]), .triangle 10 2, .gapLower 1 1 (![0, 3, 2, 4, 5])]

def cycle0352 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0353 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 0, .triangle 15 0, .gapLower 1 3 (![0, 3, 2, 4, 5]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0354 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 2, 5, 4]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0355 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 3, 1, 5, 4]), .thetaLower 2, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 0, .triangle 4 0]

def cycle0356 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 0, .gapLower 2 1 (![0, 3, 1, 5, 4]), .triangle 0 1]

def cycle0357 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 2 2 (![0, 3, 1, 5, 4]), .triangle 4 0, .triangle 0 1]

def cycle0358 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 2, .gapLower 2 3 (![0, 3, 1, 5, 4]), .triangle 10 2, .gapLower 1 1 (![0, 3, 2, 5, 4])]

def cycle0359 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![0, 3, 1, 5, 4]), .triangle 12 0, .gapLower 1 2 (![0, 3, 2, 5, 4]), .gapLower 1 1 (![0, 3, 2, 5, 4])]

def cycle0360 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 1, 5, 4]), .triangle 11 0, .triangle 10 2, .gapLower 1 1 (![0, 3, 2, 5, 4])]

def cycle0361 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 2 (![0, 3, 2, 5, 4]), .triangle 10 1, .triangle 4 0, .triangle 0 1]

def cycle0362 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 2, .gapLower 1 3 (![0, 3, 2, 5, 4]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0363 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 3, 2, 5, 4]), .triangle 12 1, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0364 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (2), (0), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 3, 1, 5, 4]), .thetaOrder 1, .gapLower 1 5 (![0, 3, 2, 5, 4]), .triangle 11 1, .triangle 10 0, .triangle 4 0]

def cycle0365 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 2 2 (![0, 3, 1, 5, 4]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0366 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 18 2, .gapLower 2 3 (![0, 3, 1, 5, 4]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0367 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![0, 3, 1, 5, 4]), .triangle 12 0, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0368 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 1, 5, 4]), .triangle 11 0, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0369 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 2, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0370 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (4), (-1), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 5, 1, 4]), .gapLower 2 5 (![0, 3, 5, 1, 4]), .triangle 11 0, .triangle 12 0, .triangle 17 1, .triangle 4 0]

def cycle0371 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .triangle 17 1, .gapLower 2 1 (![0, 3, 5, 1, 4])]

def cycle0372 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .gapLower 2 2 (![0, 3, 5, 1, 4]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0373 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 2 3 (![0, 3, 5, 1, 4]), .triangle 17 1, .triangle 4 0, .triangle 0 1]

def cycle0374 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![0, 3, 5, 1, 4]), .triangle 12 2, .triangle 14 1, .gapLower 1 1 (![0, 3, 5, 2, 4])]

def cycle0375 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 5, 1, 4]), .triangle 11 0, .triangle 12 2, .triangle 14 1, .gapLower 1 1 (![0, 3, 5, 2, 4])]

def cycle0376 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 2 3, .distance 3 5, .distance 1 3]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 10 1, .triangle 17 0, .triangle 14 0]

def cycle0377 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 2, .gapLower 1 2 (![0, 3, 5, 2, 4]), .triangle 10 1, .triangle 4 0, .triangle 0 1]

def cycle0378 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 3 (![0, 3, 5, 2, 4]), .triangle 14 1, .triangle 10 1, .triangle 4 0, .triangle 0 1]

def cycle0379 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 3, 5, 2, 4]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0380 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (2), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 5, 1, 4]), .thetaOrder 1, .gapLower 1 5 (![0, 3, 5, 2, 4]), .triangle 11 1, .triangle 12 0, .triangle 17 1, .triangle 4 0]

def cycle0381 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .distance 2 4, .distance 1 2]
    constant := ![(-1), (-2), (-1), (4), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 12 0, .gapLower 2 2 (![0, 3, 5, 1, 4]), .corridorLower 2 3, .gapLower 2 5 (![0, 3, 5, 1, 4]), .triangle 11 0]

def cycle0382 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 2 3 (![0, 3, 5, 1, 4]), .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0383 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![0, 3, 5, 1, 4]), .triangle 12 0, .triangle 17 1, .triangle 4 0, .triangle 0 1]

def cycle0384 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .distance 2 4, .distance 1 2]
    constant := ![(-1), (0), (-1), (2), (-1)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 12 0, .triangle 17 1, .corridorLower 2 3, .gapLower 2 5 (![0, 3, 5, 1, 4]), .triangle 11 0]

def cycle0385 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 2, 5]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0386 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 1, 5]), .thetaLower 2, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 11 0, .triangle 16 1, .triangle 4 0]

def cycle0387 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 4, 1, 5]), .triangle 12 0, .triangle 11 2, .triangle 13 1, .gapLower 1 1 (![0, 3, 4, 2, 5])]

def cycle0388 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (2), (0), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 1, 5]), .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 2, 5]), .triangle 12 1, .triangle 11 0, .triangle 16 1, .triangle 4 0]

def cycle0389 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (2), (0), (-1), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 2, 5]), .gapLower 1 5 (![0, 3, 4, 2, 5]), .triangle 12 1, .triangle 11 0, .gapLower 2 2 (![0, 3, 4, 1, 5]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0390 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .gapLower 2 3 (![0, 3, 4, 1, 5]), .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0391 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .gapLower 2 4 (![0, 3, 4, 1, 5]), .triangle 11 0, .triangle 16 1, .triangle 4 0, .triangle 0 1]

def cycle0392 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 4, 1, 5]), .triangle 12 0, .triangle 11 0, .triangle 16 1, .triangle 4 0, .triangle 0 1]

def cycle0393 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0394 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (3), (-1), (0), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .corridorUpper 1 2, .triangle 12 0, .triangle 18 1, .triangle 16 1, .triangle 4 0]

def cycle0395 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 13 0, .triangle 10 1, .gapLower 2 1 (![0, 3, 4, 5, 1]), .triangle 0 1]

def cycle0396 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 18 0, .gapLower 2 2 (![0, 3, 4, 5, 1]), .gapLower 2 1 (![0, 3, 4, 5, 1]), .triangle 0 1]

def cycle0397 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 12 0, .triangle 18 1, .gapLower 2 2 (![0, 3, 4, 5, 1]), .corridorLower 2 3, .corridorUpper 1 2]

def cycle0398 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 0, .gapLower 2 3 (![0, 3, 4, 5, 1]), .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0399 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 13 0, .gapLower 1 1 (![0, 3, 4, 5, 2])]

def cycle0400 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 15 0, .gapLower 1 2 (![0, 3, 4, 5, 2]), .gapLower 1 1 (![0, 3, 4, 5, 2])]

def cycle0401 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![0, 3, 4, 5, 2]), .triangle 10 1, .triangle 4 0, .triangle 0 1]

def cycle0402 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (3), (0), (-2), (0), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![0, 3, 4, 5, 2]), .triangle 11 1, .triangle 16 1, .triangle 4 0]

def cycle0403 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![0, 3, 4, 5, 2]), .triangle 11 1, .triangle 16 1, .gapLower 2 1 (![0, 3, 4, 5, 1]), .triangle 0 1]

def cycle0404 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 12 2, .gapLower 1 3 (![0, 3, 4, 5, 2]), .triangle 11 1, .gapLower 2 2 (![0, 3, 4, 5, 1]), .corridorLower 2 3, .corridorUpper 1 2]

def cycle0405 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![(-2), (0), (3), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true] }
  origin := ![.gapLower 3 0 (![0, 2, 1, 4, 5]), .thetaOrder 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![0, 3, 4, 5, 2]), .triangle 2 2, .triangle 7 1]

def cycle0406 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 2 4, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![0, 3, 4, 5, 2]), .gapLower 4 2 (![0, 2, 1, 3, 5]), .triangle 16 1, .gapLower 3 1 (![0, 2, 1, 4, 5]), .triangle 4 1, .triangle 0 1]

def cycle0407 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 12 2, .gapLower 1 3 (![0, 3, 4, 5, 2]), .triangle 13 1, .gapLower 3 2 (![0, 2, 1, 4, 5]), .corridorLower 2 3, .corridorUpper 1 2]

def cycle0408 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .gapLower 3 3 (![0, 2, 1, 4, 5]), .triangle 10 1, .triangle 4 0, .triangle 0 1]

def cycle0409 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 2, .gapLower 3 4 (![0, 2, 1, 4, 5]), .triangle 16 0, .triangle 4 0, .triangle 0 1]

def cycle0410 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 2, 1, 4, 5]), .gapLower 5 3 (![0, 2, 1, 3, 4]), .gapLower 1 3 (![0, 3, 4, 5, 2]), .triangle 2 0]

def cycle0411 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 5 3 (![0, 2, 1, 4, 3]), .gapLower 1 3 (![0, 3, 4, 5, 2]), .triangle 2 0]

def cycle0412 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 4, 5, 1]), .triangle 12 2, .gapLower 1 3 (![0, 3, 4, 5, 2]), .triangle 2 0]

def cycle0413 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 4]
    constant := ![(0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 11 1, .triangle 18 0, .triangle 15 2, .gapLower 1 3 (![0, 3, 4, 5, 2])]

def cycle0414 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 4]
    constant := ![(0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 11 1, .triangle 16 1, .triangle 17 0, .triangle 14 2, .gapLower 1 3 (![0, 3, 4, 5, 2])]

def cycle0415 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 5, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (3), (-2), (0), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 12 1, .triangle 17 1, .triangle 4 0]

def cycle0416 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 12 1, .triangle 18 1, .triangle 16 1, .gapLower 2 1 (![0, 3, 4, 5, 1]), .triangle 0 1]

def cycle0417 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(-2), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 12 1, .triangle 18 1, .gapLower 2 2 (![0, 3, 4, 5, 1]), .corridorLower 2 3, .corridorUpper 1 2]

def cycle0418 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 12 1, .gapLower 2 3 (![0, 3, 4, 5, 1]), .corridorLower 2 4, .corridorUpper 1 2]

def cycle0419 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 3]
    constant := ![(-2), (0), (3), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.gapLower 3 0 (![0, 2, 1, 4, 5]), .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 3, 4, 5, 1]), .gapLower 5 1 (![0, 2, 1, 3, 4]), .triangle 8 1]

def cycle0420 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 3, 4, 5, 1]), .triangle 18 1, .triangle 16 1, .gapLower 3 1 (![0, 2, 1, 4, 5]), .triangle 4 1, .triangle 0 1]

def cycle0421 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 14 1, .gapLower 3 2 (![0, 2, 1, 4, 5]), .corridorLower 2 3, .corridorUpper 1 2]

def cycle0422 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 5, .theta 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5]
    constant := ![(-2), (0), (0), (0), (3), (-2), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 5 0 (![0, 2, 1, 3, 4]), .thetaOrder 4, .thetaOrder 3, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 3, 4, 5, 1]), .gapLower 5 1 (![0, 2, 1, 3, 4])]

def cycle0423 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 5, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 12 1, .gapLower 5 1 (![0, 2, 1, 3, 4]), .triangle 6 1]

def cycle0424 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 2 5, .theta 2, .distance 1 2]
    constant := ![(-2), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 4 (![0, 3, 4, 5, 2]), .gapLower 5 2 (![0, 2, 1, 3, 4]), .corridorLower 2 5, .corridorUpper 1 2]

def cycle0425 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 2, 1, 4, 5]), .gapLower 5 3 (![0, 2, 1, 3, 4]), .triangle 3 0]

def cycle0426 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .gapLower 5 4 (![0, 2, 1, 3, 4]), .triangle 17 0, .triangle 4 0, .triangle 0 1]

def cycle0427 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 2, 1, 3, 4]), .triangle 19 0, .triangle 13 0, .triangle 1 0]

def cycle0428 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 3]
    constant := ![(-2), (0), (3), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.gapLower 3 0 (![0, 2, 1, 5, 4]), .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 3, 4, 5, 1]), .gapLower 5 1 (![0, 2, 1, 4, 3]), .triangle 8 1]

def cycle0429 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 3, 4, 5, 1]), .triangle 18 1, .triangle 16 1, .gapLower 3 1 (![0, 2, 1, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0430 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(-2), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 14 1, .gapLower 3 2 (![0, 2, 1, 5, 4]), .corridorLower 2 3, .corridorUpper 1 2]

def cycle0431 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .theta 5, .theta 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (1), (-2), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 1, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 5 0 (![0, 2, 1, 4, 3]), .thetaOrder 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 3 3 (![0, 2, 1, 5, 4]), .triangle 1 0]

def cycle0432 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 5, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (3), (-2), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 12 1, .gapLower 5 1 (![0, 2, 1, 4, 3]), .triangle 6 1]

def cycle0433 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 2 5, .theta 2, .distance 1 2]
    constant := ![(-2), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 4 (![0, 3, 4, 5, 2]), .gapLower 5 2 (![0, 2, 1, 4, 3]), .corridorLower 2 5, .corridorUpper 1 2]

def cycle0434 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 5 3 (![0, 2, 1, 4, 3]), .triangle 3 0]

def cycle0435 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 5 4 (![0, 2, 1, 4, 3]), .triangle 15 0, .gapLower 1 2 (![0, 3, 4, 5, 2]), .triangle 1 0]

def cycle0436 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 2, 1, 4, 3]), .gapLower 3 3 (![0, 2, 1, 5, 4]), .triangle 1 0]

def cycle0437 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![0, 2, 1, 5, 4]), .triangle 14 0, .triangle 1 0]

def cycle0438 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 2, 1, 5, 4]), .triangle 19 0, .triangle 15 0, .gapLower 1 2 (![0, 3, 4, 5, 2]), .triangle 1 0]

def cycle0439 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 4, 5, 1]), .gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 3 0]

def cycle0440 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (0), (2), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 12 0, .triangle 18 1, .triangle 16 1, .gapLower 2 1 (![0, 3, 4, 5, 1])]

def cycle0441 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 12 0, .triangle 18 1, .triangle 16 1, .gapLower 2 1 (![0, 3, 4, 5, 1])]

def cycle0442 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (2), (0), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .gapLower 1 5 (![0, 3, 4, 5, 2]), .gapLower 2 4 (![0, 3, 4, 5, 1]), .triangle 18 1, .gapLower 2 2 (![0, 3, 4, 5, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0443 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (2), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .gapLower 1 5 (![0, 3, 4, 5, 2]), .gapLower 2 4 (![0, 3, 4, 5, 1]), .gapLower 2 3 (![0, 3, 4, 5, 1]), .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0444 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(0), (2), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .gapLower 1 5 (![0, 3, 4, 5, 2]), .gapLower 2 4 (![0, 3, 4, 5, 1]), .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0445 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 3]
    constant := ![(-2), (0), (2), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 3 0 (![0, 2, 1, 4, 5]), .thetaOrder 2, .gapLower 2 5 (![0, 3, 4, 5, 1]), .triangle 12 0, .triangle 18 1, .triangle 16 1, .gapLower 3 1 (![0, 2, 1, 4, 5])]

def cycle0446 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 12 0, .triangle 18 1, .triangle 16 1, .gapLower 3 1 (![0, 2, 1, 4, 5])]

def cycle0447 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 19 0, .triangle 13 0, .gapLower 3 2 (![0, 2, 1, 4, 5]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0448 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (1), (-2), (3), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 5 0 (![0, 2, 1, 3, 4]), .corridorUpper 4 5, .triangle 19 0, .triangle 13 0, .triangle 1 0]

def cycle0449 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 5, .distance 0 5]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 5, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 12 0, .gapLower 5 1 (![0, 2, 1, 3, 4])]

def cycle0450 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 5, .distance 1 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 2, 1, 4, 5]), .gapLower 5 3 (![0, 2, 1, 3, 4]), .gapLower 5 2 (![0, 2, 1, 3, 4]), .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0451 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 2, 1, 3, 4]), .triangle 19 0, .triangle 16 0, .triangle 4 0, .triangle 0 1]

def cycle0452 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 3]
    constant := ![(-2), (0), (2), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 3 0 (![0, 2, 1, 5, 4]), .thetaOrder 2, .gapLower 2 5 (![0, 3, 4, 5, 1]), .triangle 12 0, .triangle 18 1, .triangle 16 1, .gapLower 3 1 (![0, 2, 1, 5, 4])]

def cycle0453 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 12 0, .triangle 18 1, .triangle 16 1, .gapLower 3 1 (![0, 2, 1, 5, 4])]

def cycle0454 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 15 0, .gapLower 1 2 (![0, 3, 4, 5, 2]), .gapLower 3 2 (![0, 2, 1, 5, 4]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0455 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .theta 5, .theta 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (1), (-2), (0), (3), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 5 0 (![0, 2, 1, 4, 3]), .thetaOrder 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 3 3 (![0, 2, 1, 5, 4]), .triangle 10 1, .triangle 4 0, .triangle 0 1]

def cycle0456 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 5, .distance 0 5]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 5, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 12 0, .gapLower 5 1 (![0, 2, 1, 4, 3])]

def cycle0457 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2]
    constant := ![(0), (-2), (0), (0), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false] }
  origin := ![.triangle 12 2, .gapLower 5 2 (![0, 2, 1, 4, 3]), .triangle 18 1, .triangle 16 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 3, 4, 5, 2])]

def cycle0458 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 2, 1, 5, 4]), .triangle 19 0, .triangle 18 0, .gapLower 2 2 (![0, 3, 4, 5, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0459 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0460 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 1 2]
    constant := ![(0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 11 2, .triangle 15 0, .triangle 18 2, .gapLower 2 4 (![0, 3, 4, 1, 5])]

def cycle0461 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (4), (0), (-1), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .gapLower 2 5 (![0, 3, 4, 5, 1]), .triangle 11 2, .triangle 15 0, .triangle 18 0, .triangle 16 1, .triangle 4 0]

def cycle0462 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 18 0, .gapLower 2 2 (![0, 3, 4, 5, 1]), .gapLower 2 1 (![0, 3, 4, 5, 1]), .triangle 0 1]

def cycle0463 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (4), (0), (-1), (-1), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 11 2, .triangle 15 0, .triangle 18 0, .gapLower 2 2 (![0, 3, 4, 5, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0464 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 11 2, .triangle 15 0, .triangle 18 2, .gapLower 2 3 (![0, 3, 4, 5, 1]), .corridorLower 2 4, .corridorUpper 1 2]

def cycle0465 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 3]
    constant := ![(-2), (0), (3), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 2, 1, 5, 4]), .thetaOrder 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 18 0, .gapLower 2 2 (![0, 3, 4, 5, 1]), .gapLower 3 1 (![0, 2, 1, 5, 4])]

def cycle0466 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (0), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 18 0, .triangle 16 1, .gapLower 3 1 (![0, 2, 1, 5, 4]), .triangle 4 1]

def cycle0467 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 3 2 (![0, 2, 1, 5, 4]), .triangle 4 0, .triangle 0 1]

def cycle0468 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 3 3 (![0, 2, 1, 5, 4]), .gapLower 1 1 (![0, 3, 5, 4, 2])]

def cycle0469 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![0, 2, 1, 5, 4]), .triangle 14 0, .gapLower 1 1 (![0, 3, 5, 4, 2])]

def cycle0470 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 2, 1, 5, 4]), .triangle 13 0, .gapLower 1 1 (![0, 3, 5, 4, 2])]

def cycle0471 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 11 2, .triangle 15 0, .triangle 18 0, .gapLower 2 2 (![0, 3, 4, 5, 1]), .corridorLower 2 3, .gapLower 2 5 (![0, 3, 4, 5, 1])]

def cycle0472 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 3, 5, 4, 1]), .corridorUpper 1 2, .triangle 11 0, .triangle 18 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 4 1]

def cycle0473 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-2), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0 (![0, 2, 1, 5, 4]), .thetaOrder 2, .corridorUpper 1 2, .triangle 11 0, .triangle 18 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0474 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 5, .distance 1 2]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 11 0, .triangle 18 2, .triangle 12 0]

def cycle0475 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .theta 5, .theta 4, .distance 3 4, .distance 1 3, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (1), (-2), (0), (3), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 1, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 5 0 (![0, 4, 2, 1, 3]), .thetaOrder 4, .corridorUpper 3 4, .triangle 13 0, .triangle 10 1, .gapLower 3 1 (![0, 2, 1, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0476 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (3), (-1), (-1), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 3, 5, 4, 1]), .corridorUpper 1 2, .triangle 11 0, .triangle 18 0, .gapLower 5 1 (![0, 4, 2, 1, 3]), .triangle 6 1]

def cycle0477 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 18 2, .gapLower 5 2 (![0, 4, 2, 1, 3]), .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0478 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 2 5, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 5 3 (![0, 4, 2, 1, 3]), .triangle 17 1, .gapLower 3 1 (![0, 2, 1, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0479 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 5, .distance 2 5, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 5 4 (![0, 4, 2, 1, 3]), .triangle 12 1, .triangle 17 1, .gapLower 3 1 (![0, 2, 1, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0480 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 4, 2, 1, 3]), .triangle 14 0, .gapLower 1 1 (![0, 3, 5, 4, 2])]

def cycle0481 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 3 2 (![0, 2, 1, 5, 4]), .gapLower 2 1 (![0, 3, 5, 4, 1]), .triangle 0 1]

def cycle0482 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 3 3 (![0, 2, 1, 5, 4]), .triangle 10 1, .gapLower 2 1 (![0, 3, 5, 4, 1]), .triangle 0 1]

def cycle0483 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![0, 2, 1, 5, 4]), .triangle 14 0, .triangle 10 1, .gapLower 2 1 (![0, 3, 5, 4, 1]), .triangle 0 1]

def cycle0484 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 11 0, .triangle 18 2, .gapLower 2 2 (![0, 3, 5, 4, 1]), .corridorLower 2 3, .corridorUpper 1 2]

def cycle0485 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .gapLower 2 3 (![0, 3, 5, 4, 1]), .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0486 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 3, 5, 4, 1]), .triangle 18 0, .triangle 9 0, .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0487 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 5, 4, 1]), .triangle 11 0, .triangle 18 0, .triangle 9 0, .triangle 7 1]

def cycle0488 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-2), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .gapLower 2 5 (![0, 3, 4, 5, 1]), .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 10 1, .triangle 4 0]

def cycle0489 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 3]
    constant := ![(-2), (0), (3), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.gapLower 3 0 (![0, 2, 1, 5, 4]), .thetaOrder 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 2]

def cycle0490 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (0), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .gapLower 3 2 (![0, 2, 1, 5, 4]), .gapLower 3 1 (![0, 2, 1, 5, 4]), .triangle 4 1]

def cycle0491 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (4), (0), (0), (-2), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .gapLower 3 2 (![0, 2, 1, 5, 4]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0492 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .theta 5, .theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (1), (-2), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 1, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 5 0 (![0, 2, 4, 1, 3]), .thetaOrder 4, .corridorUpper 3 4, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0493 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (3), (-2), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .corridorUpper 1 2, .gapLower 2 4 (![0, 3, 4, 5, 1]), .gapLower 5 1 (![0, 2, 4, 1, 3]), .triangle 6 1]

def cycle0494 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 11 2, .triangle 15 0, .gapLower 5 2 (![0, 2, 4, 1, 3]), .corridorLower 2 5, .corridorUpper 1 2]

def cycle0495 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-2), (-1), (0), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 11 2, .triangle 15 2, .gapLower 5 3 (![0, 2, 4, 1, 3]), .triangle 18 0, .gapLower 2 2 (![0, 3, 4, 5, 1]), .corridorLower 2 3, .corridorUpper 1 2]

def cycle0496 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 2, .gapLower 5 4 (![0, 2, 4, 1, 3]), .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0497 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 2, 4, 1, 3]), .triangle 14 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0498 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![0, 2, 1, 5, 4]), .triangle 14 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0499 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 2, 1, 5, 4]), .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0500 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 4, 5, 1]), .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0501 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2]
    constant := ![(-2), (3), (0), (0), (-2), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 5, 4, 1]), .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 10 1, .triangle 4 0]

def cycle0502 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 10 1, .gapLower 2 1 (![0, 3, 5, 4, 1]), .triangle 0 1]

def cycle0503 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 5, 4, 1]), .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0504 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 3]
    constant := ![(0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.triangle 10 1, .triangle 17 0, .gapLower 5 3 (![0, 4, 1, 3, 2]), .gapLower 1 2 (![0, 3, 5, 4, 2])]

def cycle0505 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![(0), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false] }
  origin := ![.triangle 10 1, .triangle 16 0, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2])]

def cycle0506 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(0), (-2), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 11 2, .gapLower 1 3 (![0, 3, 5, 4, 2]), .triangle 15 1, .triangle 18 0, .corridorLower 2 4, .corridorUpper 1 2]

def cycle0507 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (3), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 5, 4, 1]), .corridorUpper 1 2, .triangle 11 0, .triangle 16 1, .triangle 4 0]

def cycle0508 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![0, 3, 5, 4, 2]), .triangle 14 1, .triangle 10 1, .gapLower 2 1 (![0, 3, 5, 4, 1]), .triangle 0 1]

def cycle0509 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 5, 4, 1]), .triangle 11 2, .gapLower 1 3 (![0, 3, 5, 4, 2]), .triangle 3 0]

def cycle0510 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 5, 4, 2]), .triangle 15 0, .triangle 9 0, .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0511 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(0), (2), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 11 2, .triangle 15 0, .triangle 18 0, .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0512 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 11 0, .triangle 18 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0513 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0 (![0, 5, 3, 2, 4]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0514 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 17 0, .triangle 4 0, .triangle 0 1]

def cycle0515 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 0, .triangle 17 0, .triangle 8 0, .triangle 4 1, .triangle 0 1]

def cycle0516 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![0, 5, 3, 2, 4]), .triangle 14 1, .triangle 8 0, .triangle 4 1, .triangle 0 1]

def cycle0517 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .gapLower 1 3 (![0, 5, 3, 2, 4]), .triangle 1 0]

def cycle0518 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 5, 3, 2, 4]), .triangle 10 2, .triangle 14 0, .triangle 8 0, .triangle 4 1, .triangle 0 1]

def cycle0519 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 17 0, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0520 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0 (![0, 5, 3, 4, 2]), .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0521 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 5, 3, 4, 1]), .gapLower 2 5 (![0, 5, 3, 4, 1]), .triangle 11 0, .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0522 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3]
    constant := ![(-2), (0), (3), (-1), (0), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 3 0 (![0, 5, 2, 1, 4]), .thetaOrder 2, .corridorUpper 1 2, .triangle 11 0, .triangle 16 1, .triangle 17 0, .triangle 8 0]

def cycle0523 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (0), (-1), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 5, 3, 4, 1]), .corridorUpper 1 2, .triangle 11 0, .triangle 16 1, .triangle 17 0, .gapLower 3 1 (![0, 5, 2, 1, 4]), .triangle 4 1]

def cycle0524 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 5, 3, 4, 1]), .corridorUpper 1 2, .triangle 11 0, .triangle 16 1, .gapLower 3 2 (![0, 5, 2, 1, 4]), .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0525 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 2 3, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 3 3 (![0, 5, 2, 1, 4]), .triangle 17 2, .gapLower 2 1 (![0, 5, 3, 4, 1]), .triangle 0 1]

def cycle0526 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 2 3, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 4 (![0, 5, 2, 1, 4]), .triangle 10 1, .triangle 17 2, .gapLower 2 1 (![0, 5, 3, 4, 1]), .triangle 0 1]

def cycle0527 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 5, 2, 1, 4]), .triangle 13 0, .triangle 14 2, .gapLower 1 1 (![0, 5, 3, 4, 2])]

def cycle0528 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .distance 2 5, .theta 2, .distance 1 2]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 11 0, .triangle 16 1, .gapLower 2 2 (![0, 5, 3, 4, 1]), .corridorLower 2 5, .corridorUpper 1 2]

def cycle0529 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (-2), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 5, 3, 4, 1]), .corridorUpper 1 2, .triangle 11 0, .gapLower 2 3 (![0, 5, 3, 4, 1]), .triangle 17 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0530 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 5, 3, 4, 1]), .corridorUpper 1 2, .gapLower 2 4 (![0, 5, 3, 4, 1]), .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0531 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2]
    constant := ![(-1), (0), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 11 0, .triangle 16 1, .triangle 17 0, .corridorLower 3 5, .thetaOrder 2, .gapLower 2 5 (![0, 5, 3, 4, 1])]

def cycle0532 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![0, 5, 3, 4, 2]), .triangle 14 1, .triangle 8 0, .triangle 4 1, .triangle 0 1]

def cycle0533 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![0, 5, 3, 4, 2]), .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0534 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-2), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 3, 4, 2]), .triangle 13 1, .triangle 14 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0535 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 3, 4, 2]), .triangle 11 0, .triangle 16 1, .triangle 17 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0536 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 3, 2, 5]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0537 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0538 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 3, 5, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0539 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 0, .triangle 16 0, .triangle 4 0, .triangle 0 1]

def cycle0540 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 3, 5, 1]), .gapLower 2 5 (![0, 4, 3, 5, 1]), .triangle 12 0, .triangle 17 1, .triangle 16 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0541 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![(-2), (0), (3), (-1), (0), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 3 0 (![0, 4, 2, 1, 5]), .thetaOrder 2, .corridorUpper 1 2, .triangle 12 0, .triangle 17 1, .triangle 16 0, .triangle 7 0]

def cycle0542 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (0), (-1), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 4, 3, 5, 1]), .corridorUpper 1 2, .triangle 12 0, .triangle 17 1, .triangle 16 0, .gapLower 3 1 (![0, 4, 2, 1, 5]), .triangle 4 1]

def cycle0543 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 3, 5, 1]), .corridorUpper 1 2, .triangle 12 0, .triangle 17 1, .gapLower 3 2 (![0, 4, 2, 1, 5]), .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0544 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 3 3 (![0, 4, 2, 1, 5]), .triangle 16 2, .gapLower 2 1 (![0, 4, 3, 5, 1]), .triangle 0 1]

def cycle0545 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .gapLower 3 4 (![0, 4, 2, 1, 5]), .triangle 10 1, .triangle 16 2, .gapLower 2 1 (![0, 4, 3, 5, 1]), .triangle 0 1]

def cycle0546 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 3 5, .distance 1 3, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 4, 2, 1, 5]), .triangle 14 0, .triangle 10 1, .triangle 16 2, .gapLower 2 1 (![0, 4, 3, 5, 1])]

def cycle0547 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 12 0, .triangle 17 1, .gapLower 2 2 (![0, 4, 3, 5, 1]), .corridorLower 2 4, .corridorUpper 1 2]

def cycle0548 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (-2), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 3, 5, 1]), .corridorUpper 1 2, .triangle 12 0, .gapLower 2 3 (![0, 4, 3, 5, 1]), .triangle 16 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0549 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 4, 3, 5, 1]), .triangle 17 1, .triangle 16 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0550 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 4, 3, 5, 1]), .triangle 12 0, .triangle 17 1, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0551 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 3]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.gapLower 3 3 (![0, 4, 2, 1, 5]), .triangle 16 2, .triangle 18 0, .triangle 15 2, .gapLower 1 3 (![0, 4, 3, 5, 2])]

def cycle0552 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 2 (![0, 4, 3, 5, 2]), .triangle 13 1, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0553 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![0, 4, 3, 5, 2]), .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0554 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 3, 5, 2]), .triangle 14 1, .triangle 13 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0555 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2]
    constant := ![(0), (0), (-1), (-1), (-1), (0), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 12 2, .triangle 14 1, .triangle 13 0, .triangle 16 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 5 (![0, 4, 3, 5, 2])]

def cycle0556 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 3, 5, 2]), .triangle 10 0, .triangle 16 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0557 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0558 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![(0), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 10 2, .triangle 13 0, .triangle 16 2, .triangle 11 0]

def cycle0559 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![(0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 17 2, .gapLower 2 4 (![0, 3, 4, 1, 5])]

def cycle0560 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (4), (0), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .gapLower 2 5 (![0, 3, 4, 5, 1]), .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 4 0]

def cycle0561 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(0), (3), (0), (-1), (-1), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 16 0, .gapLower 2 1 (![0, 3, 4, 5, 1])]

def cycle0562 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 17 2, .triangle 18 1, .gapLower 2 2 (![0, 3, 4, 5, 1]), .corridorLower 2 3, .corridorUpper 1 2]

def cycle0563 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 17 2, .gapLower 2 3 (![0, 3, 4, 5, 1]), .corridorLower 2 4, .corridorUpper 1 2]

def cycle0564 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 0 3]
    constant := ![(-2), (0), (3), (0), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 3 0 (![0, 2, 4, 5, 1]), .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 19 1, .triangle 16 0, .gapLower 3 1 (![0, 2, 4, 5, 1])]

def cycle0565 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (0), (-1), (0), (-1), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 19 1, .triangle 16 0, .gapLower 3 1 (![0, 2, 4, 5, 1]), .triangle 4 1]

def cycle0566 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 19 1, .gapLower 3 2 (![0, 2, 4, 5, 1]), .corridorLower 2 3, .corridorUpper 1 2]

def cycle0567 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (-2), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 10 2, .triangle 14 0, .gapLower 3 3 (![0, 2, 4, 5, 1]), .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2]

def cycle0568 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![0, 2, 4, 5, 1]), .triangle 17 0, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0569 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 2, 4, 5, 1]), .triangle 14 0, .triangle 19 1, .triangle 16 0, .triangle 4 0, .triangle 0 1]

def cycle0570 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 0, .triangle 16 0, .corridorLower 2 3, .gapLower 2 5 (![0, 3, 4, 5, 1])]

def cycle0571 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4]
    constant := ![(0), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 13 1, .triangle 16 2, .triangle 18 0, .triangle 15 0]

def cycle0572 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (0), (-1), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 17 0, .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0573 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (0), (-1), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 17 0, .triangle 16 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0574 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .gapLower 2 5 (![0, 4, 5, 3, 1]), .triangle 10 0, .triangle 16 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0575 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3]
    constant := ![(-2), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 0 (![0, 4, 5, 2, 1]), .thetaOrder 2, .corridorUpper 1 2, .triangle 10 0, .triangle 17 0, .triangle 19 1, .triangle 7 0]

def cycle0576 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (-1), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .corridorUpper 1 2, .triangle 10 0, .triangle 17 0, .triangle 19 1, .gapLower 3 1 (![0, 4, 5, 2, 1]), .triangle 4 1]

def cycle0577 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (4), (-1), (-1), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .gapLower 2 5 (![0, 4, 5, 3, 1]), .triangle 10 0, .triangle 17 0, .gapLower 3 2 (![0, 4, 5, 2, 1]), .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0578 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .corridorUpper 1 2, .triangle 10 0, .gapLower 3 3 (![0, 4, 5, 2, 1]), .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0579 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 3 4 (![0, 4, 5, 2, 1]), .triangle 17 2, .triangle 18 1, .gapLower 2 1 (![0, 4, 5, 3, 1]), .triangle 0 1]

def cycle0580 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 5, .distance 1 2]
    constant := ![(-1), (0), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![false, true, false] }
  origin := ![.triangle 10 0, .triangle 17 2, .triangle 12 0]

def cycle0581 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (1), (-2), (3), (-1), (-2), (0)]
    coefficient := ![0, 1, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 5 0 (![0, 3, 2, 1, 4]), .corridorUpper 4 5, .triangle 18 0, .gapLower 2 1 (![0, 4, 5, 3, 1]), .triangle 0 1]

def cycle0582 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 2]
    constant := ![(0), (3), (-1), (-1), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .corridorUpper 1 2, .triangle 10 0, .triangle 17 0, .gapLower 5 1 (![0, 3, 2, 1, 4]), .triangle 6 1]

def cycle0583 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .corridorUpper 1 2, .triangle 10 0, .triangle 17 2, .gapLower 5 2 (![0, 3, 2, 1, 4]), .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0584 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 4, 5, 2, 1]), .triangle 14 2, .gapLower 5 3 (![0, 3, 2, 1, 4]), .triangle 18 1, .gapLower 2 1 (![0, 4, 5, 3, 1])]

def cycle0585 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 5, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .gapLower 5 4 (![0, 3, 2, 1, 4]), .triangle 12 1, .triangle 18 1, .gapLower 2 1 (![0, 4, 5, 3, 1]), .triangle 0 1]

def cycle0586 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![0, 3, 2, 1, 4]), .triangle 15 0, .gapLower 1 1 (![0, 4, 5, 3, 2])]

def cycle0587 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 10 0, .triangle 17 2, .gapLower 2 2 (![0, 4, 5, 3, 1]), .corridorLower 2 4, .corridorUpper 1 2]

def cycle0588 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .gapLower 2 3 (![0, 4, 5, 3, 1]), .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0589 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 4, 5, 3, 1]), .triangle 16 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0590 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 4, 5, 3, 1]), .triangle 10 0, .triangle 16 0, .triangle 7 0, .triangle 4 1]

def cycle0591 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 2, .triangle 18 0, .gapLower 4 3 (![0, 3, 1, 5, 2]), .gapLower 1 1 (![0, 4, 5, 3, 2])]

def cycle0592 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-2), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 10 2, .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 13 1, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2]

def cycle0593 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .gapLower 2 5 (![0, 4, 5, 3, 1]), .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 13 1, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0594 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 3 4, .distance 0 3]
    constant := ![(-2), (4), (0), (-2), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.gapLower 3 0 (![0, 4, 5, 2, 1]), .gapLower 3 5 (![0, 4, 5, 2, 1]), .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 13 1, .triangle 7 0]

def cycle0595 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (0), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 13 1, .gapLower 3 1 (![0, 4, 5, 2, 1]), .triangle 4 1]

def cycle0596 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 4, 5, 2, 1]), .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 2 0]

def cycle0597 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 4]
    constant := ![(0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, false] }
  origin := ![.triangle 13 1, .triangle 19 0, .triangle 15 2, .gapLower 1 2 (![0, 4, 5, 3, 2])]

def cycle0598 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 4, 5, 3, 1]), .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 2 0]

def cycle0599 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (0), (-1), (0), (-2), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 5, 4, 3, 1]), .corridorUpper 1 2, .triangle 10 0, .triangle 16 2, .triangle 18 0, .gapLower 5 3 (![0, 3, 1, 4, 2]), .gapLower 1 2 (![0, 4, 5, 3, 2]), .gapLower 4 2 (![0, 3, 1, 5, 2]), .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0600 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 15 1, .gapLower 4 3 (![0, 2, 3, 1, 5]), .triangle 16 0, .triangle 4 0, .triangle 0 1]

def cycle0601 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .gapLower 5 3 (![0, 2, 3, 1, 4]), .triangle 17 0, .triangle 16 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0602 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 1 3, .distance 1 5, .distance 3 5, .distance 3 4, .distance 0 3]
    constant := ![(-2), (4), (-2), (0), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 3 0 (![0, 4, 5, 2, 1]), .gapLower 3 5 (![0, 4, 5, 2, 1]), .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 14 1, .triangle 19 1, .triangle 7 0]

def cycle0603 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (0), (-2), (0), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 14 1, .triangle 19 1, .gapLower 3 1 (![0, 4, 5, 2, 1]), .triangle 4 1]

def cycle0604 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 4, 5, 2, 1]), .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 3 0]

def cycle0605 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 4, 5, 3, 1]), .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 3 0]

def cycle0606 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (0), (-1), (-1), (0), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 5, 4, 3, 1]), .corridorUpper 1 2, .triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 15 0, .gapLower 4 2 (![0, 3, 1, 5, 2]), .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0607 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 5, 3, 2]), .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0608 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (2), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0609 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 0, .triangle 16 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0610 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (1), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 3 1]

def cycle0611 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 1 2]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 2, .gapLower 2 4 (![0, 3, 4, 1, 5])]

def cycle0612 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-1), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .gapLower 2 5 (![0, 3, 4, 5, 1]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .triangle 16 1, .triangle 4 0]

def cycle0613 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![(0), (3), (0), (0), (-1), (-1), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 3, 4, 5, 1]), .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .gapLower 2 2 (![0, 3, 4, 5, 1]), .gapLower 2 1 (![0, 3, 4, 5, 1])]

def cycle0614 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (4), (0), (0), (-1), (-1), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .gapLower 2 2 (![0, 3, 4, 5, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0615 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 2, .gapLower 2 3 (![0, 3, 4, 5, 1]), .corridorLower 2 4, .corridorUpper 1 2]

def cycle0616 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-1), (-1), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 19 0, .triangle 16 0, .corridorLower 2 3, .corridorUpper 1 2]

def cycle0617 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (-1), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 19 0, .triangle 18 0, .gapLower 2 2 (![0, 3, 4, 5, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0618 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-1), (-1), (0), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .triangle 16 1, .corridorLower 2 3, .gapLower 2 5 (![0, 3, 4, 5, 1])]

def cycle0619 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(-2), (4), (0), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 3, 5, 4, 1]), .gapLower 2 5 (![0, 3, 5, 4, 1]), .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 4 0]

def cycle0620 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![(0), (3), (0), (-1), (-1), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 3, 5, 4, 1]), .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 16 0, .gapLower 2 1 (![0, 3, 5, 4, 1])]

def cycle0621 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 0, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![0, 3, 5, 4, 1]), .corridorLower 2 3, .corridorUpper 1 2]

def cycle0622 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .theta 2, .distance 1 2]
    constant := ![(0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 0, .triangle 16 2, .gapLower 2 3 (![0, 3, 5, 4, 1]), .corridorLower 2 5, .corridorUpper 1 2]

def cycle0623 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (0), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 5, 4, 1]), .triangle 10 2, .triangle 13 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0624 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 1 2]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 2, .gapLower 2 4 (![0, 4, 3, 1, 5])]

def cycle0625 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 3, 5, 1]), .gapLower 2 5 (![0, 4, 3, 5, 1]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .triangle 5 0]

def cycle0626 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(0), (3), (0), (0), (-1), (-1), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 3, 5, 1]), .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .gapLower 2 1 (![0, 4, 3, 5, 1])]

def cycle0627 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-1), (0), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 2, .gapLower 2 3 (![0, 4, 3, 5, 1]), .gapLower 2 2 (![0, 4, 3, 5, 1]), .corridorLower 2 4, .corridorUpper 1 2]

def cycle0628 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (0), (0), (-1), (0), (-2), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 3, 5, 1]), .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 2, .gapLower 2 3 (![0, 4, 3, 5, 1]), .triangle 16 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0629 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .corridorLower 2 4, .gapLower 2 5 (![0, 4, 3, 5, 1])]

def cycle0630 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .gapLower 2 5 (![0, 4, 5, 3, 1]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .triangle 5 0]

def cycle0631 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![(0), (3), (0), (0), (-1), (-1), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 4, 5, 3, 1]), .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .gapLower 2 1 (![0, 4, 5, 3, 1])]

def cycle0632 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 2, .gapLower 2 2 (![0, 4, 5, 3, 1]), .corridorLower 2 4, .corridorUpper 1 2]

def cycle0633 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 5, .theta 2, .distance 1 2]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 10 0, .gapLower 2 3 (![0, 4, 5, 3, 1]), .corridorLower 2 5, .corridorUpper 1 2]

def cycle0634 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-1), (-1), (-1), (2)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .corridorLower 2 4, .gapLower 2 5 (![0, 4, 5, 3, 1])]

def cycle0635 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (-1), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 5, 4, 3, 1]), .gapLower 2 5 (![0, 5, 4, 3, 1]), .triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0636 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(0), (3), (-1), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 5, 4, 3, 1]), .corridorUpper 1 2, .triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 19 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0637 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 0, .triangle 19 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0638 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .theta 2, .distance 1 2]
    constant := ![(-1), (0), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 10 0, .triangle 16 2, .gapLower 2 2 (![0, 5, 4, 3, 1]), .corridorLower 2 5, .corridorUpper 1 2]

def cycle0639 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(-1), (-2), (-1), (3)]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 10 0, .gapLower 2 3 (![0, 5, 4, 3, 1]), .corridorLower 2 4, .corridorUpper 1 2]

def cycle0640 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (-1), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 5, 4, 3, 1]), .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0641 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 5, 4, 3, 1]), .triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0642 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![(0), (0), (-2), (0), (-1), (-1), (3)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 15 1, .triangle 18 0, .corridorLower 2 4, .corridorUpper 1 2]

def cycle0643 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 5, 4, 1]), .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0644 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-2), (0), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 5, 4, 3, 1]), .gapLower 2 5 (![0, 5, 4, 3, 1]), .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 15 1, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0645 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-1), (0), (0), (2), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 5, 4, 3, 1]), .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0646 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-1), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 4 1, .triangle 0 1]

def cycle0647 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (-1), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0648 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(0), (2), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0649 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (2), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 0, .triangle 16 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0650 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0651 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0652 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 1 1]

def cycle0653 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 2, 3, 4, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .triangle 0 0]

def cycle0654 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0 (![0, 2, 3, 4, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .triangle 10 1, .triangle 0 0]

def cycle0655 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 1 (![0, 2, 3, 4, 5])]

def cycle0656 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![0, 2, 3, 4, 5]), .triangle 0 0]

def cycle0657 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 3 (![0, 2, 3, 4, 5]), .triangle 1 0]

def cycle0658 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![0, 2, 3, 4, 5]), .triangle 2 0]

def cycle0659 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 3, 4, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0660 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0661 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0662 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0663 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0664 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0665 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0666 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0667 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0668 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0669 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0670 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0671 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0672 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0673 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .triangle 0 0]

def cycle0674 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .triangle 10 1, .triangle 0 0]

def cycle0675 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 2, 3, 5, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .triangle 0 0]

def cycle0676 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .gapLower 1 2 (![0, 2, 3, 5, 4]), .triangle 0 0]

def cycle0677 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 1 (![0, 2, 3, 5, 4])]

def cycle0678 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![0, 2, 3, 5, 4]), .triangle 0 0]

def cycle0679 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 2, .gapLower 1 3 (![0, 2, 3, 5, 4]), .triangle 1 0]

def cycle0680 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 2, 3, 5, 4]), .triangle 3 0]

def cycle0681 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 3, 5, 4]), .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 1 1]

def cycle0682 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .triangle 4 1, .triangle 0 1]

def cycle0683 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 2, 4, 5, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .triangle 0 0]

def cycle0684 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (0), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 0 (![0, 2, 4, 5, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 15 0, .triangle 11 1, .triangle 0 0]

def cycle0685 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 1 (![0, 2, 4, 5, 3])]

def cycle0686 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![0, 2, 4, 5, 3]), .triangle 0 0]

def cycle0687 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 2, .gapLower 1 3 (![0, 2, 4, 5, 3]), .triangle 2 0]

def cycle0688 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 4, 5, 3]), .triangle 3 0]

def cycle0689 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 4, 5, 3]), .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0690 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 19 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0691 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (0), (0), (3), (0), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaOrder 1, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 19 0, .triangle 9 0, .triangle 7 1, .triangle 4 1]

def cycle0692 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 1 (![0, 1, 5, 4, 3]), .triangle 0 1]

def cycle0693 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![0, 1, 5, 4, 3]), .triangle 0 0]

def cycle0694 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (0), (-2), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .gapLower 2 3 (![0, 1, 5, 4, 3]), .triangle 12 0, .triangle 0 0]

def cycle0695 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 11 0, .triangle 0 0]

def cycle0696 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 0, .triangle 0 0]

def cycle0697 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0698 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0699 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 3 0]

def cycle0700 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 5, 4, 3]), .triangle 15 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0701 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 1 1]

def cycle0702 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0703 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 12 0, .triangle 18 1, .triangle 16 1, .gapLower 2 1 (![0, 3, 4, 5, 1]), .triangle 0 1]

def cycle0704 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .gapLower 1 5 (![0, 3, 4, 5, 2]), .gapLower 2 4 (![0, 3, 4, 5, 1]), .triangle 18 1, .gapLower 2 2 (![0, 3, 4, 5, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0705 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .gapLower 1 5 (![0, 3, 4, 5, 2]), .gapLower 2 4 (![0, 3, 4, 5, 1]), .gapLower 2 3 (![0, 3, 4, 5, 1]), .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0706 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 3, 4, 5, 1]), .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0707 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (-1), (0), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 4, 5, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 4, 5, 1]), .triangle 12 0, .triangle 18 1, .triangle 16 1, .triangle 4 0, .triangle 0 1]

def cycle0708 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 1 (![0, 3, 4, 5, 2])]

def cycle0709 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![0, 3, 4, 5, 2]), .triangle 1 0]

def cycle0710 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![0, 3, 4, 5, 2]), .triangle 2 0]

def cycle0711 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 4, 5, 2]), .triangle 3 0]

def cycle0712 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 4, 5, 2]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0713 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 11 2, .triangle 15 0, .triangle 18 0, .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0714 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .triangle 18 0, .triangle 9 0, .triangle 7 1, .triangle 4 1, .triangle 0 1]

def cycle0715 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 1 (![0, 3, 5, 4, 2])]

def cycle0716 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0717 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![0, 3, 5, 4, 2]), .triangle 3 0]

def cycle0718 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 5, 4, 2]), .triangle 15 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0719 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 11 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 1 1]

def cycle0720 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0721 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 4, 5, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0722 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 1 (![0, 4, 5, 3, 2])]

def cycle0723 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 2, .gapLower 1 2 (![0, 4, 5, 3, 2]), .triangle 2 0]

def cycle0724 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 4, 5, 3, 2]), .triangle 3 0]

def cycle0725 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 5, 3, 2]), .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0726 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 5, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0727 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0728 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0729 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 4 0, .triangle 0 1]

def cycle0730 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0731 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0732 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 15 0, .triangle 9 0, .triangle 7 1, .triangle 1 1]

def cycle0733 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 1 0]

def cycle0734 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-1), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .gapLower 0 2 (![1, 2, 3, 4, 5]), .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0735 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 4, 5]), .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0736 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 4 1, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0737 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .triangle 4 1, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0738 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 9 1, .triangle 7 1, .triangle 4 1, .gapLower 0 1 (![1, 2, 3, 4, 5])]

def cycle0739 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 3 (![1, 2, 3, 4, 5]), .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0740 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .triangle 7 1, .gapLower 0 2 (![1, 2, 3, 4, 5]), .triangle 0 1]

def cycle0741 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 2, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 9 1, .triangle 7 1, .gapLower 0 2 (![1, 2, 3, 4, 5])]

def cycle0742 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 2, 3, 4, 5]), .gapLower 0 3 (![1, 2, 3, 4, 5]), .triangle 4 1, .triangle 0 1]

def cycle0743 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .theta 0, .distance 0 5, .distance 0 4, .distance 0 3]
    constant := ![(-1), (2), (0), (-2)]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorLower 0 3, .gapLower 0 5 (![1, 2, 3, 4, 5]), .triangle 9 1, .gapLower 0 3 (![1, 2, 3, 4, 5])]

def cycle0744 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .theta 0, .distance 0 5, .distance 0 4]
    constant := ![(-1), (2), (-2)]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 0 4, .gapLower 0 5 (![1, 2, 3, 4, 5]), .gapLower 0 4 (![1, 2, 3, 4, 5])]

def cycle0745 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0746 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0747 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 5, 4])]

def cycle0748 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 5, 4])]

def cycle0749 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 0 4]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 9 0, .triangle 15 0, .triangle 2 2]

def cycle0750 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 3, 5, 4]), .gapLower 1 5 (![0, 2, 3, 5, 4]), .triangle 15 2, .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 1 1]

def cycle0751 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .gapLower 4 3 (![5, 0, 1, 3, 2]), .triangle 15 2, .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0752 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 2 4, .distance 0 4]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 9 0, .triangle 18 0, .triangle 5 2]

def cycle0753 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 3, 5, 4]), .gapLower 2 5 (![0, 1, 3, 5, 4]), .triangle 18 2, .triangle 12 2, .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1]

def cycle0754 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 2, .gapLower 2 4 (![0, 1, 3, 5, 4]), .gapLower 5 3 (![4, 0, 1, 2, 3]), .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0755 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (0), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 3, 5, 4]), .gapLower 4 3 (![5, 0, 1, 2, 3]), .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4])]

def cycle0756 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 17 0, .gapLower 5 3 (![4, 0, 1, 3, 2]), .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0757 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 2, 3, 5, 4]), .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0758 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 3, 5, 4]), .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4])]

def cycle0759 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .gapLower 5 2 (![4, 0, 3, 1, 2]), .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0760 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (0), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .gapLower 4 2 (![5, 0, 3, 1, 2]), .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0761 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0762 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 2, .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0763 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 2, 5, 4]), .gapLower 1 5 (![0, 3, 2, 5, 4]), .triangle 15 2, .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 1 1]

def cycle0764 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (0), (-3), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 3, 1, 5, 4]), .gapLower 2 5 (![0, 3, 1, 5, 4]), .triangle 11 2, .triangle 15 2, .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1]

def cycle0765 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-2), (0), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .gapLower 2 4 (![0, 3, 1, 5, 4]), .triangle 12 2, .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0766 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 1, 5, 4]), .triangle 5 2, .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4])]

def cycle0767 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 3, 2, 5, 4]), .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0768 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(-1), (0), (0), (2), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 2, 5, 4]), .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4])]

def cycle0769 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 12 0, .gapLower 5 2 (![4, 0, 2, 1, 3]), .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0770 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .gapLower 4 2 (![5, 0, 2, 1, 3]), .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0771 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-1), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0772 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-1), (0), (0), (-3), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0773 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .theta 4, .distance 1 4, .distance 0 4]
    constant := ![(-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 2, 3, 5, 4]), .triangle 9 1, .corridorLower 4 5, .corridorUpper 1 4, .triangle 2 2]

def cycle0774 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4]
    constant := ![(-1), (-1), (0), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.triangle 9 0, .corridorLower 4 5, .thetaOrder 3, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 3, 5, 4])]

def cycle0775 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 5, 4])]

def cycle0776 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 5, 4]), .triangle 0 1]

def cycle0777 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (0), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 2, 3, 5, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .gapLower 4 3 (![5, 0, 1, 3, 2]), .triangle 15 2, .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0778 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 1 (![0, 2, 3, 5, 4])]

def cycle0779 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![0, 2, 3, 5, 4]), .triangle 0 0]

def cycle0780 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .triangle 15 2, .gapLower 1 3 (![0, 2, 3, 5, 4]), .triangle 1 0]

def cycle0781 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 2, 3, 5, 4]), .triangle 3 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0782 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 3, 5, 4]), .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0783 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .gapLower 5 2 (![4, 0, 3, 1, 2]), .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0784 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .gapLower 4 2 (![5, 0, 3, 1, 2]), .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0785 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0786 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 2, .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0787 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0788 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .gapLower 4 2 (![5, 0, 2, 1, 3]), .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0789 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0790 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0791 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (0), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 1 0 (![0, 2, 3, 5, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .gapLower 4 3 (![5, 0, 1, 3, 2]), .triangle 2 2, .gapLower 0 4 (![1, 2, 3, 5, 4]), .triangle 8 1, .triangle 4 1, .triangle 0 1]

def cycle0792 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 2, 3, 5, 4]), .triangle 3 0]

def cycle0793 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 3, 5, 4]), .triangle 2 2, .gapLower 0 4 (![1, 2, 3, 5, 4]), .triangle 8 1, .triangle 4 1, .triangle 0 1]

def cycle0794 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 0, .triangle 8 0, .triangle 4 1, .triangle 0 1]

def cycle0795 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .gapLower 4 2 (![5, 0, 3, 1, 2]), .gapLower 0 4 (![1, 2, 3, 5, 4]), .triangle 8 1, .triangle 4 1, .triangle 0 1]

def cycle0796 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0797 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![1, 2, 3, 5, 4]), .triangle 8 1, .triangle 4 1, .triangle 0 1]

def cycle0798 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 0, .gapLower 4 2 (![5, 0, 2, 1, 3]), .gapLower 0 4 (![1, 2, 3, 5, 4]), .triangle 8 1, .triangle 4 1, .triangle 0 1]

def cycle0799 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![1, 2, 3, 5, 4]), .triangle 8 1, .triangle 4 1, .triangle 0 1]

def cycle0800 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .gapLower 0 5 (![1, 2, 3, 5, 4]), .triangle 9 0, .triangle 15 0, .gapLower 1 3 (![0, 2, 3, 4, 5]), .triangle 1 0]

def cycle0801 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0 (![0, 2, 3, 5, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .triangle 10 1, .triangle 0 0]

def cycle0802 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .triangle 0 0]

def cycle0803 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .triangle 10 1, .triangle 0 0]

def cycle0804 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .gapLower 0 5 (![1, 2, 3, 5, 4]), .triangle 9 0, .triangle 15 0, .triangle 2 0]

def cycle0805 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 3 4, .distance 0 4]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .triangle 7 2]

def cycle0806 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3]
    constant := ![(-2), (3), (0), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.gapLower 3 0 (![0, 5, 4, 1, 2]), .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 19 2, .triangle 8 0]

def cycle0807 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![(-2), (4), (-1), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 0, .triangle 19 2, .gapLower 3 1 (![0, 5, 4, 1, 2]), .triangle 1 1]

def cycle0808 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (0), (-1), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .gapLower 3 4 (![0, 5, 4, 1, 2]), .triangle 13 0, .gapLower 3 2 (![0, 5, 4, 1, 2]), .triangle 8 0, .gapLower 0 2 (![1, 2, 3, 5, 4])]

def cycle0809 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![(-2), (4), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .gapLower 3 4 (![0, 5, 4, 1, 2]), .gapLower 3 3 (![0, 5, 4, 1, 2]), .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 5, 4])]

def cycle0810 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 4 (![0, 5, 4, 1, 2]), .triangle 13 0, .triangle 19 2, .gapLower 3 1 (![0, 5, 4, 1, 2]), .gapLower 0 2 (![1, 2, 3, 5, 4])]

def cycle0811 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![(-2), (0), (0), (0), (0), (2), (0), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaOrder 1, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![0, 5, 4, 1, 2]), .triangle 10 2, .triangle 13 0, .triangle 19 2, .triangle 8 0, .triangle 4 1]

def cycle0812 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 1 (![0, 1, 5, 4, 3]), .triangle 0 1]

def cycle0813 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![0, 1, 5, 4, 3]), .triangle 0 0]

def cycle0814 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 11 0, .triangle 0 0]

def cycle0815 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 0, .triangle 0 0]

def cycle0816 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0817 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0818 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 3 0]

def cycle0819 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 5, 4, 3]), .triangle 2 0]

def cycle0820 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 5, 4]), .triangle 0 1]

def cycle0821 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0822 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (-1), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 11 0, .triangle 16 1, .gapLower 2 1 (![0, 3, 5, 4, 1]), .triangle 0 1]

def cycle0823 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .gapLower 1 5 (![0, 3, 5, 4, 2]), .gapLower 2 4 (![0, 3, 5, 4, 1]), .triangle 18 2, .gapLower 2 2 (![0, 3, 5, 4, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 5, 4])]

def cycle0824 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .gapLower 1 5 (![0, 3, 5, 4, 2]), .gapLower 2 4 (![0, 3, 5, 4, 1]), .gapLower 2 3 (![0, 3, 5, 4, 1]), .triangle 6 0, .gapLower 0 1 (![1, 2, 3, 5, 4])]

def cycle0825 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 3, 5, 4, 1]), .triangle 5 0, .gapLower 0 1 (![1, 2, 3, 5, 4])]

def cycle0826 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 3, 5, 4, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 3, 5, 4, 1]), .triangle 11 0, .triangle 16 1, .triangle 4 0, .triangle 0 1]

def cycle0827 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 1 (![0, 3, 5, 4, 2])]

def cycle0828 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .triangle 15 2, .gapLower 1 2 (![0, 3, 5, 4, 2]), .triangle 1 0]

def cycle0829 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![0, 3, 5, 4, 2]), .triangle 3 0]

def cycle0830 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 3, 5, 4, 2]), .triangle 2 0]

def cycle0831 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 3, 5, 4, 2]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0832 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 4 0, .gapLower 0 1 (![1, 2, 3, 5, 4])]

def cycle0833 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 16 0, .triangle 4 0, .triangle 0 1]

def cycle0834 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 0, .triangle 7 0, .triangle 4 1, .triangle 0 1]

def cycle0835 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0836 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 2 0]

def cycle0837 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 5, 4]), .triangle 0 1]

def cycle0838 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 5, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 0, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 5, 4]), .gapLower 0 1 (![1, 2, 3, 5, 4])]

def cycle0839 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 2 (![1, 2, 3, 5, 4]), .gapLower 0 1 (![1, 2, 3, 5, 4])]

def cycle0840 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .gapLower 0 1 (![1, 2, 3, 5, 4])]

def cycle0841 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 2, 3, 5, 4]), .triangle 8 1, .triangle 4 1, .gapLower 0 1 (![1, 2, 3, 5, 4])]

def cycle0842 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 3, 5, 4]), .triangle 7 1, .triangle 4 1, .gapLower 0 1 (![1, 2, 3, 5, 4])]

def cycle0843 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (0), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4]), .gapLower 0 2 (![1, 2, 3, 5, 4]), .triangle 0 1]

def cycle0844 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 2, 3, 5, 4]), .triangle 8 1, .gapLower 0 2 (![1, 2, 3, 5, 4]), .triangle 0 1]

def cycle0845 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![(-1), (2), (0), (-2)]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorLower 0 2, .gapLower 0 5 (![1, 2, 3, 5, 4]), .triangle 7 1, .gapLower 0 2 (![1, 2, 3, 5, 4])]

def cycle0846 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 2, 3, 5, 4]), .gapLower 0 3 (![1, 2, 3, 5, 4]), .triangle 4 1, .triangle 0 1]

def cycle0847 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .theta 0, .distance 0 4, .distance 0 5, .distance 0 3]
    constant := ![(-1), (2), (0), (-2)]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorLower 0 3, .gapLower 0 5 (![1, 2, 3, 5, 4]), .triangle 9 2, .gapLower 0 3 (![1, 2, 3, 5, 4])]

def cycle0848 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .theta 0, .distance 0 4]
    constant := ![(-2), (-1), (2)]
    coefficient := ![0, 0, 1]
    strict := ![false, false, false] }
  origin := ![.gapLower 0 4 (![1, 2, 3, 5, 4]), .corridorLower 0 5, .gapLower 0 5 (![1, 2, 3, 5, 4])]

def cycle0849 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0850 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0851 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 2 (![1, 2, 5, 3, 4]), .gapLower 0 1 (![1, 2, 5, 3, 4])]

def cycle0852 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 2 (![1, 2, 5, 3, 4])]

def cycle0853 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![1, 2, 5, 3, 4]), .corridorLower 0 5, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0]

def cycle0854 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaLower 3, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 2, 5, 3, 4])]

def cycle0855 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, true] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 5, 3, 4]), .triangle 7 1]

def cycle0856 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 2 (![1, 2, 5, 3, 4]), .gapLower 0 1 (![1, 2, 5, 3, 4])]

def cycle0857 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 2 (![1, 2, 5, 3, 4]), .triangle 0 1]

def cycle0858 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![1, 2, 5, 3, 4]), .triangle 3 1]

def cycle0859 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .distance 0 3]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 8 0, .triangle 14 0, .triangle 1 2]

def cycle0860 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 3, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .triangle 0 0]

def cycle0861 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 16 0, .triangle 7 2, .gapLower 0 4 (![1, 2, 5, 3, 4])]

def cycle0862 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 2, .gapLower 1 2 (![0, 2, 5, 3, 4]), .gapLower 1 1 (![0, 2, 5, 3, 4])]

def cycle0863 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 2, .gapLower 1 2 (![0, 2, 5, 3, 4]), .triangle 0 0]

def cycle0864 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 3 (![0, 2, 5, 3, 4]), .triangle 3 0]

def cycle0865 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 2, .gapLower 1 4 (![0, 2, 5, 3, 4]), .triangle 1 0]

def cycle0866 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![0, 2, 5, 3, 4]), .triangle 2 2, .gapLower 0 4 (![1, 2, 5, 3, 4])]

def cycle0867 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![1, 2, 5, 3, 4])]

def cycle0868 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0869 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![1, 2, 5, 3, 4])]

def cycle0870 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 2 4, .triangle 11 0, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0871 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 11 0, .triangle 5 2, .gapLower 0 4 (![1, 2, 5, 3, 4])]

def cycle0872 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 2, .gapLower 0 4 (![1, 2, 5, 3, 4])]

def cycle0873 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (0), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 3, 4]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .triangle 14 2, .triangle 12 1, .triangle 0 0]

def cycle0874 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 16 0, .triangle 10 0, .triangle 0 0]

def cycle0875 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 0, .triangle 13 0, .triangle 14 2, .triangle 12 1, .triangle 0 0]

def cycle0876 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (3), (0), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 10 2, .triangle 13 0, .triangle 7 0]

def cycle0877 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0878 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .distance 0 3]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 8 0, .triangle 17 0, .triangle 4 2]

def cycle0879 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 0 2]
    constant := ![(-2), (3), (-1), (0), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0 (![0, 5, 3, 4, 1]), .corridorUpper 1 2, .triangle 11 0, .triangle 16 1, .triangle 17 2, .triangle 6 0]

def cycle0880 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 5, 3, 4, 2]), .gapLower 1 5 (![0, 5, 3, 4, 2]), .triangle 11 0, .triangle 16 1, .triangle 17 2, .gapLower 2 1 (![0, 5, 3, 4, 1]), .triangle 0 1]

def cycle0881 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 3, 4, 2]), .gapLower 1 5 (![0, 5, 3, 4, 2]), .gapLower 2 4 (![0, 5, 3, 4, 1]), .triangle 16 1, .gapLower 2 2 (![0, 5, 3, 4, 1]), .triangle 6 0, .gapLower 0 1 (![1, 2, 5, 3, 4])]

def cycle0882 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 3, 4, 2]), .gapLower 1 5 (![0, 5, 3, 4, 2]), .gapLower 2 4 (![0, 5, 3, 4, 1]), .gapLower 2 3 (![0, 5, 3, 4, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 5, 3, 4])]

def cycle0883 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 3, 4, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 5, 3, 4, 1]), .triangle 5 0, .gapLower 0 1 (![1, 2, 5, 3, 4])]

def cycle0884 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (-1), (0), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 5, 3, 4, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 5, 3, 4, 1]), .triangle 11 0, .triangle 16 1, .triangle 17 2, .triangle 6 0, .triangle 0 1]

def cycle0885 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .triangle 14 2, .gapLower 1 1 (![0, 5, 3, 4, 2])]

def cycle0886 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 13 0, .gapLower 1 2 (![0, 5, 3, 4, 2]), .triangle 3 0]

def cycle0887 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 11 2, .gapLower 1 3 (![0, 5, 3, 4, 2]), .triangle 1 0]

def cycle0888 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 3, 4, 2]), .triangle 2 0]

def cycle0889 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 5, 3, 4]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 3, 4, 2]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0890 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (3), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 0, .triangle 7 0]

def cycle0891 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .triangle 8 2, .gapLower 0 2 (![1, 2, 5, 3, 4]), .gapLower 0 1 (![1, 2, 5, 3, 4])]

def cycle0892 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![1, 2, 5, 3, 4]), .triangle 6 1, .gapLower 0 1 (![1, 2, 5, 3, 4])]

def cycle0893 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 2, 5, 3, 4]), .triangle 4 1, .gapLower 0 1 (![1, 2, 5, 3, 4])]

def cycle0894 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 5, 3, 4]), .triangle 7 1, .triangle 8 2, .gapLower 0 2 (![1, 2, 5, 3, 4]), .gapLower 0 1 (![1, 2, 5, 3, 4])]

def cycle0895 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 7 0, .gapLower 0 3 (![1, 2, 5, 3, 4]), .gapLower 0 2 (![1, 2, 5, 3, 4]), .triangle 0 1]

def cycle0896 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 2, 5, 3, 4]), .triangle 8 2, .gapLower 0 2 (![1, 2, 5, 3, 4]), .triangle 0 1]

def cycle0897 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 2, .gapLower 0 5 (![1, 2, 5, 3, 4]), .triangle 7 1, .triangle 8 2, .gapLower 0 2 (![1, 2, 5, 3, 4])]

def cycle0898 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 1 4, .triangle 2 2, .gapLower 0 4 (![1, 2, 5, 3, 4]), .gapLower 0 3 (![1, 2, 5, 3, 4]), .triangle 6 1, .triangle 0 1]

def cycle0899 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 5, .theta 0, .distance 0 4, .distance 0 3]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 3 (![1, 2, 5, 3, 4]), .corridorLower 0 5, .gapLower 0 5 (![1, 2, 5, 3, 4]), .triangle 7 1]

def cycle0900 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.triangle 8 0, .corridorLower 3 5, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 5, 3, 4]), .gapLower 0 4 (![1, 2, 5, 3, 4])]

def cycle0901 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0902 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0903 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 1 (![1, 2, 4, 3, 5])]

def cycle0904 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (0), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .triangle 7 2, .gapLower 0 2 (![1, 2, 4, 3, 5])]

def cycle0905 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 4, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3]
    constant := ![(-3), (-1), (0), (0), (3), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3 (![1, 2, 4, 3, 5]), .corridorLower 0 4, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0]

def cycle0906 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (3), (0), (-3)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 2, 4, 3, 5])]

def cycle0907 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (1), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, true] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 4, 3, 5]), .triangle 8 1]

def cycle0908 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 1 (![1, 2, 4, 3, 5])]

def cycle0909 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .triangle 7 2, .gapLower 0 2 (![1, 2, 4, 3, 5]), .triangle 0 1]

def cycle0910 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![1, 2, 4, 3, 5]), .triangle 2 1]

def cycle0911 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 0 3]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 7 0, .triangle 13 0, .triangle 1 2]

def cycle0912 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .distance 0 3]
    constant := ![(-1), (-1), (0)]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.triangle 7 0, .triangle 16 0, .triangle 4 2]

def cycle0913 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 2, 4, 3, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .triangle 0 0]

def cycle0914 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 4, 3, 5])]

def cycle0915 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 1 (![0, 2, 4, 3, 5])]

def cycle0916 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 2, .gapLower 1 2 (![0, 2, 4, 3, 5]), .triangle 0 0]

def cycle0917 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 3 (![0, 2, 4, 3, 5]), .triangle 2 0]

def cycle0918 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 2, .gapLower 1 4 (![0, 2, 4, 3, 5]), .triangle 1 0]

def cycle0919 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (2), (0), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .gapLower 1 5 (![0, 2, 4, 3, 5]), .triangle 3 2, .gapLower 0 4 (![1, 2, 4, 3, 5])]

def cycle0920 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 2, 4, 3, 5])]

def cycle0921 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (3), (0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 4, 3, 5])]

def cycle0922 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (3), (-1), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![1, 2, 4, 3, 5])]

def cycle0923 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0924 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 2 5, .triangle 12 0, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0925 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 12 0, .triangle 6 2, .gapLower 0 4 (![1, 2, 4, 3, 5])]

def cycle0926 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (3), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 2, .gapLower 0 4 (![1, 2, 4, 3, 5])]

def cycle0927 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (3), (0), (0), (-1), (0), (-2)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 2, .gapLower 0 4 (![1, 2, 4, 3, 5])]

def cycle0928 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (0), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 0 (![0, 2, 4, 3, 5]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 15 0, .triangle 11 1, .triangle 0 0]

def cycle0929 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .triangle 0 0]

def cycle0930 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 15 0, .triangle 11 1, .triangle 0 0]

def cycle0931 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (3), (0), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 14 0, .triangle 8 0]

def cycle0932 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .thetaLower 2, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 5 1]

def cycle0933 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 1 (![0, 1, 5, 4, 3]), .triangle 0 1]

def cycle0934 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![0, 1, 5, 4, 3]), .triangle 0 0]

def cycle0935 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 11 0, .triangle 0 0]

def cycle0936 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 0, .triangle 0 0]

def cycle0937 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle0938 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle0939 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 3 0]

def cycle0940 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (2), (0), (-1), (-1), (3), (0), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .gapLower 0 5 (![1, 2, 4, 3, 5]), .triangle 8 1, .triangle 7 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 5, 4, 3]), .triangle 15 0, .triangle 9 0, .triangle 5 1, .triangle 0 1]

def cycle0941 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 3, 5]), .triangle 0 1]

def cycle0942 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle0943 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2]
    constant := ![(-2), (3), (-1), (0), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0 (![0, 4, 3, 5, 1]), .corridorUpper 1 2, .triangle 12 0, .triangle 17 1, .triangle 4 0]

def cycle0944 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (-1), (0), (0), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 3, 5, 2]), .gapLower 1 5 (![0, 4, 3, 5, 2]), .triangle 12 0, .triangle 17 1, .triangle 16 2, .gapLower 2 1 (![0, 4, 3, 5, 1]), .triangle 0 1]

def cycle0945 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 3, 5, 2]), .gapLower 1 5 (![0, 4, 3, 5, 2]), .gapLower 2 4 (![0, 4, 3, 5, 1]), .triangle 17 1, .gapLower 2 2 (![0, 4, 3, 5, 1]), .triangle 5 0, .gapLower 0 1 (![1, 2, 4, 3, 5])]

def cycle0946 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 3, 5, 2]), .gapLower 1 5 (![0, 4, 3, 5, 2]), .gapLower 2 4 (![0, 4, 3, 5, 1]), .gapLower 2 3 (![0, 4, 3, 5, 1]), .triangle 4 0, .gapLower 0 1 (![1, 2, 4, 3, 5])]

def cycle0947 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 4, 3, 5, 2]), .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 4 (![0, 4, 3, 5, 1]), .triangle 6 0, .gapLower 0 1 (![1, 2, 4, 3, 5])]

def cycle0948 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (-1), (0), (-1), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 0 (![0, 4, 3, 5, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 4, 3, 5, 1]), .triangle 12 0, .triangle 17 1, .triangle 4 0, .triangle 0 1]

def cycle0949 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 3]
    constant := ![(0), (0), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.gapLower 3 3 (![4, 0, 2, 1, 5]), .triangle 16 2, .triangle 18 0, .triangle 15 2, .gapLower 1 3 (![0, 4, 3, 5, 2])]

def cycle0950 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .triangle 13 2, .gapLower 1 1 (![0, 4, 3, 5, 2])]

def cycle0951 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 14 0, .gapLower 1 2 (![0, 4, 3, 5, 2]), .triangle 2 0]

def cycle0952 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 12 2, .gapLower 1 3 (![0, 4, 3, 5, 2]), .triangle 1 0]

def cycle0953 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 4, 3, 5, 2]), .triangle 3 0]

def cycle0954 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 4, 3, 5, 2]), .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0955 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (3), (0), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 10 2, .triangle 14 0, .triangle 8 0]

def cycle0956 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (4), (0), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .triangle 5 0, .gapLower 0 1 (![1, 2, 4, 3, 5])]

def cycle0957 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (-1), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 5, 4, 3, 2]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 5 1, .triangle 0 1]

def cycle0958 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 18 0, .triangle 5 0, .triangle 0 1]

def cycle0959 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 16 2, .triangle 18 0, .triangle 9 0, .triangle 5 1, .triangle 0 1]

def cycle0960 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .triangle 13 2, .gapLower 1 2 (![0, 5, 4, 3, 2]), .triangle 3 0]

def cycle0961 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 2, .gapLower 1 3 (![0, 5, 4, 3, 2]), .triangle 15 0, .triangle 9 0, .triangle 5 1, .triangle 0 1]

def cycle0962 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 4 (![0, 5, 4, 3, 2]), .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 3, 5]), .triangle 0 1]

def cycle0963 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 3, 5]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 5, 4, 3, 2]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 3, 5]), .gapLower 0 1 (![1, 2, 4, 3, 5])]

def cycle0964 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 3, 5]), .gapLower 0 1 (![1, 2, 4, 3, 5])]

def cycle0965 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![1, 2, 4, 3, 5]), .triangle 5 1, .gapLower 0 1 (![1, 2, 4, 3, 5])]

def cycle0966 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 2, 4, 3, 5]), .triangle 4 1, .gapLower 0 1 (![1, 2, 4, 3, 5])]

def cycle0967 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 5 (![1, 2, 4, 3, 5]), .triangle 8 1, .triangle 4 1, .gapLower 0 1 (![1, 2, 4, 3, 5])]

def cycle0968 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-2), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 3 5, .triangle 8 0, .gapLower 0 3 (![1, 2, 4, 3, 5]), .gapLower 0 2 (![1, 2, 4, 3, 5]), .triangle 0 1]

def cycle0969 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 2, 4, 3, 5]), .triangle 7 2, .gapLower 0 2 (![1, 2, 4, 3, 5]), .triangle 0 1]

def cycle0970 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![(-1), (2), (0), (0), (-2)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 2, .gapLower 0 5 (![1, 2, 4, 3, 5]), .triangle 8 1, .triangle 7 2, .gapLower 0 2 (![1, 2, 4, 3, 5])]

def cycle0971 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 1 5, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (0), (-2), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 1 5, .triangle 3 2, .gapLower 0 4 (![1, 2, 4, 3, 5]), .gapLower 0 3 (![1, 2, 4, 3, 5]), .triangle 5 1, .triangle 0 1]

def cycle0972 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 4, .theta 0, .distance 0 5, .distance 0 3]
    constant := ![(-2), (-1), (2), (0)]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 3 (![1, 2, 4, 3, 5]), .corridorLower 0 4, .gapLower 0 5 (![1, 2, 4, 3, 5]), .triangle 8 1]

def cycle0973 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 5, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (2), (-2)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 4, 3, 5]), .gapLower 0 4 (![1, 2, 4, 3, 5])]

def cycle0974 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle0975 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 0, .triangle 0 1]

def cycle0976 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 1 (![1, 2, 4, 5, 3])]

def cycle0977 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-1), (0), (0), (3), (-1), (-3)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 5, 3])]

def cycle0978 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(0), (-3), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 8 2, .gapLower 0 3 (![1, 2, 4, 5, 3]), .triangle 7 1, .corridorLower 3 4, .corridorUpper 1 3, .triangle 1 2]

def cycle0979 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .theta 3, .distance 1 3, .distance 0 3]
    constant := ![(-3), (0), (0), (-1), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 0 4 (![1, 2, 4, 5, 3]), .triangle 9 1, .triangle 7 1, .corridorLower 3 4, .corridorUpper 1 3, .triangle 1 2]

def cycle0980 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 3]
    constant := ![(-1), (-1), (0), (0), (0), (1)]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false] }
  origin := ![.triangle 7 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 5 (![1, 2, 4, 5, 3])]

def cycle0981 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 4 0, .gapLower 0 1 (![1, 2, 4, 5, 3])]

def cycle0982 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 5, 3]), .triangle 0 1]

def cycle0983 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (3), (0), (-1), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 2, 4, 5, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .gapLower 5 3 (![3, 0, 1, 4, 2]), .triangle 3 2, .gapLower 0 3 (![1, 2, 4, 5, 3]), .triangle 5 1, .triangle 0 1]

def cycle0984 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 1 (![0, 2, 4, 5, 3])]

def cycle0985 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 15 0, .gapLower 1 2 (![0, 2, 4, 5, 3]), .triangle 0 0]

def cycle0986 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 14 2, .gapLower 1 3 (![0, 2, 4, 5, 3]), .triangle 2 0]

def cycle0987 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 4, 5, 3]), .triangle 3 2, .gapLower 0 3 (![1, 2, 4, 5, 3]), .triangle 5 1, .triangle 0 1]

def cycle0988 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 4, 5, 3]), .triangle 1 2, .triangle 8 2, .gapLower 0 3 (![1, 2, 4, 5, 3]), .triangle 5 1, .triangle 0 1]

def cycle0989 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 0, .gapLower 5 2 (![3, 0, 4, 1, 2]), .gapLower 0 3 (![1, 2, 4, 5, 3]), .triangle 5 1, .triangle 0 1]

def cycle0990 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 2, .gapLower 0 3 (![1, 2, 4, 5, 3]), .triangle 5 1, .triangle 0 1]

def cycle0991 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 11 0, .triangle 5 0, .triangle 0 1]

def cycle0992 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (0), (-2), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .triangle 8 2, .gapLower 0 3 (![1, 2, 4, 5, 3]), .triangle 5 1, .triangle 0 1]

def cycle0993 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 4, 5, 3]), .triangle 3 0]

def cycle0994 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 4, 5, 3]), .triangle 1 2, .gapLower 0 4 (![1, 2, 4, 5, 3]), .triangle 9 1, .triangle 5 1, .triangle 0 1]

def cycle0995 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![(0), (-1), (-1), (-2), (3), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 13 2, .triangle 15 0, .triangle 19 0, .gapLower 3 0 (![4, 5, 0, 1, 2]), .corridorUpper 2 3, .triangle 10 2]

def cycle0996 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (0), (-2), (-1), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 4 (![1, 2, 4, 5, 3]), .gapLower 5 1 (![3, 0, 4, 1, 2]), .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0997 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (0), (-2), (0), (0), (3), (0), (0)]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, true, false, true, true] }
  origin := ![.gapLower 0 4 (![1, 2, 4, 5, 3]), .triangle 8 1, .gapLower 5 0 (![3, 0, 4, 1, 2]), .thetaOrder 4, .thetaOrder 3, .corridorUpper 2 3, .triangle 10 2, .triangle 1 2]

def cycle0998 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3]
    constant := ![(-2), (-2), (-1), (4), (0), (0)]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, true] }
  origin := ![.gapLower 0 4 (![1, 2, 4, 5, 3]), .gapLower 5 1 (![3, 0, 4, 1, 2]), .corridorLower 3 5, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 10 2, .triangle 1 2]

def cycle0999 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 1]
    constant := ![(-2), (4), (0), (-1), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 13 2, .triangle 15 0, .gapLower 5 2 (![3, 0, 4, 1, 2]), .triangle 3 1]

def cycle1000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![(-2), (4), (0), (0), (0), (-2), (-1), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .gapLower 3 4 (![4, 5, 0, 1, 2]), .triangle 13 2, .triangle 15 2, .gapLower 5 3 (![3, 0, 4, 1, 2]), .triangle 9 0, .gapLower 0 2 (![1, 2, 4, 5, 3])]

def cycle1001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 5 4 (![3, 0, 4, 1, 2]), .triangle 3 0]

def cycle1002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (-1), (-1)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 5, .gapLower 5 5 (![3, 0, 4, 1, 2]), .triangle 12 0, .triangle 0 0]

def cycle1003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2]
    constant := ![(-2), (4), (0), (-2), (-2), (0)]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 2 0 (![0, 1, 5, 4, 3]), .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 2, .gapLower 3 3 (![4, 5, 0, 1, 2]), .gapLower 0 4 (![1, 2, 4, 5, 3]), .triangle 6 1]

def cycle1004 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![(0), (-1), (-1), (0), (3), (-2)]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 13 2, .triangle 15 0, .triangle 19 0, .gapLower 3 0 (![4, 5, 0, 1, 2]), .corridorUpper 2 3, .gapLower 3 4 (![4, 5, 0, 1, 2])]

def cycle1005 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .gapLower 3 5 (![4, 5, 0, 1, 2]), .triangle 4 2, .gapLower 0 4 (![1, 2, 4, 5, 3]), .triangle 3 1]

def cycle1006 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 4 5, .distance 0 4]
    constant := ![(0), (-1), (-1)]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.triangle 7 1, .triangle 19 0, .triangle 9 0]

def cycle1007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 2 1 (![0, 1, 5, 4, 3]), .triangle 0 1]

def cycle1008 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 2, .gapLower 2 2 (![0, 1, 5, 4, 3]), .triangle 0 0]

def cycle1009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 4 (![0, 1, 5, 4, 3]), .triangle 11 0, .triangle 0 0]

def cycle1010 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (0), (2), (0), (0), (-1), (-1), (0), (0)]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, true, true] }
  origin := ![.gapLower 1 0 (![0, 2, 5, 4, 3]), .thetaOrder 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 5 (![0, 1, 5, 4, 3]), .triangle 10 2, .triangle 13 2, .triangle 15 0, .triangle 9 0, .triangle 5 1, .triangle 0 1]

def cycle1011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-2)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .gapLower 1 1 (![0, 2, 5, 4, 3])]

def cycle1012 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .triangle 15 2, .gapLower 1 2 (![0, 2, 5, 4, 3]), .triangle 0 0]

def cycle1013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (0), (-2), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 2, .triangle 13 2, .gapLower 1 3 (![0, 2, 5, 4, 3]), .triangle 3 0]

def cycle1014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4]
    constant := ![(0), (-1), (3), (0), (-2), (-1), (-1)]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 7 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 2, .gapLower 1 4 (![0, 2, 5, 4, 3]), .triangle 15 0, .triangle 9 0]

def cycle1015 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (2), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 1, .gapLower 1 5 (![0, 2, 5, 4, 3]), .triangle 1 2, .gapLower 0 4 (![1, 2, 4, 5, 3]), .triangle 9 1, .triangle 5 1, .triangle 0 1]

def cycle1016 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 12 0, .triangle 6 0, .triangle 0 1]

def cycle1017 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (0), (-2), (0), (0), (0)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 10 0, .triangle 4 2, .gapLower 0 4 (![1, 2, 4, 5, 3]), .triangle 9 1, .triangle 5 1, .triangle 0 1]

def cycle1018 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .gapLower 0 5 (![1, 2, 4, 5, 3]), .triangle 7 0, .triangle 13 0, .triangle 1 0]

def cycle1019 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![(-2), (2), (-1), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .gapLower 0 5 (![1, 2, 4, 5, 3]), .triangle 8 0, .triangle 14 0, .triangle 1 0]

def cycle1020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (-1), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 18 0, .triangle 11 0, .triangle 0 0]

def cycle1021 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![(-2), (0), (0), (3), (0), (-1), (-1), (0), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 16 2, .triangle 18 0, .triangle 15 0, .triangle 11 1, .triangle 0 0]

def cycle1022 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-1), (-2), (-1), (3), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .gapLower 0 5 (![1, 2, 4, 5, 3]), .triangle 8 0, .gapLower 3 1 (![4, 5, 0, 1, 2]), .corridorLower 3 4, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def cycle1023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 5, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-2), (2), (-2), (-1), (3), (-1), (-1)]
    coefficient := ![0, 1, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 4, 5, 3]), .gapLower 0 5 (![1, 2, 4, 5, 3]), .gapLower 3 2 (![4, 5, 0, 1, 2]), .corridorLower 3 5, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

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
  | 0 => some (.leaf 0)
  | 1 => some (.leaf 1)
  | 2 => some (.triangle 10 0 1)
  | 3 => some (.leaf 2)
  | 4 => some (.leaf 3)
  | 5 => some (.leaf 4)
  | 6 => some (.leaf 5)
  | 7 => some (.leaf 6)
  | 8 => some (.leaf 7)
  | 9 => some (.triangle 16 7 8)
  | 10 => some (.leaf 8)
  | 11 => some (.leaf 9)
  | 12 => some (.leaf 10)
  | 13 => some (.leaf 11)
  | 14 => some (.leaf 12)
  | 15 => some (.leaf 13)
  | 16 => some (.leaf 14)
  | 17 => some (.leaf 15)
  | 18 => some (.positive 1 (![12, 13, 14, 15, 16, 17]))
  | 19 => some (.leaf 16)
  | 20 => some (.triangle 18 18 19)
  | 21 => some (.leaf 17)
  | 22 => some (.triangle 17 20 21)
  | 23 => some (.leaf 18)
  | 24 => some (.leaf 19)
  | 25 => some (.triangle 17 23 24)
  | 26 => some (.leaf 20)
  | 27 => some (.triangle 18 25 26)
  | 28 => some (.triangle 16 22 27)
  | 29 => some (.leaf 21)
  | 30 => some (.positive 0 (![6, 9, 10, 11, 28, 29]))
  | 31 => some (.leaf 22)
  | 32 => some (.triangle 15 30 31)
  | 33 => some (.leaf 23)
  | 34 => some (.triangle 14 32 33)
  | 35 => some (.leaf 24)
  | 36 => some (.leaf 25)
  | 37 => some (.leaf 26)
  | 38 => some (.leaf 27)
  | 39 => some (.triangle 18 37 38)
  | 40 => some (.triangle 16 36 39)
  | 41 => some (.leaf 28)
  | 42 => some (.leaf 29)
  | 43 => some (.leaf 30)
  | 44 => some (.leaf 31)
  | 45 => some (.positive 0 (![35, 40, 41, 42, 43, 44]))
  | 46 => some (.leaf 32)
  | 47 => some (.triangle 14 45 46)
  | 48 => some (.leaf 33)
  | 49 => some (.triangle 15 47 48)
  | 50 => some (.triangle 13 34 49)
  | 51 => some (.leaf 34)
  | 52 => some (.triangle 12 50 51)
  | 53 => some (.leaf 35)
  | 54 => some (.leaf 36)
  | 55 => some (.leaf 37)
  | 56 => some (.triangle 17 54 55)
  | 57 => some (.leaf 38)
  | 58 => some (.leaf 39)
  | 59 => some (.leaf 40)
  | 60 => some (.leaf 41)
  | 61 => some (.positive 0 (![53, 56, 57, 58, 59, 60]))
  | 62 => some (.triangle 14 61 46)
  | 63 => some (.triangle 12 62 51)
  | 64 => some (.leaf 42)
  | 65 => some (.triangle 15 63 64)
  | 66 => some (.triangle 11 52 65)
  | 67 => some (.leaf 43)
  | 68 => some (.leaf 44)
  | 69 => some (.leaf 45)
  | 70 => some (.triangle 18 68 69)
  | 71 => some (.leaf 46)
  | 72 => some (.leaf 47)
  | 73 => some (.leaf 48)
  | 74 => some (.leaf 49)
  | 75 => some (.positive 0 (![67, 70, 71, 72, 73, 74]))
  | 76 => some (.triangle 15 75 31)
  | 77 => some (.leaf 50)
  | 78 => some (.triangle 12 76 77)
  | 79 => some (.leaf 51)
  | 80 => some (.leaf 52)
  | 81 => some (.leaf 53)
  | 82 => some (.leaf 54)
  | 83 => some (.leaf 55)
  | 84 => some (.leaf 56)
  | 85 => some (.leaf 57)
  | 86 => some (.positive 1 (![80, 81, 82, 83, 84, 85]))
  | 87 => some (.leaf 58)
  | 88 => some (.triangle 16 86 87)
  | 89 => some (.leaf 59)
  | 90 => some (.leaf 60)
  | 91 => some (.leaf 61)
  | 92 => some (.leaf 62)
  | 93 => some (.positive 0 (![79, 88, 89, 90, 91, 92]))
  | 94 => some (.leaf 63)
  | 95 => some (.triangle 12 93 94)
  | 96 => some (.leaf 64)
  | 97 => some (.triangle 15 95 96)
  | 98 => some (.triangle 11 78 97)
  | 99 => some (.triangle 14 98 33)
  | 100 => some (.leaf 65)
  | 101 => some (.leaf 66)
  | 102 => some (.leaf 67)
  | 103 => some (.triangle 16 101 102)
  | 104 => some (.leaf 68)
  | 105 => some (.leaf 69)
  | 106 => some (.leaf 70)
  | 107 => some (.leaf 71)
  | 108 => some (.positive 0 (![100, 103, 104, 105, 106, 107]))
  | 109 => some (.triangle 12 108 94)
  | 110 => some (.leaf 72)
  | 111 => some (.triangle 14 109 110)
  | 112 => some (.leaf 73)
  | 113 => some (.triangle 15 111 112)
  | 114 => some (.triangle 13 99 113)
  | 115 => some (.triangle 10 66 114)
  | 116 => some (.leaf 74)
  | 117 => some (.leaf 75)
  | 118 => some (.leaf 76)
  | 119 => some (.positive 1 (![117, 13, 14, 15, 16, 118]))
  | 120 => some (.leaf 77)
  | 121 => some (.triangle 18 119 120)
  | 122 => some (.leaf 78)
  | 123 => some (.triangle 17 121 122)
  | 124 => some (.leaf 79)
  | 125 => some (.triangle 17 23 124)
  | 126 => some (.leaf 80)
  | 127 => some (.triangle 18 125 126)
  | 128 => some (.triangle 16 123 127)
  | 129 => some (.leaf 81)
  | 130 => some (.leaf 82)
  | 131 => some (.leaf 83)
  | 132 => some (.leaf 84)
  | 133 => some (.triangle 19 131 132)
  | 134 => some (.positive 1 (![129, 130, 14, 15, 16, 133]))
  | 135 => some (.leaf 85)
  | 136 => some (.leaf 86)
  | 137 => some (.leaf 87)
  | 138 => some (.leaf 88)
  | 139 => some (.leaf 89)
  | 140 => some (.leaf 90)
  | 141 => some (.positive 1 (![135, 136, 137, 138, 139, 140]))
  | 142 => some (.triangle 18 134 141)
  | 143 => some (.leaf 91)
  | 144 => some (.triangle 17 142 143)
  | 145 => some (.leaf 92)
  | 146 => some (.leaf 93)
  | 147 => some (.leaf 94)
  | 148 => some (.leaf 95)
  | 149 => some (.leaf 96)
  | 150 => some (.leaf 97)
  | 151 => some (.positive 1 (![145, 146, 147, 148, 149, 150]))
  | 152 => some (.triangle 17 23 151)
  | 153 => some (.leaf 98)
  | 154 => some (.leaf 99)
  | 155 => some (.leaf 100)
  | 156 => some (.leaf 101)
  | 157 => some (.triangle 19 155 156)
  | 158 => some (.leaf 102)
  | 159 => some (.leaf 103)
  | 160 => some (.leaf 104)
  | 161 => some (.positive 1 (![153, 154, 157, 158, 159, 160]))
  | 162 => some (.triangle 18 152 161)
  | 163 => some (.triangle 16 144 162)
  | 164 => some (.positive 0 (![116, 9, 10, 11, 128, 163]))
  | 165 => some (.leaf 105)
  | 166 => some (.leaf 106)
  | 167 => some (.leaf 107)
  | 168 => some (.triangle 16 166 167)
  | 169 => some (.leaf 108)
  | 170 => some (.leaf 109)
  | 171 => some (.leaf 110)
  | 172 => some (.leaf 111)
  | 173 => some (.leaf 112)
  | 174 => some (.leaf 113)
  | 175 => some (.positive 1 (![171, 172, 137, 138, 173, 174]))
  | 176 => some (.triangle 18 170 175)
  | 177 => some (.leaf 114)
  | 178 => some (.triangle 17 176 177)
  | 179 => some (.leaf 115)
  | 180 => some (.triangle 16 178 179)
  | 181 => some (.leaf 116)
  | 182 => some (.leaf 117)
  | 183 => some (.leaf 118)
  | 184 => some (.positive 1 (![181, 182, 137, 138, 139, 183]))
  | 185 => some (.triangle 18 170 184)
  | 186 => some (.leaf 119)
  | 187 => some (.triangle 17 185 186)
  | 188 => some (.leaf 120)
  | 189 => some (.triangle 16 187 188)
  | 190 => some (.leaf 121)
  | 191 => some (.leaf 122)
  | 192 => some (.leaf 123)
  | 193 => some (.leaf 124)
  | 194 => some (.leaf 125)
  | 195 => some (.leaf 126)
  | 196 => some (.leaf 127)
  | 197 => some (.leaf 128)
  | 198 => some (.leaf 129)
  | 199 => some (.leaf 130)
  | 200 => some (.positive 3 (![194, 195, 196, 197, 198, 199]))
  | 201 => some (.leaf 131)
  | 202 => some (.leaf 132)
  | 203 => some (.leaf 133)
  | 204 => some (.leaf 134)
  | 205 => some (.positive 2 (![193, 200, 201, 202, 203, 204]))
  | 206 => some (.triangle 19 192 205)
  | 207 => some (.positive 1 (![190, 191, 137, 138, 139, 206]))
  | 208 => some (.triangle 18 170 207)
  | 209 => some (.triangle 17 208 186)
  | 210 => some (.leaf 135)
  | 211 => some (.leaf 136)
  | 212 => some (.leaf 137)
  | 213 => some (.leaf 138)
  | 214 => some (.leaf 139)
  | 215 => some (.leaf 140)
  | 216 => some (.leaf 141)
  | 217 => some (.leaf 142)
  | 218 => some (.positive 2 (![212, 213, 214, 215, 216, 217]))
  | 219 => some (.triangle 19 192 218)
  | 220 => some (.leaf 143)
  | 221 => some (.leaf 144)
  | 222 => some (.positive 1 (![210, 211, 219, 158, 220, 221]))
  | 223 => some (.triangle 18 170 222)
  | 224 => some (.triangle 16 209 223)
  | 225 => some (.positive 0 (![165, 168, 169, 180, 189, 224]))
  | 226 => some (.triangle 15 164 225)
  | 227 => some (.leaf 145)
  | 228 => some (.leaf 146)
  | 229 => some (.leaf 147)
  | 230 => some (.triangle 16 228 229)
  | 231 => some (.leaf 148)
  | 232 => some (.leaf 149)
  | 233 => some (.leaf 150)
  | 234 => some (.leaf 151)
  | 235 => some (.leaf 152)
  | 236 => some (.leaf 153)
  | 237 => some (.leaf 154)
  | 238 => some (.leaf 155)
  | 239 => some (.leaf 156)
  | 240 => some (.leaf 157)
  | 241 => some (.leaf 158)
  | 242 => some (.leaf 159)
  | 243 => some (.leaf 160)
  | 244 => some (.leaf 161)
  | 245 => some (.leaf 162)
  | 246 => some (.positive 2 (![240, 241, 242, 243, 244, 245]))
  | 247 => some (.positive 1 (![235, 236, 237, 238, 239, 246]))
  | 248 => some (.triangle 17 234 247)
  | 249 => some (.leaf 163)
  | 250 => some (.triangle 16 248 249)
  | 251 => some (.positive 0 (![227, 230, 231, 232, 233, 250]))
  | 252 => some (.triangle 14 226 251)
  | 253 => some (.leaf 164)
  | 254 => some (.leaf 165)
  | 255 => some (.triangle 18 37 254)
  | 256 => some (.triangle 16 36 255)
  | 257 => some (.leaf 166)
  | 258 => some (.leaf 167)
  | 259 => some (.leaf 168)
  | 260 => some (.leaf 169)
  | 261 => some (.leaf 170)
  | 262 => some (.leaf 171)
  | 263 => some (.leaf 172)
  | 264 => some (.leaf 173)
  | 265 => some (.leaf 174)
  | 266 => some (.leaf 175)
  | 267 => some (.leaf 176)
  | 268 => some (.positive 2 (![262, 263, 264, 265, 266, 267]))
  | 269 => some (.positive 1 (![257, 258, 259, 260, 261, 268]))
  | 270 => some (.leaf 177)
  | 271 => some (.triangle 17 269 270)
  | 272 => some (.leaf 178)
  | 273 => some (.leaf 179)
  | 274 => some (.leaf 180)
  | 275 => some (.triangle 17 274 270)
  | 276 => some (.leaf 181)
  | 277 => some (.leaf 182)
  | 278 => some (.positive 1 (![272, 273, 275, 158, 276, 277]))
  | 279 => some (.triangle 18 271 278)
  | 280 => some (.triangle 16 36 279)
  | 281 => some (.positive 0 (![253, 256, 41, 42, 43, 280]))
  | 282 => some (.leaf 183)
  | 283 => some (.leaf 184)
  | 284 => some (.leaf 185)
  | 285 => some (.triangle 18 283 284)
  | 286 => some (.triangle 16 36 285)
  | 287 => some (.leaf 186)
  | 288 => some (.leaf 187)
  | 289 => some (.leaf 188)
  | 290 => some (.leaf 189)
  | 291 => some (.leaf 190)
  | 292 => some (.positive 1 (![288, 289, 147, 148, 290, 291]))
  | 293 => some (.triangle 17 234 292)
  | 294 => some (.leaf 191)
  | 295 => some (.triangle 18 293 294)
  | 296 => some (.triangle 16 36 295)
  | 297 => some (.leaf 192)
  | 298 => some (.leaf 193)
  | 299 => some (.leaf 194)
  | 300 => some (.positive 1 (![297, 298, 147, 148, 149, 299]))
  | 301 => some (.triangle 17 234 300)
  | 302 => some (.leaf 195)
  | 303 => some (.leaf 196)
  | 304 => some (.leaf 197)
  | 305 => some (.leaf 198)
  | 306 => some (.leaf 199)
  | 307 => some (.leaf 200)
  | 308 => some (.leaf 201)
  | 309 => some (.leaf 202)
  | 310 => some (.leaf 203)
  | 311 => some (.leaf 204)
  | 312 => some (.leaf 205)
  | 313 => some (.positive 3 (![307, 308, 309, 310, 311, 312]))
  | 314 => some (.leaf 206)
  | 315 => some (.leaf 207)
  | 316 => some (.positive 2 (![304, 305, 306, 313, 314, 315]))
  | 317 => some (.leaf 208)
  | 318 => some (.triangle 19 316 317)
  | 319 => some (.leaf 209)
  | 320 => some (.positive 1 (![302, 303, 318, 158, 276, 319]))
  | 321 => some (.triangle 18 301 320)
  | 322 => some (.triangle 16 36 321)
  | 323 => some (.leaf 210)
  | 324 => some (.leaf 211)
  | 325 => some (.leaf 212)
  | 326 => some (.leaf 213)
  | 327 => some (.leaf 214)
  | 328 => some (.leaf 215)
  | 329 => some (.leaf 216)
  | 330 => some (.leaf 217)
  | 331 => some (.leaf 218)
  | 332 => some (.leaf 219)
  | 333 => some (.leaf 220)
  | 334 => some (.leaf 221)
  | 335 => some (.leaf 222)
  | 336 => some (.positive 3 (![330, 331, 332, 333, 334, 335]))
  | 337 => some (.positive 2 (![325, 326, 327, 328, 329, 336]))
  | 338 => some (.triangle 19 337 317)
  | 339 => some (.positive 1 (![323, 324, 147, 148, 149, 338]))
  | 340 => some (.triangle 17 234 339)
  | 341 => some (.leaf 223)
  | 342 => some (.leaf 224)
  | 343 => some (.leaf 225)
  | 344 => some (.leaf 226)
  | 345 => some (.positive 2 (![304, 305, 342, 343, 344, 315]))
  | 346 => some (.triangle 19 345 317)
  | 347 => some (.leaf 227)
  | 348 => some (.positive 1 (![341, 273, 346, 158, 276, 347]))
  | 349 => some (.triangle 18 340 348)
  | 350 => some (.triangle 16 36 349)
  | 351 => some (.positive 0 (![282, 286, 287, 296, 322, 350]))
  | 352 => some (.triangle 14 281 351)
  | 353 => some (.leaf 228)
  | 354 => some (.leaf 229)
  | 355 => some (.leaf 230)
  | 356 => some (.leaf 231)
  | 357 => some (.leaf 232)
  | 358 => some (.leaf 233)
  | 359 => some (.leaf 234)
  | 360 => some (.leaf 235)
  | 361 => some (.leaf 236)
  | 362 => some (.leaf 237)
  | 363 => some (.leaf 238)
  | 364 => some (.leaf 239)
  | 365 => some (.positive 3 (![359, 360, 361, 362, 363, 364]))
  | 366 => some (.leaf 240)
  | 367 => some (.leaf 241)
  | 368 => some (.positive 2 (![356, 357, 358, 365, 366, 367]))
  | 369 => some (.triangle 14 355 368)
  | 370 => some (.leaf 242)
  | 371 => some (.leaf 243)
  | 372 => some (.leaf 244)
  | 373 => some (.leaf 245)
  | 374 => some (.leaf 246)
  | 375 => some (.leaf 247)
  | 376 => some (.leaf 248)
  | 377 => some (.leaf 249)
  | 378 => some (.positive 3 (![372, 373, 374, 375, 376, 377]))
  | 379 => some (.triangle 14 371 378)
  | 380 => some (.leaf 250)
  | 381 => some (.leaf 251)
  | 382 => some (.leaf 252)
  | 383 => some (.leaf 253)
  | 384 => some (.positive 2 (![370, 379, 380, 381, 382, 383]))
  | 385 => some (.triangle 19 369 384)
  | 386 => some (.leaf 254)
  | 387 => some (.leaf 255)
  | 388 => some (.leaf 256)
  | 389 => some (.leaf 257)
  | 390 => some (.positive 1 (![354, 385, 386, 387, 388, 389]))
  | 391 => some (.triangle 18 170 390)
  | 392 => some (.triangle 16 36 391)
  | 393 => some (.leaf 258)
  | 394 => some (.leaf 259)
  | 395 => some (.leaf 260)
  | 396 => some (.leaf 261)
  | 397 => some (.positive 3 (![394, 360, 361, 362, 395, 396]))
  | 398 => some (.leaf 262)
  | 399 => some (.positive 2 (![356, 357, 358, 397, 366, 398]))
  | 400 => some (.triangle 14 355 399)
  | 401 => some (.leaf 263)
  | 402 => some (.leaf 264)
  | 403 => some (.leaf 265)
  | 404 => some (.positive 3 (![401, 373, 374, 375, 402, 403]))
  | 405 => some (.triangle 14 371 404)
  | 406 => some (.leaf 266)
  | 407 => some (.positive 2 (![370, 405, 380, 381, 382, 406]))
  | 408 => some (.triangle 19 400 407)
  | 409 => some (.leaf 267)
  | 410 => some (.leaf 268)
  | 411 => some (.leaf 269)
  | 412 => some (.positive 1 (![354, 393, 408, 409, 410, 411]))
  | 413 => some (.triangle 18 170 412)
  | 414 => some (.triangle 16 36 413)
  | 415 => some (.leaf 270)
  | 416 => some (.leaf 271)
  | 417 => some (.leaf 272)
  | 418 => some (.leaf 273)
  | 419 => some (.leaf 274)
  | 420 => some (.triangle 14 371 419)
  | 421 => some (.leaf 275)
  | 422 => some (.positive 2 (![418, 420, 380, 381, 382, 421]))
  | 423 => some (.triangle 19 417 422)
  | 424 => some (.leaf 276)
  | 425 => some (.leaf 277)
  | 426 => some (.positive 1 (![415, 416, 423, 158, 424, 425]))
  | 427 => some (.triangle 18 170 426)
  | 428 => some (.triangle 16 36 427)
  | 429 => some (.leaf 278)
  | 430 => some (.leaf 279)
  | 431 => some (.leaf 280)
  | 432 => some (.leaf 281)
  | 433 => some (.triangle 19 431 432)
  | 434 => some (.leaf 282)
  | 435 => some (.leaf 283)
  | 436 => some (.triangle 19 434 435)
  | 437 => some (.triangle 19 434 432)
  | 438 => some (.positive 1 (![430, 433, 436, 158, 220, 437]))
  | 439 => some (.triangle 18 170 438)
  | 440 => some (.triangle 16 36 439)
  | 441 => some (.positive 0 (![353, 392, 414, 428, 429, 440]))
  | 442 => some (.triangle 15 352 441)
  | 443 => some (.triangle 13 252 442)
  | 444 => some (.leaf 284)
  | 445 => some (.leaf 285)
  | 446 => some (.leaf 286)
  | 447 => some (.triangle 16 445 446)
  | 448 => some (.leaf 287)
  | 449 => some (.leaf 288)
  | 450 => some (.leaf 289)
  | 451 => some (.leaf 290)
  | 452 => some (.leaf 291)
  | 453 => some (.triangle 16 451 452)
  | 454 => some (.positive 0 (![444, 447, 448, 449, 450, 453]))
  | 455 => some (.leaf 292)
  | 456 => some (.leaf 293)
  | 457 => some (.leaf 294)
  | 458 => some (.leaf 295)
  | 459 => some (.leaf 296)
  | 460 => some (.leaf 297)
  | 461 => some (.leaf 298)
  | 462 => some (.positive 1 (![456, 457, 458, 459, 460, 461]))
  | 463 => some (.triangle 16 36 462)
  | 464 => some (.leaf 299)
  | 465 => some (.leaf 300)
  | 466 => some (.leaf 301)
  | 467 => some (.leaf 302)
  | 468 => some (.leaf 303)
  | 469 => some (.leaf 304)
  | 470 => some (.leaf 305)
  | 471 => some (.leaf 306)
  | 472 => some (.positive 1 (![467, 457, 468, 469, 470, 471]))
  | 473 => some (.triangle 16 36 472)
  | 474 => some (.positive 0 (![455, 463, 464, 465, 466, 473]))
  | 475 => some (.triangle 13 454 474)
  | 476 => some (.triangle 12 443 475)
  | 477 => some (.leaf 307)
  | 478 => some (.leaf 308)
  | 479 => some (.triangle 17 54 478)
  | 480 => some (.leaf 309)
  | 481 => some (.leaf 310)
  | 482 => some (.triangle 17 480 481)
  | 483 => some (.positive 0 (![477, 479, 57, 58, 59, 482]))
  | 484 => some (.leaf 311)
  | 485 => some (.leaf 312)
  | 486 => some (.leaf 313)
  | 487 => some (.leaf 314)
  | 488 => some (.leaf 315)
  | 489 => some (.leaf 316)
  | 490 => some (.leaf 317)
  | 491 => some (.positive 1 (![485, 486, 487, 488, 489, 490]))
  | 492 => some (.triangle 17 234 491)
  | 493 => some (.leaf 318)
  | 494 => some (.leaf 319)
  | 495 => some (.leaf 320)
  | 496 => some (.leaf 321)
  | 497 => some (.leaf 322)
  | 498 => some (.leaf 323)
  | 499 => some (.leaf 324)
  | 500 => some (.leaf 325)
  | 501 => some (.positive 1 (![496, 486, 497, 498, 499, 500]))
  | 502 => some (.triangle 17 234 501)
  | 503 => some (.positive 0 (![484, 492, 493, 494, 495, 502]))
  | 504 => some (.triangle 14 483 503)
  | 505 => some (.leaf 326)
  | 506 => some (.leaf 327)
  | 507 => some (.leaf 328)
  | 508 => some (.leaf 329)
  | 509 => some (.leaf 330)
  | 510 => some (.leaf 331)
  | 511 => some (.leaf 332)
  | 512 => some (.positive 1 (![506, 507, 508, 509, 510, 511]))
  | 513 => some (.leaf 333)
  | 514 => some (.triangle 18 512 513)
  | 515 => some (.leaf 334)
  | 516 => some (.leaf 335)
  | 517 => some (.leaf 336)
  | 518 => some (.leaf 337)
  | 519 => some (.leaf 338)
  | 520 => some (.leaf 339)
  | 521 => some (.leaf 340)
  | 522 => some (.leaf 341)
  | 523 => some (.positive 1 (![518, 507, 519, 520, 521, 522]))
  | 524 => some (.leaf 342)
  | 525 => some (.triangle 18 523 524)
  | 526 => some (.positive 0 (![505, 514, 515, 516, 517, 525]))
  | 527 => some (.triangle 12 504 526)
  | 528 => some (.leaf 343)
  | 529 => some (.leaf 344)
  | 530 => some (.leaf 345)
  | 531 => some (.triangle 18 529 530)
  | 532 => some (.leaf 346)
  | 533 => some (.leaf 347)
  | 534 => some (.leaf 348)
  | 535 => some (.leaf 349)
  | 536 => some (.triangle 18 535 530)
  | 537 => some (.positive 0 (![528, 531, 532, 533, 534, 536]))
  | 538 => some (.triangle 15 527 537)
  | 539 => some (.triangle 11 476 538)
  | 540 => some (.leaf 350)
  | 541 => some (.leaf 351)
  | 542 => some (.triangle 18 68 541)
  | 543 => some (.leaf 352)
  | 544 => some (.leaf 353)
  | 545 => some (.triangle 18 543 544)
  | 546 => some (.positive 0 (![540, 542, 71, 72, 73, 545]))
  | 547 => some (.leaf 354)
  | 548 => some (.leaf 355)
  | 549 => some (.leaf 356)
  | 550 => some (.leaf 357)
  | 551 => some (.leaf 358)
  | 552 => some (.leaf 359)
  | 553 => some (.leaf 360)
  | 554 => some (.positive 1 (![548, 549, 550, 551, 552, 553]))
  | 555 => some (.triangle 18 170 554)
  | 556 => some (.leaf 361)
  | 557 => some (.leaf 362)
  | 558 => some (.leaf 363)
  | 559 => some (.leaf 364)
  | 560 => some (.leaf 365)
  | 561 => some (.leaf 366)
  | 562 => some (.leaf 367)
  | 563 => some (.leaf 368)
  | 564 => some (.positive 1 (![559, 549, 560, 561, 562, 563]))
  | 565 => some (.triangle 18 170 564)
  | 566 => some (.positive 0 (![547, 555, 556, 557, 558, 565]))
  | 567 => some (.triangle 15 546 566)
  | 568 => some (.leaf 369)
  | 569 => some (.leaf 370)
  | 570 => some (.leaf 371)
  | 571 => some (.leaf 372)
  | 572 => some (.leaf 373)
  | 573 => some (.leaf 374)
  | 574 => some (.leaf 375)
  | 575 => some (.positive 1 (![569, 570, 571, 572, 573, 574]))
  | 576 => some (.leaf 376)
  | 577 => some (.triangle 17 575 576)
  | 578 => some (.leaf 377)
  | 579 => some (.leaf 378)
  | 580 => some (.leaf 379)
  | 581 => some (.leaf 380)
  | 582 => some (.leaf 381)
  | 583 => some (.leaf 382)
  | 584 => some (.leaf 383)
  | 585 => some (.leaf 384)
  | 586 => some (.positive 1 (![581, 570, 582, 583, 584, 585]))
  | 587 => some (.triangle 17 586 576)
  | 588 => some (.positive 0 (![568, 577, 578, 579, 580, 587]))
  | 589 => some (.triangle 12 567 588)
  | 590 => some (.leaf 385)
  | 591 => some (.leaf 386)
  | 592 => some (.leaf 387)
  | 593 => some (.positive 1 (![591, 81, 82, 83, 84, 592]))
  | 594 => some (.triangle 16 593 87)
  | 595 => some (.leaf 388)
  | 596 => some (.leaf 389)
  | 597 => some (.leaf 390)
  | 598 => some (.leaf 391)
  | 599 => some (.leaf 392)
  | 600 => some (.positive 1 (![595, 81, 596, 597, 598, 599]))
  | 601 => some (.triangle 16 600 87)
  | 602 => some (.positive 0 (![590, 594, 89, 90, 91, 601]))
  | 603 => some (.leaf 393)
  | 604 => some (.leaf 394)
  | 605 => some (.leaf 395)
  | 606 => some (.leaf 396)
  | 607 => some (.triangle 19 605 606)
  | 608 => some (.leaf 397)
  | 609 => some (.leaf 398)
  | 610 => some (.leaf 399)
  | 611 => some (.leaf 400)
  | 612 => some (.triangle 19 610 611)
  | 613 => some (.positive 1 (![604, 607, 608, 609, 612, 612]))
  | 614 => some (.triangle 18 613 524)
  | 615 => some (.triangle 17 614 576)
  | 616 => some (.triangle 16 615 87)
  | 617 => some (.leaf 401)
  | 618 => some (.leaf 402)
  | 619 => some (.leaf 403)
  | 620 => some (.leaf 404)
  | 621 => some (.leaf 405)
  | 622 => some (.leaf 406)
  | 623 => some (.leaf 407)
  | 624 => some (.leaf 408)
  | 625 => some (.leaf 409)
  | 626 => some (.leaf 410)
  | 627 => some (.positive 2 (![621, 622, 623, 624, 625, 626]))
  | 628 => some (.leaf 411)
  | 629 => some (.triangle 19 627 628)
  | 630 => some (.leaf 412)
  | 631 => some (.positive 1 (![618, 619, 620, 609, 629, 630]))
  | 632 => some (.leaf 413)
  | 633 => some (.triangle 18 631 632)
  | 634 => some (.leaf 414)
  | 635 => some (.triangle 17 633 634)
  | 636 => some (.triangle 16 635 87)
  | 637 => some (.leaf 415)
  | 638 => some (.leaf 416)
  | 639 => some (.leaf 417)
  | 640 => some (.leaf 418)
  | 641 => some (.leaf 419)
  | 642 => some (.leaf 420)
  | 643 => some (.leaf 421)
  | 644 => some (.leaf 422)
  | 645 => some (.leaf 423)
  | 646 => some (.leaf 424)
  | 647 => some (.leaf 425)
  | 648 => some (.leaf 426)
  | 649 => some (.leaf 427)
  | 650 => some (.positive 3 (![644, 645, 646, 647, 648, 649]))
  | 651 => some (.positive 2 (![641, 642, 643, 624, 625, 650]))
  | 652 => some (.leaf 428)
  | 653 => some (.leaf 429)
  | 654 => some (.leaf 430)
  | 655 => some (.leaf 431)
  | 656 => some (.leaf 432)
  | 657 => some (.leaf 433)
  | 658 => some (.leaf 434)
  | 659 => some (.leaf 435)
  | 660 => some (.leaf 436)
  | 661 => some (.positive 3 (![655, 656, 657, 658, 659, 660]))
  | 662 => some (.leaf 437)
  | 663 => some (.leaf 438)
  | 664 => some (.positive 2 (![652, 653, 654, 661, 662, 663]))
  | 665 => some (.triangle 19 651 664)
  | 666 => some (.leaf 439)
  | 667 => some (.positive 1 (![637, 638, 639, 640, 665, 666]))
  | 668 => some (.triangle 18 667 524)
  | 669 => some (.triangle 17 668 576)
  | 670 => some (.triangle 16 669 87)
  | 671 => some (.leaf 440)
  | 672 => some (.leaf 441)
  | 673 => some (.leaf 442)
  | 674 => some (.leaf 443)
  | 675 => some (.leaf 444)
  | 676 => some (.leaf 445)
  | 677 => some (.leaf 446)
  | 678 => some (.leaf 447)
  | 679 => some (.leaf 448)
  | 680 => some (.leaf 449)
  | 681 => some (.leaf 450)
  | 682 => some (.leaf 451)
  | 683 => some (.positive 3 (![679, 680, 681, 647, 648, 682]))
  | 684 => some (.positive 2 (![676, 677, 678, 624, 625, 683]))
  | 685 => some (.leaf 452)
  | 686 => some (.leaf 453)
  | 687 => some (.leaf 454)
  | 688 => some (.leaf 455)
  | 689 => some (.leaf 456)
  | 690 => some (.leaf 457)
  | 691 => some (.positive 3 (![688, 689, 690, 658, 659, 660]))
  | 692 => some (.leaf 458)
  | 693 => some (.positive 2 (![685, 686, 687, 691, 662, 692]))
  | 694 => some (.triangle 19 684 693)
  | 695 => some (.positive 1 (![671, 672, 673, 674, 675, 694]))
  | 696 => some (.triangle 18 695 524)
  | 697 => some (.triangle 17 696 576)
  | 698 => some (.triangle 16 697 87)
  | 699 => some (.positive 0 (![603, 616, 617, 636, 670, 698]))
  | 700 => some (.triangle 12 602 699)
  | 701 => some (.leaf 459)
  | 702 => some (.leaf 460)
  | 703 => some (.leaf 461)
  | 704 => some (.leaf 462)
  | 705 => some (.leaf 463)
  | 706 => some (.leaf 464)
  | 707 => some (.leaf 465)
  | 708 => some (.leaf 466)
  | 709 => some (.leaf 467)
  | 710 => some (.leaf 468)
  | 711 => some (.leaf 469)
  | 712 => some (.leaf 470)
  | 713 => some (.positive 2 (![707, 708, 709, 710, 711, 712]))
  | 714 => some (.triangle 19 192 713)
  | 715 => some (.leaf 471)
  | 716 => some (.positive 1 (![703, 704, 705, 706, 714, 715]))
  | 717 => some (.triangle 12 702 716)
  | 718 => some (.leaf 472)
  | 719 => some (.leaf 473)
  | 720 => some (.leaf 474)
  | 721 => some (.leaf 475)
  | 722 => some (.leaf 476)
  | 723 => some (.leaf 477)
  | 724 => some (.leaf 478)
  | 725 => some (.leaf 479)
  | 726 => some (.leaf 480)
  | 727 => some (.positive 3 (![721, 722, 723, 724, 725, 726]))
  | 728 => some (.triangle 12 720 727)
  | 729 => some (.leaf 481)
  | 730 => some (.leaf 482)
  | 731 => some (.leaf 483)
  | 732 => some (.positive 2 (![719, 728, 729, 730, 731, 712]))
  | 733 => some (.triangle 19 192 732)
  | 734 => some (.leaf 484)
  | 735 => some (.leaf 485)
  | 736 => some (.leaf 486)
  | 737 => some (.leaf 487)
  | 738 => some (.positive 1 (![718, 733, 734, 735, 736, 737]))
  | 739 => some (.triangle 18 717 738)
  | 740 => some (.triangle 17 739 576)
  | 741 => some (.triangle 16 740 87)
  | 742 => some (.leaf 488)
  | 743 => some (.leaf 489)
  | 744 => some (.leaf 490)
  | 745 => some (.leaf 491)
  | 746 => some (.leaf 492)
  | 747 => some (.leaf 493)
  | 748 => some (.leaf 494)
  | 749 => some (.leaf 495)
  | 750 => some (.leaf 496)
  | 751 => some (.leaf 497)
  | 752 => some (.positive 3 (![746, 747, 748, 749, 750, 751]))
  | 753 => some (.leaf 498)
  | 754 => some (.leaf 499)
  | 755 => some (.positive 2 (![743, 744, 745, 752, 753, 754]))
  | 756 => some (.triangle 19 192 755)
  | 757 => some (.leaf 500)
  | 758 => some (.positive 1 (![742, 704, 705, 706, 756, 757]))
  | 759 => some (.triangle 12 702 758)
  | 760 => some (.leaf 501)
  | 761 => some (.leaf 502)
  | 762 => some (.leaf 503)
  | 763 => some (.positive 1 (![760, 761, 734, 735, 736, 762]))
  | 764 => some (.triangle 18 759 763)
  | 765 => some (.leaf 504)
  | 766 => some (.triangle 17 764 765)
  | 767 => some (.leaf 505)
  | 768 => some (.triangle 16 766 767)
  | 769 => some (.leaf 506)
  | 770 => some (.leaf 507)
  | 771 => some (.leaf 508)
  | 772 => some (.leaf 509)
  | 773 => some (.positive 1 (![770, 771, 734, 735, 736, 772]))
  | 774 => some (.triangle 18 769 773)
  | 775 => some (.triangle 17 774 576)
  | 776 => some (.triangle 16 775 87)
  | 777 => some (.leaf 510)
  | 778 => some (.leaf 511)
  | 779 => some (.leaf 512)
  | 780 => some (.triangle 18 778 779)
  | 781 => some (.triangle 17 780 576)
  | 782 => some (.triangle 16 781 87)
  | 783 => some (.positive 0 (![701, 741, 768, 776, 777, 782]))
  | 784 => some (.triangle 15 700 783)
  | 785 => some (.triangle 11 589 784)
  | 786 => some (.leaf 513)
  | 787 => some (.leaf 514)
  | 788 => some (.leaf 515)
  | 789 => some (.triangle 17 787 788)
  | 790 => some (.leaf 516)
  | 791 => some (.leaf 517)
  | 792 => some (.leaf 518)
  | 793 => some (.leaf 519)
  | 794 => some (.triangle 17 793 788)
  | 795 => some (.positive 0 (![786, 789, 790, 791, 792, 794]))
  | 796 => some (.leaf 520)
  | 797 => some (.leaf 521)
  | 798 => some (.leaf 522)
  | 799 => some (.leaf 523)
  | 800 => some (.leaf 524)
  | 801 => some (.leaf 525)
  | 802 => some (.leaf 526)
  | 803 => some (.leaf 527)
  | 804 => some (.positive 2 (![798, 799, 800, 801, 802, 803]))
  | 805 => some (.leaf 528)
  | 806 => some (.leaf 529)
  | 807 => some (.leaf 530)
  | 808 => some (.leaf 531)
  | 809 => some (.positive 1 (![797, 804, 805, 806, 807, 808]))
  | 810 => some (.triangle 17 787 809)
  | 811 => some (.triangle 16 810 87)
  | 812 => some (.leaf 532)
  | 813 => some (.leaf 533)
  | 814 => some (.leaf 534)
  | 815 => some (.leaf 535)
  | 816 => some (.triangle 17 793 815)
  | 817 => some (.triangle 16 816 87)
  | 818 => some (.positive 0 (![796, 811, 812, 813, 814, 817]))
  | 819 => some (.triangle 11 795 818)
  | 820 => some (.triangle 14 785 819)
  | 821 => some (.leaf 536)
  | 822 => some (.leaf 537)
  | 823 => some (.triangle 16 822 102)
  | 824 => some (.positive 0 (![821, 103, 104, 105, 106, 823]))
  | 825 => some (.leaf 538)
  | 826 => some (.leaf 539)
  | 827 => some (.leaf 540)
  | 828 => some (.leaf 541)
  | 829 => some (.leaf 542)
  | 830 => some (.leaf 543)
  | 831 => some (.leaf 544)
  | 832 => some (.leaf 545)
  | 833 => some (.leaf 546)
  | 834 => some (.positive 2 (![828, 829, 830, 831, 832, 833]))
  | 835 => some (.leaf 547)
  | 836 => some (.leaf 548)
  | 837 => some (.leaf 549)
  | 838 => some (.leaf 550)
  | 839 => some (.positive 1 (![827, 834, 835, 836, 837, 838]))
  | 840 => some (.triangle 17 839 576)
  | 841 => some (.leaf 551)
  | 842 => some (.triangle 18 840 841)
  | 843 => some (.triangle 16 826 842)
  | 844 => some (.leaf 552)
  | 845 => some (.leaf 553)
  | 846 => some (.leaf 554)
  | 847 => some (.leaf 555)
  | 848 => some (.leaf 556)
  | 849 => some (.triangle 16 847 848)
  | 850 => some (.positive 0 (![825, 843, 844, 845, 846, 849]))
  | 851 => some (.triangle 12 824 850)
  | 852 => some (.leaf 557)
  | 853 => some (.leaf 558)
  | 854 => some (.leaf 559)
  | 855 => some (.leaf 560)
  | 856 => some (.leaf 561)
  | 857 => some (.leaf 562)
  | 858 => some (.leaf 563)
  | 859 => some (.leaf 564)
  | 860 => some (.leaf 565)
  | 861 => some (.leaf 566)
  | 862 => some (.leaf 567)
  | 863 => some (.leaf 568)
  | 864 => some (.leaf 569)
  | 865 => some (.positive 2 (![859, 860, 861, 862, 863, 864]))
  | 866 => some (.triangle 19 865 317)
  | 867 => some (.leaf 570)
  | 868 => some (.positive 1 (![855, 856, 857, 858, 866, 867]))
  | 869 => some (.triangle 12 854 868)
  | 870 => some (.leaf 571)
  | 871 => some (.triangle 18 869 870)
  | 872 => some (.triangle 11 853 871)
  | 873 => some (.leaf 572)
  | 874 => some (.triangle 17 872 873)
  | 875 => some (.leaf 573)
  | 876 => some (.leaf 574)
  | 877 => some (.leaf 575)
  | 878 => some (.leaf 576)
  | 879 => some (.leaf 577)
  | 880 => some (.leaf 578)
  | 881 => some (.leaf 579)
  | 882 => some (.leaf 580)
  | 883 => some (.leaf 581)
  | 884 => some (.leaf 582)
  | 885 => some (.leaf 583)
  | 886 => some (.leaf 584)
  | 887 => some (.leaf 585)
  | 888 => some (.leaf 586)
  | 889 => some (.positive 3 (![883, 884, 885, 886, 887, 888]))
  | 890 => some (.triangle 12 882 889)
  | 891 => some (.positive 2 (![877, 878, 879, 880, 881, 890]))
  | 892 => some (.triangle 19 891 317)
  | 893 => some (.leaf 587)
  | 894 => some (.leaf 588)
  | 895 => some (.leaf 589)
  | 896 => some (.leaf 590)
  | 897 => some (.positive 1 (![876, 892, 893, 894, 895, 896]))
  | 898 => some (.triangle 17 875 897)
  | 899 => some (.leaf 591)
  | 900 => some (.triangle 18 898 899)
  | 901 => some (.triangle 16 874 900)
  | 902 => some (.leaf 592)
  | 903 => some (.leaf 593)
  | 904 => some (.leaf 594)
  | 905 => some (.leaf 595)
  | 906 => some (.leaf 596)
  | 907 => some (.positive 2 (![904, 905, 879, 880, 881, 906]))
  | 908 => some (.leaf 597)
  | 909 => some (.triangle 19 907 908)
  | 910 => some (.leaf 598)
  | 911 => some (.positive 1 (![903, 909, 893, 894, 895, 910]))
  | 912 => some (.triangle 17 875 911)
  | 913 => some (.leaf 599)
  | 914 => some (.triangle 18 912 913)
  | 915 => some (.triangle 16 902 914)
  | 916 => some (.leaf 600)
  | 917 => some (.leaf 601)
  | 918 => some (.leaf 602)
  | 919 => some (.leaf 603)
  | 920 => some (.leaf 604)
  | 921 => some (.positive 2 (![918, 919, 879, 880, 881, 920]))
  | 922 => some (.triangle 19 921 317)
  | 923 => some (.leaf 605)
  | 924 => some (.positive 1 (![876, 922, 893, 894, 895, 923]))
  | 925 => some (.triangle 17 917 924)
  | 926 => some (.leaf 606)
  | 927 => some (.triangle 18 925 926)
  | 928 => some (.triangle 16 916 927)
  | 929 => some (.leaf 607)
  | 930 => some (.leaf 608)
  | 931 => some (.leaf 609)
  | 932 => some (.triangle 16 930 931)
  | 933 => some (.positive 0 (![852, 901, 915, 928, 929, 932]))
  | 934 => some (.triangle 14 851 933)
  | 935 => some (.leaf 610)
  | 936 => some (.leaf 611)
  | 937 => some (.leaf 612)
  | 938 => some (.leaf 613)
  | 939 => some (.leaf 614)
  | 940 => some (.leaf 615)
  | 941 => some (.leaf 616)
  | 942 => some (.leaf 617)
  | 943 => some (.triangle 19 941 942)
  | 944 => some (.leaf 618)
  | 945 => some (.positive 1 (![937, 938, 939, 940, 943, 944]))
  | 946 => some (.triangle 12 936 945)
  | 947 => some (.leaf 619)
  | 948 => some (.leaf 620)
  | 949 => some (.leaf 621)
  | 950 => some (.leaf 622)
  | 951 => some (.leaf 623)
  | 952 => some (.positive 1 (![947, 948, 949, 950, 736, 951]))
  | 953 => some (.triangle 18 946 952)
  | 954 => some (.triangle 11 853 953)
  | 955 => some (.triangle 17 954 873)
  | 956 => some (.leaf 624)
  | 957 => some (.leaf 625)
  | 958 => some (.leaf 626)
  | 959 => some (.leaf 627)
  | 960 => some (.leaf 628)
  | 961 => some (.leaf 629)
  | 962 => some (.positive 1 (![957, 958, 959, 960, 837, 961]))
  | 963 => some (.triangle 12 956 962)
  | 964 => some (.leaf 630)
  | 965 => some (.leaf 631)
  | 966 => some (.leaf 632)
  | 967 => some (.leaf 633)
  | 968 => some (.leaf 634)
  | 969 => some (.positive 1 (![964, 965, 966, 967, 895, 968]))
  | 970 => some (.triangle 17 963 969)
  | 971 => some (.leaf 635)
  | 972 => some (.leaf 636)
  | 973 => some (.leaf 637)
  | 974 => some (.triangle 19 972 973)
  | 975 => some (.leaf 638)
  | 976 => some (.leaf 639)
  | 977 => some (.leaf 640)
  | 978 => some (.leaf 641)
  | 979 => some (.positive 1 (![971, 974, 975, 976, 977, 978]))
  | 980 => some (.triangle 18 970 979)
  | 981 => some (.triangle 16 955 980)
  | 982 => some (.leaf 642)
  | 983 => some (.leaf 643)
  | 984 => some (.positive 1 (![947, 948, 949, 950, 736, 983]))
  | 985 => some (.triangle 18 982 984)
  | 986 => some (.triangle 11 853 985)
  | 987 => some (.triangle 17 986 873)
  | 988 => some (.leaf 644)
  | 989 => some (.leaf 645)
  | 990 => some (.positive 1 (![988, 974, 975, 976, 977, 989]))
  | 991 => some (.triangle 18 982 990)
  | 992 => some (.triangle 16 987 991)
  | 993 => some (.leaf 646)
  | 994 => some (.leaf 647)
  | 995 => some (.leaf 648)
  | 996 => some (.leaf 649)
  | 997 => some (.triangle 16 995 996)
  | 998 => some (.positive 0 (![935, 981, 992, 993, 994, 997]))
  | 999 => some (.triangle 15 934 998)
  | 1000 => some (.triangle 13 820 999)
  | 1001 => some (.triangle 10 539 1000)
  | 1002 => some (.leaf 650)
  | 1003 => some (.leaf 651)
  | 1004 => some (.leaf 652)
  | 1005 => some (.leaf 653)
  | 1006 => some (.leaf 654)
  | 1007 => some (.triangle 16 1005 1006)
  | 1008 => some (.leaf 655)
  | 1009 => some (.leaf 656)
  | 1010 => some (.leaf 657)
  | 1011 => some (.leaf 658)
  | 1012 => some (.leaf 659)
  | 1013 => some (.positive 0 (![1007, 1008, 1009, 1010, 1011, 1012]))
  | 1014 => some (.leaf 660)
  | 1015 => some (.triangle 15 1013 1014)
  | 1016 => some (.leaf 661)
  | 1017 => some (.triangle 14 1015 1016)
  | 1018 => some (.leaf 662)
  | 1019 => some (.leaf 663)
  | 1020 => some (.triangle 14 1018 1019)
  | 1021 => some (.leaf 664)
  | 1022 => some (.triangle 15 1020 1021)
  | 1023 => some (.triangle 13 1017 1022)
  | 1024 => some (.leaf 665)
  | 1025 => some (.triangle 12 1023 1024)
  | 1026 => some (.leaf 666)
  | 1027 => some (.triangle 11 1025 1026)
  | 1028 => some (.leaf 667)
  | 1029 => some (.leaf 668)
  | 1030 => some (.leaf 669)
  | 1031 => some (.triangle 12 1029 1030)
  | 1032 => some (.leaf 670)
  | 1033 => some (.triangle 15 1031 1032)
  | 1034 => some (.triangle 11 1028 1033)
  | 1035 => some (.triangle 14 1034 1016)
  | 1036 => some (.leaf 671)
  | 1037 => some (.triangle 14 1018 1036)
  | 1038 => some (.leaf 672)
  | 1039 => some (.triangle 15 1037 1038)
  | 1040 => some (.triangle 13 1035 1039)
  | 1041 => some (.triangle 10 1027 1040)
  | 1042 => some (.leaf 673)
  | 1043 => some (.leaf 674)
  | 1044 => some (.triangle 16 1042 1043)
  | 1045 => some (.positive 0 (![1007, 1008, 1009, 1010, 1011, 1044]))
  | 1046 => some (.leaf 675)
  | 1047 => some (.leaf 676)
  | 1048 => some (.triangle 16 1046 1047)
  | 1049 => some (.leaf 677)
  | 1050 => some (.leaf 678)
  | 1051 => some (.leaf 679)
  | 1052 => some (.leaf 680)
  | 1053 => some (.leaf 681)
  | 1054 => some (.positive 0 (![1048, 1049, 1050, 1051, 1052, 1053]))
  | 1055 => some (.triangle 15 1045 1054)
  | 1056 => some (.leaf 682)
  | 1057 => some (.triangle 14 1055 1056)
  | 1058 => some (.leaf 683)
  | 1059 => some (.leaf 684)
  | 1060 => some (.triangle 18 1058 1059)
  | 1061 => some (.triangle 16 36 1060)
  | 1062 => some (.leaf 685)
  | 1063 => some (.leaf 686)
  | 1064 => some (.leaf 687)
  | 1065 => some (.leaf 688)
  | 1066 => some (.leaf 689)
  | 1067 => some (.positive 0 (![1061, 1062, 1063, 1064, 1065, 1066]))
  | 1068 => some (.triangle 14 1018 1067)
  | 1069 => some (.leaf 690)
  | 1070 => some (.leaf 691)
  | 1071 => some (.triangle 19 1069 1070)
  | 1072 => some (.leaf 692)
  | 1073 => some (.leaf 693)
  | 1074 => some (.leaf 694)
  | 1075 => some (.leaf 695)
  | 1076 => some (.leaf 696)
  | 1077 => some (.positive 1 (![1071, 1072, 1073, 1074, 1075, 1076]))
  | 1078 => some (.triangle 18 170 1077)
  | 1079 => some (.triangle 16 36 1078)
  | 1080 => some (.leaf 697)
  | 1081 => some (.leaf 698)
  | 1082 => some (.leaf 699)
  | 1083 => some (.leaf 700)
  | 1084 => some (.leaf 701)
  | 1085 => some (.positive 0 (![1079, 1080, 1081, 1082, 1083, 1084]))
  | 1086 => some (.triangle 15 1068 1085)
  | 1087 => some (.triangle 13 1057 1086)
  | 1088 => some (.leaf 702)
  | 1089 => some (.triangle 12 1087 1088)
  | 1090 => some (.triangle 11 1089 1026)
  | 1091 => some (.leaf 703)
  | 1092 => some (.leaf 704)
  | 1093 => some (.leaf 705)
  | 1094 => some (.leaf 706)
  | 1095 => some (.leaf 707)
  | 1096 => some (.positive 1 (![604, 1091, 1092, 1093, 1094, 1095]))
  | 1097 => some (.triangle 18 1096 524)
  | 1098 => some (.triangle 17 1097 576)
  | 1099 => some (.triangle 16 1098 87)
  | 1100 => some (.leaf 708)
  | 1101 => some (.leaf 709)
  | 1102 => some (.leaf 710)
  | 1103 => some (.leaf 711)
  | 1104 => some (.leaf 712)
  | 1105 => some (.positive 0 (![1099, 1100, 1101, 1102, 1103, 1104]))
  | 1106 => some (.triangle 12 1029 1105)
  | 1107 => some (.leaf 713)
  | 1108 => some (.leaf 714)
  | 1109 => some (.triangle 18 1107 1108)
  | 1110 => some (.triangle 17 1109 576)
  | 1111 => some (.triangle 16 1110 87)
  | 1112 => some (.leaf 715)
  | 1113 => some (.leaf 716)
  | 1114 => some (.leaf 717)
  | 1115 => some (.leaf 718)
  | 1116 => some (.leaf 719)
  | 1117 => some (.positive 0 (![1111, 1112, 1113, 1114, 1115, 1116]))
  | 1118 => some (.triangle 15 1106 1117)
  | 1119 => some (.triangle 11 1028 1118)
  | 1120 => some (.triangle 14 1119 1056)
  | 1121 => some (.leaf 720)
  | 1122 => some (.leaf 721)
  | 1123 => some (.triangle 16 1121 1122)
  | 1124 => some (.leaf 722)
  | 1125 => some (.leaf 723)
  | 1126 => some (.leaf 724)
  | 1127 => some (.leaf 725)
  | 1128 => some (.leaf 726)
  | 1129 => some (.positive 0 (![1123, 1124, 1125, 1126, 1127, 1128]))
  | 1130 => some (.triangle 14 1018 1129)
  | 1131 => some (.leaf 727)
  | 1132 => some (.leaf 728)
  | 1133 => some (.triangle 16 1131 1132)
  | 1134 => some (.leaf 729)
  | 1135 => some (.leaf 730)
  | 1136 => some (.triangle 16 1134 1135)
  | 1137 => some (.leaf 731)
  | 1138 => some (.leaf 732)
  | 1139 => some (.leaf 733)
  | 1140 => some (.leaf 734)
  | 1141 => some (.positive 0 (![1133, 1136, 1137, 1138, 1139, 1140]))
  | 1142 => some (.triangle 15 1130 1141)
  | 1143 => some (.triangle 13 1120 1142)
  | 1144 => some (.triangle 10 1090 1143)
  | 1145 => some (.leaf 735)
  | 1146 => some (.leaf 736)
  | 1147 => some (.leaf 737)
  | 1148 => some (.leaf 738)
  | 1149 => some (.leaf 739)
  | 1150 => some (.leaf 740)
  | 1151 => some (.leaf 741)
  | 1152 => some (.leaf 742)
  | 1153 => some (.leaf 743)
  | 1154 => some (.leaf 744)
  | 1155 => some (.heavy (![2, 3, 4, 5, 115, 1001, 1002, 1003, 1004, 1041, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154]))
  | 1156 => some (.leaf 745)
  | 1157 => some (.leaf 746)
  | 1158 => some (.triangle 10 1156 1157)
  | 1159 => some (.leaf 747)
  | 1160 => some (.leaf 748)
  | 1161 => some (.leaf 749)
  | 1162 => some (.leaf 750)
  | 1163 => some (.leaf 751)
  | 1164 => some (.triangle 16 166 1163)
  | 1165 => some (.leaf 752)
  | 1166 => some (.leaf 753)
  | 1167 => some (.leaf 754)
  | 1168 => some (.leaf 755)
  | 1169 => some (.positive 1 (![1166, 172, 137, 138, 1167, 1168]))
  | 1170 => some (.triangle 18 1165 1169)
  | 1171 => some (.leaf 756)
  | 1172 => some (.triangle 17 1170 1171)
  | 1173 => some (.triangle 16 1172 1163)
  | 1174 => some (.leaf 757)
  | 1175 => some (.leaf 758)
  | 1176 => some (.positive 0 (![1162, 1164, 169, 1173, 1174, 1175]))
  | 1177 => some (.triangle 15 1161 1176)
  | 1178 => some (.leaf 759)
  | 1179 => some (.triangle 14 1177 1178)
  | 1180 => some (.leaf 760)
  | 1181 => some (.triangle 13 1179 1180)
  | 1182 => some (.leaf 761)
  | 1183 => some (.triangle 12 1181 1182)
  | 1184 => some (.leaf 762)
  | 1185 => some (.triangle 11 1183 1184)
  | 1186 => some (.leaf 763)
  | 1187 => some (.leaf 764)
  | 1188 => some (.leaf 765)
  | 1189 => some (.leaf 766)
  | 1190 => some (.positive 1 (![1187, 549, 550, 551, 1188, 1189]))
  | 1191 => some (.triangle 18 1165 1190)
  | 1192 => some (.leaf 767)
  | 1193 => some (.leaf 768)
  | 1194 => some (.positive 0 (![1186, 1191, 556, 557, 1192, 1193]))
  | 1195 => some (.triangle 15 1161 1194)
  | 1196 => some (.leaf 769)
  | 1197 => some (.triangle 12 1195 1196)
  | 1198 => some (.leaf 770)
  | 1199 => some (.triangle 11 1197 1198)
  | 1200 => some (.leaf 771)
  | 1201 => some (.triangle 14 1199 1200)
  | 1202 => some (.leaf 772)
  | 1203 => some (.triangle 13 1201 1202)
  | 1204 => some (.triangle 10 1185 1203)
  | 1205 => some (.leaf 773)
  | 1206 => some (.leaf 774)
  | 1207 => some (.leaf 775)
  | 1208 => some (.leaf 776)
  | 1209 => some (.leaf 777)
  | 1210 => some (.triangle 16 1046 1209)
  | 1211 => some (.leaf 778)
  | 1212 => some (.leaf 779)
  | 1213 => some (.leaf 780)
  | 1214 => some (.leaf 781)
  | 1215 => some (.leaf 782)
  | 1216 => some (.positive 0 (![1210, 1211, 1212, 1213, 1214, 1215]))
  | 1217 => some (.triangle 15 1161 1216)
  | 1218 => some (.leaf 783)
  | 1219 => some (.triangle 14 1217 1218)
  | 1220 => some (.leaf 784)
  | 1221 => some (.triangle 13 1219 1220)
  | 1222 => some (.leaf 785)
  | 1223 => some (.triangle 12 1221 1222)
  | 1224 => some (.leaf 786)
  | 1225 => some (.triangle 11 1223 1224)
  | 1226 => some (.leaf 787)
  | 1227 => some (.leaf 788)
  | 1228 => some (.triangle 11 1226 1227)
  | 1229 => some (.leaf 789)
  | 1230 => some (.triangle 14 1228 1229)
  | 1231 => some (.leaf 790)
  | 1232 => some (.triangle 13 1230 1231)
  | 1233 => some (.triangle 10 1225 1232)
  | 1234 => some (.leaf 791)
  | 1235 => some (.triangle 16 1046 1234)
  | 1236 => some (.leaf 792)
  | 1237 => some (.leaf 793)
  | 1238 => some (.positive 0 (![1235, 1211, 1212, 1213, 1236, 1237]))
  | 1239 => some (.triangle 15 1161 1238)
  | 1240 => some (.leaf 794)
  | 1241 => some (.triangle 14 1239 1240)
  | 1242 => some (.leaf 795)
  | 1243 => some (.triangle 13 1241 1242)
  | 1244 => some (.leaf 796)
  | 1245 => some (.triangle 12 1243 1244)
  | 1246 => some (.leaf 797)
  | 1247 => some (.triangle 11 1245 1246)
  | 1248 => some (.leaf 798)
  | 1249 => some (.triangle 11 1226 1248)
  | 1250 => some (.triangle 14 1249 1240)
  | 1251 => some (.leaf 799)
  | 1252 => some (.triangle 13 1250 1251)
  | 1253 => some (.triangle 10 1247 1252)
  | 1254 => some (.leaf 800)
  | 1255 => some (.leaf 801)
  | 1256 => some (.triangle 16 1046 1255)
  | 1257 => some (.leaf 802)
  | 1258 => some (.leaf 803)
  | 1259 => some (.triangle 16 1257 1258)
  | 1260 => some (.positive 0 (![1256, 1211, 1212, 1213, 1236, 1259]))
  | 1261 => some (.triangle 15 1254 1260)
  | 1262 => some (.triangle 14 1261 1240)
  | 1263 => some (.leaf 804)
  | 1264 => some (.leaf 805)
  | 1265 => some (.leaf 806)
  | 1266 => some (.leaf 807)
  | 1267 => some (.leaf 808)
  | 1268 => some (.leaf 809)
  | 1269 => some (.leaf 810)
  | 1270 => some (.leaf 811)
  | 1271 => some (.positive 2 (![1265, 1266, 1267, 1268, 1269, 1270]))
  | 1272 => some (.triangle 19 1264 1271)
  | 1273 => some (.leaf 812)
  | 1274 => some (.leaf 813)
  | 1275 => some (.leaf 814)
  | 1276 => some (.leaf 815)
  | 1277 => some (.positive 1 (![1272, 1273, 1274, 1074, 1275, 1276]))
  | 1278 => some (.triangle 18 1165 1277)
  | 1279 => some (.triangle 16 36 1278)
  | 1280 => some (.leaf 816)
  | 1281 => some (.leaf 817)
  | 1282 => some (.leaf 818)
  | 1283 => some (.leaf 819)
  | 1284 => some (.leaf 820)
  | 1285 => some (.positive 0 (![1279, 1280, 1281, 1282, 1283, 1284]))
  | 1286 => some (.triangle 15 1263 1285)
  | 1287 => some (.triangle 13 1262 1286)
  | 1288 => some (.triangle 12 1287 1244)
  | 1289 => some (.leaf 821)
  | 1290 => some (.triangle 11 1288 1289)
  | 1291 => some (.leaf 822)
  | 1292 => some (.leaf 823)
  | 1293 => some (.leaf 824)
  | 1294 => some (.leaf 825)
  | 1295 => some (.leaf 826)
  | 1296 => some (.positive 1 (![770, 1291, 1292, 1293, 1294, 1295]))
  | 1297 => some (.triangle 18 1165 1296)
  | 1298 => some (.triangle 17 1297 576)
  | 1299 => some (.triangle 16 1298 87)
  | 1300 => some (.leaf 827)
  | 1301 => some (.leaf 828)
  | 1302 => some (.leaf 829)
  | 1303 => some (.leaf 830)
  | 1304 => some (.leaf 831)
  | 1305 => some (.positive 0 (![1299, 1300, 1301, 1302, 1303, 1304]))
  | 1306 => some (.triangle 15 1263 1305)
  | 1307 => some (.triangle 11 1226 1306)
  | 1308 => some (.triangle 14 1307 1240)
  | 1309 => some (.leaf 832)
  | 1310 => some (.triangle 16 1309 1132)
  | 1311 => some (.leaf 833)
  | 1312 => some (.leaf 834)
  | 1313 => some (.triangle 16 1311 1312)
  | 1314 => some (.leaf 835)
  | 1315 => some (.leaf 836)
  | 1316 => some (.leaf 837)
  | 1317 => some (.leaf 838)
  | 1318 => some (.positive 0 (![1310, 1313, 1314, 1315, 1316, 1317]))
  | 1319 => some (.triangle 15 1263 1318)
  | 1320 => some (.triangle 13 1308 1319)
  | 1321 => some (.triangle 10 1290 1320)
  | 1322 => some (.leaf 839)
  | 1323 => some (.leaf 840)
  | 1324 => some (.leaf 841)
  | 1325 => some (.leaf 842)
  | 1326 => some (.leaf 843)
  | 1327 => some (.leaf 844)
  | 1328 => some (.leaf 845)
  | 1329 => some (.leaf 846)
  | 1330 => some (.leaf 847)
  | 1331 => some (.leaf 848)
  | 1332 => some (.heavy (![1158, 1159, 1160, 1204, 1205, 1206, 1207, 1208, 1233, 1253, 1321, 1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329, 1330, 1331]))
  | 1333 => some (.triangle 9 1155 1332)
  | 1334 => some (.leaf 849)
  | 1335 => some (.leaf 850)
  | 1336 => some (.triangle 10 1334 1335)
  | 1337 => some (.leaf 851)
  | 1338 => some (.leaf 852)
  | 1339 => some (.leaf 853)
  | 1340 => some (.leaf 854)
  | 1341 => some (.leaf 855)
  | 1342 => some (.leaf 856)
  | 1343 => some (.leaf 857)
  | 1344 => some (.leaf 858)
  | 1345 => some (.leaf 859)
  | 1346 => some (.leaf 860)
  | 1347 => some (.leaf 861)
  | 1348 => some (.triangle 16 1346 1347)
  | 1349 => some (.leaf 862)
  | 1350 => some (.leaf 863)
  | 1351 => some (.leaf 864)
  | 1352 => some (.leaf 865)
  | 1353 => some (.leaf 866)
  | 1354 => some (.positive 0 (![1348, 1349, 1350, 1351, 1352, 1353]))
  | 1355 => some (.triangle 14 1345 1354)
  | 1356 => some (.leaf 867)
  | 1357 => some (.triangle 13 1355 1356)
  | 1358 => some (.leaf 868)
  | 1359 => some (.triangle 12 1357 1358)
  | 1360 => some (.leaf 869)
  | 1361 => some (.triangle 11 1359 1360)
  | 1362 => some (.leaf 870)
  | 1363 => some (.leaf 871)
  | 1364 => some (.triangle 11 1362 1363)
  | 1365 => some (.triangle 14 1345 1364)
  | 1366 => some (.leaf 872)
  | 1367 => some (.triangle 13 1365 1366)
  | 1368 => some (.triangle 10 1361 1367)
  | 1369 => some (.leaf 873)
  | 1370 => some (.triangle 16 1346 1369)
  | 1371 => some (.leaf 874)
  | 1372 => some (.leaf 875)
  | 1373 => some (.triangle 16 1371 1372)
  | 1374 => some (.positive 0 (![1370, 1349, 1350, 1351, 1352, 1373]))
  | 1375 => some (.triangle 14 1345 1374)
  | 1376 => some (.leaf 876)
  | 1377 => some (.triangle 13 1375 1376)
  | 1378 => some (.triangle 12 1377 1358)
  | 1379 => some (.leaf 877)
  | 1380 => some (.triangle 11 1378 1379)
  | 1381 => some (.leaf 878)
  | 1382 => some (.leaf 879)
  | 1383 => some (.leaf 880)
  | 1384 => some (.leaf 881)
  | 1385 => some (.leaf 882)
  | 1386 => some (.leaf 883)
  | 1387 => some (.leaf 884)
  | 1388 => some (.positive 1 (![1382, 1383, 1384, 1385, 1386, 1387]))
  | 1389 => some (.triangle 17 1381 1388)
  | 1390 => some (.triangle 16 1389 87)
  | 1391 => some (.leaf 885)
  | 1392 => some (.leaf 886)
  | 1393 => some (.leaf 887)
  | 1394 => some (.leaf 888)
  | 1395 => some (.leaf 889)
  | 1396 => some (.positive 0 (![1390, 1391, 1392, 1393, 1394, 1395]))
  | 1397 => some (.triangle 11 1362 1396)
  | 1398 => some (.triangle 14 1345 1397)
  | 1399 => some (.leaf 890)
  | 1400 => some (.triangle 13 1398 1399)
  | 1401 => some (.triangle 10 1380 1400)
  | 1402 => some (.leaf 891)
  | 1403 => some (.leaf 892)
  | 1404 => some (.leaf 893)
  | 1405 => some (.leaf 894)
  | 1406 => some (.leaf 895)
  | 1407 => some (.leaf 896)
  | 1408 => some (.leaf 897)
  | 1409 => some (.leaf 898)
  | 1410 => some (.leaf 899)
  | 1411 => some (.leaf 900)
  | 1412 => some (.heavy (![1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1368, 1401, 1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411]))
  | 1413 => some (.triangle 8 1333 1412)
  | 1414 => some (.leaf 901)
  | 1415 => some (.leaf 902)
  | 1416 => some (.triangle 10 1414 1415)
  | 1417 => some (.leaf 903)
  | 1418 => some (.leaf 904)
  | 1419 => some (.leaf 905)
  | 1420 => some (.leaf 906)
  | 1421 => some (.leaf 907)
  | 1422 => some (.leaf 908)
  | 1423 => some (.leaf 909)
  | 1424 => some (.leaf 910)
  | 1425 => some (.leaf 911)
  | 1426 => some (.leaf 912)
  | 1427 => some (.leaf 913)
  | 1428 => some (.leaf 914)
  | 1429 => some (.triangle 18 1427 1428)
  | 1430 => some (.triangle 16 1426 1429)
  | 1431 => some (.leaf 915)
  | 1432 => some (.leaf 916)
  | 1433 => some (.leaf 917)
  | 1434 => some (.leaf 918)
  | 1435 => some (.leaf 919)
  | 1436 => some (.positive 0 (![1430, 1431, 1432, 1433, 1434, 1435]))
  | 1437 => some (.leaf 920)
  | 1438 => some (.triangle 14 1436 1437)
  | 1439 => some (.leaf 921)
  | 1440 => some (.triangle 15 1438 1439)
  | 1441 => some (.triangle 13 1425 1440)
  | 1442 => some (.leaf 922)
  | 1443 => some (.triangle 12 1441 1442)
  | 1444 => some (.leaf 923)
  | 1445 => some (.triangle 11 1443 1444)
  | 1446 => some (.leaf 924)
  | 1447 => some (.leaf 925)
  | 1448 => some (.triangle 12 1446 1447)
  | 1449 => some (.leaf 926)
  | 1450 => some (.triangle 14 1448 1449)
  | 1451 => some (.leaf 927)
  | 1452 => some (.triangle 15 1450 1451)
  | 1453 => some (.triangle 13 1425 1452)
  | 1454 => some (.triangle 10 1445 1453)
  | 1455 => some (.leaf 928)
  | 1456 => some (.triangle 18 1427 1455)
  | 1457 => some (.triangle 16 1426 1456)
  | 1458 => some (.leaf 929)
  | 1459 => some (.leaf 930)
  | 1460 => some (.triangle 18 1458 1459)
  | 1461 => some (.triangle 16 1426 1460)
  | 1462 => some (.positive 0 (![1457, 1431, 1432, 1433, 1434, 1461]))
  | 1463 => some (.leaf 931)
  | 1464 => some (.triangle 14 1462 1463)
  | 1465 => some (.leaf 932)
  | 1466 => some (.triangle 14 1465 1463)
  | 1467 => some (.leaf 933)
  | 1468 => some (.leaf 934)
  | 1469 => some (.leaf 935)
  | 1470 => some (.leaf 936)
  | 1471 => some (.positive 1 (![1466, 1467, 1468, 1074, 1469, 1470]))
  | 1472 => some (.triangle 18 170 1471)
  | 1473 => some (.triangle 16 1426 1472)
  | 1474 => some (.leaf 937)
  | 1475 => some (.leaf 938)
  | 1476 => some (.leaf 939)
  | 1477 => some (.leaf 940)
  | 1478 => some (.leaf 941)
  | 1479 => some (.positive 0 (![1473, 1474, 1475, 1476, 1477, 1478]))
  | 1480 => some (.triangle 15 1464 1479)
  | 1481 => some (.triangle 13 1425 1480)
  | 1482 => some (.leaf 942)
  | 1483 => some (.triangle 12 1481 1482)
  | 1484 => some (.triangle 11 1483 1444)
  | 1485 => some (.leaf 943)
  | 1486 => some (.leaf 944)
  | 1487 => some (.leaf 945)
  | 1488 => some (.leaf 946)
  | 1489 => some (.leaf 947)
  | 1490 => some (.leaf 948)
  | 1491 => some (.positive 1 (![1485, 1486, 1487, 1488, 1489, 1490]))
  | 1492 => some (.triangle 17 1491 576)
  | 1493 => some (.leaf 949)
  | 1494 => some (.triangle 18 1492 1493)
  | 1495 => some (.triangle 16 1426 1494)
  | 1496 => some (.leaf 950)
  | 1497 => some (.leaf 951)
  | 1498 => some (.leaf 952)
  | 1499 => some (.leaf 953)
  | 1500 => some (.leaf 954)
  | 1501 => some (.positive 0 (![1495, 1496, 1497, 1498, 1499, 1500]))
  | 1502 => some (.triangle 12 1446 1501)
  | 1503 => some (.leaf 955)
  | 1504 => some (.triangle 14 1502 1503)
  | 1505 => some (.leaf 956)
  | 1506 => some (.leaf 957)
  | 1507 => some (.triangle 18 1505 1506)
  | 1508 => some (.triangle 16 1426 1507)
  | 1509 => some (.leaf 958)
  | 1510 => some (.leaf 959)
  | 1511 => some (.triangle 18 1509 1510)
  | 1512 => some (.triangle 16 1426 1511)
  | 1513 => some (.leaf 960)
  | 1514 => some (.leaf 961)
  | 1515 => some (.leaf 962)
  | 1516 => some (.leaf 963)
  | 1517 => some (.positive 0 (![1508, 1512, 1513, 1514, 1515, 1516]))
  | 1518 => some (.triangle 15 1504 1517)
  | 1519 => some (.triangle 13 1425 1518)
  | 1520 => some (.triangle 10 1484 1519)
  | 1521 => some (.leaf 964)
  | 1522 => some (.leaf 965)
  | 1523 => some (.leaf 966)
  | 1524 => some (.leaf 967)
  | 1525 => some (.leaf 968)
  | 1526 => some (.leaf 969)
  | 1527 => some (.leaf 970)
  | 1528 => some (.leaf 971)
  | 1529 => some (.leaf 972)
  | 1530 => some (.leaf 973)
  | 1531 => some (.heavy (![1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1454, 1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530]))
  | 1532 => some (.leaf 974)
  | 1533 => some (.leaf 975)
  | 1534 => some (.triangle 10 1532 1533)
  | 1535 => some (.leaf 976)
  | _ => none

end Jsp404.SevenLowerBranchShard00
